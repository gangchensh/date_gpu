#!/usr/bin/env bash
# ==============================================================================
# run.sh — Ventus GPGPU Verilator channel bug reproduction package:
# environment check + build + run + verdict
#
# ⚠️ All artifacts of this package are "ready-to-run"; the authoring
# environment has no verilator/mill, so they were NOT executed here.
#
# Usage:
#   ./run.sh check          # environment prerequisite check only
#   ./run.sh build          # check + build libVentusRTL.so and sim-VentusRTL
#   ./run.sh run [kernel…]  # run the specified kernels (default: all), judge each
#   ./run.sh all            # check + build + run (default action)
#
# Environment variables:
#   VENTUS_REPO  path to the ventus-gpgpu repository
#                (default <project root>/opengpgpu/original/ventus-gpgpu)
#   RELEASE=0    use a Debug build (default Release=1)
# ==============================================================================
set -u
cd "$(dirname "$0")"
REPRO_DIR="$(pwd)"
ROOT_DIR="$(cd "$REPRO_DIR/../.." && pwd)"
VENTUS_REPO="${VENTUS_REPO:-$ROOT_DIR/opengpgpu/original/ventus-gpgpu}"
SIMVER_DIR="$VENTUS_REPO/sim-verilator"
RELEASE="${RELEASE:-1}"

KERNELS="k00_smoke i12_vmerge_deadlock i15_mulhsu_low32 i16_amo_nop \
i17_divu_cnt_trunc i18_rem_recovery i19_rem_stale_zeroq \
i21_lds_alias i32_fcsr_write_dropped i33_vl_dead"

say()  { printf '[run.sh] %s\n' "$*"; }
fail() { printf '[run.sh][ERROR] %s\n' "$*" >&2; exit 1; }

# ------------------------------------------------------- environment check ----
check_env() {
    say "== environment prerequisite check =="
    [ -d "$VENTUS_REPO" ] || fail "ventus repository not found: $VENTUS_REPO (set VENTUS_REPO)"
    [ -d "$SIMVER_DIR" ]  || fail "sim-verilator directory not found: $SIMVER_DIR"

    if command -v verilator >/dev/null 2>&1; then
        local vver; vver="$(verilator --version 2>/dev/null | grep -o '[0-9]\+\.[0-9]\+' | head -1)"
        say "verilator: $(verilator --version)"
        # sim-verilator/README.md requires >= 5.026, 5.034 recommended
        if [ -n "$vver" ]; then
            local vmaj vmin; vmaj="${vver%%.*}"; vmin="${vver##*.}"
            if [ "$vmaj" -lt 5 ] || { [ "$vmaj" -eq 5 ] && [ "$vmin" -lt 26 ]; }; then
                say "WARNING: verilator $vver is below the required 5.026; build/run may fail"
            fi
        fi
    else
        fail "verilator not on PATH (requires >= 5.026, 5.034 recommended; see sim-verilator/README.md)"
    fi

    if [ -x "$VENTUS_REPO/mill" ]; then
        say "mill: $VENTUS_REPO/mill"
    elif command -v mill >/dev/null 2>&1; then
        say "mill: $(command -v mill) (note: verilate.mk hard-codes a call to ../mill, may need adjustment)"
    else
        fail "mill not found ($VENTUS_REPO/mill). You also need to fetch the ventus/dependencies submodules and the Chisel dependencies (this package's authoring environment could not, due to network restrictions; see doc/13 §2.3)"
    fi

    command -v g++ >/dev/null 2>&1 || fail "g++ not on PATH"
    command -v make >/dev/null 2>&1 || fail "make not on PATH"
    command -v python3 >/dev/null 2>&1 || say "hint: no python3 (only needed by kernels/regen.py when regenerating images)"

    if command -v pkg-config >/dev/null 2>&1; then
        pkg-config --exists spdlog || fail "missing spdlog (apt install libspdlog-dev)"
        pkg-config --exists fmt    || fail "missing fmt (apt install libfmt-dev)"
        say "spdlog/fmt: OK"
    else
        say "hint: no pkg-config, skipping spdlog/fmt check (if linking fails with -lspdlog/-lfmt, install them)"
    fi
    say "environment check passed"
}

# ------------------------------------------------------------------- build ----
# Build chain (corresponding to sim-verilator/verilate.mk:145-166 and the Makefile):
#   1. cd ventus && ./mill ventus[6.4.0].runMain top.emitVerilog
#      → generates GPGPU_SimTop.v, renamed to sim-verilator/dut.v (+ parameters.json)
#   2. verilator -cc --build dut.v + C++ wrapper → libVdut.a
#   3. linked into libVentusRTL.so (-lspdlog -lfmt ...)
#   4. the Makefile then builds the mini driver: build/driver_example/{debug,release}/sim-VentusRTL
build_sim() {
    check_env
    say "== build (RELEASE=$RELEASE, output under sim-verilator/build/) =="
    if [ "$RELEASE" = "1" ]; then
        make -C "$SIMVER_DIR" RELEASE=1 -j"$(nproc)" || fail "build failed"
    else
        make -C "$SIMVER_DIR" -j"$(nproc)" || fail "build failed"
    fi
}

sim_bin() {
    if [ "$RELEASE" = "1" ]; then
        echo "$SIMVER_DIR/build/driver_example/release/sim-VentusRTL"
    else
        echo "$SIMVER_DIR/build/driver_example/debug/sim-VentusRTL"
    fi
}

# ------------------------------------------------------------------ verdict ---
# Extract the dump-mem value at a given address from the log (uppercase hex,
# no 0x prefix)
get_word() { # $1=log file $2=address (uppercase hex)
    sed -n "s/^dump-mem: mem\[0x$2 +: 4\] = 0x\([0-9A-Fa-f]*\).*/\1/p" "$1" | tail -1 | tr a-f A-F
}

judge() { # $1=kernel name $2=log file
    local k="$1" log="$2" w0 w4 w8 fin
    w0="$(get_word "$log" 90000000)"
    w4="$(get_word "$log" 90000004)"
    w8="$(get_word "$log" 90000008)"
    fin="$(grep -c "kernel.* $k finished" "$log")"
    case "$k" in
    k00_smoke)
        # channel self-check: bug-independent, both should PASS
        [ "$w0" = "600D600D" ] && [ "$fin" -ge 1 ] \
            && { say "$k: channel OK (PASS word + finished)"; return 0; }
        say "$k: [ENVIRONMENT/IMAGE ANOMALY] w0=$w0 finished=$fin — fix the channel before judging bugs"; return 2 ;;
    i12_vmerge_deadlock)
        if [ "$fin" -eq 0 ] && [ "$w0" = "DEAD0001" ] && [ "$w4" = "EEEEEEEE" ]; then
            say "$k: [I-12 REPRODUCED] kernel never finished (deadlocked until sim-time-max), canary written, PASS word not written"; return 0
        elif [ "$fin" -ge 1 ] && [ "$w4" = "600D0001" ]; then
            say "$k: not reproduced (kernel completed normally) — I-12 may already be fixed"; return 1
        fi ;;
    i15_mulhsu_low32)
        [ "$w0" = "00000001" ] && { say "$k: [I-15 REPRODUCED] mulhsu returned the low 32 bits (0x00000001), expected 0xFFFFFFFF"; return 0; }
        [ "$w0" = "FFFFFFFF" ] && { say "$k: not reproduced (result correct)"; return 1; } ;;
    i16_amo_nop)
        if grep -qi "UNDEFINED INSTRUCTION\|Assertion" "$log"; then
            say "$k: [I-16 REPRODUCED] issue-stage assertion fired (AMO decoded to the default row alu_fn=63)"; return 0
        fi
        [ "$w4" = "00000005" ] && { say "$k: [I-16 REPRODUCED] AMO silently NOPed: read back 5 instead of 12"; return 0; }
        [ "$w4" = "0000000C" ] && { say "$k: not reproduced (AMO took effect)"; return 1; } ;;
    i17_divu_cnt_trunc)
        [ "$w0" = "00000001" ] && { say "$k: [I-17 REPRODUCED] 0x80000000/1 quotient = 1, expected 0x80000000"; return 0; }
        [ "$w0" = "80000000" ] && { say "$k: not reproduced (quotient correct)"; return 1; } ;;
    i18_rem_recovery)
        [ "$w4" = "00000005" ] && [ "$w0" = "00000001" ] && { say "$k: [I-18 REPRODUCED] 4%3 remainder = 5 (quotient=1 correct), expected 1"; return 0; }
        [ "$w4" = "00000001" ] && { say "$k: not reproduced (remainder correct)"; return 1; } ;;
    i19_rem_stale_zeroq)
        [ "$w4" = "80000000" ] && [ "$w0" = "00000003" ] && [ "$w8" = "80000000" ] \
            && { say "$k: [I-19 REPRODUCED] after 3/5, INT_MIN%-1 remainder = 0x80000000 (stale zeroQReg), expected 0"; return 0; }
        [ "$w4" = "00000000" ] && { say "$k: not reproduced (remainder correct)"; return 1; } ;;
    i21_lds_alias)
        [ "$w0" = "22222222" ] && { say "$k: [I-21 REPRODUCED] LDS high-region write overwrote the low region: read back 0x22222222, expected 0x11111111"; return 0; }
        [ "$w0" = "11111111" ] && { say "$k: not reproduced (no high/low region alias)"; return 1; } ;;
    i32_fcsr_write_dropped)
        [ "$w0" = "00000000" ] && { say "$k: [I-32 REPRODUCED] csrrw fcsr dropped, read back 0, expected 0x000000E5"; return 0; }
        [ "$w0" = "000000E5" ] && { say "$k: not reproduced (fcsr write took effect)"; return 1; } ;;
    i33_vl_dead)
        [ "$w4" = "00000000" ] && [ "$w0" = "00000020" ] \
            && { say "$k: [I-33 REPRODUCED] vsetvli wrote back 32 but vl reads 0 (dead state), expected 0x20"; return 0; }
        [ "$w4" = "00000020" ] && { say "$k: not reproduced (vl readable)"; return 1; } ;;
    esac
    say "$k: [VERDICT FAILED/INDETERMINATE] w0=$w0 w4=$w4 w8=$w8 finished=$fin — review $log manually"
    return 2
}

# --------------------------------------------------------------------- run ----
run_kernels() {
    local sim; sim="$(sim_bin)"
    [ -x "$sim" ] || fail "simulator not found: $sim (run ./run.sh build first)"
    local list="${*:-$KERNELS}" rc=0
    mkdir -p "$REPRO_DIR/logs"
    for k in $list; do
        local args="$REPRO_DIR/kernels/$k.ventus_args.txt"
        local log="$REPRO_DIR/logs/$k.log"
        [ -f "$args" ] || fail "missing argument file: $args"
        say "== running $k =="
        # at -f parse time the CWD switches to the argument file's directory,
        # so the relative metafile/datafile paths resolve there
        "$sim" -f "$args" >"$log" 2>&1
        judge "$k" "$log" || rc=1
    done
    say "logs in $REPRO_DIR/logs/"
    return $rc
}

case "${1:-all}" in
    check) check_env ;;
    build) build_sim ;;
    run)   shift; run_kernels "$@" ;;
    all)   build_sim && run_kernels ;;
    *)     fail "unknown action: $1 (check|build|run|all)" ;;
esac
