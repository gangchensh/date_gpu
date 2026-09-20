# repro/verilator — Ventus GPGPU Verilator channel bug reproduction package

> **Status: EXECUTED 2026-09-07** — channel built and all 10 kernels run on the
> snapshot 6811725 RTL (verilator 5.034 built from source; spdlog/fmt/mold via a
> local apt-download prefix). Results: k00_smoke OK; I-12/15/16/17/19/21/32/33
> reproduced; I-18 not reproduced. Full verdicts and build notes:
> `doc/22-复现执行结果.md` (Verilator section); per-kernel logs: `logs/`.
> (The §4 gap list below is the historical record of the authoring environment.)
> Target bugs and mechanisms: `doc/03-bug-reports.md`; reproduction tiering:
> doc/13 (reproduction analysis report).
> This package covers Tier-A (instruction-level) entries: I-12, I-15, I-16,
> I-17, I-18, I-19, I-21, I-32, I-33.

## 1. Principle and layout

Uses the whole-chip RTL simulator `sim-VentusRTL` from
`opengpgpu/original/ventus-gpgpu/sim-verilator/`: hand-assembled minimal
kernels are packaged into `.metadata`+`.data` images (same format as the
official `testcase/vecadd`), loaded and executed by the mini driver, and the
result buffer is read back with `--dump-mem` for verdict.

```
repro/verilator/
├── run.sh                 # env check + build + run + auto verdict (bash)
├── README.md              # this file
├── logs/                  # generated at run time, one log per kernel
└── kernels/
    ├── regen.py           # .asm → .data/.metadata generator (already run,
    │                      #   artifacts committed)
    ├── <name>.asm         # hand-assembled source: each line = 8-hex-digit
    │                      #   instruction word + comment (comments cite the
    │                      #   DecodeUnit.lean line numbers justifying the
    │                      #   encoding)
    ├── <name>.data        # image data (code section + result buffer, hex)
    ├── <name>.metadata    # kernel metadata (hex, format in §3)
    └── <name>.ventus_args.txt  # sim-VentusRTL command-line arguments
```

Kernel list (one minimal kernel per bug, plus 1 channel self-check):

| Kernel | Target bug | Triggering instruction | Verdict anchor |
|---|---|---|---|
| `k00_smoke` | — (channel self-check) | sw/endprg | mem[0x90000000]=0x600D600D + finished |
| `i12_vmerge_deadlock` | I-12 masked-instruction deadlock | `vmerge.vvm v1,v2,v3` | no finished + canary written + PASS not written |
| `i15_mulhsu_low32` | I-15 MULHSU returns low 32 bits | `mulhsu x3,x1,x2` (a=b=0xFFFFFFFF) | 0x00000001 (bug) vs 0xFFFFFFFF |
| `i16_amo_nop` | I-16 AMO silently NOPs | `amoadd.w x3,x2,(x10)` | read-back 5 (bug) vs 12; or assertion abort |
| `i17_divu_cnt_trunc` | I-17 cnt truncation | `divu` 0x80000000/1 | quotient 1 (bug) vs 0x80000000 |
| `i18_rem_recovery` | I-18 remainder truncated-then-added | `rem` 4/3 | remainder 5 (bug) vs 1 (quotient=1 in both versions, self-check) |
| `i19_rem_stale_zeroq` | I-19 stale zeroQReg | rem 3/5 then rem INT_MIN/-1 | remainder 0x80000000 (bug) vs 0 |
| `i21_lds_alias` | I-21 LDS high-region alias | sw 0x70008040 then read 0x70000040 | 0x22222222 (bug) vs 0x11111111 |
| `i32_fcsr_write_dropped` | I-32 fcsr write dropped | `csrrw fcsr` then read back | 0 (bug) vs 0x000000E5 |
| `i33_vl_dead` | I-33 vl dead state | `vsetvli` then `csrrs vl` | 0 (bug) vs 0x20 |

Conventions: all kernels are single workgroup / single warp / 32 threads;
code section @0x80000000; result buffer @0x90000000 (16 words, image
pre-filled with sentinel 0xEEEEEEEE to distinguish "not written" from
"written 0"); terminating instruction `endprg` (0x0000400B,
DecodeUnit.lean:393).

## 2. Run manual

Prerequisites (the checks performed by `run.sh check`):

- Verilator ≥ 5.026 (5.034 recommended), g++, make, (optional mold/ccache)
- spdlog and fmt development libraries (`apt install libspdlog-dev libfmt-dev`)
- Full checkout of the ventus repository (**including `dependencies/`
  submodules**) with mill able to resolve the Chisel dependencies (needs
  network or a pre-populated coursier cache)

```bash
cd repro/verilator
./run.sh check        # environment check only
./run.sh build        # build libVentusRTL.so + sim-VentusRTL
./run.sh run          # run all 10 kernels and judge each
./run.sh run i15_mulhsu_low32   # run one specific kernel
./run.sh all          # all of the above (default)
```

`./run.sh build` is equivalent to `make -C <ventus>/sim-verilator RELEASE=1 -j`;
its internal chain (verilate.mk:145-166):

1. `cd ventus && ./mill ventus[6.4.0].runMain top.emitVerilog`
   → generates `GPGPU_SimTop.v`, renamed to `sim-verilator/dut.v`
   (+ `parameters.json`);
2. `verilator -cc --build` (with `--assert --trace-fst -DRANDOMIZE` etc.,
   see verilate.mk:88-137) compiles dut.v + C++ wrapper into `libVdut.a`;
3. links `libVentusRTL.so` (-lspdlog -lfmt -pthread -lz -latomic);
4. the top-level Makefile then builds the mini driver
   `build/driver_example/release/sim-VentusRTL`.

Run a single kernel manually (bypassing run.sh):

```bash
<ventus>/sim-verilator/build/driver_example/release/sim-VentusRTL \
    -f repro/verilator/kernels/i15_mulhsu_low32.ventus_args.txt
# watch the dump-mem lines and the "kernel 0 <name> finished" log
```

The verdict is per run.sh output; for manual review see the
`dump-mem: mem[0x........ +: 4] = 0x........` lines in `logs/<name>.log`
(sim_main.cpp:99-102). Expected-vs-actual per bug: §1 table and the header
comments of each .asm.

### Per-bug notes

- **I-12** (deadlock): the correctness criterion is "timeout + not finished",
  not a value. With the bug the warp deadlocks at vmerge and the simulation
  runs to `--sim-time-max 20000`; the log has no finished, the canary
  (0xDEAD0001) is written, and the PASS word retains the sentinel. With the
  fix the kernel completes normally and mem[0x90000004]=0x600D0001.
- **I-16** (AMO): verilate.mk:110 passes `--assert`, so the Chisel issue-stage
  assertion (pipe.scala:276-287, `alu_fn =/= 63.U`) may fire when the AMO is
  issued and abort the simulation — that abort itself is direct evidence of
  I-16. If the assertion does not abort the simulation (build-config
  differences), judge by value: the AMO has no effect, read-back is the
  initial value 5. mem[0x90000000] is the amoadd rd (old-value read-back);
  with the bug this instruction has no writeback so the value is the
  register's random initial value — **it does not participate in the verdict**.
- **I-19** (cross-transaction): relies on "a preceding division (|a|<|d|)
  immediately followed by the overflow division entering the same IntDivMod
  instance". Scalar divisions are processed serially via the single SFUexe
  queue (execution.scala:806+), and all instances start each transaction
  simultaneously (in.valid broadcast), so the sequence necessarily holds.
- **I-21** (LDS): the kernel metadata has `ldsSize=0x20000`
  (128KB=NUM_LDS_MAX); the high/low region addresses are built around
  LDS_BASE=0x70000000 (parameters.scala:136) ±32KB.

## 3. Image format (conclusions from reviewing sim-verilator sources)

- `.metadata`: kernel.cpp `readHexFile(itemSize=64)`+`assignMetadata`.
  Each 64-bit field = two lines of 8-hex-digit words, **low 32 bits first,
  then high 32 bits**; field order = startaddr, kernel_id, kernel_size[3],
  wf_size, wg_size, metaDataBaseAddr, ldsSize, pdsSize, sgprUsage, vgprUsage,
  pdsBaseAddr, num_buffer, buffer_base[], buffer_size[],
  buffer_allocsize[]. **The file may contain hex only** (any other character
  triggers an "Invalid character" message).
- `.data`: sim_main.cpp `kernel_load_data_callback`. In num_buffer order,
  each buffer has exactly buffer_size/4 lines, each line 8 hex digits = one
  32-bit word, written to physical memory **little-endian**. In this package
  buffer[0] = code section @0x80000000, buffer[1] = result buffer
  @0x90000000 (16 words of sentinel 0xEEEEEEEE).
- Argument file `-f`: cmdarg.cpp `parse_arg`, `#` starts a comment; at parse
  time the CWD is switched to the argument file's directory, so relative
  filenames suffice for metafile/datafile.

After modifying a kernel, regenerate the images:
`cd kernels && python3 regen.py` (the .asm is the single source of truth;
the generator includes an endprg termination check).

## 4. Environment gaps (why "not executed in this environment")

Measured in the authoring environment (2026-08-31):

- `verilator` exists but is 5.020, **below the required 5.026** (run.sh will
  warn);
- the `mill` launcher works (JVM 21), but the ventus `dependencies/`
  submodules are **not checked out** (`./mill resolve` reports missing
  common.sc from rocket-chip/hardfloat/fpuv2 etc.; fetching fails due to
  network restrictions — the same gap recorded in doc/13 §2.3);
- the spdlog/fmt development libraries are missing.

Remediation (on a networked machine):

```bash
cd opengpgpu/original/ventus-gpgpu
git submodule update --init --recursive   # fetch dependencies/
sudo apt install verilator libspdlog-dev libfmt-dev   # verilator >= 5.026
cd repro/verilator && ./run.sh all
```

## 5. Limitations

- The encodings are hand-assembled. A script checked each instruction against
  the BitPat (mask,value) entries of DecodeUnit.lean to confirm it hits the
  expected decode line (including the dead-table pattern of AMOADD_W,
  Instructions.scala:19), and a Python re-implementation of the loader
  semantics checked .data/.metadata consistency; but they have **not been
  verified by a real assembler/simulator** — if the simulator reports a
  decode anomaly, suspect this package's encodings first.
- Tier-B timing-class bugs (I-5/I-6/I-7, I-25, the cache family, etc.) are
  not covered — whole-chip software stimulus can hardly construct the
  same-cycle events in a directed way; those entries stay on the ChiselSim
  channel (repro/*.scala).
- I-34 (ICache invalidate tied off) is relevant to this channel (multiple
  kernels reusing the same address), but the sim-verilator driver loads each
  kernel through an exclusive flow, so it is not a target of this package.
