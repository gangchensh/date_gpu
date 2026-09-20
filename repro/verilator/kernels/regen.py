#!/usr/bin/env python3
"""regen.py — generate sim-verilator image files (.data/.metadata) from
kernels/*.asm.

Image format (from a line-by-line review of sim-verilator/kernel.cpp +
sim_main.cpp):

.metadata (kernel.cpp readHexFile(itemSize=64) + assignMetadata):
  Each 64-bit field = two lines of 8-hex-digit words, low 32 bits first,
  then high 32 bits; field order = startaddr, kernel_id, kernel_size[3],
  wf_size, wg_size, metaDataBaseAddr, ldsSize, pdsSize, sgprUsage,
  vgprUsage, pdsBaseAddr, num_buffer, buffer_base[], buffer_size[],
  buffer_allocsize[]. The file may contain hex only (any other character
  triggers an "Invalid character" message).

.data (sim_main.cpp kernel_load_data_callback):
  In num_buffer order, each buffer has exactly buffer_size/4 lines, each
  line 8 hex digits = one 32-bit word (written to physical memory
  little-endian). This package's layout: buffer[0] = code section
  @0x80000000; buffer[1] = result buffer @0x90000000, 16 words, all
  pre-filled with sentinel 0xEEEEEEEE (to distinguish "not written" from
  "written 0").

.asm source format: each instruction line = 8-hex-digit word + ';' comment;
  the header line '; kernel: <name>' is mandatory, '; ldsSize: 0x...' is
  optional (default 0).
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

CODE_BASE = 0x80000000   # code-section physical address = metadata.startaddr
RESULT_BASE = 0x90000000  # result-buffer physical address
SENTINEL = 0xEEEEEEEE
RESULT_WORDS = 16         # result-buffer word count (buffer_size[1] = 64 bytes)

METADATA_COMMON = dict(
    kernel_id=0,
    kernel_size=(1, 1, 1),  # single workgroup
    wf_size=32,             # 32 threads per warp (parameters.scala num_thread=32)
    wg_size=1,              # single warp
    metaDataBaseAddr=0x90404000,  # only written to CSR knl_base; this package's kernels never read it
    pdsSize=0,
    sgprUsage=32,
    vgprUsage=32,
    pdsBaseAddr=0x90004000,
)


def parse_asm(path: Path):
    """Return (kernel_name, ldsSize, [instruction words...])."""
    name, lds_size, words = None, 0, []
    for lineno, raw in enumerate(path.read_text().splitlines(), 1):
        line = raw.strip()
        if not line:
            continue
        m = re.match(r"^;\s*kernel:\s*(\S+)", line)
        if m:
            name = m.group(1)
            continue
        m = re.match(r"^;\s*ldsSize:\s*(0x[0-9a-fA-F]+|\d+)", line)
        if m:
            lds_size = int(m.group(1), 0)
            continue
        if line.startswith(";"):
            continue
        token = line.split()[0]
        if not re.fullmatch(r"[0-9a-fA-F]{8}", token):
            sys.exit(f"{path}:{lineno}: illegal instruction line: {raw!r}")
        words.append(int(token, 16))
    if name is None:
        sys.exit(f"{path}: missing '; kernel: <name>' header directive")
    if not words or words[-1] != 0x0000400B:
        sys.exit(f"{path}: the last instruction must be endprg (0x0000400B)")
    return name, lds_size, words


def write_metadata(path: Path, lds_size: int, code_bytes: int):
    c = METADATA_COMMON
    fields = [
        CODE_BASE, c["kernel_id"], *c["kernel_size"], c["wf_size"], c["wg_size"],
        c["metaDataBaseAddr"], lds_size, c["pdsSize"], c["sgprUsage"],
        c["vgprUsage"], c["pdsBaseAddr"],
        2,  # num_buffer
        CODE_BASE, RESULT_BASE,                    # buffer_base
        code_bytes, RESULT_WORDS * 4,              # buffer_size
        0x1000, 0x1000,                            # buffer_allocsize
    ]
    lines = []
    for f in fields:
        lines.append(f"{f & 0xFFFFFFFF:08x}")       # low 32 bits
        lines.append(f"{(f >> 32) & 0xFFFFFFFF:08x}")  # high 32 bits
    path.write_text("\n".join(lines) + "\n")


def write_data(path: Path, words):
    lines = [f"{w:08x}" for w in words]
    lines += [f"{SENTINEL:08x}"] * RESULT_WORDS
    path.write_text("\n".join(lines) + "\n")


def main():
    for asm in sorted(HERE.glob("*.asm")):
        name, lds_size, words = parse_asm(asm)
        write_metadata(asm.with_suffix(".metadata"), lds_size, len(words) * 4)
        write_data(asm.with_suffix(".data"), words)
        print(f"{name}: {len(words)} instructions, ldsSize={lds_size:#x}")


if __name__ == "__main__":
    main()
