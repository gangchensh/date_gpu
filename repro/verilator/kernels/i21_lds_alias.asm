; kernel: i21_lds_alias
; ldsSize: 0x20000
; ============================================================
; Target bug: I-21 [confirmed] ShareMem request setIdx is only 8 bits; the
; upper 96KB of the LDS aliases the low 32KB byte by byte.
;
; Mechanism (doc/03 I-21): LSU.scala:171,216 use dcache_SetIdxBits=8-bit
;   setIdx, while SharedMemory NSets=1024 needs 10 bits → LDS address bits
;   addr(16:15) are dropped, so the high region [LDS_BASE+32KB, +128KB)
;   aliases the low 32KB. LDS_BASE = 0x70000000 (parameters.scala:136);
;   sharemem_size = 128KB (parameters.scala:93-97). This kernel's metadata
;   ldsSize=0x20000 (128KB, =NUM_LDS_MAX) to obtain the high-region
;   allocation.
;
; Sequence (isomorphic to the Lean witness smI21_witness):
;   t0: [0x70000040]       ← 0x11111111 (low-region write)
;   t1: [0x70008040]       ← 0x22222222 (high-region write, +32KB; with bug
;                            the alias overwrites the same low-region SRAM row)
;   t2: x3 ← [0x70000040]  (low-region read: correct = 0x11111111;
;                            with bug = 0x22222222)
;
; Verdict: dump-mem mem[0x90000000]: correct = 0x11111111; with bug = 0x22222222.
; ============================================================

90000FB7  ; lui x31, 0x90000     ; x31 = result buffer base 0x90000000 (LUI, DecodeUnit.lean:145)
70000537  ; lui x10, 0x70000     ; x10 = LDS_BASE = 0x70000000
111110B7  ; lui x1, 0x11111      ; x1 = 0x11111000
11108093  ; addi x1, x1, 0x111   ; x1 = 0x11111111 (ADDI, DecodeUnit.lean:146)
04152023  ; sw x1, 0x40(x10)     ; t0 low-region write [0x70000040] (SW, DecodeUnit:142)
22222137  ; lui x2, 0x22222      ; x2 = 0x22222000
22210113  ; addi x2, x2, 0x222   ; x2 = 0x22222222
700085B7  ; lui x11, 0x70008     ; x11 = 0x70008000
04058593  ; addi x11, x11, 0x40  ; x11 = 0x70008040 (high region, LDS_BASE+32KB+0x40)
0025A023  ; sw x2, 0(x11)        ; t1 high-region write [0x70008040]
04052183  ; lw x3, 0x40(x10)     ; t2 low-region read x3 ← [0x70000040] (LW, DecodeUnit.lean:137)
003FA023  ; sw x3, 0(x31)        ; result → mem[0x90000000]
0000400B  ; endprg               ; ENDPRG, DecodeUnit.lean:393
