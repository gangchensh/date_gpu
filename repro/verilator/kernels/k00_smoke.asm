; kernel: k00_smoke
; ============================================================
; Smoke test (not tied to any bug): verifies that the .metadata/.data image
; format, the loading chain, kernel execution, and the dump-mem verdict
; channel itself all work. If this test fails, the problem is the
; environment/image format, not a target bug.
;
; Encoding basis: the decode table rows of lean/Ventus/Arith/DecodeUnit.lean
; (each BitPat verified by (mask,value) hit); standard RISC-V instruction
; formats.
;
; Expected (correct and buggy hardware behave identically):
;   the log shows "kernel 0 k00_smoke finished"
;   dump-mem: mem[0x90000000] = 0x600D600D
; ============================================================

90000FB7  ; lui x31, 0x90000    ; x31 = result buffer base 0x90000000 (LUI, DecodeUnit.lean:145)
600D60B7  ; lui x1, 0x600D6     ; x1 = 0x600D6000
00D08093  ; addi x1, x1, 0xD    ; x1 = 0x600D600D (ADDI, DecodeUnit.lean:146)
001FA023  ; sw x1, 0(x31)       ; write PASS word (SW, DecodeUnit.lean:142)
0000400B  ; endprg              ; end this warp (ENDPRG, DecodeUnit.lean:393, encoding per :613 regression)
