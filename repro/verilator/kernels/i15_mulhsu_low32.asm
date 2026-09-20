; kernel: i15_mulhsu_low32
; ============================================================
; Target bug: I-15 [confirmed] ArrayMultiplier high-half select misses
; FN_MULHSU, so MULHSU returns the low 32 bits of the product.
;
; Mechanism (doc/03 I-15): Multiplier.scala:204-205 the high-half select
;   condition only has FN_MULH|FN_MULHU, missing FN_MULHSU(23) → MULHSU
;   falls into the low-half branch.
;
; Test vector: a = b = 0xFFFFFFFF (i.e. x1 as signed -1, x2 as unsigned max).
;   64-bit true product = 0xFFFFFFFF_00000001
;   correct MULHSU (high 32 bits) = 0xFFFFFFFF
;   with bug (returns low 32 bits) = 0x00000001
;
; Verdict: dump-mem mem[0x90000000]: correct = 0xFFFFFFFF; with bug = 0x00000001.
; ============================================================

90000FB7  ; lui x31, 0x90000    ; x31 = result buffer base 0x90000000 (LUI, DecodeUnit.lean:145)
FFF00093  ; addi x1, x0, -1     ; x1 = 0xFFFFFFFF (ADDI, DecodeUnit.lean:146)
FFF00113  ; addi x2, x0, -1     ; x2 = 0xFFFFFFFF
0220A1B3  ; mulhsu x3, x1, x2   ; ← I-15 trigger (MULHSU, DecodeUnit.lean:167, funct3=010)
003FA023  ; sw x3, 0(x31)       ; result → mem[0x90000000] (SW, DecodeUnit.lean:142)
0000400B  ; endprg              ; ENDPRG, DecodeUnit.lean:393
