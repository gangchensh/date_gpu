; kernel: i18_rem_recovery
; ============================================================
; Target bug: I-18 [confirmed] IntDivMod remainder recovery truncates
; before adding; the remainder is systematically too large when remIsNeg.
;
; Mechanism (doc/03 I-18): IntDivMod.scala:70 recoveryR = Mux(remIsNeg,
;   aReg.tail(1).head(32)+dReg.tail(1).head(32), ...) — the two 34-bit
;   addends are each truncated before being added, so the sign bit of the
;   negative partial remainder is dropped. The quotient is unaffected; the
;   remainder is wrong if and only if remIsNeg=1.
;
; Test vector: 4 / 3 (triggers the remIsNeg path).
;   correct: q = 1, r = 1
;   with bug: q = 1 (quotient correct, serves as control), r = 5
;
; Verdict: dump-mem mem[0x90000000] (q, always = 1, channel self-check) and
;   mem[0x90000004] (r): correct = 0x00000001; with bug = 0x00000005.
; ============================================================

90000FB7  ; lui x31, 0x90000    ; x31 = result buffer base 0x90000000 (LUI, DecodeUnit.lean:145)
00400093  ; addi x1, x0, 4      ; x1 = 4 (ADDI, DecodeUnit.lean:146)
00300113  ; addi x2, x0, 3      ; x2 = 3
0220C233  ; div x4, x1, x2      ; control: q = 1 (DIV, DecodeUnit.lean:169; I-18 does not affect the quotient)
0220E1B3  ; rem x3, x1, x2      ; ← I-18 trigger (REM, DecodeUnit.lean:171)
004FA023  ; sw x4, 0(x31)       ; q → mem[0x90000000] (SW, DecodeUnit.lean:142)
003FA223  ; sw x3, 4(x31)       ; r → mem[0x90000004]
0000400B  ; endprg              ; ENDPRG, DecodeUnit.lean:393
