; kernel: i17_divu_cnt_trunc
; ============================================================
; Target bug: I-17 [confirmed] IntDivMod cnt width truncation: dividing a
; large dividend by 1 gives a completely wrong quotient.
;
; Mechanism (doc/03 I-17): IntDivMod.scala:56 cnt has only log2Up(32)=5
;   bits, while :46 iter = dLez-aLez+1 can reach 32 (a 6-bit value);
;   :118 cnt:=iter truncates to 0 → only 1 iteration runs (should be 32).
;
; Test vector: DIVU 0x80000000 / 1 (aLez=0 and dLez=31 → iter=32).
;   correct quotient = 0x80000000; with bug quotient = 0x00000001 (r is 0
;   in both versions, not judged).
;
; Verdict: dump-mem mem[0x90000000]: correct = 0x80000000; with bug = 0x00000001.
; ============================================================

90000FB7  ; lui x31, 0x90000    ; x31 = result buffer base 0x90000000 (LUI, DecodeUnit.lean:145)
800000B7  ; lui x1, 0x80000     ; x1 = 0x80000000 (dividend, MSB set)
00100113  ; addi x2, x0, 1      ; x2 = 1 (divisor, ADDI, DecodeUnit.lean:146)
0220D1B3  ; divu x3, x1, x2     ; ← I-17 trigger (DIVU, DecodeUnit.lean:170)
003FA023  ; sw x3, 0(x31)       ; quotient → mem[0x90000000] (SW, DecodeUnit.lean:142)
0000400B  ; endprg              ; ENDPRG, DecodeUnit.lean:393
