; kernel: i19_rem_stale_zeroq
; ============================================================
; Target bug: I-19 [confirmed] IntDivMod stale zeroQReg pollutes the
; remainder of an overflow transaction (cross-transaction timing dependency;
; a single transaction cannot expose it).
;
; Mechanism (doc/03 I-19): IntDivMod.scala:54 zeroQReg is only updated in
;   the s_pre cycle and has no reset; :77 specialR = Mux(divByZeroReg||
;   zeroQReg, rawAReg, 0.U). Overflow/divByZero transactions go from s_idle
;   straight to s_finish without s_pre, so zeroQReg keeps the previous
;   transaction's stale value.
;
; Transaction sequence (SFUexe processes scalar divisions serially via a
;   single queue, execution.scala:806+, so the two adjacent rems necessarily
;   land on consecutive transactions of the same IntDivMod instance):
;   txn1: rem 3, 5  → |a|<|d| → zeroQReg set to 1 (r=3 correct)
;   txn2: rem INT_MIN, -1 → overflow; RISC-V mandates r=0;
;         with bug r = stale zeroQReg(=1) ? rawAReg : 0 = 0x80000000
;   txn3: div INT_MIN, -1 → control: overflow quotient = 0x80000000 (same
;         in both versions; I-19 does not affect the quotient)
;
; Verdict: dump-mem
;   mem[0x90000000] = 3          (txn1 remainder, same in both versions, channel self-check)
;   mem[0x90000004]: correct = 0x00000000; with bug = 0x80000000
;   mem[0x90000008] = 0x80000000 (txn3 quotient, same in both versions, channel self-check)
; ============================================================

90000FB7  ; lui x31, 0x90000    ; x31 = result buffer base 0x90000000 (LUI, DecodeUnit.lean:145)
00300093  ; addi x1, x0, 3      ; x1 = 3 (ADDI, DecodeUnit.lean:146)
00500113  ; addi x2, x0, 5      ; x2 = 5
0220E233  ; rem x4, x1, x2      ; txn1: 3%5=3, sets zeroQReg=1 (REM, DecodeUnit.lean:171)
800000B7  ; lui x1, 0x80000     ; x1 = 0x80000000 = INT_MIN
FFF00113  ; addi x2, x0, -1     ; x2 = -1
0220E2B3  ; rem x5, x1, x2      ; ← I-19 trigger: txn2 overflow (REM)
0220C333  ; div x6, x1, x2      ; txn3 control: q = INT_MIN (DIV, DecodeUnit.lean:169)
004FA023  ; sw x4, 0(x31)       ; txn1 r → mem[0x90000000] (SW, DecodeUnit.lean:142)
005FA223  ; sw x5, 4(x31)       ; txn2 r → mem[0x90000004]
006FA423  ; sw x6, 8(x31)       ; txn3 q → mem[0x90000008]
0000400B  ; endprg              ; ENDPRG, DecodeUnit.lean:393
