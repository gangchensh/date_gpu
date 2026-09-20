; kernel: i16_amo_nop
; ============================================================
; Target bug: I-16 [confirmed (mechanism)] IDecodeLUT_A is dead code; all
; LR/SC/AMO silently decode to NOP.
;
; Mechanism (doc/03 I-16): the AMO decode table at DecodeUnit.scala:453-468
;   is never referenced by the outer table select at :556-568 → AMOADD_W
;   (opcode 0101111) falls into the IMF table, which has no such row →
;   decodes to the default row (alu_fn=63, no writeback, no memory access).
;
; This kernel: mem[0x90000010] initial value 5, executes amoadd.w +7, then
;   reads back.
;   correct: AMO takes effect → reads back 12 (0x0000000C)
;   with bug: AMO silently NOPs → reads back 5 (0x00000005)
;
; Verdict (two levels of evidence, either one confirms):
;   1. dump-mem: mem[0x90000004] (read-back value) and mem[0x90000010]
;      (target cell) are both 0x00000005 with bug, both 0x0000000C correct.
;   2. verilate.mk passes --assert: the issue-stage assertion at
;      pipe.scala:276-287 (alu_fn =/= 63.U, "UNDEFINED INSTRUCTION") fires
;      when the AMO is issued and the simulation aborts with an error —
;      that abort itself is direct evidence of I-16.
;      (The assertion firing and the dump-mem verdict may be observable
;      only one at a time; both are expected detection paths.)
;   Note: mem[0x90000000] is the amoadd rd (old-value read-back); with bug
;      the instruction has no writeback and the register holds a random
;      initial value — this word does not participate in the verdict.
; ============================================================

90000FB7  ; lui x31, 0x90000         ; x31 = result buffer base 0x90000000 (LUI, DecodeUnit.lean:145)
010F8513  ; addi x10, x31, 0x10      ; x10 = 0x90000010 (AMO target address, ADDI, DecodeUnit.lean:146)
00500093  ; addi x1, x0, 5           ; x1 = 5
00152023  ; sw x1, 0(x10)            ; mem[0x90000010] = 5 (SW, DecodeUnit.lean:142)
00700113  ; addi x2, x0, 7           ; x2 = 7
002521AF  ; amoadd.w x3, x2, (x10)   ; ← I-16 trigger (AMOADD_W, Instructions.scala:19; dead table DecodeUnit.scala:453-468)
00052203  ; lw x4, 0(x10)            ; x4 = mem[0x90000010] (LW, DecodeUnit.lean:137)
003FA023  ; sw x3, 0(x31)            ; AMO old-value read-back (random value with bug, not judged)
004FA223  ; sw x4, 4(x31)            ; read-back value → mem[0x90000004]
0000400B  ; endprg                   ; ENDPRG, DecodeUnit.lean:393
