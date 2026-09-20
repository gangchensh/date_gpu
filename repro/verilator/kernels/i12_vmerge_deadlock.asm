; kernel: i12_vmerge_deadlock
; ============================================================
; Target bug: I-12 [confirmed] masked vector instructions (vm=0 and all
; vmerge) deadlock in collectorUnit.
;
; Mechanism (doc/03-bug-reports.md I-12):
;   operandCollector.scala:214  mask read request rsTypeWire(3):=0.U;
;   operandCollector.scala:362-365  operandArbiter only grants rsType==1/2,
;   so the rsType=0 mask read request is never granted → ready(3) stays 0
;   → CU stuck in s_add forever → warp deadlocks, kernel never completes.
;   Decode side: DecodeUnit.scala:588 c.mask := ((~inst(25)) | alu_fn===
;   FN_VMERGE) & isvec & !disable_mask — vmerge forces mask=1.
;
; Triggering instruction: vmerge.vvm v1, v2, v3 (VMERGE_VVM row
;   DecodeUnit.lean:302, corresponding to DecodeUnit.scala:367; bit25(vm)=0
;   in encoding 0x5C2180D7).
;
; Verdict:
;   with bug: the warp deadlocks at vmerge → the kernel never finishes →
;     simulation ends with time_exceed (--sim-time-max reached); the canary
;     (0xDEAD0001) is written, the PASS word (0x600D0001) is not written,
;     mem[0x90000004] retains the sentinel 0xEEEEEEEE.
;   after fix: the kernel finishes normally, mem[0x90000004] = 0x600D0001.
; ============================================================

90000FB7  ; lui x31, 0x90000       ; x31 = result buffer base 0x90000000 (LUI, DecodeUnit.lean:145)
DEAD00B7  ; lui x1, 0xDEAD0        ; x1 = 0xDEAD0000
00108093  ; addi x1, x1, 1         ; x1 = 0xDEAD0001 (canary, proves the kernel is running)
001FA023  ; sw x1, 0(x31)          ; canary → mem[0x90000000] (SW, DecodeUnit.lean:142)
5C2180D7  ; vmerge.vvm v1, v2, v3  ; ← I-12 trigger (VMERGE_VVM, DecodeUnit.lean:302); unreachable after this with bug
600D0137  ; lui x2, 0x600D0        ; x2 = 0x600D0000
00110113  ; addi x2, x2, 1         ; x2 = 0x600D0001 (PASS word)
002FA223  ; sw x2, 4(x31)          ; PASS → mem[0x90000004]
0000400B  ; endprg                 ; ENDPRG, DecodeUnit.lean:393
