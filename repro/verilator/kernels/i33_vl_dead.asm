; kernel: i33_vl_dead
; ============================================================
; Target bug: I-33 [confirmed] the vector CSR state (vl/vstart/vcsr/vlenb/
; vxrm/vxsat) is entirely dead state.
;
; Mechanism (doc/03 I-33): CSR.scala:262-264 the isvec write branch only
;   changes the writeback data to min(AVL,VLMAX); the vl register is never
;   written; and addresses like vl(0xC20) are not in the read Lookup table
;   → reading vl takes the default 0.U.
;
; Sequence: vsetvli x2, x1(=32), e32,m1 → x2 = min(32,32) = 32 (this
;   writeback path works, serves as control); csrrs reads vl.
;   correct (RVV semantics): vl = 32 = 0x20; with bug: vl reads back 0.
;
; Verdict: dump-mem
;   mem[0x90000000] = 0x00000020 (vsetvli writeback, same in both versions, channel self-check)
;   mem[0x90000004]: correct = 0x00000020; with bug = 0x00000000
; ============================================================

90000FB7  ; lui x31, 0x90000       ; x31 = result buffer base 0x90000000 (LUI, DecodeUnit.lean:145)
02000093  ; addi x1, x0, 32        ; x1 = AVL = 32 (ADDI, DecodeUnit.lean:146)
0100F157  ; vsetvli x2, x1, e32,m1 ; x2 = min(AVL,32) = 32 (VSETVLI, DecodeUnit.lean:350; vtypei=0x010)
C20021F3  ; csrrs x3, vl, x0       ; ← I-33 trigger: read vl (CSRRS, DecodeUnit.lean:131; vl=0xC20, CSR.scala:49)
002FA023  ; sw x2, 0(x31)          ; vsetvli writeback → mem[0x90000000] (SW, DecodeUnit.lean:142)
003FA223  ; sw x3, 4(x31)          ; vl read-back → mem[0x90000004]
0000400B  ; endprg                 ; ENDPRG, DecodeUnit.lean:393
