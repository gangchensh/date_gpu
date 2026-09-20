; kernel: i32_fcsr_write_dropped
; ============================================================
; Target bug: I-32 [confirmed] fcsr (0x003) is in the read table but has no
; branch in the write chain, so csrrw/csrrs fcsr are silently dropped.
;
; Mechanism (doc/03 I-32): the CSR.scala read Lookup table (around :254)
;   contains BitPat(CSR.fcsr)->fcsr, but the write chain (the when/elsewhen
;   chain at :257-295) only has separate branches for fflags(0x001) and
;   frm(0x002), no fcsr branch → writes to fcsr are dropped and the read
;   returns the old value.
;
; Sequence: x1 = 0xE5 (frm=111, fflags=00101); csrrw fcsr ← x1;
;   csrrs reads fcsr back.
;   correct: reads back 0x000000E5; with bug: reads back 0x00000000 (reset
;   value).
;
; Verdict: dump-mem mem[0x90000000]: correct = 0x000000E5; with bug = 0x00000000.
; ============================================================

90000FB7  ; lui x31, 0x90000     ; x31 = result buffer base 0x90000000 (LUI, DecodeUnit.lean:145)
0E500093  ; addi x1, x0, 0xE5    ; x1 = 0xE5 (ADDI, DecodeUnit.lean:146)
00309173  ; csrrw x2, fcsr, x1   ; ← I-32 trigger: write fcsr (CSRRW, DecodeUnit.lean:130)
003021F3  ; csrrs x3, fcsr, x0   ; read fcsr back (CSRRS, DecodeUnit.lean:131)
003FA023  ; sw x3, 0(x31)        ; result → mem[0x90000000] (SW, DecodeUnit.lean:142)
0000400B  ; endprg               ; ENDPRG, DecodeUnit.lean:393
