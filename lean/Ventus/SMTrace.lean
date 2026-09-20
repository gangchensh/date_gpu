/- ========================================================================= -/
/-                        SMTrace.lean（探测/轨迹文件，不挂 Ventus.lean）       -/
/-  SM 组合骨架（Ventus/SM.lean）上的长轨迹/多 warp 端到端验证。               -/
/-                                                                           -/
/-  场景（全部 native_decide，单遍折叠监控，一次求值出全部结论）：             -/
/-  S1 多 warp：warp0/1/2 三个 warp（wg0/1/2，sgpr_base=0/128/256 物理隔离）， -/
/-     并发执行各自程序，验证写回互不串扰（bank/地址隔离 + 值正确）与          -/
/-     取指/发射在 warp 间轮换。                                              -/
/-  S2 循环程序：warp0 是 10 次计数累加循环（回跳 bne），x1 期望 55、x2=73。  -/
/-  S3 分支分化/汇合：vbranch/join 属 issueV 通路，SM.lean D4/D6 为           -/
/-     ready=false 的 stub（branch_join 每拍喂 nop），该场景**无法构造**       -/
/-     （障碍记录见文件末尾）。改测标量分支双向覆盖：bne 回跳 taken/不        -/
/-     taken、beq 前跳 taken/not-taken、恒真 beq 冲刷后继指令。               -/
/-  S4 endprg 收尾：warp_active 清除、endprgCnt 清空、wgValid 经 flush 回收。 -/
/-  S5 不变式监控：全程每拍断言（见 smtInvAt）：                               -/
/-     (a) WsState 五个 Array 字段尺寸恒 8；                                  -/
/-     (b) 记分板 opColX(w) ⟺ ∃CU 被 warp w 占用；                            -/
/-     (c) 记分板 beqReg(w) ⟺ ∃CU 持有 w 的分支/barrier 指令（在途分支）；    -/
/-     (d) 记分板 scalarReg(w,a)（a≤31）⟺ ∃CU 持有 w 的写 a 指令。            -/
/-     依据：i2iXFire 同拍置 sb 位且 CU 接受；ocOutXFire 同拍清 sb 位且 CU    -/
/-     释放（D3：CU→sALU→wb 同拍组合，无延迟错拍）。                          -/
/-                                                                           -/
/-  机器码全部为真实 RV32（+ ventus 自定义 endprg 0x0000400B），立即数经       -/
/-  RegFile.lean 的 rfImmGen 回归钉死（smtD_* 系列）。                         -/
/- ========================================================================= -/

import Ventus.SM

namespace Ventus

open Ventus.Schedule Ventus.SIMT Ventus.Arith Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 测试程序（3 个 warp 共用一片 imem；PC 区间互不重叠，tag=pc[9:2] 唯一）  -/
/- ========================================================================= -/

/-- 测试程序：
    warp0 @ 0x00（sgpr_base=0）：x1 := Σ_{k=1..10} k = 55；x2: 10→0 后 := 73
      0x00 addi x1, x0, 0     ; 0x00000093
      0x04 addi x2, x0, 10    ; 0x00A00113
      0x08 add  x1, x1, x2    ; 0x002080B3   ┐ 循环体
      0x0C addi x2, x2, -1    ; 0xFFF10113   │
      0x10 bne  x2, x0, -8    ; 0xFE011CE3 ──┘ → 0x08（taken×9，末次 fall-through）
      0x14 addi x2, x2, 73    ; 0x04910113
      0x18 endprg             ; 0x0000400B
    warp1 @ 0x40（sgpr_base=128）：x1 := 7+3+2+1 = 13；x3 := x1+100 = 113
      0x40 addi x1, x0, 7     ; 0x00700093
      0x44 addi x2, x0, 3     ; 0x00300113
      0x48 add  x1, x1, x2    ; 0x002080B3   ┐ 循环体
      0x4C addi x2, x2, -1    ; 0xFFF10113   │
      0x50 beq  x2, x0, +8    ; 0x00010463 → 0x58（not-taken×2，末次 taken）
      0x54 bne  x2, x0, -12   ; 0xFE011AE3 ──┘ → 0x48
      0x58 addi x3, x1, 100   ; 0x06408193
      0x5C endprg             ; 0x0000400B
    warp2 @ 0x80（sgpr_base=256）：恒真分支冲刷 0x88 的 addi
      0x80 addi x5, x0, 42    ; 0x02A00293
      0x84 beq  x0, x0, +8    ; 0x00000463 → 0x8C（恒 taken）
      0x88 addi x5, x0, 99    ; 0x06300293（应被分支冲刷，永不写回）
      0x8C addi x5, x5, 1     ; 0x00128293   ; x5 = 43
      0x90 endprg             ; 0x0000400B -/
def smtProg : SmProg where
  imem := fun pc =>
    if pc = 0x00#32 then 0x00000093#32
    else if pc = 0x04#32 then 0x00A00113#32
    else if pc = 0x08#32 then 0x002080B3#32
    else if pc = 0x0C#32 then 0xFFF10113#32
    else if pc = 0x10#32 then 0xFE011CE3#32
    else if pc = 0x14#32 then 0x04910113#32
    else if pc = 0x18#32 then 0x0000400B#32
    else if pc = 0x40#32 then 0x00700093#32
    else if pc = 0x44#32 then 0x00300113#32
    else if pc = 0x48#32 then 0x002080B3#32
    else if pc = 0x4C#32 then 0xFFF10113#32
    else if pc = 0x50#32 then 0x00010463#32
    else if pc = 0x54#32 then 0xFE011AE3#32
    else if pc = 0x58#32 then 0x06408193#32
    else if pc = 0x5C#32 then 0x0000400B#32
    else if pc = 0x80#32 then 0x02A00293#32
    else if pc = 0x84#32 then 0x00000463#32
    else if pc = 0x88#32 then 0x06300293#32
    else if pc = 0x8C#32 then 0x00128293#32
    else if pc = 0x90#32 then 0x0000400B#32
    else 0#32

/- ---- 1.1 机器码译码回归（钉死手工编码，III 类自检） ---- -/

-- bne x2, x0, -8 @ 0x10：branch=B_B(1)、FN_SNE(3)、rs1=x2、rs2=x0、IMM_B、imm=-8
example :
    let c := smDecode 0xFE011CE3#32 0#3 0x10#32
    (c.row.branch == 1#2) && (c.row.aluFn == 3#6) && (c.row.wxd == false) &&
    (c.regIdx1 == 2#8) && (c.regIdx2 == 0#8) && (c.row.selImm == rfIMM_B) &&
    (rfImmGen rfIMM_B c.inst 0#7 == 0xFFFFFFF8#32) = true := by native_decide

-- beq x2, x0, +8 @ 0x50：FN_SEQ(2)、imm=+8
example :
    let c := smDecode 0x00010463#32 1#3 0x50#32
    (c.row.branch == 1#2) && (c.row.aluFn == 2#6) && (c.row.wxd == false) &&
    (c.regIdx1 == 2#8) && (c.regIdx2 == 0#8) &&
    (rfImmGen rfIMM_B c.inst 0#7 == 8#32) = true := by native_decide

-- bne x2, x0, -12 @ 0x54：imm=-12
example :
    let c := smDecode 0xFE011AE3#32 1#3 0x54#32
    (c.row.branch == 1#2) && (c.row.aluFn == 3#6) &&
    (rfImmGen rfIMM_B c.inst 0#7 == 0xFFFFFFF4#32) = true := by native_decide

-- beq x0, x0, +8 @ 0x84：恒真，imm=+8
example :
    let c := smDecode 0x00000463#32 2#3 0x84#32
    (c.row.branch == 1#2) && (c.row.aluFn == 2#6) &&
    (c.regIdx1 == 0#8) && (rfImmGen rfIMM_B c.inst 0#7 == 8#32) = true := by
  native_decide

-- add x1, x1, x2：FN_ADD(0)、wxd、idxw=1、A1_RS1/A2_RS2
example :
    let c := smDecode 0x002080B3#32 0#3 0x08#32
    (c.row.aluFn == 0#6) && (c.row.wxd == true) && (c.regIdxw == 1#8) &&
    (c.regIdx1 == 1#8) && (c.regIdx2 == 2#8) &&
    (c.row.selAlu1 == 1#2) && (c.row.selAlu2 == 1#2) = true := by native_decide

-- addi x2, x2, -1：imm=-1（I 型符号扩展）
example :
    let c := smDecode 0xFFF10113#32 0#3 0x0C#32
    (c.row.aluFn == 0#6) && (c.row.wxd == true) && (c.regIdxw == 2#8) &&
    (rfImmGen rfIMM_I c.inst 0#7 == 0xFFFFFFFF#32) = true := by native_decide

-- 观察项（III 类，测试侧）：SM.lean 6 拍示范程序的 beq 编码 0x00108863 的
-- B 型立即数是 +16 而非其注释所称 +8（inst[11:8]=imm[4:1]=1000）。
-- 即该程序若跑过分支解析拍，将跳往 0x18（NOP 区）而非注释声称的 0x10，
-- 0x10 的 add x4 与 0x14 的 endprg 永远不会执行。6 拍内定理不受影响
-- （分支尚未解析）。此处钉死模型语义层面的实际立即数值。
example : rfImmGen rfIMM_B 0x00108863#32 0#7 = 16#32 := by native_decide

/- ========================================================================= -/
/- 2. 期望写回序列（手算；per-warp 程序序，单发射按序写回）                     -/
/- ========================================================================= -/

/-- warp0 期望写回（idxw, data）：x1=0; x2=10; 循环 k=10..1: x1+=k, x2=k-1;
    出循环 x2 := 73 -/
def smtWbExp0 : List (BitVec 8 × BitVec 32) :=
  [(1#8, 0#32), (2#8, 10#32),
   (1#8, 10#32), (2#8, 9#32), (1#8, 19#32), (2#8, 8#32),
   (1#8, 27#32), (2#8, 7#32), (1#8, 34#32), (2#8, 6#32),
   (1#8, 40#32), (2#8, 5#32), (1#8, 45#32), (2#8, 4#32),
   (1#8, 49#32), (2#8, 3#32), (1#8, 52#32), (2#8, 2#32),
   (1#8, 54#32), (2#8, 1#32), (1#8, 55#32), (2#8, 0#32),
   (2#8, 73#32)]

/-- warp1 期望写回：x1=7; x2=3; x1=10,x2=2; x1=12,x2=1; x1=13,x2=0; x3=113 -/
def smtWbExp1 : List (BitVec 8 × BitVec 32) :=
  [(1#8, 7#32), (2#8, 3#32),
   (1#8, 10#32), (2#8, 2#32), (1#8, 12#32), (2#8, 1#32),
   (1#8, 13#32), (2#8, 0#32), (3#8, 113#32)]

/-- warp2 期望写回：x5=42; x5=43（99 被冲刷） -/
def smtWbExp2 : List (BitVec 8 × BitVec 32) :=
  [(5#8, 42#32), (5#8, 43#32)]

/-- 终态寄存器堆期望（bank, addr, val）。
    物理地址：bank = regIdx[1:0] + wid[1:0]，addr = (sgpr_base>>>2) + regIdx>>>2。
    w0: x1→(1,0)=55, x2→(2,0)=73；w1: x1→(2,32)=13, x2→(3,32)=0, x3→(0,32)=113；
    w2: x5→(3,65)=43。(1,32)=0 为隔离反例槽：任何把 w1 的 x1 错误落到
    bank1/addr32（忽略 wid 或 sgpr_base）的串扰都会命中这些检查。 -/
def smtRfExp3 : List (BitVec 2 × BitVec 8 × BitVec 32) :=
  [(1#2, 0#8, 55#32), (2#2, 0#8, 73#32),
   (2#2, 32#8, 13#32), (3#2, 32#8, 0#32), (0#2, 32#8, 113#32),
   (3#2, 65#8, 43#32), (1#2, 32#8, 0#32)]

/-- 单 warp（仅 warp0）场景的终态期望：只含 w0 的槽位 -/
def smtRfExp1w : List (BitVec 2 × BitVec 8 × BitVec 32) :=
  [(1#2, 0#8, 55#32), (2#2, 0#8, 73#32)]

/- ========================================================================= -/
/- 3. 监控器：单遍 fold，一次求值得到全部结论                                  -/
/- ========================================================================= -/

/-- 不变式检查用的 CU 投影行 -/
structure SmtCuRow where
  occ  : Bool      -- state ≠ s_idle
  wid  : BitVec 3
  wxd  : Bool
  idxw : BitVec 8
  brk  : Bool      -- branch ≠ B_N ∨ barrier（在途分支/barrier，对应 beqReg）

/-- 全程不变式（对每拍步后状态检查；占记分板 ⟺ 在途指令，见文件头 S5）：
    寄存器号只查 0..31（regidx_width=5、GVM off ⇒ regIdx = 0 扩展的 5 位字段）。 -/
def smtInvAt (prog : SmProg) (s : SmState) : Bool :=
  let cus : List SmtCuRow := (List.finRange 8).map fun j =>
    let cu := smCuAt s j
    if cu.state != cuSIdle then
      let c := smCtrlOfTag prog cu.controlReg.tag cu.controlReg.wid
      ⟨true, cu.controlReg.wid, c.row.wxd, c.regIdxw,
       (c.row.branch != 0#2) || c.row.barrier⟩
    else ⟨false, 0#3, false, 0#8, false⟩
  (s.ws.barCurArr.size == 8) && (s.ws.barExpArr.size == 8) &&
  (s.ws.barBelongArr.size == 8) && (s.ws.endprgCntArr.size == 8) &&
  (s.ws.wgValidArr.size == 8) &&
  ((List.finRange 8).all fun w =>
    let w3 : BitVec 3 := BitVec.ofNat 3 w.val
    let occW : SmtCuRow → Bool := fun e => e.occ && (e.wid == w3)
    (sbReadOpColX (s.sb w) == cus.any occW) &&
    (sbReadB (s.sb w) == cus.any fun e => occW e && e.brk) &&
    ((List.finRange 32).all fun a =>
      let a8 : BitVec 8 := BitVec.ofNat 8 a.val
      (sbRead true (s.sb w).scalarReg a8 ==
        cus.any fun e => occW e && e.wxd && (e.idxw == a8))))

/-- 终态检查：warp 全退、flush 簿记回收、寄存器堆终值 -/
def smtFinOk (s : SmState) (rfExp : List (BitVec 2 × BitVec 8 × BitVec 32)) : Bool :=
  (s.ws.warpActive == 0#8) &&
  (wsMask0 s.ws.endprgCnt s.ws.wgValid == 0#8) &&
  ((List.finRange 8).all fun j => !(s.ws.wgValid j)) &&
  (rfExp.all fun (b, a, v) => rf_read (smSrfAt s b.toFin).mem a.toFin == v)

/-- 监控累积器 -/
structure SmtChk where
  tick     : Nat
  okInv    : Bool                                -- 不变式全程保持
  wbBad    : Bool                                -- 出现不期望的写回
  wb0      : List (BitVec 8 × BitVec 32)         -- 各 warp 剩余期望写回
  wb1      : List (BitVec 8 × BitVec 32)
  wb2      : List (BitVec 8 × BitVec 32)
  fetchM   : BitVec 8                            -- 见过取指的 warp 位
  issueM   : BitVec 8                            -- 见过发射（i2i out_x）的 warp 位
  brT      : BitVec 8                            -- 见过分支 taken 的 warp 位
  brN      : BitVec 8                            -- 见过分支 not-taken 的 warp 位
  endM     : BitVec 8                            -- 见过 endprg（warp_control.fire）的 warp 位
  firstEnd : Nat                                 -- 首个 endprg 拍（0=未见，否则拍号+1）
  endT0    : Nat                                 -- warp0/1/2 各自 endprg 拍（同编码）
  endT1    : Nat
  endT2    : Nat
  lastWb   : Nat                                 -- 最后一次写回拍（0=无，否则拍号+1）
  finOk    : Bool
  deriving DecidableEq, Repr

/-- 场景配置：期望写回序列 + 终态寄存器期望 -/
structure SmtCfg where
  wb0   : List (BitVec 8 × BitVec 32)
  wb1   : List (BitVec 8 × BitVec 32)
  wb2   : List (BitVec 8 × BitVec 32)
  rfExp : List (BitVec 2 × BitVec 8 × BitVec 32)

/-- 从期望队列弹出一笔并核对 -/
def smtWbPop (q : List (BitVec 8 × BitVec 32)) (e : BitVec 8 × BitVec 32) :
    List (BitVec 8 × BitVec 32) × Bool :=
  match q with
  | [] => ([], true)
  | h :: t => (t, h != e)

def smtMonStep (prog : SmProg) (acc : SmtChk × SmState) (inp : SmIn) : SmtChk × SmState :=
  let (m, s) := acc
  let c := smComb prog s inp
  let s' := smStep prog s inp
  let t := m.tick
  let (wb0', wb1', wb2', bad) :=
    if c.wbXFire then
      let e := (c.wbXIdxw, c.wbXData)
      if c.wbXWid == 0#3 then
        let (q, b) := smtWbPop m.wb0 e; (q, m.wb1, m.wb2, b)
      else if c.wbXWid == 1#3 then
        let (q, b) := smtWbPop m.wb1 e; (m.wb0, q, m.wb2, b)
      else if c.wbXWid == 2#3 then
        let (q, b) := smtWbPop m.wb2 e; (m.wb0, m.wb1, q, b)
      else (m.wb0, m.wb1, m.wb2, true)
    else (m.wb0, m.wb1, m.wb2, false)
  ({ m with
      tick := t + 1
    , okInv := m.okInv && smtInvAt prog s'
    , wbBad := m.wbBad || bad
    , wb0 := wb0', wb1 := wb1', wb2 := wb2'
    , fetchM := if c.fetchV then m.fetchM ||| (1#8 <<< c.fetchWid.zeroExtend 8) else m.fetchM
    , issueM := if c.i2iXFire then m.issueM ||| (1#8 <<< c.i2iXWid.zeroExtend 8) else m.issueM
    , brT := if c.brFire && c.brJump then m.brT ||| (1#8 <<< c.brWid.zeroExtend 8) else m.brT
    , brN := if c.brFire && !c.brJump then m.brN ||| (1#8 <<< c.brWid.zeroExtend 8) else m.brN
    , endM := if c.fireWs then m.endM ||| (1#8 <<< c.outXWid.zeroExtend 8) else m.endM
    , firstEnd := if c.fireWs && m.firstEnd == 0 then t + 1 else m.firstEnd
    , endT0 := if c.fireWs && c.outXWid == 0#3 && m.endT0 == 0 then t + 1 else m.endT0
    , endT1 := if c.fireWs && c.outXWid == 1#3 && m.endT1 == 0 then t + 1 else m.endT1
    , endT2 := if c.fireWs && c.outXWid == 2#3 && m.endT2 == 0 then t + 1 else m.endT2
    , lastWb := if c.wbXFire then t + 1 else m.lastWb }, s')

/-- 单遍跑完一条输入轨迹并给出全部检查结论 -/
def smtRunChk (prog : SmProg) (cfg : SmtCfg) (ins : List SmIn) : SmtChk :=
  let init : SmtChk × SmState :=
    ({ tick := 0, okInv := true, wbBad := false
     , wb0 := cfg.wb0, wb1 := cfg.wb1, wb2 := cfg.wb2
     , fetchM := 0#8, issueM := 0#8, brT := 0#8, brN := 0#8, endM := 0#8
     , firstEnd := 0, endT0 := 0, endT1 := 0, endT2 := 0, lastWb := 0
     , finOk := false }, smInit)
  let (m, s) := ins.foldl (smtMonStep prog) init
  { m with finOk := smtFinOk s cfg.rfExp }

/- ========================================================================= -/
/- 4. 场景 A：单 warp 长循环（场景 S2/S3标量/S4/S5 的小版本）                   -/
/- ========================================================================= -/

/-- 场景 A 拍数 -/
def smtAN : Nat := 260

/-- 场景 A 输入：拍 0 派发 warp0（wg0、wfCount=1、pc=0、sgpr/vgpr base=0） -/
def smtInsA : List SmIn :=
  smInDispatch 0#3 0#3 1#4 0#32 0#12 0#11 :: List.replicate (smtAN - 1) smInNop

/-- 场景 A 配置 -/
def smtCfgA : SmtCfg := ⟨smtWbExp0, [], [], smtRfExp1w⟩

/-- 场景 A 期望结论（firstEnd/endT0/lastWb 为探测到的实际拍号+1，
    作为时间线回归一并钉死：任何时序变化都会使本期望失配） -/
def smtExpA : SmtChk :=
  { tick := smtAN, okInv := true, wbBad := false, wb0 := [], wb1 := [], wb2 := []
  , fetchM := 0b001#8, issueM := 0b001#8, brT := 0b001#8, brN := 0b001#8
  , endM := 0b001#8, firstEnd := 155, endT0 := 155, endT1 := 0, endT2 := 0
  , lastWb := 153, finOk := true }

/- ========================================================================= -/
/- 5. 场景 B：三 warp 并发（S1+S2+S3标量+S4+S5）                               -/
/- ========================================================================= -/

/-- 场景 B 拍数 -/
def smtBN : Nat := 340

/-- 场景 B 第 t 拍输入：拍 0/1/2 依次派发 warp0/1/2；
    wgIdTag 在各自 endprg 拍回填（wsEndWgId/wsEndWfId 消费，wf=0，
    tag = wg<<<3）：endprg 拍号经全 0 探测得到（w2@t26、w1@t71、w0@t156），
    wgIdTag 只进 endprg 簿记清除/flush 路径，不影响取指与发射时序，
    故回填后时序不变（fixpoint 稳定）。 -/
def smtInBAt (t : Nat) : SmIn :=
  match t with
  | 0 => smInDispatch 0#3 0#3 1#4 0x00#32 0#12 0#11
  | 1 => smInDispatch 1#3 1#3 1#4 0x40#32 128#12 0#11
  | 2 => smInDispatch 2#3 2#3 1#4 0x80#32 256#12 0#11
  | 26 => { smInNop with wgIdTag := 16#6 }   -- warp2（wg2）endprg
  | 71 => { smInNop with wgIdTag := 8#6 }    -- warp1（wg1）endprg
  | 156 => { smInNop with wgIdTag := 0#6 }   -- warp0（wg0）endprg
  | _ => smInNop

/-- 场景 B 输入轨迹 -/
def smtInsB : List SmIn := (List.range smtBN).map smtInBAt

/-- 场景 B 配置 -/
def smtCfgB : SmtCfg := ⟨smtWbExp0, smtWbExp1, smtWbExp2, smtRfExp3⟩

/-- 场景 B 期望结论（拍号同 A 的口径：0=未见，否则拍号+1；
    w2 最短 5 条指令最先 endprg（t26），w1 13 条（t71），w0 34 条（t156）；
    三 warp 共享单发射通路，w0 比单跑（t154）晚 2 拍——并发调度开销可见） -/
def smtExpB : SmtChk :=
  { tick := smtBN, okInv := true, wbBad := false, wb0 := [], wb1 := [], wb2 := []
  , fetchM := 0b111#8, issueM := 0b111#8, brT := 0b111#8, brN := 0b011#8
  , endM := 0b111#8, firstEnd := 27, endT0 := 157, endT1 := 72, endT2 := 27
  , lastWb := 155, finOk := true }

/- ---- 6. 主定理（单遍 native_decide；结构相等即全部子检查同时成立） ---- -/

/-- 场景 A 全程判收：单 warp、10 次计数累加循环（34 条指令、23 笔写回、
    bne 回跳 taken×9 + 末次 fall-through），260 拍轨迹上：
    不变式全程保持（okInv）、写回流逐笔等于手算期望（wbBad=false 且队列耗尽）、
    分支双向覆盖（brT/brN）、endprg 于拍 154 触发（endT0=155）、
    终态 warp_active=0、簿记回收、RF 中 x1=55（bank1@0）、x2=73（bank2@0）。 -/
theorem smtA_ok : smtRunChk smtProg smtCfgA smtInsA = smtExpA := by
  native_decide

/-- 场景 B 全程判收：三 warp 并发（warp0 循环 / warp1 双向分支循环 /
    warp2 恒真分支冲刷），拍 0/1/2 连续派发，340 拍轨迹上：
    不变式全程保持；三个 warp 的写回流各自逐笔等于手算期望（隔离性：
    同名架构寄存器 x1/x2 在三个 warp 下落到不同物理 bank/地址，互不串扰）；
    三 warp 均被取指与发射（fetchM=issueM=0b111，固定优先级 + ibuffer
    反压下的轮换）；分支 taken 三 warp 全覆盖、not-taken 覆盖 w0/w1
    （brN=0b011）；warp2 的 0x88 addi x5,99 被正确冲刷（x5 终值 43≠99/100）；
    endprg 分别于拍 26/71/156（w2/w1/w0）触发，终态 warp_active=0、
    三个 wg 的 cnt/valid 簿记全部回收、flush 不再悬挂。 -/
theorem smtB_ok : smtRunChk smtProg smtCfgB smtInsB = smtExpB := by
  native_decide

/- ========================================================================= -/
/- 7. 发现与障碍记录（上报主会话）                                             -/
/- ========================================================================= -/
/-
  F-SMT-1【III 类，测试侧，SM.lean 6 拍示范程序立即数错】
    SM.lean 的 smTestProg 中 `0x08 beq x1, x1, +8`（注释称跳过 0x0C 落 0x10）
    的机器码 0x00108863，其 B 型立即数实际为 +16（inst[11:8]=imm[4:1]=1000，
    本文件第 1.1 节最后一条 example 以 rfImmGen 钉死：imm=16）。该程序若
    跑过分支解析拍，将跳往 0x18（NOP 区），0x10 的 add x4 与 0x14 的
    endprg 永远不会执行——注释语义与实际编码不符。SM.lean 已证的 6 拍定理
    不受影响（分支在拍 ~14 才解析，超出其覆盖范围）。本文件不复用该编码，
    全部机器码经第 1.1 节译码回归钉死。
  F-SMT-2【障碍，场景 S3】vbranch/join 的 SIMT 分支分化/汇合轨迹无法构造：
    SM.lean D4 中 issueV 全端口 ready=false（向量/SIMT 指令在 DualIssue 处
    永久阻塞），D6 中 branch_join 每拍喂 BjEvent.nop、complete/fetchValid
    以常量 false 占位。vbranch 需要 issueV→SIMT 端口→branch_back.in1 通路，
    当前骨架不具备。故 S3 改以标量分支覆盖：bne 回跳（taken×9 + 末次
    fall-through）、beq 前跳（not-taken×2 + taken）、恒真 beq 冲刷后继
    指令（ibuffer 冲刷正确性由 warp2 的 x5=43 证实）。
  F-SMT-3【观察，非 bug】warp_scheduler 的 wgIdTag 是环境输入（D7），
    本文件按探测到的 endprg 拍回填正确 tag；若喂错 tag，cnt/belong 清错
    wg、wgValid 永不回收（属测试刺激错误而非硬件 bug，与 WarpScheduler
    Q4/Q5 记录的风险同源但此处为驱动侧问题）。
  F-SMT-4【正面结论】三 warp 并发 340 拍，不变式 smtInvAt（WsState 数组
    尺寸、记分板 opColX/beqReg/scalarReg 与 CU 占用逐拍一致）全程保持；
    未发现 I/II 类新异常。
-/

/- 公理审计：native_decide 定理带 Lean.ofReduceBool（见下）；其余为
   Lean 标准公理（propext/Quot.sound 等）。 -/
#print axioms smtA_ok
#print axioms smtB_ok

end Ventus
