/- ========================================================================= -/
/-                          MultiSM.lean                                     -/
/-  多 SM 整机组合第一块：2 个 SM（SMMemDc.lean 的 SmdState/smdStep 全通路      -/
/-  模型）+ 共享函数式 L2 stub 的状态级组合骨架，与首个跨 SM 场景（SM0 store    -/
/-  → flush 写回共享 L2 → SM1 load miss→refill 读回）。                        -/
/-                                                                           -/
/-  组合方式（每拍 msmStep）：                                                 -/
/-    1. 把共享 L2 注入两 SM 的 dc.l2（两 SM 从同一拍前 L2 视图步进）；         -/
/-    2. 各自 smdStep（CTA 派发以 SmIn 事件注入，不建 CTA 全模型，MSM-D4）；    -/
/-    3. 写回仲裁合并：各 SM 本拍对 L2 的写经 dc.wbLog 增量提取（smdDcStep      -/
/-       对 L2 的写只有 dirty 驱逐与 flush 两处，均记 wbLog——**契约**：若       -/
/-       SMMemDc.lean 后续新增 L2 写路径而漏记 wbLog，本合并会丢写），同拍      -/
/-       多块全部落地，同拍同块冲突 SM0 优先（MSM-D1）。                        -/
/-                                                                           -/
/- ======================== 建模决策（MSM-D 区） ============================= -/
/-  MSM-D0. sm_id = 组合槽位（0/1）。SM 内部无依赖 sm_id 的硬件行为             -/
/-      （wg_id_tag 由 SmIn 环境输入携带，SM.lean D7），故两实例同构、无需      -/
/-      在 SmdState 内加 id 字段。                                              -/
/-  MSM-D1. 共享 L2 stub 仲裁 = 固定优先级（SM0 > SM1），非轮换：本壳的          -/
/-      L1MSHR 是单 outstanding（SMD-D2），同拍同块写写冲突极罕；真 L2 的        -/
/-      slice/通道仲裁（L2/Scheduler.lean）留后续波次接入后再建模。             -/
/-  MSM-D2. 同拍读旧值：写→读无转发（两 SM 都从拍前共享 L2 读）。               -/
/-  MSM-D3. 无一致性目录：DCache 间无 probe/invalidate（真 L2 Directory 未接    -/
/-      入，见 MSM-O1（已消解，2026-08-30：由 MultiSML2.lean + SMMemDc.lean SMD-D7 承接））。跨 SM 可见性 = 写方 flush 写回 + 读方 miss refill，    -/
/-      与真实 GPGPU"L1 不互一致、靠 flush/fence 在 L2 做同步点"语义一致；      -/
/-      本骨架不检测 staleness 竞态（MSM-B2）。                                 -/
/-  MSM-D4. CTA 派发 = SmIn 事件注入（场景 A：t=0 派 SM0、t=32 派 SM1）；       -/
/-      CTA/Allocator 全模型接入的缺口见 MSM-O2。                               -/
/-  MSM-D5. 求值预算：轨迹 96 拍 × 2 SM ≈ 1.5× 场景 D（128 拍单 SM）；断言      -/
/-      用终态值 + 事件序不等式（不写死拍号，免 /tmp 探针步）。                  -/
/- ========================================================================= -/

import Ventus.SMMemDc

namespace Ventus

open Ventus.Schedule Ventus.SIMT Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 组合状态 / 共享 L2 仲裁合并 / msmStep / msmRun                            -/
/- ========================================================================= -/

/-- 多 SM 组合状态：两个 SmdState 实例 + 共享 L2 函数式内存（唯一真源） -/
structure MsmState where
  sm0 : SmdState
  sm1 : SmdState
  l2  : BitVec 25 → Fin 32 → BitVec 32   -- 共享 L2：blockAddr → 32 字

/-- 初始共享 L2 内容（与 smdDcInit 同模式，便于反证对照） -/
def msmL2Init : BitVec 25 → Fin 32 → BitVec 32 := smdL2Init

/-- 写回合并：把 bas 中各块的行内容（rowf 取样）依序写入 l；后写覆盖先写 -/
def msmWbUpd (l : BitVec 25 → Fin 32 → BitVec 32) (bas : List (BitVec 25))
    (rowf : BitVec 25 → Fin 32 → BitVec 32) : BitVec 25 → Fin 32 → BitVec 32 :=
  bas.foldl (fun acc b => smdUpdL2 acc b (rowf b)) l

/-- 多 SM 单拍：两 SM 并行 smdStep + 共享 L2 仲裁合并（MSM-D0/D1/D2）。
    合并序 = 先 SM1 后 SM0 ⇒ 同拍同块冲突 SM0 优先（msmT_merge_priority）。 -/
def msmStep (p0 p1 : SmProg) (s : MsmState) (i0 i1 : SmIn) : MsmState :=
  let raw0 := smdStep p0 { s.sm0 with dc := { s.sm0.dc with l2 := s.l2 } } i0
  let raw1 := smdStep p1 { s.sm1 with dc := { s.sm1.dc with l2 := s.l2 } } i1
  let w0 := raw0.dc.wbLog.drop s.sm0.dc.wbLog.length
  let w1 := raw1.dc.wbLog.drop s.sm1.dc.wbLog.length
  let l2' := msmWbUpd (msmWbUpd s.l2 w1 (fun ba => raw1.dc.l2 ba))
               w0 (fun ba => raw0.dc.l2 ba)
  { sm0 := { raw0 with dc := { raw0.dc with l2 := l2' } }
  , sm1 := { raw1 with dc := { raw1.dc with l2 := l2' } }
  , l2 := l2' }

/-- 多拍运行（输入 = 每拍两 SM 各自的 SmIn） -/
def msmRun (p0 p1 : SmProg) (s : MsmState) (ins : List (SmIn × SmIn)) : MsmState :=
  ins.foldl (fun acc inp => msmStep p0 p1 acc inp.1 inp.2) s

/- ========================================================================= -/
/- 2. 连线定理（rfl）与共享 L2 仲裁定理（归纳）                                  -/
/- ========================================================================= -/

/-- 连线：SM0 本拍从共享 L2 视图步进，步进后其 dc.l2 视图 = 合并后的共享 L2 -/
theorem msmT_sm0_wire (p0 p1 : SmProg) (s : MsmState) (i0 i1 : SmIn) :
    (msmStep p0 p1 s i0 i1).sm0 =
      { (smdStep p0 { s.sm0 with dc := { s.sm0.dc with l2 := s.l2 } } i0) with
        dc := { (smdStep p0 { s.sm0 with dc := { s.sm0.dc with l2 := s.l2 } } i0).dc
          with l2 := (msmStep p0 p1 s i0 i1).l2 } } := rfl

/-- 连线：SM1 同 -/
theorem msmT_sm1_wire (p0 p1 : SmProg) (s : MsmState) (i0 i1 : SmIn) :
    (msmStep p0 p1 s i0 i1).sm1 =
      { (smdStep p1 { s.sm1 with dc := { s.sm1.dc with l2 := s.l2 } } i1) with
        dc := { (smdStep p1 { s.sm1 with dc := { s.sm1.dc with l2 := s.l2 } } i1).dc
          with l2 := (msmStep p0 p1 s i0 i1).l2 } } := rfl

/-- 两 SM 的 L2 视图状态一致（次拍注入的前提） -/
theorem msmT_view_same (p0 p1 : SmProg) (s : MsmState) (i0 i1 : SmIn) :
    (msmStep p0 p1 s i0 i1).sm0.dc.l2 = (msmStep p0 p1 s i0 i1).sm1.dc.l2 := rfl

/-- 写回合并规格：被写块取 rowf、未写块保持原值（最后写入者胜出） -/
theorem msmT_wbUpd_spec (l : BitVec 25 → Fin 32 → BitVec 32)
    (bas : List (BitVec 25)) (rowf : BitVec 25 → Fin 32 → BitVec 32)
    (ba : BitVec 25) (w : Fin 32) :
    msmWbUpd l bas rowf ba w =
      (if ba ∈ bas then rowf ba w else l ba w) := by
  induction bas generalizing l with
  | nil => rfl
  | cons b bs ih =>
      rw [show msmWbUpd l (b :: bs) rowf = msmWbUpd (smdUpdL2 l b (rowf b)) bs rowf
            from rfl, ih]
      by_cases hs : ba ∈ bs
      · rw [if_pos hs, if_pos (List.mem_cons_of_mem b hs)]
      · rw [if_neg hs]
        by_cases hb : ba = b
        · subst hb
          rw [if_pos List.mem_cons_self]
          simp [smdUpdL2]
        · have hnb : ¬ ba ∈ b :: bs :=
            fun h => (List.mem_cons.mp h).elim hb hs
          rw [if_neg hnb]
          have hbb : (ba == b) = false := by
            cases h : (ba == b) with
            | false => rfl
            | true => exact absurd (beq_iff_eq.mp h) hb
          simp [smdUpdL2, hbb]

/-- **仲裁优先级（MSM-D1）**：同拍写写冲突 SM0（后落）胜出；SM1 独有块落地；
    未写块不变 -/
theorem msmT_merge_priority (l : BitVec 25 → Fin 32 → BitVec 32)
    (bas0 bas1 : List (BitVec 25))
    (row0 row1 : BitVec 25 → Fin 32 → BitVec 32) (ba : BitVec 25) (w : Fin 32) :
    msmWbUpd (msmWbUpd l bas1 row1) bas0 row0 ba w =
      (if ba ∈ bas0 then row0 ba w
       else if ba ∈ bas1 then row1 ba w
       else l ba w) := by
  -- 两次重写后左右两端语法相同（rw 自动以 rfl 收口）
  rw [msmT_wbUpd_spec, msmT_wbUpd_spec]

/- ========================================================================= -/
/- 3. 场景 A（首个跨 SM 场景）：SM0 store 全局地址 A → endprg flush 写回共享   -/
/-    L2 → SM1（延迟 32 拍派发）load 同一地址 A，miss→refill 读回               -/
/-                                                                           -/
/-  A = 0x10000000（global、非 LDS；tag=0x2000/setIdx=0 ⇒ blockAddr=0x200000，  -/
/-  地址分解回归见 SMMemDc.lean §6.1）。两 SM 各自 warp0、vgpr_base=16：        -/
/-  SM0 v1（bank1 addr4）= rowA 预置；SM1 读回 v2（bank2 addr4）。              -/
/- ========================================================================= -/

/-- SM0 程序：lui x1,0x10000 ; vse32.v v1,(x1) ; endprg（endprg 触发 flush，
    dirty 行 A 写回共享 L2，SMD-D6） -/
def msmProgSt : SmProg where
  imem := fun pc =>
    if pc = 0x00#32 then 0x100000B7#32        -- lui  x1, 0x10000
    else if pc = 0x04#32 then 0x0200E0A7#32   -- vse32.v v1, (x1)
    else if pc = 0x08#32 then 0x0000400B#32   -- endprg
    else 0#32

/-- SM1 程序：lui x1,0x10000 ; vle32.v v2,(x1) ; endprg（load miss→refill） -/
def msmProgLd : SmProg where
  imem := fun pc =>
    if pc = 0x00#32 then 0x100000B7#32        -- lui  x1, 0x10000
    else if pc = 0x04#32 then 0x0200E107#32   -- vle32.v v2, (x1)
    else if pc = 0x08#32 then 0x0000400B#32   -- endprg
    else 0#32

/-- SM0 初态：v1（bank1 addr4）= rowA 预置 + tmask 全 1（同 smdS0C 布局） -/
def msmSmSt0 : SmdState :=
  let vrf : Array RfVState := ((List.finRange 4).map fun i =>
    if i.val = 1 then { rfVInit with mem := fun a =>
        if a.val = 4 then smdRowA else rfVInit.mem a }
    else rfVInit).toArray
  smdInitOf
    { base := { smInit with
        vrf := vrf
      , csr := { smInit.csr with simtRpc := 0#32 }
      , bj := { stack := bjStackInit 4 32, tmask := 0xFFFFFFFF#32 } }
    , fcV := false, fcJ := false, fcPC := 0#32, fcWid := 0#3 }

/-- SM1 初态：寄存器堆全默认（v2 由 load 覆写） -/
def msmSmLd0 : SmdState :=
  smdInitOf
    { base := { smInit with
        csr := { smInit.csr with simtRpc := 0#32 }
      , bj := { stack := bjStackInit 4 32, tmask := 0xFFFFFFFF#32 } }
    , fcV := false, fcJ := false, fcPC := 0#32, fcWid := 0#3 }

def msmS0A : MsmState := ⟨msmSmSt0, msmSmLd0, msmL2Init⟩

/-- 场景 A 拍数（96 拍 × 2 SM，MSM-D5） -/
def msmNA : Nat := 96

/-- SM1 派发延迟（拍）：SM0 flush 写回（参照场景 C 时序，约 t20-26）之后 -/
def msmDelayA : Nat := 32

/-- 输入：t=0 派 SM0 warp0，t=32 派 SM1 warp0（wg0、wfCount=1、pc=0、
    sgpr base=0、vgpr base=16），其余空转 -/
def msmInsA : List (SmIn × SmIn) :=
  (List.range msmNA).map fun t =>
    (if t = 0 then smInDispatch 0#3 0#3 1#4 0#32 0#12 16#11 else smInNop,
     if t = msmDelayA then smInDispatch 0#3 0#3 1#4 0#32 0#12 16#11 else smInNop)

/- ---- 3.1 机器码译码回归（III 类自检；lui/vse32 的回归见 SMMemDc §6.1） ---- -/

-- vle32.v v2, (x1)：VLE32_V 行、rd(v2)=2、rs1=1、非写 mem_cmd、路由 LSU
example :
    let c := smDecode 0x0200E107#32 0#3 0x04#32
    (c.row == (decRowOf decAllTables "VLE32_V")) && (c.regIdxw == 2#8) &&
    (c.regIdx1 == 1#8) && (Mem.lsuMemCmdWr c.row.memCmd == false) &&
    (issRoute (smToIssCtrl c) == [.LSU]) = true := by native_decide

-- 跨 SM 地址前提：两程序用同一全局地址 ⇒ 同一 L2 blockAddr
example :
    (Mem.lsuAllShared Mem.lsuSmaxDefault
      ⟨fun _ => 0x10000000#32, fun _ => 0, fun _ => 0, fun _ => true,
       smmLsuCtrlOf (smDecode 0x0200E107#32 0#3 0x04#32)⟩ 0 0 0 == false) &&
    (Mem.dcBlockAddr (Mem.lsuTagOf 0x10000000#32) (Mem.lsuSetOf 0x10000000#32) ==
      0x200000#25) = true := by native_decide

/- ---- 3.2 监控器（轻量：只记跨 SM 事件序，不写死拍号，MSM-D5） ---- -/

/-- 监控累积器：SM0 写共享 L2 / SM1 miss 捕获 / SM1 回填 的首拍（+1，0=未发生） -/
structure MsmChk where
  tick    : Nat
  wb0T    : Nat   -- 首个 SM0 写共享 L2（wbLog 增量非空）拍+1
  miss1T  : Nat   -- 首个 SM1 miss 捕获拍+1
  ref1T   : Nat   -- 首个 SM1 回填完成拍+1
  deriving DecidableEq, Repr

def msmChk0 : MsmChk := { tick := 0, wb0T := 0, miss1T := 0, ref1T := 0 }

def msmMonStep (p0 p1 : SmProg) (acc : MsmChk × MsmState) (inp : SmIn × SmIn) :
    MsmChk × MsmState :=
  let (m, s) := acc
  let s' := msmStep p0 p1 s inp.1 inp.2
  let t := m.tick
  let wb0 : Bool := s'.sm0.dc.wbLog.length > s.sm0.dc.wbLog.length
  let missCap1 : Bool := s.sm1.dc.miss.isNone && s'.sm1.dc.miss.isSome
  let refill1 : Bool := s.sm1.dc.miss.isSome && s'.sm1.dc.miss.isNone
  ({ tick := t + 1
   , wb0T := if wb0 && m.wb0T == 0 then t + 1 else m.wb0T
   , miss1T := if missCap1 && m.miss1T == 0 then t + 1 else m.miss1T
   , ref1T := if refill1 && m.ref1T == 0 then t + 1 else m.ref1T }, s')

def msmRunChkA : MsmChk × MsmState :=
  msmInsA.foldl (msmMonStep msmProgSt msmProgLd) (msmChk0, msmS0A)

/-- 终态判收（全部 Bool；native_decide 求值） -/
def msmFinOkA (m : MsmChk) (sf : MsmState) : Bool :=
  -- **跨 SM 写读一致**：SM1 v2（bank2 addr4）全 32 lane = SM0 写入的 rowA
  (List.finRange 32).all (fun t =>
    (smVrfAt sf.sm1.base.base ⟨2, by decide⟩).mem ⟨4, by decide⟩ t == smdRowA t) &&
  -- 共享 L2 的块 A = rowA（采样 lane0/31）
  (sf.l2 0x200000#25 ⟨0, by decide⟩ == 0xAB00#32) &&
  (sf.l2 0x200000#25 ⟨31, by decide⟩ == 0xAB1F#32) &&
  -- 反证对照：L2 初值 ≠ rowA（SM1 读到的确实来自 SM0 写回而非初值）
  (smdL2Init 0x200000#25 ⟨0, by decide⟩ != smdRowA ⟨0, by decide⟩) &&
  -- **跨 SM 事件序**：SM0 写回先于 SM1 miss 捕获，miss 之后有回填
  (m.wb0T > 0) && (m.miss1T > m.wb0T) && (m.ref1T > m.miss1T) &&
  -- 写回日志：SM0 仅 flush 写回块 A；SM1 无写回（refill 行 clean，flush 无可写）
  (sf.sm0.dc.wbLog == [0x200000#25]) && (sf.sm1.dc.wbLog == []) &&
  -- 双 SM 归位
  (sf.sm0.base.base.ws.warpActive == 0#8) &&
  (sf.sm1.base.base.ws.warpActive == 0#8) &&
  (sf.sm0.lsu.state == Mem.lsuSIdle) && (sf.sm1.lsu.state == Mem.lsuSIdle) &&
  (sf.sm0.mshr.used == 0#8) && (sf.sm1.mshr.used == 0#8) &&
  (sf.sm0.dc.miss.isNone) && (sf.sm1.dc.miss.isNone) &&
  (sf.sm0.dc.rspQ.isNone) && (sf.sm1.dc.rspQ.isNone)

/-- **场景 A 主定理（首个跨 SM 场景：经共享 L2 的跨 SM 写读一致）**：
    SM0 warp0 store rowA → 全局地址 A（miss→L2 refill→写分配，dirty）→
    endprg flush 把 dirty 行 A 写回**共享 L2**；32 拍后 SM1 warp0 load 同一
    地址 A → miss → 从共享 L2 refill ⇒ v2 全 lane = rowA。
    写读一致性证据链：事件序（SM0 写回 ≺ SM1 miss ≺ SM1 回填）+ 终态值
    （SM1.v2 = rowA、L2[A] = rowA、L2 初值 ≠ rowA 的反证对照）。
    （单遍 native_decide；公理审计多 Lean.ofReduceBool，归档注明。） -/
theorem msmTraceA_ok : msmFinOkA msmRunChkA.1 msmRunChkA.2 = true := by
  native_decide

/- ========================================================================= -/
/- 4. 障碍清单与发现（上报主会话）                                             -/
/- ========================================================================= -/
/-
  MSM-O1【障碍】接真实 L2 模型（L2/Channels/L2MSHR/Directory/SourceD/
    Scheduler，对方会话第 25-27 波所建）缺：
    (a) 接口错配：SmdDc 壳的 L2 交互是"读块即时返回 + 固定延迟倒计
        （smdL2Lat=4，SmdMiss.cnt）+ 写回即时落"，memArb0/1Rdy 恒 true
        （SMD-D3），无 memReq/memRsp 通道事件；接真 L2 需把 miss 倒计替换为
        通道握手（acquire/release），把 wbLog 写回改为 sourceA 请求——改动
        点在 SMMemDc.lean 的 smdDcInA/smdDcStep（既有文件，需主会话协调）。
    (b) flush 的 hintAck（SMD-D3/D6）真 L2 侧对应 release ack，延迟不定 →
        smdHintAck 的驱动（flushCnt 倒计）需改为响应通道驱动。
    (c) 一致性：真 L2 Directory 的 probe 需要 DCache 壳接
        probeStatus/injectTagProbe（DcIn 已有字段，本壳恒 false）——跨 SM
        staleness 场景（SM1 已缓存旧行时 SM0 写同块）只有接入后才可建模。
    (d) wbLog 合并契约（§1 头注）：若真 L2 化后 L2 写不再经 wbLog，msmStep
        的增量提取需同步改造。
  MSM-O2【障碍】CTA 全模型接入缺：warp 派发目前是 SmIn 事件注入（wid/wg/
    sgpr/vgpr 基址手工指定，MSM-D4）；接 CTA/Allocator.lean 需 sm_id 分配、
    wg_id_tag 生成与 warpRsp 回流（SmIn.wgIdTag/warpRspReady 已留口）、
    两 SM 间的资源静态划分。
  MSM-B1【模型边界】同拍同块写写冲突 SM0 恒赢（MSM-D1 固定优先级），非真
    L2 仲裁行为；本场景无冲突，未覆盖。
  MSM-B2【模型边界】无一致性目录（MSM-D3）：SM1 若在 SM0 flush 前已缓存
    旧行 A 会读到旧值——真实硬件同样如此（L1 间不互一致，靠软件 flush/
    fence 在 L2 同步），建模语义忠实但不检测此类竞态。

  发现（I/II/III 类审查）：本文件为组合骨架，新逻辑 = msmWbUpd 仲裁合并
    （纯函数，已配 msmT_wbUpd_spec/msmT_merge_priority 两条符号定理）与
    msmStep 接线（rfl 连线定理 ×3）；smdStep 复用既有模型未改。II 类风险点
    即上述 wbLog 合并契约（已在 §1 头注与 MSM-O1(d) 标注）。I/III 类未见新
    疑点；场景 A 机器码译码回归（3.1）native_decide 通过。
-/

/- 公理审计：native_decide 定理带 Lean.ofReduceBool（预期，AGENTS.md 已备案） -/
#print axioms msmT_sm0_wire
#print axioms msmT_sm1_wire
#print axioms msmT_view_same
#print axioms msmT_wbUpd_spec
#print axioms msmT_merge_priority
#print axioms msmTraceA_ok

end Ventus
