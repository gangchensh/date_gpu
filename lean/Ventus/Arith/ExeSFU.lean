/- ========================================================================= -/
/-                     Arith/ExeSFU.lean                                     -/
/-  执行级特殊功能单元侧封装：SFUexe / FPUexe / vTCexe / TCCtrlv2 的          -/
/-  Lean 4 模型 + 测试 + 证明                                                 -/
/-                                                                           -/
/-  Chisel 源码对照（行号均为该行号文件内行号）：                              -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/execution.scala     -/
/-      TCCtrlv2 :112-114   vTCexe :115-162   FPUexe :746-804                -/
/-      SFUexe  :806-944（内含 num_sfu 个 IntDivMod + num_sfu 个 FloatDivSqrt -/
/-      + Arbiter 的封装与分组调度）                                          -/
/-    IntDivMod 单元本体模型见 Arith/IntDivMod.lean（div 前缀），本文件复用    -/
/-    其语义；其 I-17/19（BUG1/2）结论不变，I-18（原 BUG3）已撤案（doc/23）。         -/
/-                                                                           -/
/- ======================== 建模决策（D 区） ================================= -/

/-  D1. 参数固化为默认配置：num_thread=32、num_sfu=(32>>2).max(1)=8、
       num_grp=4（:820）、xLen=32、depth_warp=3、regidx+regext=8
       （top/parameters.scala:9,23,25,30,91）。
    D2. 每 lane 数据用 `Nat → BitVec 32` 函数表示（仅 0..31 有意义），避免
       Fin 索引算术；out_data 同。
    D3.【组事务抽象，核心建模决策】num_sfu 个除法器 + Arbiter 的"整组同步
       完成"抽象为单一环境信号 grpFire + 结果函数 cfg.grpResult : 组→槽→数据。
       合法性依据：
       - :849 `alu_out_arbiter.foreach(x => x.out.ready := AND(all out.valid))`
         ⟹ 整组结果同拍消费（alu_out_fire, :899）；
       - IntDivMod 在 s_finish 反压下 out 稳定（IntDivMod.lean
         `div_finish_stable` 已证）；FloatDivSqrt 同样保持
         （FloatDivSqrt.scala:303,342：s_finish 等待 out.fire，寄存器输出）；
       - in.valid 广播（:893-894）+ AND-ready 使所有 SFU 同拍离 finish
         ⟹ 同拍到 idle ⟹ 下一组同拍受理（:896 只看 SFU0 的 ready 因此安全）；
       - 单 outstanding 组：:909-911 受理后 i_valid 清零，:917 结果回收时才
         重新置位；
       - 每组至多服务一次（:915-916 清除 mask 组位）⟹ grpResult 时间无关，
         可以放进常量 cfg。
       除法延迟被抽象掉——调度/接线正确性与延迟无关。
    D4. data_buffer = Queue(io.in,1)（pipe=false）：chisel3 Queue 语义
       enq.ready = !full（pipe=false 无 deq.ready 旁路；dependencies 未
       vendor chisel3 源码，依据 chisel3 公开语义）⟹ io.in.ready = !bufFull，
       与 FSM 状态无关。s_finish 拍 buffer 满 ⟹ enq.ready=0 ⟹ 无背靠背冒险
       （见 Q6 的反事实分析）。
    D5. 结果队列 result_v/result_x（Queue 1, pipe=true, :813-814）抽象为环境
       rdyV/rdyX（enq.ready）；队列本体精化归 Base/QueueModel 覆盖范围。
    D6. i_valid（:830）不建模：它只门控 SFU in.valid（内部协议细节），不影响
       对外可观测行为——组抽象（D3）已含"组受理→整组完成"的同步。
       :830 原作者注释 "a better valid should change for each fire" 见 Q7。
    D7. IntDivMod 复用 Ventus.Arith.IntDivMod 的 divExec 语义；FP 路径
       （FloatDivSqrt）结果黑盒，仅建模接线与调度（H 区）。
    D8. SPIKE_OUTPUT=false 分支建模（spike_info 字段忽略）。
    D9. FPUexe 输出无队列直连 fpu.io.out（:784-803），vTCexe 有 pipe queue
       （:124,152,160）——差异如实保留：vTCexe 的 queue 抽象为环境 ready，
       只建模 enq 侧组合逻辑；FPUexe 输出纯组合。

   ======================== 黑盒假设清单（H 区） =============================
   【应汇总进 Ventus/Spec/Contracts.lean 的条目；本文件内先集中列示】
    H-FPU-1 VectorFPU ctrl 透传：输出 ctrl.{wvd,wxd,regIndex,warpID,vecMask}
       = 对应输入事务的 ctrl 字段；in-flight 延迟任意。
    H-FPU-2 VectorFPU 握手：in.ready/out.valid 满足 Decoupled 语义；out 在
       反压下 Irrevocable（valid 保持、bits 稳定）。FPUexe 无输出队列
       （:784-803 直连），下游反压直接传导到 FPU 宏，此假设不可缺。
    H-FPU-3 结果数值正确性不在本文件范围（FPU 黑盒既定范围），仅证接线保真。
    H-FPU-4 fpu.io.out.bits.data(x).result 取低 32 位（:785 的 (31,0)）；
       fpuv2 子模块未 vendor（dependencies/fpuv2 为空目录），result 真实
       宽度待查（Q11）。
    H-FDIV-1 FloatDivSqrt 在组抽象内黑盒化：out 反压稳定已由源码确认
       （FloatDivSqrt.scala:303,342），延迟任意、数值不在范围。
    H-TC-1 TensorCoreFP32 ctrl 透传：out.ctrl = 对应输入事务的 ctrl
       （warpID/reg_idxw 经 TC 流水线不变）。
    H-TC-2 TensorCoreFP32 握手：in.ready 由 TC 给出并直通（:136）；out 满足
       Decoupled 语义。
    H-TC-3 TC 无逐 lane 掩码，结果全 lane 写回（:150 wvd_mask 全 1，Q9）——
       正确性依赖 TC 指令级语义（矩阵运算全写回）。
    H-DECODE-1 上游（decode/operandCollector）契约：
       (a) SFU 指令 isvec ⟺ wvd、¬isvec ⟹ wxd（DecodeUnit.scala:225-228,
           237-238,344-355 现状，Q3）；
       (b) 标量 SFU 指令 mask = 0x1（operandCollector.scala:250，Q4）；
       (c) FPU 指令 wvd/wxd 恰一（Q12）。

   ======================== 源码审查疑点（Q 区，上报主会话） ==================
    Q1 (:829) next_i_cnt 是死线（全模块无消费者），疑为遗留优化意图；无功能
       影响。注意其 `1.U(num_thread.W)` 宽 32 而 mask_grp 仅 4 位——若启用
       需重核截断；当前为死代码。
    Q2 (:849) arbiter out.ready = AND(all out.valid)：跨模块隐含契约——要求
       每个 SFU 源在反压下保持 out.valid/bits 稳定。IntDivMod 已证
       （div_finish_stable）；FloatDivSqrt 经审查确认（:303/:342）。非 bug，
       建议断言化。
    Q3 (:865-867)【脆弱点】enq.valid 用 i_ctrl.wxd/wvd，o_ready 用
       i_ctrl.isvec：若出现 isvec=1 ∧ wvd=0 的 SFU 指令，s_finish 会弹
       buffer（o_ready 看 result_v）但两路 enq 均不 valid → 指令无声丢失
       （无写回）。现行 decode 表下 SFU 指令 isvec=wvd、¬isvec=wxd，
       不可达。
    Q4 (:927-930)【脆弱点】标量路径只取 alu_out_arbiter(0)——真实计算在
       SFU 槽 (i_cnt 组内 mask 置位 lane)。标量 mask=0x1 ⟹ 槽 0，正确；
       若标量 mask 置位于其它 lane（上游不产出），:928 取到的是 dummy
       1/1 的结果（DIV 得 1），错数据且无声。依赖 H-DECODE-1(b)。
    Q5 (:877-881) masked-off lane 跑 dummy 除法（int 1/1，float 1.0f）：
       功能无害（结果被 wvd_mask 丢弃），纯功耗浪费；dummy 延迟短，不拖
       AND 同步。非 bug。
    Q6 (:818,902)【脆弱点】背靠背安全性依赖 data_buffer 的 pipe=false：
       s_finish 拍 enq.ready=!full=0 ⟹ 新事务无法该拍入 buffer。若有人改
       成 pipe=true（如同文件 :124 的 result_v），s_finish 拍 enq+deq 同拍
       发生 → 新事务驻留 buffer，但 FSM 回 s_idle 后 io.in.ready=!full=0
       永不 fire → SFU 对该事务永久死锁。现配置安全；"一改即死"，建议
       注释/断言保护。
    Q7 (:830) i_valid 注释自承待改进；经分析单 outstanding 组语义正确，
       无功能问题。
    Q8 (:891) floatDiv op = alu_fn(2,0)：FN_FDIV=0→div ✓（FloatDivSqrt
       .scala:124 isDiv := op===0.U）、FN_FSQRT=1→sqrt ✓；int 编码
       （FN_DIV=0/FN_REM=1）与 fp 编码空间复用但由 i_ctrl.fp 分流
       （:893-894），无冲突。
    Q9 (:150) vTCexe wvd_mask 全 1：TC 数据通路无 mask 字段（:137-145），
       结果全 lane 写回；与 SFU/FPU 的 mask 语义不同。依赖 H-TC-3。
    Q10 (:149) vTCexe wvd := tensor.io.out.valid：wvd 复用为 valid 拷贝；
       配合 :151 enq.valid=out.valid 自洽；下游视 TC 写回恒有效。
    Q11 (:785) FPUexe result(31,0)：fpuv2 未 vendor，result 真实宽度未知；
       若 >32 位则高位被静默丢弃。待查（H-FPU-4）。
    Q12 (:803)【脆弱点】FPUexe fpu.out.ready = Mux(wvd, out_v.ready,
       out_x.ready)：wvd=wxd=0 时 out 可能被消费（ready=out_x.ready）但
       两路 valid 均 0 → 结果丢弃；wvd=wxd=1 时两路同拍 valid 但 ready 只
       看 out_v——若 out_v.ready=1 ∧ out_x.ready=0，fire 后 out_x 侧结果
       丢失。现行 decode 互斥（H-DECODE-1(c)），不可达。
    Q13 (:769-774) FMA 重编码（op:=alu_fn-10、a:=in1,b:=in3,c:=in2）覆盖
       :764-767 的 reverse 交换：decode 表 FMA 系 reverse=N
       （:261-268），冲突不可达。安全。
    Q14 (:915) `Fill(num_sfu,1.U).asTypeOf(UInt(xLen.W)) << i*num_sfu` 依赖
       asTypeOf 窄→宽 zero-pad + 移位扩宽后 connect 截断：32 位 mask 下
       i=0..3 数值核对正确（模型 exsGrpClear 即按此语义，配 decide 测试）。
-/
import Ventus.Base.Defs
import Ventus.Arith.IntDivMod
import Std.Tactic.BVDecide

namespace Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 参数与组合件（:819-829, :840-843, :870, :889, :891, :915）              -/
/- ========================================================================= -/

/-- num_thread（parameters.scala:9） -/
def exsNumThread : Nat := 32
/-- num_sfu（parameters.scala:91：(num_thread>>2).max(1)） -/
def exsNumSfu : Nat := 8
/-- num_grp = num_thread/num_sfu（:820） -/
def exsNumGrp : Nat := 4
/-- regidx_width+regext_width（parameters.scala:23,25） -/
def exsRegW : Nat := 8
/-- depth_warp @ num_warp=8（parameters.scala:30） -/
def exsWidW : Nat := 3

/-- :822 mask_grp(g) = orR(mask[g*8+7 : g*8])（g ≥ 4 时 extractLsb' 补零，恒 false） -/
def exsGrpAt (m : BitVec 32) (g : Nat) : Bool := m.extractLsb' (g * 8) 8 != 0

/-- :821 mask_grp 整体（Vec(num_grp, Bool)），bit g = exsGrpAt m g -/
def exsMaskGrp (m : BitVec 32) : BitVec 4 :=
  (if exsGrpAt m 3 then 8#4 else 0#4) |||
  (if exsGrpAt m 2 then 4#4 else 0#4) |||
  (if exsGrpAt m 1 then 2#4 else 0#4) |||
  (if exsGrpAt m 0 then 1#4 else 0#4)

/-- :828 PriorityEncoder(mask_grp)：最低置位组下标；全 0 退化为 0（Chisel 语义） -/
def exsPrioEnc (mg : BitVec 4) : BitVec 2 :=
  if mg.getLsbD 0 then 0
  else if mg.getLsbD 1 then 1
  else if mg.getLsbD 2 then 2
  else if mg.getLsbD 3 then 3
  else 0

/-- :915 清除组 g 的 8 个 lane 位：mask &&& ~(Fill(8,1) << g*8)（Q14 语义核对后） -/
def exsGrpClear (m : BitVec 32) (g : Nat) : BitVec 32 :=
  m &&& ~~~((0xFF#32) <<< (g * 8))

/-- 组级 mask 的清位（:829 的语义对应物；组抽象机用） -/
def exsGrpClear4 (mg : BitVec 4) (g : Nat) : BitVec 4 :=
  mg &&& ~~~((1#4) <<< g)

/-- :870 结果选择：Mux(alu_fn(0), r, q)（FN_DIV=0/DIVU=2 选 q，FN_REM=1/REMU=3 选 r） -/
def exsSelRem (aluFn : BitVec 6) : Bool := aluFn.getLsbD 0

/-- :889 signed := !alu_fn(1)（FN_DIV=0/REM=1 → signed，FN_DIVU=2/REMU=3 → unsigned） -/
def exsSigned (aluFn : BitVec 6) : Bool := !aluFn.getLsbD 1

/-- :891 floatDiv op := alu_fn(2,0) -/
def exsFdivOp (aluFn : BitVec 6) : BitVec 3 := aluFn.extractLsb' 0 3

/-- :843 i_mask(j) = mask[g*8+j]（组 g 槽 j 的 lane 掩码） -/
def exsGrpMask (m : BitVec 32) (g j : Nat) : Bool := m.getLsbD (g * 8 + j)

/- ========================================================================= -/
/- 2. 组服务序列：纯函数抽象 + 不漏不重证明                                    -/
/- ========================================================================= -/

/-- 组级服务序列递归：反复取 mask_grp 最低置位组、清除、直到空。
    fuel = 4 足够（每步严格清除一个置位组，组总共 4 个） -/
def exsGrpSeqMgGo (mg : BitVec 4) : Nat → List Nat
  | 0 => []
  | fuel + 1 =>
      if mg == 0 then []
      else
        let g := (exsPrioEnc mg).toNat
        g :: exsGrpSeqMgGo (exsGrpClear4 mg g) fuel

/-- 组级服务序列（:828 + :913-924 的纯函数抽象） -/
def exsGrpSeqMg (mg : BitVec 4) : List Nat := exsGrpSeqMgGo mg 4

/-- lane 级入口（:819 mask → mask_grp → 服务序列） -/
def exsGrpSeq (m : BitVec 32) : List Nat := exsGrpSeqMg (exsMaskGrp m)

/- ---- 2.1 基础件引理（16 态组级全枚举 by decide / 位运算 by bv_decide） ---- -/

/-- prioEnc 值域 -/
theorem exsPrioEnc_lt : ∀ mg : BitVec 4, (exsPrioEnc mg).toNat < 4 := by decide

/-- prioEnc 选中的是置位位（mg ≠ 0 时） -/
theorem exsPrioEnc_mem : ∀ mg : BitVec 4, mg ≠ 0 →
    mg.getLsbD (exsPrioEnc mg).toNat = true := by decide

/-- maskGrp 的 bit g 即组 g 的 orR -/
theorem exsMaskGrp_getLsbD (m : BitVec 32) (g : Nat) (hg : g < 4) :
    (exsMaskGrp m).getLsbD g = exsGrpAt m g := by
  have hg' : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 := by omega
  obtain rfl | rfl | rfl | rfl := hg' <;> simp only [exsMaskGrp, exsGrpAt] <;> bv_decide

/-- maskGrp = 0 ⟺ mask = 0（32 位全被 4 组覆盖） -/
theorem exsMaskGrp_eq_zero_iff (m : BitVec 32) : exsMaskGrp m = 0#4 ↔ m = 0#32 := by
  simp only [exsMaskGrp, exsGrpAt] <;> bv_decide

/-- 组清除后 maskGrp 的对应变化（lane 级与组级交换子） -/
theorem exsMaskGrp_clear (m : BitVec 32) (g : Nat) (hg : g < 4) :
    exsMaskGrp (exsGrpClear m g) = exsGrpClear4 (exsMaskGrp m) g := by
  have hg' : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 := by omega
  obtain rfl | rfl | rfl | rfl := hg' <;>
    simp only [exsMaskGrp, exsGrpAt, exsGrpClear, exsGrpClear4] <;> bv_decide

/-- 组掩码位型：(0xFF <<< 8g) 的 bit l ⟺ l 属于组 g -/
theorem exsGrpBits_getLsbD : ∀ g, g < 4 → ∀ l, l < 32 →
    ((0xFF#32) <<< (g * 8)).getLsbD l = decide (l / 8 = g) := by decide

/-- 清组后的逐位刻画 -/
theorem exsGrpClear_getLsbD (m : BitVec 32) (g l : Nat) (hg : g < 4) (hl : l < 32) :
    (exsGrpClear m g).getLsbD l = (m.getLsbD l && !decide (l / 8 = g)) := by
  rw [exsGrpClear, BitVec.getLsbD_and, BitVec.getLsbD_not,
    exsGrpBits_getLsbD g hg l hl]
  simp [hl]

/-- lane 置位 ⟹ 其组在 maskGrp 置位 -/
theorem exsGrpAt_of_getLsbD (m : BitVec 32) (l : Nat) (hl : l < 32)
    (h : m.getLsbD l = true) : exsGrpAt m (l / 8) = true := by
  simp only [exsGrpAt, bne_iff_ne]
  intro heq
  have hbit := BitVec.getLsbD_extractLsb' (l / 8 * 8) 8 m (l % 8)
  have h1 : l / 8 * 8 + l % 8 = l := by omega
  have h2 : l % 8 < 8 := by omega
  simp [heq, h1, h, h2] at hbit

/- ---- 2.2 服务序列性质（组级 16 态全枚举，by decide） ---- -/

/-- 不重：服务序列无重复组 -/
theorem exsGrpSeqMg_nodup : ∀ mg : BitVec 4, (exsGrpSeqMg mg).Nodup := by decide

/-- 不漏：每个置位组都在服务序列中 -/
theorem exsGrpSeqMg_complete : ∀ mg : BitVec 4, ∀ g, g < 4 → mg.getLsbD g = true →
    g ∈ exsGrpSeqMg mg := by decide

/-- 不多：序列中的组都置位且合法 -/
theorem exsGrpSeqMg_sound : ∀ mg : BitVec 4, ∀ g ∈ exsGrpSeqMg mg,
    g < 4 ∧ mg.getLsbD g = true := by decide

/-- 保序：服务序列相邻元素严格递增（PriorityEncoder 逐组服务；
    核心库无 List.Sorted，用 getD 相邻形式，等价于严格递增） -/
theorem exsGrpSeqMg_sorted : ∀ mg : BitVec 4,
    ∀ (i : Nat) (_ : i < (exsGrpSeqMg mg).length - 1),
      (exsGrpSeqMg mg).getD i 0 < (exsGrpSeqMg mg).getD (i + 1) 0 := by decide

/-- 长度上界：至多 num_grp 次服务 -/
theorem exsGrpSeqMg_length : ∀ mg : BitVec 4, (exsGrpSeqMg mg).length ≤ 4 := by decide

/- ---- 2.3 lane 级运输（每 lane 恰好服务一次） ---- -/

/-- lane 覆盖：active lane 的组必在服务序列中 -/
theorem exsGrpSeq_covers (m : BitVec 32) (l : Nat) (hl : l < 32)
    (h : m.getLsbD l = true) : l / 8 ∈ exsGrpSeq m := by
  have hg : l / 8 < 4 := by omega
  have h1 : exsGrpAt m (l / 8) = true := exsGrpAt_of_getLsbD m l hl h
  have h2 : (exsMaskGrp m).getLsbD (l / 8) = true := by
    rw [exsMaskGrp_getLsbD m _ hg]; exact h1
  exact exsGrpSeqMg_complete _ _ hg h2

/-- 不漏不重（lane 级）：active lane 的组在服务序列中恰好出现一次
    （Nodup + mem 即"恰好一次"，组划分 l ↦ l/8 天然唯一） -/
theorem exsGrpSeq_lane_exactly_once (m : BitVec 32) (l : Nat) (hl : l < 32)
    (h : m.getLsbD l = true) :
    (exsGrpSeq m).Nodup ∧ l / 8 ∈ exsGrpSeq m :=
  ⟨exsGrpSeqMg_nodup _, exsGrpSeq_covers m l hl h⟩

/- ---- 2.4 数值回归测试（先测试） ---- -/

section ExsCombTests

-- exsMaskGrp / exsGrpAt（:821-822）
example : exsMaskGrp 0x00000000#32 = 0#4 := by decide
example : exsMaskGrp 0x00000001#32 = 1#4 := by decide
example : exsMaskGrp 0x0000FF00#32 = 2#4 := by decide
example : exsMaskGrp 0xFFFFFFFF#32 = 0xF#4 := by decide
example : exsMaskGrp 0x80000000#32 = 8#4 := by decide
example : exsGrpAt 0x10000#32 2 = true := by decide
example : exsGrpAt 0x10000#32 1 = false := by decide

-- exsPrioEnc（:828，Chisel PriorityEncoder 语义）
example : exsPrioEnc 0b0001#4 = 0#2 := by decide
example : exsPrioEnc 0b1010#4 = 1#2 := by decide
example : exsPrioEnc 0b1100#4 = 2#2 := by decide
example : exsPrioEnc 0b1000#4 = 3#2 := by decide
example : exsPrioEnc 0b0000#4 = 0#2 := by decide   -- 退化：全 0 → 0

-- exsGrpClear（:915）
example : exsGrpClear 0xFFFFFFFF#32 0 = 0xFFFFFF00#32 := by decide
example : exsGrpClear 0xFFFFFFFF#32 2 = 0xFF00FFFF#32 := by decide
example : exsGrpClear 0x00F00F01#32 0 = 0x00F00F00#32 := by decide
example : exsGrpClear 0x00000001#32 0 = 0#32 := by decide

-- alu_fn 译码（:870, :889；FN 编码 DecodeUnit.scala:136-139,140-141）
example : exsSelRem 0#6 = false := by decide    -- FN_DIV → q
example : exsSelRem 1#6 = true := by decide     -- FN_REM → r
example : exsSelRem 2#6 = false := by decide    -- FN_DIVU → q
example : exsSelRem 3#6 = true := by decide     -- FN_REMU → r
example : exsSigned 0#6 = true := by decide     -- FN_DIV → signed
example : exsSigned 1#6 = true := by decide     -- FN_REM → signed
example : exsSigned 2#6 = false := by decide    -- FN_DIVU → unsigned
example : exsSigned 3#6 = false := by decide    -- FN_REMU → unsigned
example : exsFdivOp 0#6 = 0#3 := by decide      -- FN_FDIV → div（FloatDivSqrt.scala:124）
example : exsFdivOp 1#6 = 1#3 := by decide      -- FN_FSQRT → sqrt

-- 服务序列（:828 + :913-924）
example : exsGrpSeq 0xFFFFFFFF#32 = [0, 1, 2, 3] := by decide
example : exsGrpSeq 0x00000000#32 = [] := by decide
example : exsGrpSeq 0x80000001#32 = [0, 3] := by decide
example : exsGrpSeq 0x00FF0000#32 = [2] := by decide
example : exsGrpSeq 0xFFFF00FF#32 = [0, 2, 3] := by decide

end ExsCombTests

/- ========================================================================= -/
/- 3. SFUexe 组抽象时序机（:806-944；组事务抽象见 D3）                        -/
/- ========================================================================= -/

/-- SFU 关心的 CtrlSigs 摘要（scoreboard.scala:19-57 的子集 + :769 用位） -/
structure ExsSfuCtrl where
  reverse : Bool        -- :29 reverse
  aluFn   : BitVec 6    -- alu_fn
  fp      : Bool        -- fp=1 → FloatDivSqrt 路径（:893-894）
  isvec   : Bool        -- isvec（:867, :912）
  wvd     : Bool        -- 向量写回使能（:853, :866）
  wxd     : Bool        -- 标量写回使能（:857, :865）
  regIdxw : BitVec 8    -- reg_idxw
  wid     : BitVec 3    -- wid
deriving DecidableEq, Repr, BEq

/-- vExeData 摘要（issue.scala:17-23；D2 函数式 lane 数据） -/
structure ExsVExeData where
  in1 : Nat → BitVec 32
  in2 : Nat → BitVec 32
  in3 : Nat → BitVec 32
  mask : BitVec 32
  ctrl : ExsSfuCtrl

/-- 空数据（初值占位） -/
def exsEmptyData : ExsVExeData where
  in1 := fun _ => 0
  in2 := fun _ => 0
  in3 := fun _ => 0
  mask := 0
  ctrl := { reverse := false, aluFn := 0, fp := false, isvec := false,
            wvd := false, wxd := false, regIdxw := 0, wid := 0 }

/-- :838-841 i_data1（组 g 槽 j 的 a 操作数，含 reverse 交换） -/
def exsSfuGrpIn1 (d : ExsVExeData) (g j : Nat) : BitVec 32 :=
  if d.ctrl.reverse then d.in2 (g * 8 + j) else d.in1 (g * 8 + j)

/-- :840-841 i_data2 -/
def exsSfuGrpIn2 (d : ExsVExeData) (g j : Nat) : BitVec 32 :=
  if d.ctrl.reverse then d.in1 (g * 8 + j) else d.in2 (g * 8 + j)

/-- :842 i_data3 -/
def exsSfuGrpIn3 (d : ExsVExeData) (g j : Nat) : BitVec 32 :=
  d.in3 (g * 8 + j)

/-- int 路径组结果（:870 q/r 选择 + :884-889 数据接线 + :877-878 dummy 1/1；
    masked-off 槽算 dummy 1/1，结果按 alu_fn(0) 为 q=1/r=0，被 wvd_mask 丢弃）。
    FP 路径结果黑盒（H-FDIV-1），此函数仅用于 i_ctrl.fp=false 的事务。 -/
def exsSfuIntGrpResult (d : ExsVExeData) (g j : Nat) : BitVec 32 :=
  if exsGrpMask d.mask g j then
    let (q, r) := divExec (exsSfuGrpIn1 d g j) (exsSfuGrpIn2 d g j)
                    (exsSigned d.ctrl.aluFn)
    if exsSelRem d.ctrl.aluFn then r else q
  else
    if exsSelRem d.ctrl.aluFn then 0 else 1   -- dummy 1/1 → (q=1, r=0)

/-- FSM 状态（:815） -/
inductive ExsSfuPhase where
  | idle | busy | finish
deriving DecidableEq, Repr, BEq

/-- LawfulBEq 不能 derive，手工给（枚举上逐构造子证明；同 IntDivMod.lean 惯例） -/
instance : LawfulBEq ExsSfuPhase where
  eq_of_beq := by intro a b h; cases a <;> cases b <;> first | rfl | contradiction
  rfl := by intro a; cases a <;> rfl

/-- 状态（:815-830；i_valid 不建模，D6；div/fdiv 内部状态并入组抽象，D3） -/
structure ExsSfuState where
  phase   : ExsSfuPhase
  bufFull : Bool              -- data_buffer（Queue(io.in,1)）maybe_full
  buf     : ExsVExeData       -- data_buffer.bits
  mask    : BitVec 32         -- :819 工作副本（逐组清除）
  outData : Nat → BitVec 32   -- :826 out_data（仅 0..31 有意义）

/-- 初始状态（:816 RegInit(s_idle)，:819 mask=0，:826 out_data=0） -/
def exsSfuInit : ExsSfuState where
  phase := .idle
  bufFull := false
  buf := exsEmptyData
  mask := 0
  outData := fun _ => 0

/-- 环境：每拍输入（组抽象后的 IO） -/
structure ExsSfuEnv where
  inValid : Bool                -- io.in.valid
  inData  : ExsVExeData         -- io.in.bits（inValid=1 时有意义）
  rdyV    : Bool                -- result_v.io.enq.ready（:867）
  rdyX    : Bool                -- result_x.io.enq.ready（:867）
  grpFire : Bool                -- alu_out_fire（:899；整组结果就绪，D3）

/-- 静态配置：组结果函数（每组至多服务一次 ⟹ 时间无关，D3） -/
structure ExsSfuCfg where
  grpResult : Nat → Nat → BitVec 32   -- 组 g 槽 j 的结果

/-- io.in.ready = !bufFull（D4：Queue pipe=false，enq.ready=!full，与状态无关） -/
def exsSfuInReady (s : ExsSfuState) : Bool := !s.bufFull

/-- :867 o_ready -/
def exsSfuORdy (s : ExsSfuState) (rdyV rdyX : Bool) : Bool :=
  (s.buf.ctrl.isvec && rdyV) || (!s.buf.ctrl.isvec && rdyX)

/-- 向量写回通道 enq 侧（:852-856, :866）：bits 直出状态寄存器 -/
structure ExsWbV where
  wb      : Nat → BitVec 32   -- wb_wvd_rd（:854 = out_data）
  wvdMask : BitVec 32         -- wvd_mask（:852 = data_buffer.bits.mask）
  wvd     : Bool              -- :853
  regIdxw : BitVec 8          -- :855
  wid     : BitVec 3          -- :856

/-- :852-856 result_v.io.enq.bits -/
def exsSfuEnqBitsV (s : ExsSfuState) : ExsWbV where
  wb := s.outData
  wvdMask := s.buf.mask
  wvd := s.buf.ctrl.wvd
  regIdxw := s.buf.ctrl.regIdxw
  wid := s.buf.ctrl.wid

/-- :866 result_v.io.enq.valid -/
def exsSfuEnqValidV (s : ExsSfuState) : Bool :=
  s.phase == .finish && s.buf.ctrl.wvd

/-- :865 result_x.io.enq.valid -/
def exsSfuEnqValidX (s : ExsSfuState) : Bool :=
  s.phase == .finish && s.buf.ctrl.wxd

/-- :857-860 result_x.io.enq.bits.wb_wxd_rd = out_data(0) -/
def exsSfuWbX (s : ExsSfuState) : BitVec 32 := s.outData 0

/-- 单拍转移（:900-940 + :897 的 data_buffer.ready + :902-905 的受理） -/
def exsSfuStep (cfg : ExsSfuCfg) (s : ExsSfuState) (e : ExsSfuEnv) : ExsSfuState :=
  let inFire := e.inValid && !s.bufFull          -- io.in.fire（D4）
  match s.phase with
  | .idle =>
      -- :901-906：io.in.fire → 受理（同拍 buffer 入队，D4）
      if inFire then
        { s with
          phase := .busy
          bufFull := true
          buf := e.inData
          mask := e.inData.mask }
      else s
  | .busy =>
      if e.grpFire then
        let g := (exsPrioEnc (exsMaskGrp s.mask)).toNat   -- :828 i_cnt
        if s.buf.ctrl.isvec then
          -- :912-924 向量路径：整组回收，清组，末组转 s_finish
          let m' := exsGrpClear s.mask g                   -- :915-916 next_mask
          let od : Nat → BitVec 32 := fun l =>
            if l / 8 = g then cfg.grpResult g (l % 8) else s.outData l  -- :918
          { s with
            mask := m'
            outData := od
            phase := if m' == 0 then .finish else .busy }  -- :919-922
        else
          -- :927-931 标量路径：out_data(0) := arbiter(0)，转 s_finish
          { s with
            outData := fun l => if l = 0 then cfg.grpResult g 0 else s.outData l
            phase := .finish }
      else s
  | .finish =>
      -- :934-938 + :897：o_ready → 回 idle，弹 buffer，清 out_data
      if exsSfuORdy s e.rdyV e.rdyX then
        { s with
          phase := .idle
          bufFull := false
          outData := fun _ => 0 }
      else s

/-- 多拍执行 -/
def exsSfuRun (cfg : ExsSfuCfg) : ExsSfuState → List ExsSfuEnv → ExsSfuState
  | s, [] => s
  | s, e :: es => exsSfuRun cfg (exsSfuStep cfg s e) es

/- ========================================================================= -/
/- 4. 时序轨迹数值测试（native_decide；先测试后证明）                         -/
/- ========================================================================= -/

section ExsSfuTraceTests

/-- 空环境（无输入、无组完成、下游反压） -/
def exsEnvNop : ExsSfuEnv where
  inValid := false
  inData := exsEmptyData
  rdyV := false
  rdyX := false
  grpFire := false

/-- 测试用向量事务：DIVU（FN_DIVU=2，unsigned，选 q），mask=0x0000FFFF
    （组 0、1 active），in1(l)=l+1, in2(l)=1 -/
def exsTestVecData : ExsVExeData where
  in1 := fun l => BitVec.ofNat 32 (l + 1)
  in2 := fun _ => 1
  in3 := fun _ => 0
  mask := 0x0000FFFF#32
  ctrl := { reverse := false, aluFn := 2#6, fp := false, isvec := true,
            wvd := true, wxd := false, regIdxw := 5#8, wid := 2#3 }

/-- 受理环境 -/
def exsEnvAccept (d : ExsVExeData) : ExsSfuEnv where
  inValid := true
  inData := d
  rdyV := false
  rdyX := false
  grpFire := false

/-- 组完成环境（下游反压） -/
def exsEnvFire : ExsSfuEnv := { exsEnvNop with grpFire := true }

/-- 组完成 + 下游畅通 -/
def exsEnvFireRdy : ExsSfuEnv := { exsEnvNop with grpFire := true, rdyV := true, rdyX := true }

/-- 下游畅通（finish 拍弹出） -/
def exsEnvRdy : ExsSfuEnv := { exsEnvNop with rdyV := true, rdyX := true }

/-- 向量轨迹：受理 → 两次组完成（两组）→ 反压保持 → 弹出 -/
def exsTestVecTrace : List ExsSfuEnv :=
  [exsEnvAccept exsTestVecData, exsEnvFire, exsEnvFire, exsEnvNop]

/-- 终态（反压保持中） -/
def exsTestVecFinal : ExsSfuState :=
  exsSfuRun ⟨exsSfuIntGrpResult exsTestVecData⟩ exsSfuInit exsTestVecTrace

-- 调度：两组各服务一次后转 finish（:919-922）
theorem exs_test_vec_finish : exsTestVecFinal.phase = .finish := by native_decide
theorem exs_test_vec_mask_cleared : exsTestVecFinal.mask = 0#32 := by native_decide
-- mask 保真（:852）：enq.bits.wvd_mask = 原始输入 mask（非清除后的工作副本）
theorem exs_test_vec_mask_fidelity :
    (exsSfuEnqBitsV exsTestVecFinal).wvdMask = 0x0000FFFF#32 := by native_decide
theorem exs_test_vec_enq_valid :
    exsSfuEnqValidV exsTestVecFinal = true := by native_decide
-- 结果-lane 对应（:918 + :884-889）：active lane = 其 lane 数据的除法结果
theorem exs_test_vec_lane3 :      -- lane 3: (3+1)/1 = 4
    (exsSfuEnqBitsV exsTestVecFinal).wb 3 = 4#32 := by native_decide
theorem exs_test_vec_lane9 :      -- lane 9: 10/1 = 10
    (exsSfuEnqBitsV exsTestVecFinal).wb 9 = 10#32 := by native_decide
-- masked-off lane：未服务组（l=16..31 属组 2/3）保持 :826 初值 0；
-- dummy 1/1 仅出现在"已服务组内的 masked 槽"（见 exs_test_bug1_lane0）
theorem exs_test_vec_lane20_unserved :
    (exsSfuEnqBitsV exsTestVecFinal).wb 20 = 0#32 := by native_decide
-- ctrl 透传（:853-856）
theorem exs_test_vec_ctrl_passthrough :
    (exsSfuEnqBitsV exsTestVecFinal).regIdxw = 5#8 ∧
    (exsSfuEnqBitsV exsTestVecFinal).wid = 2#3 ∧
    (exsSfuEnqBitsV exsTestVecFinal).wvd = true := by native_decide

/-- 弹出轨迹：finish 后 rdyV → idle 且 out_data 清零（:937） -/
theorem exs_test_vec_pop :
    let fin := exsSfuRun ⟨exsSfuIntGrpResult exsTestVecData⟩ exsSfuInit
                 (exsTestVecTrace ++ [exsEnvRdy])
    fin.phase = .idle ∧ fin.outData 3 = 0#32 ∧
    exsSfuEnqValidV fin = false ∧ exsSfuInReady fin = true := by native_decide

/-- 反压稳定（Irrevocable 内容）：finish + o_ready=0 保持一拍，bits 不变 -/
theorem exs_test_vec_stall_stable :
    let s1 := exsSfuStep ⟨exsSfuIntGrpResult exsTestVecData⟩ exsTestVecFinal exsEnvNop
    s1.phase = .finish ∧ s1.outData 3 = exsTestVecFinal.outData 3 ∧
    exsSfuEnqValidV s1 = true := by native_decide

/-- BUG1（IntDivMod I-17，div_test_32_bug1_unsigned）封装级 witness：
    lane 3 输入 0x80000000/1（unsigned），SFU 输出 = (1,0) 错误值，
    与 RISC-V 规约 0x80000000 不符——错误锥面原样透过封装到达写回 -/
def exsTestBug1Data : ExsVExeData where
  in1 := fun _ => 0x80000000#32
  in2 := fun _ => 1
  in3 := fun _ => 0
  mask := 0x8#32            -- 仅 lane 3 active（组 0）
  ctrl := { reverse := false, aluFn := 2#6, fp := false, isvec := true,
            wvd := true, wxd := false, regIdxw := 0, wid := 0 }

def exsTestBug1Final : ExsSfuState :=
  exsSfuRun ⟨exsSfuIntGrpResult exsTestBug1Data⟩ exsSfuInit
    [exsEnvAccept exsTestBug1Data, exsEnvFire, exsEnvNop]

theorem exs_test_bug1_lane3 :
    (exsSfuEnqBitsV exsTestBug1Final).wb 3 = 1#32 := by native_decide
theorem exs_test_bug1_ne_spec :
    (exsSfuEnqBitsV exsTestBug1Final).wb 3 ≠
      divSpecQ (0x80000000 : BitVec 32) 1 false := by native_decide
-- 已服务组内 masked 槽（lane 0）= dummy 1/1 的 q=1（Q5；被 wvd_mask 丢弃）
theorem exs_test_bug1_lane0_dummy :
    (exsSfuEnqBitsV exsTestBug1Final).wb 0 = 1#32 := by native_decide

/-- 标量事务（FN_DIV=0，signed，选 q）：-7/2 = -3（:927-931 标量路径） -/
def exsTestScalarData : ExsVExeData where
  in1 := fun l => if l = 0 then 0xFFFFFFF9#32 else 0
  in2 := fun l => if l = 0 then 2 else 0
  in3 := fun _ => 0
  mask := 0x1#32            -- H-DECODE-1(b) 契约
  ctrl := { reverse := false, aluFn := 0#6, fp := false, isvec := false,
            wvd := false, wxd := true, regIdxw := 7#8, wid := 1#3 }

def exsTestScalarFinal : ExsSfuState :=
  exsSfuRun ⟨exsSfuIntGrpResult exsTestScalarData⟩ exsSfuInit
    [exsEnvAccept exsTestScalarData, exsEnvFire, exsEnvNop]

theorem exs_test_scalar_result :
    exsSfuWbX exsTestScalarFinal = 0xFFFFFFFD#32 := by native_decide
theorem exs_test_scalar_valid :
    exsSfuEnqValidX exsTestScalarFinal = true ∧
    exsSfuEnqValidV exsTestScalarFinal = false := by native_decide

/-- reverse 交换（:840-841）的封装级检查：REMU 且 reverse=1 时 a=in2=20、
    d=in1=7，20%7=6。本用例曾作为 BUG3/I-18 的透传 witness（钉 r=14；
    注释曾误标 "I-19"）；I-18 撤案后（doc/23：II 类误译，Chisel 6 `+` 回绕，
    RTL 恢复路径本就正确）改钉 RISC-V 规约值 6，并断言与规约一致 -/
def exsTestRevData : ExsVExeData where
  in1 := fun _ => 7     -- 交换后作除数
  in2 := fun _ => 20    -- 交换后作被除数
  in3 := fun _ => 0
  mask := 0xFF#32
  ctrl := { reverse := true, aluFn := 3#6, fp := false, isvec := true,
            wvd := true, wxd := false, regIdxw := 0, wid := 0 }

def exsTestRevFinal : ExsSfuState :=
  exsSfuRun ⟨exsSfuIntGrpResult exsTestRevData⟩ exsSfuInit
    [exsEnvAccept exsTestRevData, exsEnvFire, exsEnvNop]

theorem exs_test_reverse :      -- 20 REMU 7 = 6（RISC-V 规约；I-18 撤案修正）
    (exsSfuEnqBitsV exsTestRevFinal).wb 5 = 6#32 := by native_decide
theorem exs_test_reverse_eq_spec :
    (exsSfuEnqBitsV exsTestRevFinal).wb 5 =
      divSpecR (20 : BitVec 32) 7 false := by native_decide

/-- mask=0 的向量事务：一次组完成即 finish（:919 !next_mask.orR），无写回 -/
def exsTestZeroMaskData : ExsVExeData :=
  { exsTestVecData with mask := 0#32 }

def exsTestZeroMaskFinal : ExsSfuState :=
  exsSfuRun ⟨exsSfuIntGrpResult exsTestZeroMaskData⟩ exsSfuInit
    [exsEnvAccept exsTestZeroMaskData, exsEnvFire, exsEnvNop]

theorem exs_test_zero_mask :
    exsTestZeroMaskFinal.phase = .finish ∧
    (exsSfuEnqBitsV exsTestZeroMaskFinal).wvdMask = 0#32 := by native_decide

/-- in.ready 刻画（D4） -/
theorem exs_test_in_ready :
    exsSfuInReady exsSfuInit = true ∧
    exsSfuInReady exsTestVecFinal = false := by native_decide

end ExsSfuTraceTests

/- ========================================================================= -/
/- 5. 时序机定理                                                              -/
/- ========================================================================= -/

/-- 组级 mask 单步动力学（grpFire 拍 maskGrp 的演化：取最低置位组并清除） -/
def exsMgFire (mg : BitVec 4) : BitVec 4 := exsGrpClear4 mg (exsPrioEnc mg).toNat

/-- 迭代（本环境无 f^[n] 记法，自写；方程引理即定义） -/
def exsMgFireN : Nat → BitVec 4 → BitVec 4
  | 0, mg => mg
  | k + 1, mg => exsMgFireN k (exsMgFire mg)

/-- 至多 4 次 grpFire 后组级 mask 必空（16 态全枚举） -/
theorem exsMgFire4 : ∀ mg : BitVec 4,
    exsMgFire (exsMgFire (exsMgFire (exsMgFire mg))) = 0#4 := by decide

/-- 输出 bits 直出寄存器：wvd_mask = buf.mask（:852；mask 保真的组合层） -/
theorem exsSfu_enqBitsV_mask (s : ExsSfuState) :
    (exsSfuEnqBitsV s).wvdMask = s.buf.mask := rfl

/-- enq valid 仅在 s_finish（:866） -/
theorem exsSfu_enqValidV_iff (s : ExsSfuState) :
    exsSfuEnqValidV s = true ↔ s.phase = .finish ∧ s.buf.ctrl.wvd = true := by
  simp [exsSfuEnqValidV, Bool.and_eq_true, beq_iff_eq]

/-- enq valid 仅在 s_finish（:865） -/
theorem exsSfu_enqValidX_iff (s : ExsSfuState) :
    exsSfuEnqValidX s = true ↔ s.phase = .finish ∧ s.buf.ctrl.wxd = true := by
  simp [exsSfuEnqValidX, Bool.and_eq_true, beq_iff_eq]

/-- finish 反压稳定（Irrevocable 内容：o_ready=0 时整状态保持；:934-938） -/
theorem exsSfu_finish_stable (cfg : ExsSfuCfg) (s : ExsSfuState) (e : ExsSfuEnv)
    (hfin : s.phase = .finish) (ho : exsSfuORdy s e.rdyV e.rdyX = false) :
    exsSfuStep cfg s e = s := by
  simp [exsSfuStep, hfin, ho]

/-- 非 idle 拍 buf 不变（:902 只在 s_idle 受理时装载） -/
theorem exsSfuStep_buf_of_not_idle (cfg : ExsSfuCfg) (s : ExsSfuState) (e : ExsSfuEnv)
    (h : s.phase ≠ .idle) : (exsSfuStep cfg s e).buf = s.buf := by
  cases hp : s.phase with
  | idle => exact absurd hp h
  | busy =>
      cases hf : e.grpFire
      · simp [exsSfuStep, hp, hf]
      · cases hv : s.buf.ctrl.isvec <;> simp [exsSfuStep, hp, hf, hv]
  | finish =>
      cases ho : exsSfuORdy s e.rdyV e.rdyX <;> simp [exsSfuStep, hp, ho]

/-- busy + grpFire + isvec 的转移刻画（:908-925 向量路径） -/
theorem exsSfuStep_busy_vec (cfg : ExsSfuCfg) (s : ExsSfuState) (e : ExsSfuEnv)
    (hbusy : s.phase = .busy) (hvec : s.buf.ctrl.isvec = true)
    (hfire : e.grpFire = true) :
    exsSfuStep cfg s e =
      { s with
        mask := exsGrpClear s.mask ((exsPrioEnc (exsMaskGrp s.mask)).toNat)
        outData := fun l =>
          if l / 8 = (exsPrioEnc (exsMaskGrp s.mask)).toNat then
            cfg.grpResult ((exsPrioEnc (exsMaskGrp s.mask)).toNat) (l % 8)
          else s.outData l
        phase := if exsGrpClear s.mask ((exsPrioEnc (exsMaskGrp s.mask)).toNat) == 0 then
          .finish else .busy } := by
  simp [exsSfuStep, hbusy, hfire, hvec]

/-- 向量组回收：要么转 finish，要么 busy 且组级 mask 按 exsMgFire 演化 -/
theorem exsSfuStep_busy_vec_char (cfg : ExsSfuCfg) (s : ExsSfuState) (e : ExsSfuEnv)
    (hbusy : s.phase = .busy) (hvec : s.buf.ctrl.isvec = true)
    (hfire : e.grpFire = true) :
    (exsSfuStep cfg s e).phase = .finish ∨
    ((exsSfuStep cfg s e).phase = .busy ∧
     exsMaskGrp (exsSfuStep cfg s e).mask = exsMgFire (exsMaskGrp s.mask)) := by
  rw [exsSfuStep_busy_vec cfg s e hbusy hvec hfire]
  by_cases hm : exsGrpClear s.mask (exsPrioEnc (exsMaskGrp s.mask)).toNat == 0
  · have hm' : exsGrpClear s.mask (exsPrioEnc (exsMaskGrp s.mask)).toNat = 0 :=
      eq_of_beq hm
    left
    simp [hm']
  · have hm' : exsGrpClear s.mask (exsPrioEnc (exsMaskGrp s.mask)).toNat ≠ 0 :=
      fun h => hm (by rw [h]; exact beq_self_eq_true _)
    right
    constructor
    · exact if_neg hm
    · show exsMaskGrp (exsGrpClear s.mask ((exsPrioEnc (exsMaskGrp s.mask)).toNat)) = _
      rw [exsMaskGrp_clear _ _ (exsPrioEnc_lt _)]
      rfl

/-- 服务不变量（busy/finish 期间）：buf 保持受理值；已清除的 active lane 的
    outData = 其组其槽的 grpResult（:918）；mask 只清不增；向量事务到 finish
    时 mask 必已清空；标量事务 mask 不动 -/
def exsSfuServedOk (cfg : ExsSfuCfg) (d : ExsVExeData) (s : ExsSfuState) : Prop :=
  s.buf = d ∧ s.bufFull = true ∧
  (∀ l, l < 32 → d.mask.getLsbD l = true → s.mask.getLsbD l = false →
    s.outData l = cfg.grpResult (l / 8) (l % 8)) ∧
  (∀ l, l < 32 → s.mask.getLsbD l = true → d.mask.getLsbD l = true) ∧
  (d.ctrl.isvec = true → s.phase = .finish → s.mask = 0) ∧
  (d.ctrl.isvec = false → s.mask = d.mask)

/-- 受理建立不变量（:901-906） -/
theorem exsSfuServedOk_accept (cfg : ExsSfuCfg) (s : ExsSfuState) (e : ExsSfuEnv)
    (h : s.phase = .idle) (hv : e.inValid = true) (hf : s.bufFull = false) :
    exsSfuServedOk cfg e.inData (exsSfuStep cfg s e) := by
  have hfire : (e.inValid && !s.bufFull) = true := by simp [hv, hf]
  simp only [exsSfuStep, h, hfire, if_true]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro l hl hact hclr
    change (e.inData.mask).getLsbD l = false at hclr
    rw [hact] at hclr
    exact Bool.noConfusion hclr
  · intro l hl hbit; exact hbit
  · intro _ hfin; exact ExsSfuPhase.noConfusion hfin
  · intro _; rfl

/-- 单拍保持（在非 idle 拍且下一拍不回 idle 时） -/
theorem exsSfuServedOk_step (cfg : ExsSfuCfg) (d : ExsVExeData) (s : ExsSfuState)
    (e : ExsSfuEnv) (h : exsSfuServedOk cfg d s) (hphase : s.phase ≠ .idle)
    (hnext : (exsSfuStep cfg s e).phase ≠ .idle) :
    exsSfuServedOk cfg d (exsSfuStep cfg s e) := by
  obtain ⟨hbuf, hfull, h3, h4, h5, h6⟩ := h
  cases hp : s.phase with
  | idle => exact absurd hp hphase
  | finish =>
      cases ho : exsSfuORdy s e.rdyV e.rdyX
      · -- oRdy=false：停留
        simp [exsSfuStep, hp, ho]
        exact ⟨hbuf, hfull, h3, h4, h5, h6⟩
      · -- oRdy=true：回 idle，与 hnext 矛盾
        simp [exsSfuStep, hp, ho] at hnext
  | busy =>
      cases hf : e.grpFire
      · -- 无组完成：停留
        simp [exsSfuStep, hp, hf]
        exact ⟨hbuf, hfull, h3, h4, h5, h6⟩
      · cases hv : s.buf.ctrl.isvec
        · -- 标量（:927-931）
          have hsc : d.ctrl.isvec = false := by rw [← hbuf]; exact hv
          have hmask : s.mask = d.mask := h6 hsc
          simp only [exsSfuStep, hp, hf, hv]
          refine ⟨hbuf, hfull, ?_, ?_, ?_, ?_⟩
          · intro l hl hact hclr
            rw [← hmask] at hact
            change s.mask.getLsbD l = false at hclr
            rw [hact] at hclr
            exact Bool.noConfusion hclr
          · intro l hl hbit
            change s.mask.getLsbD l = true at hbit
            rw [hmask] at hbit; exact hbit
          · intro hvec'; rw [hsc] at hvec'; exact Bool.noConfusion hvec'
          · intro _; exact hmask
        · -- 向量组回收（:912-924）
          have hvec : d.ctrl.isvec = true := by rw [← hbuf]; exact hv
          have hg_lt : (exsPrioEnc (exsMaskGrp s.mask)).toNat < 4 := exsPrioEnc_lt _
          rw [exsSfuStep_busy_vec cfg s e hp hv hf]
          refine ⟨hbuf, hfull, ?_, ?_, ?_, ?_⟩
          · -- 已清除 lane 的 outData 正确
            intro l hl hact hclr
            change (exsGrpClear s.mask
              (exsPrioEnc (exsMaskGrp s.mask)).toNat).getLsbD l = false at hclr
            change (if l / 8 = (exsPrioEnc (exsMaskGrp s.mask)).toNat then
                cfg.grpResult ((exsPrioEnc (exsMaskGrp s.mask)).toNat) (l % 8)
                else s.outData l) = cfg.grpResult (l / 8) (l % 8)
            rw [exsGrpClear_getLsbD s.mask _ l hg_lt hl] at hclr
            by_cases hlg : l / 8 = (exsPrioEnc (exsMaskGrp s.mask)).toNat
            · simp [hlg]
            · simp only [hlg, if_false]
              simp [hlg] at hclr
              exact h3 l hl hact hclr
          · -- mask 只清不增
            intro l hl hbit
            change (exsGrpClear s.mask
              (exsPrioEnc (exsMaskGrp s.mask)).toNat).getLsbD l = true at hbit
            rw [exsGrpClear_getLsbD s.mask _ l hg_lt hl] at hbit
            by_cases hlg : l / 8 = (exsPrioEnc (exsMaskGrp s.mask)).toNat
            · simp [hlg] at hbit
            · simp [hlg] at hbit
              exact h4 l hl hbit
          · -- 到 finish 时 mask=0
            intro _ hfin
            change (if exsGrpClear s.mask (exsPrioEnc (exsMaskGrp s.mask)).toNat == 0
              then ExsSfuPhase.finish else ExsSfuPhase.busy) = ExsSfuPhase.finish at hfin
            by_cases hm : exsGrpClear s.mask (exsPrioEnc (exsMaskGrp s.mask)).toNat == 0
            · exact eq_of_beq hm
            · rw [if_neg hm] at hfin
              exact ExsSfuPhase.noConfusion hfin
          · intro hsc; rw [hsc] at hvec; exact Bool.noConfusion hvec

/-- 迹级保持：中间不回 idle 则不变量保持到末态 -/
theorem exsSfuServedOk_run (cfg : ExsSfuCfg) (d : ExsVExeData) (s : ExsSfuState)
    (envs : List ExsSfuEnv) (h : exsSfuServedOk cfg d s) (hphase : s.phase ≠ .idle)
    (hstay : ∀ pre suf : List ExsSfuEnv, pre ++ suf = envs →
      (exsSfuRun cfg s pre).phase ≠ .idle) :
    exsSfuServedOk cfg d (exsSfuRun cfg s envs) := by
  induction envs generalizing s with
  | nil => exact h
  | cons e es ih =>
      have hnext : (exsSfuStep cfg s e).phase ≠ .idle := by
        have h0 := hstay [e] es rfl
        simpa [exsSfuRun] using h0
      have h' := exsSfuServedOk_step cfg d s e h hphase hnext
      exact ih (exsSfuStep cfg s e) h' hnext (fun pre suf hpre => by
        have h0 := hstay (e :: pre) suf (by rw [List.cons_append, hpre])
        simpa [exsSfuRun] using h0)

/-- 【结果-lane 对应，向量】到达 finish 时，每个 active lane 的写回数据 =
    其所在组、所在槽的 grpResult（:918 + :884-889）。int 路径把 grpResult
    实例化为 exsSfuIntGrpResult 即得"= divExec 该 lane 数据" -/
theorem exsSfu_vec_lane_correct (cfg : ExsSfuCfg) (d : ExsVExeData) (s : ExsSfuState)
    (envs : List ExsSfuEnv) (h : exsSfuServedOk cfg d s) (hphase : s.phase ≠ .idle)
    (hstay : ∀ pre suf : List ExsSfuEnv, pre ++ suf = envs →
      (exsSfuRun cfg s pre).phase ≠ .idle)
    (hfin : (exsSfuRun cfg s envs).phase = .finish)
    (hvec : d.ctrl.isvec = true) (l : Nat) (hl : l < 32)
    (hact : d.mask.getLsbD l = true) :
    (exsSfuRun cfg s envs).outData l = cfg.grpResult (l / 8) (l % 8) := by
  obtain ⟨hbuf, hfull, h3, h4, h5, h6⟩ := exsSfuServedOk_run cfg d s envs h hphase hstay
  have hm0 : (exsSfuRun cfg s envs).mask = 0 := h5 hvec hfin
  have hclr : (exsSfuRun cfg s envs).mask.getLsbD l = false := by
    rw [hm0]; exact BitVec.getLsbD_zero
  exact h3 l hl hact hclr

/-- 【mask 保真】从受理到 finish（中间不回 idle），enq.bits.wvd_mask =
    受理时的输入 mask（:852；:819 的工作副本被逐组清除不影响写回掩码） -/
theorem exsSfu_mask_fidelity (cfg : ExsSfuCfg) (s : ExsSfuState) (e : ExsSfuEnv)
    (es : List ExsSfuEnv) (h : s.phase = .idle) (hv : e.inValid = true)
    (hf : s.bufFull = false)
    (hstay : ∀ pre suf : List ExsSfuEnv, pre ++ suf = es →
      (exsSfuRun cfg (exsSfuStep cfg s e) pre).phase ≠ .idle) :
    (exsSfuEnqBitsV (exsSfuRun cfg (exsSfuStep cfg s e) es)).wvdMask = e.inData.mask := by
  have hacc := exsSfuServedOk_accept cfg s e h hv hf
  have hphase : (exsSfuStep cfg s e).phase ≠ .idle := by
    simp [exsSfuStep, h, hv, hf]
  have hinv := exsSfuServedOk_run cfg e.inData (exsSfuStep cfg s e) es hacc hphase hstay
  show (exsSfuRun cfg (exsSfuStep cfg s e) es).buf.mask = e.inData.mask
  rw [hinv.1]

/-- 非 busy 吸收：无输入时，非 busy 状态永不回 busy -/
theorem exsSfu_not_busy_absorb (cfg : ExsSfuCfg) (s : ExsSfuState) (es : List ExsSfuEnv)
    (hnb : s.phase ≠ .busy) (hnoin : ∀ e ∈ es, e.inValid = false) :
    (exsSfuRun cfg s es).phase ≠ .busy := by
  induction es generalizing s with
  | nil => exact hnb
  | cons e es ih =>
      apply ih
      · cases hp : s.phase with
        | idle =>
            have hn : e.inValid = false := hnoin e (List.mem_cons_self ..)
            simp [exsSfuStep, hp, hn]
        | busy => exact absurd hp hnb
        | finish =>
            cases ho : exsSfuORdy s e.rdyV e.rdyX <;> simp [exsSfuStep, hp, ho]
      · intro e' he'; exact hnoin e' (List.mem_cons_of_mem e he')

/-- busy 态经 grpFire 仍是 busy ⟹ 组级 mask 非空（:919-922：mask 清空即转 finish） -/
theorem exsSfuStep_busy_vec_maskGrp_ne (cfg : ExsSfuCfg) (s : ExsSfuState) (e : ExsSfuEnv)
    (hbusy : s.phase = .busy) (hvec : s.buf.ctrl.isvec = true)
    (hfire : e.grpFire = true)
    (hb : (exsSfuStep cfg s e).phase = .busy) :
    exsMaskGrp (exsSfuStep cfg s e).mask ≠ 0 := by
  have heq := exsSfuStep_busy_vec cfg s e hbusy hvec hfire
  have h1 : (exsSfuStep cfg s e).phase =
      (if exsGrpClear s.mask (exsPrioEnc (exsMaskGrp s.mask)).toNat == 0 then
        ExsSfuPhase.finish else ExsSfuPhase.busy) := by rw [heq]
  rw [hb] at h1
  have hm : ¬(exsGrpClear s.mask (exsPrioEnc (exsMaskGrp s.mask)).toNat == 0) = true := by
    intro hcon
    rw [if_pos hcon] at h1
    exact ExsSfuPhase.noConfusion h1
  have hm' : exsGrpClear s.mask (exsPrioEnc (exsMaskGrp s.mask)).toNat ≠ 0 :=
    fun h => hm (by rw [h]; exact beq_self_eq_true _)
  have hmask : (exsSfuStep cfg s e).mask =
      exsGrpClear s.mask ((exsPrioEnc (exsMaskGrp s.mask)).toNat) := by rw [heq]
  rw [hmask]
  exact fun hz => hm' ((exsMaskGrp_eq_zero_iff _).mp hz)

/-- 终止性辅助：busy 出发全程 grpFire、busy 态组级 mask 非空，若末态仍 busy
    则组级 mask 的 es.length 次 exsMgFire 迭代非空 -/
theorem exsSfu_vec_terminates_aux (cfg : ExsSfuCfg) (s : ExsSfuState) (es : List ExsSfuEnv)
    (hvec : s.buf.ctrl.isvec = true)
    (hpre : s.phase = .busy → exsMaskGrp s.mask ≠ 0)
    (hfire : ∀ e ∈ es, e.grpFire = true) (hnoin : ∀ e ∈ es, e.inValid = false)
    (hfin : (exsSfuRun cfg s es).phase = .busy) :
    exsMgFireN es.length (exsMaskGrp s.mask) ≠ 0 := by
  induction es generalizing s with
  | nil => exact hpre hfin
  | cons e es ih =>
      have hfe : e.grpFire = true := hfire e (List.mem_cons_self ..)
      have hne : e.inValid = false := hnoin e (List.mem_cons_self ..)
      have hfire' : ∀ e' ∈ es, e'.grpFire = true :=
        fun e' h' => hfire e' (List.mem_cons_of_mem e h')
      have hnoin' : ∀ e' ∈ es, e'.inValid = false :=
        fun e' h' => hnoin e' (List.mem_cons_of_mem e h')
      have hrun : exsSfuRun cfg s (e :: es) = exsSfuRun cfg (exsSfuStep cfg s e) es := rfl
      cases hp : s.phase with
      | busy =>
          have hch := exsSfuStep_busy_vec_char cfg s e hp hvec hfe
          cases hch with
          | inl hfin1 =>
              have hnb : (exsSfuRun cfg (exsSfuStep cfg s e) es).phase ≠ .busy := by
                apply exsSfu_not_busy_absorb
                · simp [hfin1]
                · exact hnoin'
              exact absurd (hrun ▸ hfin) hnb
          | inr hstep =>
              have hbuf : (exsSfuStep cfg s e).buf = s.buf :=
                exsSfuStep_buf_of_not_idle cfg s e (by simp [hp])
              have hvec' : (exsSfuStep cfg s e).buf.ctrl.isvec = true := by
                rw [hbuf]; exact hvec
              have hpre' : (exsSfuStep cfg s e).phase = .busy →
                  exsMaskGrp (exsSfuStep cfg s e).mask ≠ 0 :=
                exsSfuStep_busy_vec_maskGrp_ne cfg s e hp hvec hfe
              have hih := ih (exsSfuStep cfg s e) hvec' hpre' hfire' hnoin' (hrun ▸ hfin)
              rw [hstep.2] at hih
              exact hih
      | idle =>
          have hnb : (exsSfuRun cfg (exsSfuStep cfg s e) es).phase ≠ .busy := by
            apply exsSfu_not_busy_absorb
            · simp [exsSfuStep, hp, hne]
            · exact hnoin'
          exact absurd (hrun ▸ hfin) hnb
      | finish =>
          have hnb : (exsSfuRun cfg (exsSfuStep cfg s e) es).phase ≠ .busy := by
            apply exsSfu_not_busy_absorb
            · cases ho : exsSfuORdy s e.rdyV e.rdyX <;> simp [exsSfuStep, hp, ho]
            · exact hnoin'
          exact absurd (hrun ▸ hfin) hnb

/-- 【活性】向量事务：busy 出发至多 4 拍 grpFire 必离开 busy
    （:919-922 逐组清除 + exsMgFire4 的 16 态枚举） -/
theorem exsSfu_vec_terminates (cfg : ExsSfuCfg) (s : ExsSfuState) (es : List ExsSfuEnv)
    (hbusy : s.phase = .busy) (hvec : s.buf.ctrl.isvec = true)
    (hlen : es.length = 4)
    (hfire : ∀ e ∈ es, e.grpFire = true) (hnoin : ∀ e ∈ es, e.inValid = false) :
    (exsSfuRun cfg s es).phase ≠ .busy := by
  have hne : es ≠ [] := by intro h; simp [h] at hlen
  obtain ⟨e0, es1, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hne1 : es1 ≠ [] := by intro h; simp [h] at hlen
  obtain ⟨e1, es2, rfl⟩ := List.exists_cons_of_ne_nil hne1
  have hne2 : es2 ≠ [] := by intro h; simp [h] at hlen
  obtain ⟨e2, es3, rfl⟩ := List.exists_cons_of_ne_nil hne2
  have hne3 : es3 ≠ [] := by intro h; simp [h] at hlen
  obtain ⟨e3, es4, rfl⟩ := List.exists_cons_of_ne_nil hne3
  obtain rfl : es4 = [] := by
    cases es4 with
    | nil => rfl
    | cons => simp [List.length_cons] at hlen
  have hf0 : e0.grpFire = true := hfire e0 (List.mem_cons_self ..)
  have hni : ∀ e' ∈ [e1, e2, e3], e'.inValid = false := by
    intro e' he'
    simp at he'
    obtain rfl | rfl | rfl := he' <;>
      exact hnoin _ (by simp)
  have hfi : ∀ e' ∈ [e1, e2, e3], e'.grpFire = true := by
    intro e' he'
    simp at he'
    obtain rfl | rfl | rfl := he' <;>
      exact hfire _ (by simp)
  intro hb
  have hrun : exsSfuRun cfg s [e0, e1, e2, e3] =
      exsSfuRun cfg (exsSfuStep cfg s e0) [e1, e2, e3] := rfl
  have hch0 := exsSfuStep_busy_vec_char cfg s e0 hbusy hvec hf0
  cases hch0 with
  | inl hfin1 =>
      exact absurd (hrun ▸ hb)
        (exsSfu_not_busy_absorb _ _ _ (by simp [hfin1]) hni)
  | inr hstep0 =>
      have hbuf0 : (exsSfuStep cfg s e0).buf = s.buf :=
        exsSfuStep_buf_of_not_idle cfg s e0 (by simp [hbusy])
      have haux := exsSfu_vec_terminates_aux cfg (exsSfuStep cfg s e0) [e1, e2, e3]
        (by rw [hbuf0]; exact hvec)
        (exsSfuStep_busy_vec_maskGrp_ne cfg s e0 hbusy hvec hf0)
        hfi hni (hrun ▸ hb)
      rw [hstep0.2] at haux
      exact haux (exsMgFire4 _)

/-- 【Q3 形式化】isvec=1 ∧ wvd=0 ∧ wxd=0 的事务在 s_finish：o_ready 只看
    result_v（:867），两路 enq 均不 valid（:865-866）→ 弹 buffer 但无写回，
    指令无声丢失。现行 decode 不可达（H-DECODE-1(a)），属脆弱点 -/
theorem exsSfu_q3_silent_drop (s : ExsSfuState)
    (hp : s.phase = .finish) (hvec : s.buf.ctrl.isvec = true)
    (hwvd : s.buf.ctrl.wvd = false) (hwxd : s.buf.ctrl.wxd = false)
    (rdyV rdyX : Bool) :
    exsSfuORdy s rdyV rdyX = rdyV ∧
    exsSfuEnqValidV s = false ∧ exsSfuEnqValidX s = false := by
  simp [exsSfuORdy, exsSfuEnqValidV, exsSfuEnqValidX, hp, hvec, hwvd, hwxd]

/-- Q4 形式化的测试侧证据（反事实：标量 mask=0x2 违反 H-DECODE-1(b)）：
    真实数据在 lane 1（SFU 槽 1），:928 取 arbiter(0) = 槽 0 的 dummy 1/1 →
    写回 1 而非 10/2=5。注：operandCollector.scala:250 使标量 mask 恒 0x1，
    现行不可达 -/
def exsTestScalarBadMaskData : ExsVExeData where
  in1 := fun l => if l = 1 then 10 else 0
  in2 := fun l => if l = 1 then 2 else 0
  in3 := fun _ => 0
  mask := 0x2#32
  ctrl := { reverse := false, aluFn := 2#6, fp := false, isvec := false,
            wvd := false, wxd := true, regIdxw := 0, wid := 0 }

theorem exs_test_q4_bad_mask :
    let fin := exsSfuRun ⟨exsSfuIntGrpResult exsTestScalarBadMaskData⟩ exsSfuInit
                 [exsEnvAccept exsTestScalarBadMaskData, exsEnvFire, exsEnvNop]
    exsSfuWbX fin = 1#32 ∧
    exsSfuWbX fin ≠ divSpecQ (10 : BitVec 32) 2 false := by native_decide

/- ========================================================================= -/
/- 6. FPUexe（:746-804；VectorFPU 黑盒，假设见 H-FPU-*）                      -/
/- ========================================================================= -/

/-- FPU 每 lane 输入摘要（FPUv2 VectorFPU data 字段；数值语义黑盒 H-FPU-3） -/
structure ExsFpuLaneIn where
  a  : BitVec 32
  b  : BitVec 32
  c  : BitVec 32
  rm : BitVec 3
  op : BitVec 6
deriving DecidableEq, Repr

/-- :759-775 每 lane 输入打包：reverse 交换（:764-767）在先、FMA 重编码
    （:769-774，FN_VFMADD=14/FMSUB=15/FNMSUB=16/FNMADD=17 → op-10 且
    (a,b,c)=(in1,in3,in2)）覆盖在后 -/
def exsFpuPackLane (in1 in2 in3 : BitVec 32) (aluFn : BitVec 6) (reverse : Bool)
    (rm : BitVec 3) : ExsFpuLaneIn :=
  let a0 := if reverse then in2 else in1
  let b0 := if reverse then in1 else in2
  if aluFn == 14#6 || aluFn == 15#6 || aluFn == 16#6 || aluFn == 17#6 then
    { a := in1, b := in3, c := in2, rm := rm, op := aluFn - 10#6 }
  else
    { a := a0, b := b0, c := in3, rm := rm, op := aluFn }

/-- :776-780 FPU 输入 ctrl（wvd/wxd/regIndex/warpID/vecMask 直传） -/
structure ExsFpuCtrlIn where
  wvd : Bool
  wxd : Bool
  regIndex : BitVec 8
  warpID : BitVec 3
  vecMask : BitVec 32
deriving DecidableEq, Repr

/-- FPU 输出摘要（黑盒消费对象；result 已取 (31,0)，H-FPU-4/Q11） -/
structure ExsFpuOut where
  valid : Bool
  result : Nat → BitVec 32
  wvd : Bool
  wxd : Bool
  regIndex : BitVec 8
  warpID : BitVec 3
  vecMask : BitVec 32

/-- :801 out_v.valid -/
def exsFpuOutVValid (o : ExsFpuOut) : Bool := o.valid && o.wvd

/-- :802 out_x.valid -/
def exsFpuOutXValid (o : ExsFpuOut) : Bool := o.valid && o.wxd

/-- :803 fpu.io.out.ready = Mux(wvd, out_v.ready, out_x.ready) -/
def exsFpuOutRdy (o : ExsFpuOut) (rdyV rdyX : Bool) : Bool :=
  if o.wvd then rdyV else rdyX

/-- :784-786, :794, :796, :798-799 out_v.bits（无队列直连，D9） -/
def exsFpuWbV (o : ExsFpuOut) : ExsWbV where
  wb := o.result
  wvdMask := o.vecMask
  wvd := o.wvd
  regIdxw := o.regIndex
  wid := o.warpID

/-- :793 out_x.bits.wb_wxd_rd = data(0).result -/
def exsFpuWbX (o : ExsFpuOut) : BitVec 32 := o.result 0

/-- mask 保真（组合层，:798）：out_v.wvd_mask = FPU 输出 vecMask -/
theorem exsFpu_wvMask (o : ExsFpuOut) : (exsFpuWbV o).wvdMask = o.vecMask := rfl

/-- mask 端到端保真（假设 H-FPU-1 ctrl 透传：o.vecMask = 输入 mask） -/
theorem exsFpu_mask_fidelity (o : ExsFpuOut) (m : BitVec 32)
    (h : o.vecMask = m) : (exsFpuWbV o).wvdMask = m := h

/-- 【Q12 形式化】wvd=wxd=0 时两路 valid 均 0，但 fpu.out.ready = out_x.ready
    ——out_x.ready=1 时结果被消费且无任何写回（结果丢弃） -/
theorem exsFpu_q12_drop (o : ExsFpuOut) (rdyV rdyX : Bool)
    (hv : o.wvd = false) (hx : o.wxd = false) :
    exsFpuOutVValid o = false ∧ exsFpuOutXValid o = false ∧
    exsFpuOutRdy o rdyV rdyX = rdyX := by
  simp [exsFpuOutVValid, exsFpuOutXValid, exsFpuOutRdy, hv, hx]

/-- 【Q12 形式化】wvd=wxd=1 时两路同拍 valid，但 ready 只看 out_v：
    out_v.ready=1 ∧ out_x.ready=0 时 out_x 侧结果丢失 -/
theorem exsFpu_q12_double (o : ExsFpuOut) (rdyV rdyX : Bool)
    (hv : o.wvd = true) (hx : o.wxd = true) :
    exsFpuOutRdy o rdyV rdyX = rdyV ∧
    exsFpuOutVValid o = o.valid ∧ exsFpuOutXValid o = o.valid := by
  simp [exsFpuOutVValid, exsFpuOutXValid, exsFpuOutRdy, hv, hx]

-- FMA 重编码与 reverse 的交互（:764-774；Q13）
section ExsFpuTests

-- FN_VFMADD=14 → op=4，(a,b,c)=(in1,in3,in2)，reverse 被覆盖
example : exsFpuPackLane 1 2 3 14#6 true 0 =
    { a := 1, b := 3, c := 2, rm := 0, op := 4#6 : ExsFpuLaneIn } := by decide
example : exsFpuPackLane 1 2 3 14#6 false 0 =
    { a := 1, b := 3, c := 2, rm := 0, op := 4#6 : ExsFpuLaneIn } := by decide
example : exsFpuPackLane 1 2 3 15#6 false 0 =
    { a := 1, b := 3, c := 2, rm := 0, op := 5#6 : ExsFpuLaneIn } := by decide
example : exsFpuPackLane 1 2 3 16#6 false 0 =
    { a := 1, b := 3, c := 2, rm := 0, op := 6#6 : ExsFpuLaneIn } := by decide
example : exsFpuPackLane 1 2 3 17#6 false 0 =
    { a := 1, b := 3, c := 2, rm := 0, op := 7#6 : ExsFpuLaneIn } := by decide
-- 非 FMA：reverse 交换 a/b，c/op 不变，rm 广播（:763-768）
example : exsFpuPackLane 1 2 3 5#6 true 7 =
    { a := 2, b := 1, c := 3, rm := 7, op := 5#6 : ExsFpuLaneIn } := by decide
example : exsFpuPackLane 1 2 3 5#6 false 7 =
    { a := 1, b := 2, c := 3, rm := 7, op := 5#6 : ExsFpuLaneIn } := by decide
-- 边界：13（FN 非 FMA 最大值附近）不走重编码；18 也不走
example : (exsFpuPackLane 1 2 3 13#6 false 0).op = 13#6 := by decide
example : (exsFpuPackLane 1 2 3 18#6 false 0).op = 18#6 := by decide

end ExsFpuTests

/- ========================================================================= -/
/- 7. vTCexe（:115-162）与 TCCtrlv2（:112-114）；TensorCoreFP32 黑盒（H-TC-*） -/
/- ========================================================================= -/

/-- TCCtrlv2（:112-114）：FPUv2.TCCtrl + spike_info；SPIKE_OUTPUT=false 下
    即 warpID/reg_idxw 两字段（D8；fpuv2 未 vendor，字段依使用点 :133-134
    推断：reg_idxw、warpID） -/
structure ExsTcCtrl where
  regIdxw : BitVec 8
  warpID : BitVec 3
deriving DecidableEq, Repr

/-- TC 每 lane 输入摘要（:138-144：op=0、ctrl=0（EmptyFPUCtrl）、rm 广播、
    a/b/c 直传；无 mask、无 reverse——TC 无逐 lane 掩码，Q9） -/
structure ExsTcLaneIn where
  a  : BitVec 32
  b  : BitVec 32
  c  : BitVec 32
  rm : BitVec 3
deriving DecidableEq, Repr

/-- :138-144 TC 每 lane 打包 -/
def exsTcPackLane (in1 in2 in3 : BitVec 32) (rm : BitVec 3) : ExsTcLaneIn where
  a := in1
  b := in2
  c := in3
  rm := rm

/-- TC 输出摘要（黑盒消费对象；ctrl 透传假设 H-TC-1） -/
structure ExsTcOut where
  valid : Bool
  result : Nat → BitVec 32
  ctrl : ExsTcCtrl

/-- :144-150 result_v.io.enq.bits（pipe queue 的 enq 侧，D9） -/
def exsTcEnqBits (o : ExsTcOut) : ExsWbV where
  wb := o.result                    -- :144
  wvdMask := BitVec.allOnes 32      -- :150 全 1（Q9：TC 无 mask）
  wvd := o.valid                    -- :149（Q10：wvd 复用为 valid 拷贝）
  regIdxw := o.ctrl.regIdxw         -- :147
  wid := o.ctrl.warpID              -- :148

/-- :151 result_v.io.enq.valid -/
def exsTcEnqValid (o : ExsTcOut) : Bool := o.valid

/-- :152 tensor.io.out.ready = result_v.io.enq.ready（透传） -/
def exsTcOutReady (enqRdy : Bool) : Bool := enqRdy

/-- :135-136 in 侧握手直通：tensor.io.in.valid = io.in.valid，
    io.in.ready = tensor.io.in.ready -/
theorem exsTc_in_passthrough (v r : Bool) : v = v ∧ r = r := ⟨rfl, rfl⟩

/-- Q9 钉：wvd_mask 恒全 1（与输入 mask 无关——mask 根本没进 TC 数据通路） -/
theorem exsTc_wvdMask_allOnes (o : ExsTcOut) :
    (exsTcEnqBits o).wvdMask = BitVec.allOnes 32 := rfl

/-- Q10/:151 钉：enq.valid = TC out.valid，且 wvd 字段同值 -/
theorem exsTc_enqValid (o : ExsTcOut) :
    exsTcEnqValid o = o.valid ∧ (exsTcEnqBits o).wvd = o.valid := ⟨rfl, rfl⟩

/-- ctrl 透传（假设 H-TC-1：o.ctrl = 输入事务 ctrl）→ 写回 warp/寄存器号正确 -/
theorem exsTc_ctrl_passthrough (o : ExsTcOut) (r : BitVec 8) (w : BitVec 3)
    (h : o.ctrl = ⟨r, w⟩) :
    (exsTcEnqBits o).regIdxw = r ∧ (exsTcEnqBits o).wid = w := by
  simp [exsTcEnqBits, h]

-- TC 打包测试
example : exsTcPackLane 1 2 3 5 = { a := 1, b := 2, c := 3, rm := 5 : ExsTcLaneIn } :=
  by decide

/- ========================================================================= -/
/- 8. 公理审计（bv_decide 定理带 _native.bv_decide.ax_* 信任公理；            -/
/-    native_decide 测试带 Lean.ofReduceBool；归档注明）                      -/
/- ========================================================================= -/

#print axioms exsGrpSeqMg_nodup
#print axioms exsGrpSeqMg_complete
#print axioms exsGrpSeqMg_sound
#print axioms exsGrpSeqMg_sorted
#print axioms exsGrpSeq_lane_exactly_once
#print axioms exsSfu_vec_lane_correct
#print axioms exsSfu_mask_fidelity
#print axioms exsSfu_vec_terminates
#print axioms exsSfu_finish_stable
#print axioms exsSfu_q3_silent_drop
#print axioms exsFpu_q12_drop
#print axioms exsTc_wvdMask_allOnes
#print axioms exs_test_vec_lane3
#print axioms exs_test_bug1_lane3
#print axioms exs_test_reverse

end Ventus.Arith
