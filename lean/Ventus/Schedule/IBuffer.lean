/- ========================================================================= -/
/-                      Schedule/IBuffer.lean                                -/
/-  指令缓冲（InstrBufferV2，WP2）的 Lean 4 模型、测试与精化证明              -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/ibuffer.scala      -/
/-    （instbuffer :21-41；ibuffer2issue :42-101；InstrBufferV2 :105-203；    -/
/-      SlowDown :137-177；IBuffer2OpC :205-227）                             -/
/-  连接方式（pipe.scala）：:103 例化 InstrBufferV2、:104 例化 ibuffer2issue；-/
/-    :220-226 每 warp：ibuffer2issue.in(i).valid = ibuffer.out(i).valid &    -/
/-    warp_sche.warp_ready(i)，ibuffer.out(i).ready = ibuffer2issue.in(i).ready-/
/-    & warp_ready(i)；:288-289 out_x/out_v 接 operand_collector。            -/
/-                                                                           -/
/- ======================== 例化关系核查（2026-08-25 全仓 grep） ============= -/
/-  * InstrBufferV2、ibuffer2issue：仅 pipe.scala:103-104 例化 —— 活代码。    -/
/-  * instbuffer（:21-41）：全仓（含 tests/gvm）无任何例化 —— 死代码，不建模。-/
/-  * IBuffer2OpC（:205-227）：同上，死代码，不建模（其 in_split/arbiters      -/
/-    下标技巧见疑点 Q6，仅记录）。                                           -/
/-  参数（top/parameters.scala）：num_warp=8、num_fetch=2、size_ibuffer=2、    -/
/-    depth_warp=3、INST_CNT=true、SINGLE_INST=false、GVM_ENABLED 默认 false。-/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. CtrlSigs 有 40+ 字段，ibuffer 行为只触及 wid（入队导向 :118）与       -/
/-      inst_is_vec 的 tc/fp/mul/sfu/mem/csr/barrier/isvec（:70-76）。        -/
/-      IbInsn 只保留这些字段 + tag（指令身份占位，对应 inst/pc 等）；        -/
/-      对 ibuffer 的缓冲/发射行为而言这是无损失抽象。                        -/
/-  D2. chisel3.util.Queue（hasFlush=true，深度 2）建模为具体循环缓冲：       -/
/-      r0/r1 两槽 + 1 位 enqP/deqP + full（chisel 的 maybe_full）。empty =   -/
/-      ptr_match && !maybe_full、full = ptr_match && maybe_full；            -/
/-      maybe_full 在 do_enq ≠ do_deq 时更新为 do_enq。flush 拍指针清零、     -/
/-      maybe_full 清 false，当拍 enq 被丢弃（flush 的 when 块覆盖指针更新，  -/
/-      见疑点 Q1）。deq.bits 恒为 ram[deqP]。                                -/
/-  D3. SlowDown（:137-177）：control_reg 建模为 IbGrp 的 (c0,c1)，mask_reg   -/
/-      为 BitVec 2；ptr = PriorityEncoder(mask)（最低置位位下标，0 输入得 0）；-/
/-      mask_next = mask & ~(1<<ptr)（:151）。更新优先级：flush > in.fire >   -/
/-      out.fire（:155-168 程序序，in.fire 覆盖 out.fire）。GVM 的            -/
/-      dispatchCounter（:153,:161-163）默认关闭且不影响缓冲语义，不建模。    -/
/-  D4. flush 当拍的组合输出（out.valid/out.bits/enq.ready）仍由旧状态驱动，  -/
/-      flush 只影响下一拍状态 —— 与 Chisel 寄存器语义一致。flush 拍从         -/
/-      SlowDown 发出一条指令是可能的（out.fire 与 flush 同拍），模型保留。   -/
/-  D5. ibuffer2issue 只建模纯组合函数 inst_is_vec（:66-80）；双 RRArbiter    -/
/-      的轮转仲裁留待后续波次（需先有 RRArbiter 模型）。cnt（:52-62）为       -/
/-      只读计数器，不影响数据通路，不建模。SINGLE_INST=false，pipe.scala:225-/
/-      226 分支不生效。                                                     -/
/-  D6. :129-136 的 `when(io.in.fire){ ... enq.bits 重赋值 / flush 清零 }`     -/
/-      块经逐情形分析无可观测效果（enq.bits 只在 enq.valid 时被采样；valid 时-/
/-      若同拍 flush 同 warp 则被 Q1 的丢弃覆盖），模型不复现该死逻辑，见 Q2。-/
/-  D7. flush 时 SlowDown 的 control_reg 清零（:157）建模为 Inhabited         -/
/-      default；mask=0 时 out.valid=false，control_reg 值不可观测，无损失。  -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话，详见返回报告） ========= -/
/-  Q1（I 类候选，数据丢失）：flush 与入队同拍同 warp 时，enq.ready 恒为      -/
/-      !full（:124/:128，不看 flush），上游 icache_rsp（pipe.scala:218        -/
/-      `io.icache_rsp.ready := ibuffer.io.in.ready`）看到 fire；但 Queue 内   -/
/-      flush 的 when 块覆盖 enq_ptr 更新，该拍入队被静默丢弃。定理           -/
/-      ibT_flush_enq_drop 给出具体复现轨迹。可否触发取决于 warp_sche flush   -/
/-      与 icache 响应的时序关系，需主会话结合上游模块判定。                  -/
/-  Q2（死逻辑）：:129-136 when(io.in.fire) 块（见 D6）无可观测效果，疑似     -/
/-      调试残留；另 :124 与 :128 对 io.in.ready 重复赋值同一表达式。         -/
/-  Q3（提示性）：SlowDown 的 in.ready = (mask_next==0) && out.ready（:170）  -/
/-      在 mask_reg=0（空）时也要求 out.ready，产生保守气泡（每装入一组至少   -/
/-      停一拍），只损性能不损正确性。                                       -/
/-  Q4（提示性）：flush 与 SlowDown 的 in.fire 同拍（deq.ready 不看 flush）时 -/
/-      队列头被弹出并丢弃 —— 这是 flush 的预期语义（清空该 warp 未发射指     -/
/-      令），但注意被丢弃的那拍 buffers(i).deq.valid 为高、SlowDown 并未接    -/
/-      收：若上层把 deq.fire 当作"已消费"记账会失真（本仓未见此类记账）。   -/
/-  Q5（提示性）：ibuffer2issue 中 io.in(i).ready 用 inst_is_vec 二选一        -/
/-      （:86），rrarbit_x 与 rrarbit_v 独立仲裁；同 warp 头指令在 x/v 间切    -/
/-      换不会改变 ibuffer 出队顺序（每 warp 单通道），未见顺序问题。         -/
/-  Q6（死代码内疑点）：IBuffer2OpC 的 `in_split.reverse.dropWhile(_ <= 1)`   -/
/-      （:211）只在 in_split 全部 ≤ 1 时才丢元素（in_split 单调不减，反转后  -/
/-      首元素最大），故 arbiters 下标不越界；逻辑迂回但安全。模块未例化。   -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Ventus.Base.QueueModel
import Std.Tactic.BVDecide

namespace Ventus.Schedule

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 参数常量（top/parameters.scala:8,30,38,45）                             -/
/- ========================================================================= -/

def ibNumWarp : Nat := 8      -- parameters.scala:8
def ibNumFetch : Nat := 2     -- parameters.scala:38
def ibSizeIbuffer : Nat := 2  -- parameters.scala:45
def ibDepthWarp : Nat := 3    -- parameters.scala:30（log2Ceil 8）

/- ========================================================================= -/
/- 2. IbInsn：CtrlSigs 的行为相关切片（D1）与 inst_is_vec（:66-80）           -/
/- ========================================================================= -/

structure IbInsn where
  tag     : BitVec 8   -- 指令身份占位（对应 inst/pc 等不参与 ibuffer 行为的字段）
  wid     : BitVec 3   -- CtrlSigs.wid（depth_warp=3）
  tc      : Bool
  fp      : Bool
  mul     : Bool
  sfu     : Bool
  mem     : Bool
  csr     : BitVec 2   -- CtrlSigs.csr（UInt(2.W)，:72 用 .orR）
  barrier : Bool
  isvec   : Bool
deriving DecidableEq

instance : Inhabited IbInsn :=
  ⟨⟨0, 0, false, false, false, false, false, 0, false, false⟩⟩

def ibInsn0 : IbInsn := default

/-- ibuffer2issue.inst_is_vec（:70-78）：vFPU|vSFU|vALU|vMUL|vTC|LSU → 向量；
    其次 CSR|barrier → 标量；再 isvec → 向量；否则标量。分支优先级即源码顺序。 -/
def ibInstIsVec (c : IbInsn) : Bool :=
  if c.tc || c.fp || c.mul || c.sfu || c.mem then true
  else if (c.csr ≠ 0#2) || c.barrier then false
  else c.isvec

/- ---- inst_is_vec 测试（真值表关键点，全 `by decide`） ---- -/

def ibMkInsn (tc fp mul sfu mem : Bool) (csr : BitVec 2) (barrier isvec : Bool) : IbInsn :=
  ⟨0, 0, tc, fp, mul, sfu, mem, csr, barrier, isvec⟩

-- 第一优先级：tc/fp/mul/sfu/mem 任一为真即向量，压过 csr/barrier/isvec
example : ibInstIsVec (ibMkInsn true false false false false 3 true false) = true := by decide
example : ibInstIsVec (ibMkInsn false true false false false 0 false false) = true := by decide
example : ibInstIsVec (ibMkInsn false false true false false 0 false false) = true := by decide
example : ibInstIsVec (ibMkInsn false false false true false 0 false false) = true := by decide
example : ibInstIsVec (ibMkInsn false false false false true 3 true true) = true := by decide
-- 第二优先级：csr≠0 或 barrier → 标量，压过 isvec
example : ibInstIsVec (ibMkInsn false false false false false 1 false true) = false := by decide
example : ibInstIsVec (ibMkInsn false false false false false 0 true true) = false := by decide
-- 第三优先级：仅 isvec → 向量
example : ibInstIsVec (ibMkInsn false false false false false 0 false true) = true := by decide
-- 全假 → 标量
example : ibInstIsVec (ibMkInsn false false false false false 0 false false) = false := by decide

/- ========================================================================= -/
/- 3. IbGrp：一拍 fetch 组（Vec(num_fetch, CtrlSigs) + control_mask）         -/
/-    num_fetch=2，故组 = (c0, c1) + 2 位 mask。flatten 为按位序的有效指令表。-/
/- ========================================================================= -/

structure IbGrp (α : Type) where
  c0   : α
  c1   : α
  mask : BitVec 2

instance [Inhabited α] : Inhabited (IbGrp α) := ⟨⟨default, default, 0#2⟩⟩

/-- 组内有效指令按位序展开（mask bit0 → c0，bit1 → c1）。
    用移位/掩码形式取位（`&&&`），规避 bv_decide 对变量下标 getLsbD 的限制。 -/
def ibGrpFlat (g : IbGrp α) : List α :=
  (if g.mask &&& 1#2 = 1#2 then [g.c0] else []) ++
  (if g.mask &&& 2#2 = 2#2 then [g.c1] else [])

/- ---- IbGrp 测试 ---- -/

example : ibGrpFlat ⟨'a', 'b', 0#2⟩ = ([] : List Char) := by decide
example : ibGrpFlat ⟨'a', 'b', 1#2⟩ = ['a'] := by decide
example : ibGrpFlat ⟨'a', 'b', 2#2⟩ = ['b'] := by decide
example : ibGrpFlat ⟨'a', 'b', 3#2⟩ = ['a', 'b'] := by decide

/- ========================================================================= -/
/- 4. IbQ：chisel3.util.Queue（深度 2，hasFlush）的具体循环缓冲模型（D2）     -/
/- ========================================================================= -/

structure IbQ (α : Type) where
  r0   : α          -- ram 槽 0
  r1   : α          -- ram 槽 1
  enqP : BitVec 1
  deqP : BitVec 1
  full : Bool        -- chisel maybe_full

/-- ram 读（deq.bits 恒为 ram[deqP]） -/
def IbQ.read (q : IbQ α) (p : BitVec 1) : α := if p = 0#1 then q.r0 else q.r1

/-- ptr_match && !maybe_full -/
def IbQ.isEmpty (q : IbQ α) : Bool := (q.enqP == q.deqP) && !q.full
/-- ptr_match && maybe_full -/
def IbQ.isFull (q : IbQ α) : Bool := (q.enqP == q.deqP) && q.full
/-- enq.ready = !full（不看 flush，疑点 Q1 的源头之一） -/
def IbQ.canEnq (q : IbQ α) : Bool := !q.isFull
/-- deq.valid = !empty -/
def IbQ.canDeq (q : IbQ α) : Bool := !q.isEmpty

def IbQ.deqBits (q : IbQ α) : α := q.read q.deqP

/-- 抽象视图：队首→队尾的内容表。enqP ≠ deqP 时恰有一个元素（在 deqP 槽）。 -/
def IbQ.abs (q : IbQ α) : List α :=
  if q.enqP = q.deqP then
    (if q.full then [q.read q.deqP, q.read (q.deqP + 1)] else [])
  else [q.read q.deqP]

/-- 非 flush 拍的状态更新。do_enq = enqV && canEnq；do_deq = canDeq && deqR；
    maybe_full 在 do_enq ≠ do_deq 时更新为 do_enq（chisel Queue 语义）。 -/
def IbQ.step (q : IbQ α) (enqV : Bool) (x : α) (deqR : Bool) : IbQ α :=
  let enqF := enqV && q.canEnq
  let deqF := q.canDeq && deqR
  { r0 := if enqF then (if q.enqP = 0#1 then x else q.r0) else q.r0
    r1 := if enqF then (if q.enqP = 1#1 then x else q.r1) else q.r1
    enqP := if enqF then q.enqP + 1 else q.enqP
    deqP := if deqF then q.deqP + 1 else q.deqP
    full := if enqF = deqF then q.full else enqF }

/-- flush：指针清零、maybe_full 清 false（ram 保留但不可达） -/
def IbQ.flushStep (q : IbQ α) : IbQ α :=
  { q with enqP := 0#1, deqP := 0#1, full := false }

def IbQ.empty [Inhabited α] : IbQ α := ⟨default, default, 0#1, 0#1, false⟩

/- ---- IbQ 测试（decide；多拍用小轨迹） ---- -/

section IbQTests

def ibQ0 : IbQ (BitVec 8) := IbQ.empty

-- 空队列谓词
example : ibQ0.canEnq = true := by decide
example : ibQ0.canDeq = false := by decide
example : ibQ0.abs = ([] : List (BitVec 8)) := by decide

-- 入队一个
example : (ibQ0.step true 5 false).abs = [5#8] := by decide
example : (ibQ0.step true 5 false).canDeq = true := by decide

-- 入队两个即满，ready 拉低（不溢出前提）
def ibQ2 := (ibQ0.step true 5 false).step true 6 false
example : ibQ2.abs = [5#8, 6#8] := by decide
example : ibQ2.canEnq = false := by decide
example : ibQ2.canDeq = true := by decide

-- 满时入队被拒（不溢出）：内容不变
example : (ibQ2.step true 7 false).abs = [5#8, 6#8] := by decide
-- 满时同拍出队+入队仍被拒（chisel Queue 无 bypass，enq.ready 只看 full）
example : (ibQ2.step true 7 true).abs = [6#8] := by decide

-- 出队顺序：FIFO
example : ((ibQ2.step false 0 true).step false 0 true).abs = ([] : List (BitVec 8)) := by decide
example : ibQ2.deqBits = 5#8 := by decide
example : (ibQ2.step false 0 true).deqBits = 6#8 := by decide
example : ((ibQ2.step false 0 true).step false 0 true).canDeq = false := by decide

-- 空时出队被拒（不欠载）
example : (ibQ0.step false 0 true).abs = ([] : List (BitVec 8)) := by decide

-- 半满同拍出入队：出一个进一个
example : ((ibQ0.step true 5 false).step true 6 true).abs = [6#8] := by decide

-- flush 清空
example : ibQ2.flushStep.abs = ([] : List (BitVec 8)) := by decide
example : ibQ2.flushStep.canEnq = true := by decide

end IbQTests

/- ---- IbQ 证明 ---- -/

/-- BitVec 1 穷举 -/
theorem ibBv1_cases (p : BitVec 1) : p = 0#1 ∨ p = 1#1 := by bv_decide

/-- BitVec 2 穷举 -/
theorem ibBv2_cases (m : BitVec 2) : m = 0#2 ∨ m = 1#2 ∨ m = 2#2 ∨ m = 3#2 := by bv_decide

/-- 单拍精化（主引理）：非 flush 拍下，新内容 = 旧内容（出队则去头）++（入队则追加）。
    出队与否、入队与否四情形全覆盖；对应 QueueModel 的 enq/deq/enqDeq/skip 四标签。 -/
theorem ibQ_step_abs (q : IbQ α) (enqV : Bool) (x : α) (deqR : Bool) :
    (q.step enqV x deqR).abs =
      (if q.canDeq && deqR then q.abs.drop 1 else q.abs) ++
      (if enqV && q.canEnq then [x] else []) := by
  rcases ibBv1_cases q.enqP with he | he <;> rcases ibBv1_cases q.deqP with hd | hd <;>
    cases hf : q.full <;> cases enqV <;> cases deqR <;>
    simp [IbQ.step, IbQ.abs, IbQ.read, IbQ.canEnq, IbQ.canDeq, IbQ.isEmpty, IbQ.isFull,
      he, hd, hf]

/-- 队首刻画：可出队时，内容 = deq.bits :: 其余 -/
theorem ibQ_abs_eq_read_cons (q : IbQ α) (h : q.canDeq = true) :
    q.abs = q.deqBits :: q.abs.drop 1 := by
  rcases ibBv1_cases q.enqP with he | he <;> rcases ibBv1_cases q.deqP with hd | hd <;>
    cases hf : q.full <;>
    simp [IbQ.canDeq, IbQ.isEmpty, IbQ.abs, IbQ.deqBits, IbQ.read, he, hd, hf] at h ⊢

/-- 容量上界（不溢出的量化形式） -/
theorem ibQ_abs_length_le (q : IbQ α) : q.abs.length ≤ ibSizeIbuffer := by
  rcases ibBv1_cases q.enqP with he | he <;> rcases ibBv1_cases q.deqP with hd | hd <;>
    cases hf : q.full <;> simp [IbQ.abs, IbQ.read, he, hd, hf, ibSizeIbuffer]

/-- 不溢出：满时入队被忽略（状态仅可能因出队而变） -/
theorem ibQ_no_overflow (q : IbQ α) (enqV : Bool) (x : α) (deqR : Bool)
    (h : q.canEnq = false) :
    (q.step enqV x deqR).abs =
      (if q.canDeq && deqR then q.abs.drop 1 else q.abs) := by
  rw [ibQ_step_abs]
  simp [h]

/-- 不欠载：空时出队无效，内容只能因入队而变 -/
theorem ibQ_no_underflow (q : IbQ α) (enqV : Bool) (x : α) (deqR : Bool)
    (h : q.canDeq = false) :
    (q.step enqV x deqR).abs = q.abs ++ (if enqV && q.canEnq then [x] else []) := by
  rw [ibQ_step_abs]
  simp [h]

/-- flush 后内容为空 -/
theorem ibQ_flush_abs (q : IbQ α) : q.flushStep.abs = [] := by
  simp [IbQ.flushStep, IbQ.abs]

/-- enq.ready 不被 flush 拉低（Q1 的形式化一半：ready 与 flush 无关） -/
theorem ibQ_canEnq_flush_indep (q : IbQ α) : q.flushStep.canEnq = true := by
  simp [IbQ.flushStep, IbQ.canEnq, IbQ.isFull]

/- ========================================================================= -/
/- 5. SlowDown（:137-177）：一组 num_fetch 条指令逐条发射                     -/
/-    状态复用 IbGrp：control_reg = (c0,c1)（:147），mask_reg = mask（:148）  -/
/- ========================================================================= -/

/-- PriorityEncoder(mask)（:149）：最低置位位下标；mask=0 时为 0 -/
def ibPtr (m : BitVec 2) : BitVec 1 :=
  if m &&& 1#2 = 1#2 then 0#1 else if m &&& 2#2 = 2#2 then 1#1 else 0#1

/-- mask_next = mask & ~(1 << ptr)（:151，截取低 2 位后取反相与） -/
def ibMaskNext (m : BitVec 2) : BitVec 2 :=
  m &&& ~~~(1#2 <<< BitVec.zeroExtend 2 (ibPtr m))

/-- out.bits = control_reg(ptr)（:172） -/
def ibSdEmit (sd : IbGrp α) : α := if ibPtr sd.mask = 0#1 then sd.c0 else sd.c1

/-- out.valid = (mask_reg ≠ 0)（:171） -/
def ibSdValid (sd : IbGrp α) : Bool := !(sd.mask == 0#2)

/-- in.ready = (mask_next == 0) && out.ready（:170） -/
def ibSdInRdy (sd : IbGrp α) (outRdy : Bool) : Bool :=
  (ibMaskNext sd.mask == 0#2) && outRdy

/-- SlowDown 滞留指令表（按发射顺序）：即当前 mask 下的组展开 -/
def ibSdPending (sd : IbGrp α) : List α := ibGrpFlat sd

/- ---- SlowDown 测试 ---- -/

section IbSdTests

def ibSdA : IbGrp Char := ⟨'a', 'b', 3#2⟩

-- ptr 为最低置位位
example : ibPtr 0#2 = 0#1 := by decide
example : ibPtr 1#2 = 0#1 := by decide
example : ibPtr 2#2 = 1#1 := by decide
example : ibPtr 3#2 = 0#1 := by decide

-- mask_next 清最低置位位
example : ibMaskNext 0#2 = 0#2 := by decide
example : ibMaskNext 1#2 = 0#2 := by decide
example : ibMaskNext 2#2 = 0#2 := by decide
example : ibMaskNext 3#2 = 2#2 := by decide

-- 发射顺序：c0 先于 c1
example : ibSdEmit ibSdA = 'a' := by decide
example : ibSdEmit ⟨'a', 'b', ibMaskNext 3#2⟩ = 'b' := by decide
example : ibSdPending ibSdA = ['a', 'b'] := by decide

-- in.ready：仅当本组即将抽空且下游 ready
example : ibSdInRdy ⟨'a', 'b', 3#2⟩ true = false := by decide  -- 还剩 2 条，拒装新组
example : ibSdInRdy ⟨'a', 'b', 2#2⟩ true = true := by decide   -- 最后一条在飞，可装
example : ibSdInRdy ⟨'a', 'b', 0#2⟩ true = true := by decide   -- 空，可装
example : ibSdInRdy ⟨'a', 'b', 0#2⟩ false = false := by decide -- Q3：空也要求 out.ready

end IbSdTests

/- ---- SlowDown 证明 ---- -/

/-- 发射消耗队首：非空时 pending = 发射指令 :: mask_next 下的 pending -/
theorem ibSd_pending_cons (sd : IbGrp α) (h : sd.mask ≠ 0#2) :
    ibSdPending sd = ibSdEmit sd :: ibSdPending ⟨sd.c0, sd.c1, ibMaskNext sd.mask⟩ := by
  obtain ⟨c0, c1, m⟩ := sd
  rcases ibBv2_cases m with hm | hm | hm | hm
  · exact absurd hm h
  · subst hm; simp [ibSdPending, ibGrpFlat, ibSdEmit, ibPtr, ibMaskNext]
  · subst hm; simp [ibSdPending, ibGrpFlat, ibSdEmit, ibPtr, ibMaskNext]
  · subst hm; simp [ibSdPending, ibGrpFlat, ibSdEmit, ibPtr, ibMaskNext]

/-- 关键耦合引理：mask_next = 0 时，本组要么空、要么只剩一条（即发射指令本身）。
    这是"in.fire 覆盖 out.fire 不丢指令"（:166 注释 cover io.out.fire）的根据。 -/
theorem ibSd_pending_eq_of_maskNext_zero (sd : IbGrp α)
    (h : ibMaskNext sd.mask = 0#2) :
    ibSdPending sd = if sd.mask = 0#2 then [] else [ibSdEmit sd] := by
  obtain ⟨c0, c1, m⟩ := sd
  rcases ibBv2_cases m with hm | hm | hm | hm
  · subst hm; simp [ibSdPending, ibGrpFlat]
  · subst hm; simp [ibSdPending, ibGrpFlat, ibSdEmit, ibPtr]
  · subst hm; simp [ibSdPending, ibGrpFlat, ibSdEmit, ibPtr]
  · -- mask = 3：mask_next = 2 ≠ 0，与前提矛盾
    subst hm; exact absurd h (by simp [ibMaskNext, ibPtr])

/- ========================================================================= -/
/- 6. IbLane：单 warp 通道 = IbQ（组队列） + SlowDown（逐条发射）             -/
/-    对应 InstrBufferV2 内 (0 until num_warp).foreach 的单条支路（:117-126, -/
/-    :179-188），外加输入导向（enq.valid 的 wid==i 由上层给出，见第 7 节）。 -/
/- ========================================================================= -/

structure IbLane (α : Type) where
  q  : IbQ (IbGrp α)
  sd : IbGrp α    -- SlowDown 的 control_reg/mask_reg

/-- 单 warp 输入：enqV 已含 wid 导向（= io.in.valid && control(0).wid==i，:118）；
    outRdy 为下游 ready（pipe.scala:224：ibuffer2issue ready & warp_ready） -/
structure IbLaneIn (α : Type) where
  enqV   : Bool
  grp    : IbGrp α
  outRdy : Bool
  flush  : Bool   -- io.flush_wid.valid && bits==i（:120,:180）

def IbLane.enqRdy (s : IbLane α) : Bool := s.q.canEnq         -- :124/:125/:128
def IbLane.outV (s : IbLane α) : Bool := ibSdValid s.sd       -- :171
def IbLane.outBits (s : IbLane α) : α := ibSdEmit s.sd        -- :172
def IbLane.deqRdy (s : IbLane α) (outRdy : Bool) : Bool := ibSdInRdy s.sd outRdy  -- :170,:184
def IbLane.outFire (s : IbLane α) (outRdy : Bool) : Bool := s.outV && outRdy
def IbLane.deqFire (s : IbLane α) (outRdy : Bool) : Bool := s.q.canDeq && s.deqRdy outRdy
def IbLane.enqFire (s : IbLane α) (enqV : Bool) : Bool := enqV && s.q.canEnq

/-- 当拍可观测发射（out.fire 时输出 out.bits） -/
def IbLane.obs (s : IbLane α) (outRdy : Bool) : Option α :=
  if s.outFire outRdy then some s.outBits else none

/-- 单拍更新。flush 优先且清空两级（:120,:155-157；Q1：当拍 enq 被丢弃）。
    非 flush：队列按 (enqV, deqRdy) 走；SlowDown 按 in.fire > out.fire 更新。 -/
def IbLane.step [Inhabited α] (s : IbLane α) (i : IbLaneIn α) : IbLane α :=
  if i.flush then
    { q := s.q.flushStep, sd := ⟨default, default, 0#2⟩ }
  else
    let deqF := s.deqFire i.outRdy
    let head := s.q.deqBits
    { q := s.q.step i.enqV i.grp (s.deqRdy i.outRdy)
      sd := if deqF then head                      -- :165-168 in.fire 覆盖
            else if s.outFire i.outRdy then ⟨s.sd.c0, s.sd.c1, ibMaskNext s.sd.mask⟩  -- :159-160
            else s.sd }

/-- 通道级抽象视图：SlowDown 滞留 ++ 队列内容逐组展开（按发射先后顺序） -/
def IbLane.abs (s : IbLane α) : List α :=
  ibSdPending s.sd ++ (s.q.abs).flatMap ibGrpFlat

def IbLane.empty [Inhabited α] : IbLane α := ⟨IbQ.empty, default⟩

/- ---- IbLane 测试 ---- -/

section IbLaneTests

def ibLane0 : IbLane IbInsn := IbLane.empty

def ibInsnW (w : BitVec 3) (t : BitVec 8) : IbInsn :=
  { ibInsn0 with wid := w, tag := t }

def ibGrpW (w : BitVec 3) (t0 t1 : BitVec 8) (m : BitVec 2) : IbGrp IbInsn :=
  ⟨ibInsnW w t0, ibInsnW w t1, m⟩

def ibIn (enqV : Bool) (g : IbGrp IbInsn) (outRdy flush : Bool) : IbLaneIn IbInsn :=
  ⟨enqV, g, outRdy, flush⟩

/-- 取 lane 的 tag 序列（测试便于比较） -/
def IbLane.absTags (s : IbLane IbInsn) : List (BitVec 8) :=
  s.abs.map IbInsn.tag

-- 入队一组（mask=3 两条），不出队：abs = 两条
example : (ibLane0.step (ibIn true (ibGrpW 0 10 11 3#2) false false)).absTags = [10, 11] := by decide

-- 逐条发射：先 10 后 11（SlowDown 保序）。
-- 时序注意（Q3）：SlowDown 空时 in.ready 也要求 out.ready，故空 lane 从入队到首次
-- 发射有 2 拍 latency：拍0 入队（deq.valid 尚低），拍1 装入 SlowDown，拍2 起发射。
def ibLane1 := ibLane0.step (ibIn true (ibGrpW 0 10 11 3#2) true false)
def ibLane2 := ibLane1.step (ibIn false (ibGrpW 0 0 0 0#2) true false)
example : (ibLane2.obs true).map IbInsn.tag = some 10 := by decide
def ibLane3 := ibLane2.step (ibIn false (ibGrpW 0 0 0 0#2) true false)
example : (ibLane3.obs true).map IbInsn.tag = some 11 := by decide
example : (ibLane3.step (ibIn false (ibGrpW 0 0 0 0#2) true false)).absTags = [] := by decide

-- 反压保持：outRdy=false 时不发射、状态不变（契约保持的测试面）
example : (ibLane1.obs false) = none := by decide
example : (ibLane1.step (ibIn false (ibGrpW 0 0 0 0#2) false false)).absTags = [10, 11] := by decide

-- 两组跨组保序（队列保序 + SlowDown 保序的组合）
def ibLaneB := (ibLane0.step (ibIn true (ibGrpW 1 20 21 3#2) true false))
                |>.step (ibIn true (ibGrpW 1 22 23 1#2) true false)
-- 拍0：组[20,21]入队；拍1：装入 SlowDown 同时组[22]入队；拍2 起依次发 20/21/22
example : (ibLaneB.obs true).map IbInsn.tag = some 20 := by decide
def ibLaneB2 := ibLaneB.step (ibIn false (ibGrpW 0 0 0 0#2) true false)
example : (ibLaneB2.obs true).map IbInsn.tag = some 21 := by decide
-- 拍4：发 21 的下一拍装入组[22]（mask_next=0 时 in.fire 覆盖 out.fire，不丢指令）
example : ((ibLaneB2.step (ibIn false (ibGrpW 0 0 0 0#2) true false)).obs true).map IbInsn.tag
    = some 22 := by decide

-- 满时 enq.ready 拉低（不溢出，lane 级）
def ibLaneFull := (ibLane0.step (ibIn true (ibGrpW 2 30 31 3#2) false false))
                   |>.step (ibIn true (ibGrpW 2 32 33 3#2) false false)
example : ibLaneFull.enqRdy = false := by decide
example : ibLaneFull.q.abs.length = 2 := by decide

-- flush：滞留与队列全清，之后可重新入队
example : (ibLaneB.step (ibIn true (ibGrpW 1 40 41 3#2) false true)).absTags = [] := by decide
example : ((ibLaneB.step (ibIn false (ibGrpW 0 0 0 0#2) false true))
            |>.step (ibIn true (ibGrpW 1 50 51 1#2) false false)).absTags = [50] := by decide

end IbLaneTests

/- ---- IbLane 证明 ---- -/

/-- flatMap 与单元素 if 交换（精化主引理的列表辅助；条件取任意 Decidable Prop，
    以兼容 simp 把 Bool && 条件规范化为 ∧ 后的形态） -/
theorem ibFlatMap_if (c : Prop) [Decidable c] (g : IbGrp α) :
    List.flatMap ibGrpFlat (if c then [g] else []) = (if c then ibGrpFlat g else []) := by
  by_cases h : c <;> simp [h]

/-- 单拍精化（lane 主引理，无 flush）：发射序列 ++ 新滞留 = 旧滞留 ++ 新入队展开。
    即：该 lane 是一个保序 FIFO（组展平后的指令级）。 -/
theorem ibLane_step_abs [Inhabited α] (s : IbLane α) (i : IbLaneIn α)
    (hf : i.flush = false) :
    (s.obs i.outRdy).toList ++ (s.step i).abs =
      s.abs ++ (if s.enqFire i.enqV then ibGrpFlat i.grp else []) := by
  -- 队列层单拍方程
  have hq := ibQ_step_abs s.q i.enqV i.grp (s.deqRdy i.outRdy)
  -- 分情形：deqFire（装入新组）/ 仅 outFire / 静止
  by_cases hd : s.deqFire i.outRdy = true
  · -- deqFire ⇒ deqRdy ⇒ mask_next = 0 ∧ outRdy = true；且队列非空
    have hdr : s.deqRdy i.outRdy = true := by
      simp [IbLane.deqFire] at hd; exact hd.2
    have hmn : ibMaskNext s.sd.mask = 0#2 := by
      simp [IbLane.deqRdy, ibSdInRdy] at hdr; exact hdr.1
    have hor : i.outRdy = true := by
      simp [IbLane.deqRdy, ibSdInRdy] at hdr; exact hdr.2
    have hcd : s.q.canDeq = true := by
      simp [IbLane.deqFire] at hd; exact hd.1
    have hhead : s.q.abs = s.q.deqBits :: s.q.abs.drop 1 := ibQ_abs_eq_read_cons _ hcd
    -- 队首组弹出后，队列展开 = 队首组展开 ++ 余下展开（conv 聚焦避免 hhead 成环）
    have hfm : (s.q.abs).flatMap ibGrpFlat =
        ibSdPending s.q.deqBits ++ (s.q.abs.drop 1).flatMap ibGrpFlat := by
      conv => lhs; rw [hhead]
      simp [List.flatMap_cons, ibSdPending]
    -- SlowDown 侧：mask_next = 0 ⇒ pending 为空或单条（in.fire 覆盖不丢指令的根据）
    have hsd := ibSd_pending_eq_of_maskNext_zero s.sd hmn
    -- step 展开（deqF 分支装入队首组）
    have hstep : s.step i = ⟨s.q.step i.enqV i.grp (s.deqRdy i.outRdy), s.q.deqBits⟩ := by
      simp [IbLane.step, hf, hd]
    rw [hstep]
    simp only [IbLane.abs]
    rw [hq, hfm]
    by_cases hm : s.sd.mask = 0#2
    · -- out 不 fire：obs = none
      have hof : s.outFire i.outRdy = false := by
        simp [IbLane.outFire, IbLane.outV, ibSdValid, hm]
      simp [IbLane.obs, hof, hsd, hm, hcd, hdr, IbLane.enqFire,
        ibFlatMap_if, List.flatMap_append, List.append_assoc]
    · -- out fire：obs = [emit]，pending = [emit]
      have hof : s.outFire i.outRdy = true := by
        simp [IbLane.outFire, IbLane.outV, ibSdValid, hm, hor]
      simp [IbLane.obs, hof, IbLane.outBits, hsd, hm, hcd, hdr, IbLane.enqFire,
        ibFlatMap_if, List.flatMap_append, List.append_assoc]
  · -- deqFire = false
    have hdf : s.deqFire i.outRdy = false := by
      revert hd; cases s.deqFire i.outRdy <;> simp
    have hstep : s.step i =
        ⟨s.q.step i.enqV i.grp (s.deqRdy i.outRdy),
         if s.outFire i.outRdy then ⟨s.sd.c0, s.sd.c1, ibMaskNext s.sd.mask⟩ else s.sd⟩ := by
      simp [IbLane.step, hf, hdf]
    have hq' : (s.q.step i.enqV i.grp (s.deqRdy i.outRdy)).abs =
        s.q.abs ++ (if s.enqFire i.enqV then [i.grp] else []) := by
      rw [hq]
      have hcd' : (s.q.canDeq && s.deqRdy i.outRdy) = false := by
        simp only [IbLane.deqFire] at hdf; exact hdf
      simp [hcd', IbLane.enqFire]
    rw [hstep]
    simp only [IbLane.abs]
    by_cases hof : s.outFire i.outRdy = true
    · -- 仅发射：pending 去头
      have hv : s.sd.mask ≠ 0#2 := by
        simp [IbLane.outFire, IbLane.outV, ibSdValid] at hof; exact hof.1
      have hcons := ibSd_pending_cons s.sd hv
      simp [IbLane.obs, hof, IbLane.outBits, hq', hcons, IbLane.enqFire,
        ibFlatMap_if, List.flatMap_append, List.append_assoc]
    · -- 静止（含反压）
      have hof' : s.outFire i.outRdy = false := by
        revert hof; cases s.outFire i.outRdy <;> simp
      simp [IbLane.obs, hof', hq', IbLane.enqFire, ibFlatMap_if, List.flatMap_append,
        List.append_assoc]

/-- flush 拍：两级全清（enq 当拍被丢弃 —— Q1 的模型侧刻画） -/
theorem ibLane_step_flush_abs [Inhabited α] (s : IbLane α) (i : IbLaneIn α)
    (hf : i.flush = true) : (s.step i).abs = [] := by
  simp [IbLane.step, hf, IbLane.abs, ibSdPending, ibGrpFlat, ibQ_flush_abs]

/-- 契约保持（valid/ready）：无 flush 且下游反压时，out.valid 保持、out.bits 稳定
    （Handshake 的 NoWithdraw ∧ Stable 在单 lane 上的形式）。 -/
theorem ibLane_irrevocable [Inhabited α] (s : IbLane α) (i : IbLaneIn α)
    (hf : i.flush = false) (hr : i.outRdy = false) (hv : s.outV = true) :
    (s.step i).outV = true ∧ (s.step i).outBits = s.outBits := by
  have hof : s.outFire i.outRdy = false := by simp [IbLane.outFire, hr]
  have hdr : s.deqRdy i.outRdy = false := by simp [IbLane.deqRdy, ibSdInRdy, hr]
  have hdf : s.deqFire i.outRdy = false := by simp [IbLane.deqFire, hdr]
  have hv' : ibSdValid s.sd = true := hv
  simp [IbLane.step, hf, hdf, hof, IbLane.outV, IbLane.outBits, hv']

/- ---- 多拍 run 与顺序保持（精化主定理） ---- -/

/-- 多拍执行：返回 (终态, 依次发射的指令序列) -/
def IbLane.run [Inhabited α] (s : IbLane α) : List (IbLaneIn α) → IbLane α × List α
  | [] => (s, [])
  | i :: is =>
    let (sn, os) := (s.step i).run is
    (sn, (s.obs i.outRdy).toList ++ os)

/-- 多拍接受的入队（展平为指令序列；enq.fire 才算接受） -/
def IbLane.accepted [Inhabited α] (s : IbLane α) : List (IbLaneIn α) → List α
  | [] => []
  | i :: is =>
    (if s.enqFire i.enqV then ibGrpFlat i.grp else []) ++ (s.step i).accepted is

/-- 精化主定理（无 flush 轨迹）：发射序列 ++ 终态滞留 = 初始滞留 ++ 接受序列。
    直接推论：发射序列是接受序列的前缀（队列抽象意义上的 FIFO 精化）。 -/
theorem ibLane_run_abs [Inhabited α] (s : IbLane α) (is : List (IbLaneIn α))
    (hf : ∀ i ∈ is, i.flush = false) :
    (s.run is).2 ++ (s.run is).1.abs = s.abs ++ s.accepted is := by
  induction is generalizing s with
  | nil => simp [IbLane.run, IbLane.accepted]
  | cons i is ih =>
    have hfi : i.flush = false := hf i List.mem_cons_self
    have hf' : ∀ j ∈ is, j.flush = false := fun j hj => hf j (List.mem_cons_of_mem _ hj)
    have hstep := ibLane_step_abs s i hfi
    have hih := ih (s.step i) hf'
    simp only [IbLane.run, IbLane.accepted]
    -- ++ 左结合：先右结合化才能匹配 hih / hstep 的左端
    rw [List.append_assoc, hih]
    conv => lhs; rw [← List.append_assoc]
    rw [hstep, List.append_assoc]

/-- 从空 lane 出发：发射序列是接受序列的前缀 -/
theorem ibLane_run_prefix [Inhabited α] (is : List (IbLaneIn α))
    (hf : ∀ i ∈ is, i.flush = false) :
    ∃ t, ((IbLane.empty (α := α)).run is).2 ++ t =
      (IbLane.empty (α := α)).accepted is := by
  have h := ibLane_run_abs (IbLane.empty (α := α)) is hf
  have hm0 : (default : IbGrp α).mask = 0#2 := rfl
  have he : (IbLane.empty (α := α)).abs = ([] : List α) := by
    simp [IbLane.empty, IbLane.abs, ibSdPending, ibGrpFlat, IbQ.empty, IbQ.abs, hm0]
  exact ⟨(IbLane.empty.run is).1.abs, h.trans (by rw [he]; simp)⟩

#print axioms ibLane_run_abs
#print axioms ibLane_step_abs
#print axioms ibLane_irrevocable

/- ========================================================================= -/
/- 7. IbTop：InstrBufferV2 整机（8 warp）：输入导向 + 每 warp flush + 发射    -/
/- ========================================================================= -/

/-- InstrBufferV2 整机状态：每 warp 一条 lane（:115-116,:178） -/
structure IbTop where
  lanes : Fin 8 → IbLane IbInsn

/-- 整机输入：io.in（valid + 组，:107-110）、io.flush_wid（:111）、
    每 warp 下游 ready（pipe.scala:224 的 ibuffer2issue.ready & warp_ready） -/
structure IbTopIn where
  inV    : Bool
  grp    : IbGrp IbInsn
  flushV : Bool
  flushW : BitVec 3
  outRdy : BitVec 8   -- 每 warp 一比特

/-- warp w 的 lane 输入：enq 导向（:118 `control(0).wid == i.U && io.in.valid`）、
    flush 导向（:120,:180）、outRdy 取第 w 位（移位形式取位） -/
def ibTopLaneIn (i : IbTopIn) (w : Fin 8) : IbLaneIn IbInsn :=
  { enqV := i.inV && (i.grp.c0.wid == BitVec.ofNat 3 w.val)
    grp := i.grp
    outRdy := (i.outRdy >>> BitVec.ofNat 8 w.val) &&& 1#8 = 1#8
    flush := i.flushV && (i.flushW == BitVec.ofNat 3 w.val) }

/-- 整机单拍：pointwise 各 lane（:117-126 的 foreach 循环） -/
def ibTopStep (t : IbTop) (i : IbTopIn) : IbTop :=
  ⟨fun w => (t.lanes w).step (ibTopLaneIn i w)⟩

/-- io.in.ready = 导向 warp 的 enq.ready（:124/:128） -/
def IbTop.inRdy (t : IbTop) (i : IbTopIn) : Bool :=
  (t.lanes ⟨i.grp.c0.wid.toNat, by have := i.grp.c0.wid.isLt; omega⟩).enqRdy

/-- io.ibuffer_ready(w)（:125） -/
def IbTop.ibufRdy (t : IbTop) (w : Fin 8) : Bool := (t.lanes w).enqRdy

/-- io.out(w).valid（:187 经 SlowDown :171） -/
def IbTop.outV (t : IbTop) (w : Fin 8) : Bool := (t.lanes w).outV

/-- io.out(w).bits（:187 经 SlowDown :172） -/
def IbTop.outBits (t : IbTop) (w : Fin 8) : IbInsn := (t.lanes w).outBits

/-- 整机多拍 -/
def ibTopRun (t : IbTop) : List IbTopIn → IbTop
  | [] => t
  | i :: is => ibTopRun (ibTopStep t i) is

def ibTopEmpty : IbTop := ⟨fun _ => IbLane.empty⟩

/-- 局部性/提升引理：warp w 的演化只取决于导向它的输入。
    由此 per-warp 精化定理（ibLane_run_abs）原样提升到整机。 -/
theorem ibTopRun_get (t : IbTop) (is : List IbTopIn) (w : Fin 8) :
    (ibTopRun t is).lanes w =
      ((t.lanes w).run (is.map fun i => ibTopLaneIn i w)).1 := by
  induction is generalizing t with
  | nil => rfl
  | cons i is ih =>
    show (ibTopRun (ibTopStep t i) is).lanes w = _
    rw [ih]
    rfl

/-- 整机 per-warp 顺序保持：warp w 无 flush 时，其发射序列是接受序列的前缀
    （即 ibLane_run_prefix 经 ibTopLaneIn 投影到整机轨迹）。 -/
theorem ibTop_warp_prefix (t : IbTop) (is : List IbTopIn) (w : Fin 8)
    (he : t.lanes w = IbLane.empty)
    (hf : ∀ i ∈ is, (ibTopLaneIn i w).flush = false) :
    ∃ tl, (((t.lanes w).run (is.map fun i => ibTopLaneIn i w)).2) ++ tl =
      (t.lanes w).accepted (is.map fun i => ibTopLaneIn i w) := by
  rw [he]
  have hf' : ∀ j ∈ is.map fun i => ibTopLaneIn i w, j.flush = false := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    exact hf i hi
  have h := ibLane_run_abs (IbLane.empty (α := IbInsn)) _ hf'
  have hm0 : (default : IbGrp IbInsn).mask = 0#2 := rfl
  have hee : (IbLane.empty (α := IbInsn)).abs = ([] : List IbInsn) := by
    simp [IbLane.empty, IbLane.abs, ibSdPending, ibGrpFlat, IbQ.empty, IbQ.abs, hm0]
  exact ⟨_, h.trans (by rw [hee]; simp)⟩

#print axioms ibTop_warp_prefix

/- ---- IbTop 测试（多拍轨迹，native_decide） ---- -/

section IbTopTests

def ibTopIn (inV : Bool) (g : IbGrp IbInsn) (fv : Bool) (fw : BitVec 3) (rdy : BitVec 8) :
    IbTopIn := ⟨inV, g, fv, fw, rdy⟩

def ibIdle : IbTopIn := ibTopIn false (ibGrpW 0 0 0 0#2) false 0 0

/-- warp w 的发射序列（经局部性引理取 lane run 之输出） -/
def ibTopWarpOuts (is : List IbTopIn) (w : Fin 8) : List IbInsn :=
  ((IbLane.empty (α := IbInsn)).run (is.map fun i => ibTopLaneIn i w)).2

-- 双 warp 交织入队、各自独立发射：warp0 得 [10,11]，warp1 得 [20]
def ibTrInterleave : List IbTopIn :=
  [ ibTopIn true (ibGrpW 0 10 11 3#2) false 0 0b00000000#8   -- 拍0：组[10,11]→warp0
  , ibTopIn true (ibGrpW 1 20 21 1#2) false 0 0b00000001#8   -- 拍1：组[20]→warp1；warp0 发 10
  , ibTopIn false (ibGrpW 0 0 0 0#2) false 0 0b00000011#8    -- 拍2：warp0 发 11；warp1 发 20
  , ibTopIn false (ibGrpW 0 0 0 0#2) false 0 0b00000011#8 ]

theorem ibT_interleave_w0 :
    (ibTopWarpOuts ibTrInterleave ⟨0, by decide⟩).map IbInsn.tag = [10, 11] := by
  native_decide

theorem ibT_interleave_w1 :
    (ibTopWarpOuts ibTrInterleave ⟨1, by decide⟩).map IbInsn.tag = [20] := by
  native_decide

-- 提升一致性：整机 lane = lane 单独跑（数值层面印证 ibTopRun_get）
theorem ibT_lift :
    ((ibTopRun ibTopEmpty ibTrInterleave).lanes ⟨0, by decide⟩).abs.map IbInsn.tag =
      ((IbLane.empty (α := IbInsn)).run
        (ibTrInterleave.map fun i => ibTopLaneIn i ⟨0, by decide⟩)).1.abs.map IbInsn.tag := by
  native_decide

-- Q1 复现：flush warp3 与"向 warp3 入队"同拍 —— in.ready 为高（上游认为已接受），
-- 但该组被静默丢弃：后续若干净拍发射，warp3 无任何输出。
def ibTrFlushRace : List IbTopIn :=
  [ ibTopIn true (ibGrpW 3 77 78 3#2) true 3 0b00001000#8    -- 拍0：enq warp3 与 flush warp3 同拍
  , ibTopIn false (ibGrpW 0 0 0 0#2) false 0 0b00001000#8
  , ibTopIn false (ibGrpW 0 0 0 0#2) false 0 0b00001000#8
  , ibTopIn false (ibGrpW 0 0 0 0#2) false 0 0b00001000#8 ]

/-- in.ready 在竞态拍为高（队列空 → canEnq；ready 不看 flush） -/
theorem ibT_flush_race_ready :
    IbTop.inRdy ibTopEmpty (ibTopIn true (ibGrpW 3 77 78 3#2) true 3 0b00001000#8) = true := by
  native_decide

/-- 竞态后 warp3 的发射序列为空：被"接受"的 [77,78] 丢失 -/
theorem ibT_flush_enq_drop :
    ibTopWarpOuts ibTrFlushRace ⟨3, by decide⟩ = [] := by
  native_decide

-- 对照：无 flush 时同样入队正常发射（空 lane 2 拍装入 latency，第 3、4 拍发射）
theorem ibT_no_flush_ok :
    (ibTopWarpOuts [ ibTopIn true (ibGrpW 3 77 78 3#2) false 0 0b00001000#8
                   , ibTopIn false (ibGrpW 0 0 0 0#2) false 0 0b00001000#8
                   , ibTopIn false (ibGrpW 0 0 0 0#2) false 0 0b00001000#8
                   , ibTopIn false (ibGrpW 0 0 0 0#2) false 0 0b00001000#8 ]
                   ⟨3, by decide⟩).map IbInsn.tag = [77, 78] := by
  native_decide

-- flush 只清目标 warp：flush warp1 不影响 warp0 的滞留
theorem ibT_flush_local :
    (((ibTopRun ibTopEmpty
        [ ibTopIn true (ibGrpW 0 60 61 3#2) false 0 0
        , ibTopIn false (ibGrpW 0 0 0 0#2) true 1 0 ]).lanes ⟨0, by decide⟩).abs.map IbInsn.tag)
    = [60, 61] := by
  native_decide

end IbTopTests

end Ventus.Schedule
