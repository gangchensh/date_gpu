/- ========================================================================= -/
/-                     SIMT/BranchJoin.lean                                  -/
/-  SIMT 分支分化/汇合模块 branch_join 的 Lean 4 模型（M0 试点）              -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/branch_join.scala   -/
/-  （实际被 pipe.scala:129 以 `new branch_join(num_thread)` 例化，           -/
/-    即 depth_stack = num_thread = 32。SIMT_STACK.scala 为死代码，不建模。） -/
/-                                                                           -/
/- ======================== 建模假设 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 三个缓冲队列按直通处理：branch_ctl_buf(Queue(.,1,flow=true))、        -/
/-      if_mask_buf(Queue(.,0))、PC_reconv_buf(Queue(.,1,flow=true)) 不建模， -/
/-      branch op 的各字段（opcode/PC_branch/PC_execute/PC_reconv/mask_init） -/
/-      与 valu 的 if_mask 作为同拍输入事件（branch_join.scala:84-86）。       -/
/-      队列精化留待后续波次用 Ventus.Base.QueueModel 做。                    -/
/-  D2. 单 warp 建模：Chisel 例化 num_warp=8 个独立 branch_join_stack 并以    -/
/-      warp_id 选择（:112, :158-169）。各 warp 栈与 thread_masks 项完全独立、-/
/-      无交互，故只建模单 warp；wid 索引、io.out_mask 的 mux（:260）、        -/
/-      io.complete.bits 的 wid（:122）省略。                                 -/
/-  D3. stack_mem 未初始化项建模为全 0（bjStackInit / bjEntryDefault）。       -/
/-      Chisel Mem 未初始化读为未定值；本模型取 0，依赖"pop 前必有 push"的    -/
/-      使用契约（pop 的有效性由 reconPC 匹配 + wr≠0 保证，匹配项必为已写项）。-/
/-  D4. Mem 索引取 `ptr.toNat % depth`（bjIdx）。合法契约下指针 < depth，     -/
/-      与 Chisel 一致；栈被掏空后 rd_ptr 可能回绕到 ≥ depth（见 T1 注释），   -/
/-      此时 Chisel 读出界为未定值、本模型读出模 depth 的值——差异仅出现在    -/
/-      wr=0（下溢保护生效、jump 必为 0）时，不可观测。                       -/
/-  D5. 指针宽度：Chisel `log2Ceil(depth+1)`（:35-36），depth ≥ 1 时恒等于    -/
/-      `Nat.log2 depth + 1`，本模型取后者（bjPtrWidth）。指针加减为 BitVec   -/
/-      运算，忠实建模 2^pw 回绕。                                            -/
/-  D6. debug/常量输出不建模：io.CurSig / io.PrevSig / missTableTrigger 恒 0   -/
/-      （:262-264），SPIKE_OUTPUT printf（:204-244）无副作用。               -/
/-  D7. join 事件的 stack 输入 threadMask/pushData 填默认值（bjJoinIn）：      -/
/-      push=false 时这两个字段不被使用（:48-60）。                           -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.SIMT

open Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. branch_join_stack：栈状态与组合逻辑                                    -/
/-    对应 branch_join.scala:18-63                                           -/
/- ========================================================================= -/

/-- 指针宽度：Chisel `log2Ceil(depth+1)`（:35-36），depth ≥ 1 时等于 `Nat.log2 depth + 1`。 -/
def bjPtrWidth (depth : Nat) : Nat := Nat.log2 depth + 1

/-- stackEntry（:18-22）：reconPC / jumpPC / newMask。 -/
structure BjEntry (nT : Nat) where
  reconPC : BitVec 32
  jumpPC  : BitVec 32
  newMask : BitVec nT
deriving DecidableEq, Repr

/-- 未初始化项建模值（见 D3）。 -/
def bjEntryDefault {nT : Nat} : BjEntry nT := ⟨0, 0, 0⟩

/-- branch_join_stack 状态（:35-38）：stack_mem / rd_ptr / wr_ptr。 -/
structure BjStackState (depth nT : Nat) where
  mem : Fin depth → BjEntry nT
  rd  : BitVec (bjPtrWidth depth)
  wr  : BitVec (bjPtrWidth depth)

/-- 初始状态：rd_ptr = wr_ptr = 0（RegInit 0，:35-36），mem 全 0（建模假设 D3）。 -/
def bjStackInit (depth nT : Nat) : BjStackState depth nT :=
  { mem := fun _ => bjEntryDefault, rd := 0, wr := 0 }

/-- Mem 索引：BitVec 指针 → Fin depth（取模，见 D4）。 -/
def bjIdx {depth : Nat} [NeZero depth] (p : BitVec (bjPtrWidth depth)) : Fin depth :=
  ⟨p.toNat % depth, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne depth))⟩

/-- stack 输入（io.push/pop/pushData/threadMask/PCexecute，:26-30）。 -/
structure BjStackIn (nT : Nat) where
  push      : Bool
  pop       : Bool
  pushData  : BjEntry nT
  threadMask : BitVec nT
  PCexecute : BitVec 32

/-- is_pop = is_pop_pc && !is_pop_underflow（:42-44）：
    TOS 汇合 PC 匹配当前执行 PC，且 wr_ptr ≠ 0（下溢保护）。 -/
def bjCanPop {depth nT : Nat} [NeZero depth] (s : BjStackState depth nT) (pc : BitVec 32) : Bool :=
  ((s.mem (bjIdx s.rd)).reconPC == pc) && !(s.wr == 0)

/-- io.jump = is_pop && io.pop（:45）。 -/
def bjStackJump {depth nT : Nat} [NeZero depth] (s : BjStackState depth nT) (i : BjStackIn nT) :
    Bool :=
  i.pop && bjCanPop s i.PCexecute

/-- io.newPC = stack_mem(rd_ptr).jumpPC（:61）。 -/
def bjStackNewPC {depth nT : Nat} [NeZero depth] (s : BjStackState depth nT) : BitVec 32 :=
  (s.mem (bjIdx s.rd)).jumpPC

/-- io.newMask = stack_mem(rd_ptr).newMask（:62）。 -/
def bjStackNewMask {depth nT : Nat} [NeZero depth] (s : BjStackState depth nT) : BitVec nT :=
  (s.mem (bjIdx s.rd)).newMask

/-- Mem 写（与 Ventus.Base.Defs 的 mem_write 同风格，entry 版）。 -/
def bjMemUpdate {depth nT : Nat} (m : Fin depth → BjEntry nT) (i : Fin depth) (v : BjEntry nT) :
    Fin depth → BjEntry nT :=
  fun j => if i = j then v else m j

@[simp] theorem bjMemUpdate_self {depth nT : Nat} (m : Fin depth → BjEntry nT)
    (i : Fin depth) (v : BjEntry nT) : bjMemUpdate m i v i = v := by
  simp [bjMemUpdate]

theorem bjMemUpdate_of_ne {depth nT : Nat} (m : Fin depth → BjEntry nT)
    (i j : Fin depth) (v : BjEntry nT) (h : i ≠ j) : bjMemUpdate m i v j = m j := by
  simp [bjMemUpdate, h]

/-- branch_join_stack 单拍转移（:47-60）。
    push（仅分化时发生）：stack_mem(wr_ptr) ← {reconPC, jumpPC=reconPC, newMask=threadMask}；
    stack_mem(wr_ptr+1) ← pushData；rd_ptr := wr_ptr+1；wr_ptr := wr_ptr+2。
    pop（io.jump 有效）：wr_ptr/rd_ptr 各减 1。push 与 pop 同拍时 push 优先
    （`when ... .elsewhen`，:48/57）。 -/
def bjStackStep {depth nT : Nat} [NeZero depth] (s : BjStackState depth nT) (i : BjStackIn nT) :
    BjStackState depth nT :=
  if i.push then
    { mem := bjMemUpdate (bjMemUpdate s.mem (bjIdx (s.wr + 1)) i.pushData)
                (bjIdx s.wr) ⟨i.pushData.reconPC, i.pushData.reconPC, i.threadMask⟩,
      rd := s.wr + 1,
      wr := s.wr + 2 }
  else if bjStackJump s i then
    { s with wr := s.wr - 1, rd := s.rd - 1 }
  else s

/- ---- bjStackStep 投影微引理（供 T1/T2 组合用） ---- -/

theorem bjStackStep_push_eq {depth nT : Nat} [NeZero depth] (s : BjStackState depth nT)
    (i : BjStackIn nT) (h : i.push = true) :
    bjStackStep s i =
      { mem := bjMemUpdate (bjMemUpdate s.mem (bjIdx (s.wr + 1)) i.pushData)
                  (bjIdx s.wr) ⟨i.pushData.reconPC, i.pushData.reconPC, i.threadMask⟩,
        rd := s.wr + 1, wr := s.wr + 2 } := by
  simp [bjStackStep, h]

theorem bjStackStep_push_wr {depth nT : Nat} [NeZero depth] (s : BjStackState depth nT)
    (i : BjStackIn nT) (h : i.push = true) : (bjStackStep s i).wr = s.wr + 2 := by
  simp [bjStackStep, h]

theorem bjStackStep_push_rd {depth nT : Nat} [NeZero depth] (s : BjStackState depth nT)
    (i : BjStackIn nT) (h : i.push = true) : (bjStackStep s i).rd = s.wr + 1 := by
  simp [bjStackStep, h]

theorem bjStackStep_pop_eq {depth nT : Nat} [NeZero depth] (s : BjStackState depth nT)
    (i : BjStackIn nT) (h : i.push = false) (hj : bjStackJump s i = true) :
    bjStackStep s i = { mem := s.mem, rd := s.rd - 1, wr := s.wr - 1 } := by
  simp [bjStackStep, h, hj]

theorem bjStackStep_pop_wr {depth nT : Nat} [NeZero depth] (s : BjStackState depth nT)
    (i : BjStackIn nT) (h : i.push = false) (hj : bjStackJump s i = true) :
    (bjStackStep s i).wr = s.wr - 1 := by
  simp [bjStackStep, h, hj]

theorem bjStackStep_pop_rd {depth nT : Nat} [NeZero depth] (s : BjStackState depth nT)
    (i : BjStackIn nT) (h : i.push = false) (hj : bjStackJump s i = true) :
    (bjStackStep s i).rd = s.rd - 1 := by
  simp [bjStackStep, h, hj]

/-- 符号位宽下的数值引理：(2 : BitVec (log2 depth + 1)) = 1 + 1。
    （bv_omega 在符号位宽下无法处理 `w + 2 - 1 - 1`，拆成两个 +1 用 add_sub_cancel。） -/
theorem bjTwo_eq_one_add_one {depth : Nat} [NeZero depth] :
    (2 : BitVec (bjPtrWidth depth)) = 1 + 1 := by
  show (2 : BitVec (Nat.log2 depth + 1)) = 1 + 1
  apply BitVec.eq_of_toNat_eq
  simp

/- ========================================================================= -/
/- 2. branch_join 组合逻辑（单 warp，:78-172）                                -/
/- ========================================================================= -/

/-- branch（vbranch，opcode=0）事件的同拍输入（直通假设 D1）：
    valuMask = valu 给的 if_mask 原始值（if_mask_buf.bits.if_mask，:141）；
    maskInit = branch_ctl.bits.mask_init（:141-142）。 -/
structure BjBranchIn (nT : Nat) where
  valuMask  : BitVec nT
  maskInit  : BitVec nT
  PCbranch  : BitVec 32
  PCexecute : BitVec 32
  PCreconv  : BitVec 32

/-- if_mask（:141）。 -/
def bjIfMask {nT : Nat} (bi : BjBranchIn nT) : BitVec nT := bi.valuMask &&& bi.maskInit
/-- else_mask（:142）。 -/
def bjElseMask {nT : Nat} (bi : BjBranchIn nT) : BitVec nT := ~~~bi.valuMask &&& bi.maskInit
/-- ifOnly := else_mask == 0（:146）。 -/
def bjIfOnly {nT : Nat} (bi : BjBranchIn nT) : Bool := bjElseMask bi == 0
/-- elseOnly := if_mask == 0（:147）。 -/
def bjElseOnly {nT : Nat} (bi : BjBranchIn nT) : Bool := bjIfMask bi == 0
/-- divOccur := ~(ifOnly | elseOnly)（:148）。 -/
def bjDivOccur {nT : Nat} (bi : BjBranchIn nT) : Bool := !(bjIfOnly bi || bjElseOnly bi)

/-- PopCount（:98-99, :143-144）。 -/
def bjPopcount {n : Nat} (m : BitVec n) : Nat :=
  (List.finRange n).foldl (fun acc (i : Fin n) => acc + (if m.getLsbD i.val then 1 else 0)) 0

/-- takeif := ((ifCnt < elseCnt) && divOccur) || ifOnly（:145）。 -/
def bjTakeif {nT : Nat} (bi : BjBranchIn nT) : Bool :=
  (decide (bjPopcount (bjIfMask bi) < bjPopcount (bjElseMask bi)) && bjDivOccur bi) || bjIfOnly bi

/-- pushentry（:149-156）：reconPC = PC_reconv；
    takeif 时 {newMask=else_mask, jumpPC=PC_branch}，否则 {newMask=if_mask, jumpPC=PC_execute+4}。 -/
def bjPushentry {nT : Nat} (bi : BjBranchIn nT) : BjEntry nT :=
  { reconPC := bi.PCreconv,
    jumpPC  := if bjTakeif bi then bi.PCbranch else bi.PCexecute + 4,
    newMask := if bjTakeif bi then bjElseMask bi else bjIfMask bi }

/- ========================================================================= -/
/- 3. 单 warp 系统模型：stack + thread_masks + 输出事件                       -/
/- ========================================================================= -/

/-- 输入事件：branch = vbranch fire（opcode=0，含 valu if_mask）；join = join fire
    （opcode=1，:160）；nop = 无操作。 -/
inductive BjEvent (nT : Nat) where
  | nop
  | branch (bi : BjBranchIn nT)
  | join (pcExecute : BitVec 32)

/-- 单拍可观测输出。 -/
structure BjOut (nT : Nat) where
  complete   : Bool       -- io.complete.valid（:120）
  fetchValid : Bool       -- fetch_ctl_valid（:179-200）
  fetchJump  : Bool       -- fetch_ctl.jump
  fetchPC    : BitVec 32  -- fetch_ctl.new_pc
  popJump    : Bool       -- popjump = bjjump(warp_id)（:170）
  popPC      : BitVec 32  -- popPC（:171）
  popMask    : BitVec nT  -- popMask（:172）

def bjOutDefault {nT : Nat} : BjOut nT := ⟨false, false, false, 0, false, 0, 0⟩

/-- 单 warp 系统状态：栈 + thread_masks(warp_id)（:90）。 -/
structure BjSysState (depth nT : Nat) where
  stack : BjStackState depth nT
  tmask : BitVec nT

/-- branch 事件对应的 stack 输入：push = divOccur（:159），pop = false。 -/
def bjBranchStackIn {depth nT : Nat} (s : BjSysState depth nT) (bi : BjBranchIn nT) : BjStackIn nT :=
  { push := bjDivOccur bi, pop := false, pushData := bjPushentry bi,
    threadMask := s.tmask, PCexecute := bi.PCexecute }

/-- join 事件对应的 stack 输入：push = false，pop = true（:160）。
    threadMask/pushData 不会被使用（D7）。 -/
def bjJoinIn {nT : Nat} (pc : BitVec 32) : BjStackIn nT :=
  { push := false, pop := true, pushData := bjEntryDefault, threadMask := 0, PCexecute := pc }

/-- 单 warp branch_join 单拍转移 + 输出。
    thread_masks 更新（:249-259）：branch fire 且 divOccur 时取所走路径掩码
    （takeif → if_mask，否则 else_mask）；否则 join 且 popjump 时取 popMask。
    fetch_ctl（:185-200）：join 时总发（popjump → {jump=1, new_pc=popPC}，否则
    {jump=0, new_pc=0}）；branch 时仅 (!takeif || elseOnly) 发 {jump=1, new_pc=PC_branch}。
    complete（:120）：branch fire 且 takeif 时拉高。 -/
def bjSysStep {depth nT : Nat} [NeZero depth] (s : BjSysState depth nT) (e : BjEvent nT) :
    BjSysState depth nT × BjOut nT :=
  match e with
  | .nop => (s, bjOutDefault)
  | .branch bi =>
      let div := bjDivOccur bi
      let tk  := bjTakeif bi
      let st' := bjStackStep s.stack (bjBranchStackIn s bi)
      let tm' := if div then (if tk then bjIfMask bi else bjElseMask bi) else s.tmask
      let fc  := (!tk) || bjElseOnly bi
      ({ stack := st', tmask := tm' },
       { complete := tk, fetchValid := fc, fetchJump := fc,
         fetchPC := if fc then bi.PCbranch else 0,
         popJump := false, popPC := 0, popMask := 0 })
  | .join pc =>
      let j   := bjStackJump s.stack (bjJoinIn pc)
      let st' := bjStackStep s.stack (bjJoinIn pc)
      let tm' := if j then bjStackNewMask s.stack else s.tmask
      ({ stack := st', tmask := tm' },
       { complete := false, fetchValid := true, fetchJump := j,
         fetchPC := if j then bjStackNewPC s.stack else 0,
         popJump := j, popPC := bjStackNewPC s.stack, popMask := bjStackNewMask s.stack })

/-- 多拍迭代（run）。 -/
def bjRun {depth nT : Nat} [NeZero depth] (s : BjSysState depth nT) (es : List (BjEvent nT)) :
    BjSysState depth nT :=
  es.foldl (fun st e => (bjSysStep st e).1) s

/- ========================================================================= -/
/- 4. 具体数值测试（depth = 4, nT = 4，即 pw = 3）                             -/
/-                                                                           -/
/-  注意（重要，与直觉相反处）：栈从空状态做一次 push + 两次有效 pop 后，      -/
/-  wr_ptr 回到 0，但 rd_ptr 回绕为 7（= 0-1 mod 2^3）。这是 Chisel 真实行为 -/
/-  （pop 无条件 rd_ptr-1，:59）；无害：rd 仅在栈非空时有效（rd = wr-1），     -/
/-  且 pop 有 wr≠0 下溢保护、push 会重置 rd := wr+1。测试中如实断言 rd = 7。  -/
/-  多拍轨迹一律 native_decide（多拍多合取 by decide 内核归约爆炸，见          -/
/-  AGENTS.md 已知踩坑），公理审计会多 Lean.ofReduceBool，属预期。            -/
/- ========================================================================= -/

section BJTests

/-- 初始系统状态：栈空，thread_mask = 0b1111（RegInit ~0，:90）。 -/
def tInit : BjSysState 4 4 := { stack := bjStackInit 4 4, tmask := 0b1111 }

/- ---- 测试 A：先 if 后 else 完整分化-汇合（takeif = true），join 三拍通过 ---- -/
/-  valuMask=0b1000 → if=0b1000(1 线程) < else=0b0111(3 线程) → takeif。
    pushData = {reconPC=0x300, newMask=else=0b0111, jumpPC=PC_branch=0x200}；
    RPC 项 = {0x300, 0x300, 0b1111}；所走路径掩码 = if = 0b1000（fallthrough，无 fetch）。 -/

def tA_branch : BjBranchIn 4 :=
  { valuMask := 0b1000, maskInit := 0b1111, PCbranch := 0x200, PCexecute := 0x100, PCreconv := 0x300 }

def tA_r1 := bjSysStep tInit (.branch tA_branch)
def tA_r2 := bjSysStep tA_r1.1 (.join 0x300)
def tA_r3 := bjSysStep tA_r2.1 (.join 0x300)
def tA_r4 := bjSysStep tA_r3.1 (.join 0x300)

-- A 拍 1（分化）：takeif → complete 拉高、无 fetch、push 两项、走 if 路径掩码
theorem tA_beat1 :
    tA_r1.2.complete = true ∧ tA_r1.2.fetchValid = false ∧
    tA_r1.1.tmask = 0b1000 ∧ tA_r1.1.stack.wr = 2 ∧ tA_r1.1.stack.rd = 1 := by
  native_decide
theorem tA_beat1_mem :
    tA_r1.1.stack.mem (bjIdx 1) = ⟨0x300, 0x200, 0b0111⟩ ∧
    tA_r1.1.stack.mem (bjIdx 0) = ⟨0x300, 0x300, 0b1111⟩ := by
  native_decide
-- A 拍 2（第一条路径到 join）：弹路径项 → 跳 else 路径 PC_branch=0x200，掩码换 else
theorem tA_beat2 :
    tA_r2.2.popJump = true ∧ tA_r2.2.popPC = 0x200 ∧ tA_r2.2.popMask = 0b0111 ∧
    tA_r2.2.fetchValid = true ∧ tA_r2.2.fetchJump = true ∧ tA_r2.2.fetchPC = 0x200 ∧
    tA_r2.1.tmask = 0b0111 ∧ tA_r2.1.stack.wr = 1 ∧ tA_r2.1.stack.rd = 0 := by
  native_decide
-- A 拍 3（第二条路径到 join）：弹 RPC 项 → 跳回 reconPC=0x300，恢复完整掩码；
-- 注意 rd 回绕为 7（0-1 mod 8），见本节头部注释
theorem tA_beat3 :
    tA_r3.2.popJump = true ∧ tA_r3.2.popPC = 0x300 ∧ tA_r3.2.popMask = 0b1111 ∧
    tA_r3.2.fetchPC = 0x300 ∧
    tA_r3.1.tmask = 0b1111 ∧ tA_r3.1.stack.wr = 0 ∧ tA_r3.1.stack.rd = 7 := by
  native_decide
-- A 拍 4（join 第三次以完整掩码执行）：栈空 → 无操作、fallthrough（fetchValid 但 jump=0）
theorem tA_beat4 :
    tA_r4.2.popJump = false ∧ tA_r4.2.fetchValid = true ∧ tA_r4.2.fetchJump = false ∧
    tA_r4.2.fetchPC = 0 ∧ tA_r4.1.tmask = 0b1111 ∧
    tA_r4.1.stack.wr = 0 ∧ tA_r4.1.stack.rd = 7 := by
  native_decide

/- ---- 测试 B：else 优先（ifCnt > elseCnt → takeif = false）完整汇合 ---- -/
/-  valuMask=0b0111 → if=0b0111(3) > else=0b1000(1) → takeif=false。
    pushData = {reconPC=0x300, newMask=if=0b0111, jumpPC=PC_execute+4=0x104}；
    走 else 路径（fetch 跳 PC_branch=0x200），所走掩码 = else = 0b1000。 -/

def tB_branch : BjBranchIn 4 :=
  { valuMask := 0b0111, maskInit := 0b1111, PCbranch := 0x200, PCexecute := 0x100, PCreconv := 0x300 }

def tB_r1 := bjSysStep tInit (.branch tB_branch)
def tB_r2 := bjSysStep tB_r1.1 (.join 0x300)
def tB_r3 := bjSysStep tB_r2.1 (.join 0x300)

theorem tB_beat1 :
    tB_r1.2.complete = false ∧ tB_r1.2.fetchValid = true ∧ tB_r1.2.fetchJump = true ∧
    tB_r1.2.fetchPC = 0x200 ∧ tB_r1.1.tmask = 0b1000 ∧
    tB_r1.1.stack.wr = 2 ∧ tB_r1.1.stack.rd = 1 ∧
    tB_r1.1.stack.mem (bjIdx 1) = ⟨0x300, 0x104, 0b0111⟩ := by
  native_decide
-- 弹路径项 → 跳回 if 路径 PC_execute+4 = 0x104，掩码换 if
theorem tB_beat2 :
    tB_r2.2.popJump = true ∧ tB_r2.2.popPC = 0x104 ∧ tB_r2.2.popMask = 0b0111 ∧
    tB_r2.1.tmask = 0b0111 ∧ tB_r2.1.stack.wr = 1 ∧ tB_r2.1.stack.rd = 0 := by
  native_decide
-- 弹 RPC 项 → 跳回 0x300，恢复完整掩码
theorem tB_beat3 :
    tB_r3.2.popJump = true ∧ tB_r3.2.popPC = 0x300 ∧ tB_r3.2.popMask = 0b1111 ∧
    tB_r3.1.tmask = 0b1111 ∧ tB_r3.1.stack.wr = 0 ∧ tB_r3.1.stack.rd = 7 := by
  native_decide

/- ---- 测试 C：ifOnly（else_mask = 0）→ takeif、不分化、无 fetch、无 push ---- -/

def tC_branch : BjBranchIn 4 :=
  { valuMask := 0b1111, maskInit := 0b1111, PCbranch := 0x200, PCexecute := 0x100, PCreconv := 0x300 }

def tC_r1 := bjSysStep tInit (.branch tC_branch)

theorem tC_ifOnly :
    tC_r1.2.complete = true ∧ tC_r1.2.fetchValid = false ∧
    tC_r1.1.tmask = 0b1111 ∧ tC_r1.1.stack.wr = 0 ∧ tC_r1.1.stack.rd = 0 := by
  native_decide

/- ---- 测试 D：elseOnly（if_mask = 0）→ 不 takeif、complete 不拉高（审查疑点 S3）、
       fetch 跳 PC_branch、无 push、掩码不变 ---- -/

def tD_branch : BjBranchIn 4 :=
  { valuMask := 0b0000, maskInit := 0b1111, PCbranch := 0x200, PCexecute := 0x100, PCreconv := 0x300 }

def tD_r1 := bjSysStep tInit (.branch tD_branch)

theorem tD_elseOnly :
    tD_r1.2.complete = false ∧ tD_r1.2.fetchValid = true ∧ tD_r1.2.fetchJump = true ∧
    tD_r1.2.fetchPC = 0x200 ∧ tD_r1.1.tmask = 0b1111 ∧
    tD_r1.1.stack.wr = 0 ∧ tD_r1.1.stack.rd = 0 := by
  native_decide

/- ---- 测试 E：两级嵌套分化 ---- -/
/-  A：valu=0b1100（if=else=2 线程，计数相等 → takeif=false）走 else，push A；
    B（在 A 的 else 路径上，maskInit=0b0011）：valu=0b0001 → if=0b0001(1)，else=0b0010(1)
    → takeif=false，push B；之后 join B×2、join A×2 逐层汇合，最终掩码恢复 0b1111、栈空。 -/

def tE_branchA : BjBranchIn 4 :=
  { valuMask := 0b1100, maskInit := 0b1111, PCbranch := 0x200, PCexecute := 0x100, PCreconv := 0x400 }
def tE_branchB : BjBranchIn 4 :=
  { valuMask := 0b0001, maskInit := 0b0011, PCbranch := 0x280, PCexecute := 0x200, PCreconv := 0x300 }

def tE_r1 := bjSysStep tInit (.branch tE_branchA)
def tE_r2 := bjSysStep tE_r1.1 (.branch tE_branchB)
def tE_r3 := bjSysStep tE_r2.1 (.join 0x300)
def tE_r4 := bjSysStep tE_r3.1 (.join 0x300)
def tE_r5 := bjSysStep tE_r4.1 (.join 0x400)
def tE_r6 := bjSysStep tE_r5.1 (.join 0x400)

theorem tE_nestA :
    tE_r1.1.stack.wr = 2 ∧ tE_r1.1.stack.rd = 1 ∧ tE_r1.1.tmask = 0b0011 ∧
    tE_r1.2.fetchPC = 0x200 := by
  native_decide
theorem tE_nestB :
    tE_r2.1.stack.wr = 4 ∧ tE_r2.1.stack.rd = 3 ∧ tE_r2.1.tmask = 0b0010 ∧
    tE_r2.2.fetchPC = 0x280 ∧
    tE_r2.1.stack.mem (bjIdx 3) = ⟨0x300, 0x204, 0b0001⟩ ∧
    tE_r2.1.stack.mem (bjIdx 2) = ⟨0x300, 0x300, 0b0011⟩ := by
  native_decide
-- 弹 B 路径项 → 跳 0x204（B 的 if 路径）
theorem tE_joinB1 :
    tE_r3.2.popJump = true ∧ tE_r3.2.popPC = 0x204 ∧ tE_r3.2.popMask = 0b0001 ∧
    tE_r3.1.tmask = 0b0001 ∧ tE_r3.1.stack.wr = 3 ∧ tE_r3.1.stack.rd = 2 := by
  native_decide
-- 弹 B RPC 项 → 回 0x300，掩码回 0b0011（A 的 else 路径掩码）
theorem tE_joinB2 :
    tE_r4.2.popJump = true ∧ tE_r4.2.popPC = 0x300 ∧ tE_r4.2.popMask = 0b0011 ∧
    tE_r4.1.tmask = 0b0011 ∧ tE_r4.1.stack.wr = 2 ∧ tE_r4.1.stack.rd = 1 := by
  native_decide
-- 弹 A 路径项 → 跳 0x104（A 的 if 路径）
theorem tE_joinA1 :
    tE_r5.2.popJump = true ∧ tE_r5.2.popPC = 0x104 ∧ tE_r5.2.popMask = 0b1100 ∧
    tE_r5.1.tmask = 0b1100 ∧ tE_r5.1.stack.wr = 1 ∧ tE_r5.1.stack.rd = 0 := by
  native_decide
-- 弹 A RPC 项 → 回 0x400，恢复完整掩码 0b1111，栈空（rd 回绕 7）
theorem tE_joinA2 :
    tE_r6.2.popJump = true ∧ tE_r6.2.popPC = 0x400 ∧ tE_r6.2.popMask = 0b1111 ∧
    tE_r6.1.tmask = 0b1111 ∧ tE_r6.1.stack.wr = 0 ∧ tE_r6.1.stack.rd = 7 := by
  native_decide

/- ---- 测试 F：空栈 pop 为无操作（下溢保护，:43-44） ---- -/

def tF_r1 := bjSysStep tInit (.join 0x300)

theorem tF_empty_pop :
    tF_r1.2.popJump = false ∧ tF_r1.2.fetchValid = true ∧ tF_r1.2.fetchJump = false ∧
    tF_r1.2.fetchPC = 0 ∧ tF_r1.1.tmask = 0b1111 ∧
    tF_r1.1.stack.wr = 0 ∧ tF_r1.1.stack.rd = 0 := by
  native_decide

/- ---- 测试 G：非匹配 PCexecute 的 join 不弹栈（:42, :45） ---- -/

def tG_r1 := bjSysStep tA_r1.1 (.join 0x99C)

theorem tG_nomatch :
    tG_r1.2.popJump = false ∧ tG_r1.2.fetchValid = true ∧ tG_r1.2.fetchJump = false ∧
    tG_r1.1.tmask = 0b1000 ∧ tG_r1.1.stack.wr = 2 ∧ tG_r1.1.stack.rd = 1 := by
  native_decide

end BJTests

/- ========================================================================= -/
/- 5. 一般性定理（参数化 depth / nT）                                         -/
/- ========================================================================= -/

/-- T1 指针守恒：栈非空不变量 `rd = wr - 1`（合法使用契约：push 前栈非满、
    pop 仅在 TOS 匹配时有效——由 hj1/hj2 假设表达）下，一次 push + 两次有效 pop
    后 wr_ptr/rd_ptr 回到 push 前值。
    注意：rd 守恒依赖非空不变量。从空栈出发 push+2pop 后 wr 归零但 rd 回绕为
    全 1（测试 A 拍 3/4 实测 rd = 7），这是 Chisel 真实行为（:58-59 无条件 -1），
    无害（下溢保护 + push 重置 rd），但见测试节头部注释。 -/
theorem bjT1_ptr_conserve {depth nT : Nat} [NeZero depth]
    (s : BjStackState depth nT) (ip i1 i2 : BjStackIn nT)
    (hp : ip.push = true)
    (h1p : i1.push = false) (h2p : i2.push = false)
    (hinv : s.rd = s.wr - 1)
    (hj1 : bjStackJump (bjStackStep s ip) i1 = true)
    (hj2 : bjStackJump (bjStackStep (bjStackStep s ip) i1) i2 = true) :
    (bjStackStep (bjStackStep (bjStackStep s ip) i1) i2).wr = s.wr ∧
    (bjStackStep (bjStackStep (bjStackStep s ip) i1) i2).rd = s.rd := by
  have p1 := bjStackStep_push_wr s ip hp
  have q1 := bjStackStep_push_rd s ip hp
  have p2 := bjStackStep_pop_wr (bjStackStep s ip) i1 h1p hj1
  have q2 := bjStackStep_pop_rd (bjStackStep s ip) i1 h1p hj1
  have p3 := bjStackStep_pop_wr (bjStackStep (bjStackStep s ip) i1) i2 h2p hj2
  have q3 := bjStackStep_pop_rd (bjStackStep (bjStackStep s ip) i1) i2 h2p hj2
  constructor
  · rw [p3, p2, p1, bjTwo_eq_one_add_one, ← BitVec.add_assoc,
        BitVec.add_sub_cancel, BitVec.add_sub_cancel]
  · rw [q3, q2, q1, hinv, BitVec.add_sub_cancel]

/-- T2 掩码恢复：分化分支（divOccur）+ 两次有效 join（hj1/hj2 表达 pop 有效）后，
    thread_masks 恢复为分支前掩码；且第一次 join 后掩码为未走路径掩码
    （pushentry.newMask）。
    合约假设：hwr（push 前栈非满：wr+1 < depth，保证两项写入索引不同）；
    hovf（wr+1 在指针位宽内不溢出，合法使用契约的一部分）。 -/
theorem bjT2_mask_restore {depth nT : Nat} [NeZero depth]
    (s : BjSysState depth nT) (bi : BjBranchIn nT)
    (hdiv : bjDivOccur bi = true)
    (hwr : s.stack.wr.toNat + 1 < depth)
    (hovf : (s.stack.wr + 1).toNat = s.stack.wr.toNat + 1)
    (pc1 pc2 : BitVec 32)
    (hj1 : bjCanPop (bjSysStep s (.branch bi)).1.stack pc1 = true)
    (hj2 : bjCanPop (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.stack pc2 = true) :
    (bjSysStep (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1 (.join pc2)).1.tmask
      = s.tmask ∧
    (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.tmask
      = (bjPushentry bi).newMask := by
  have hb_st : (bjSysStep s (.branch bi)).1.stack
      = bjStackStep s.stack (bjBranchStackIn s bi) := rfl
  have hj1' : bjStackJump (bjSysStep s (.branch bi)).1.stack (bjJoinIn pc1) = true := hj1
  have hj2' : bjStackJump (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.stack
      (bjJoinIn pc2) = true := hj2
  have hpush : (bjBranchStackIn s bi).push = true := by simp [bjBranchStackIn, hdiv]
  -- push 后的栈（两项写入：wr+1 ← pushentry，wr ← RPC 项）
  have hs1 : (bjSysStep s (.branch bi)).1.stack =
      { mem := bjMemUpdate (bjMemUpdate s.stack.mem (bjIdx (s.stack.wr + 1))
                  (bjBranchStackIn s bi).pushData)
                  (bjIdx s.stack.wr)
                  ⟨(bjBranchStackIn s bi).pushData.reconPC,
                    (bjBranchStackIn s bi).pushData.reconPC,
                    (bjBranchStackIn s bi).threadMask⟩,
        rd := s.stack.wr + 1, wr := s.stack.wr + 2 } := by
    rw [hb_st, bjStackStep_push_eq _ _ hpush]
  -- 第一次有效 join 后的栈（pop：wr/rd 各减 1，mem 不变）
  have hs2e : (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.stack
      = bjStackStep (bjSysStep s (.branch bi)).1.stack (bjJoinIn pc1) := rfl
  have hs2 : (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.stack =
      { mem := (bjSysStep s (.branch bi)).1.stack.mem,
        rd := (bjSysStep s (.branch bi)).1.stack.rd - 1,
        wr := (bjSysStep s (.branch bi)).1.stack.wr - 1 } := by
    rw [hs2e, bjStackStep_pop_eq _ _ rfl hj1']
  -- 投影链
  have hs1_mem : (bjSysStep s (.branch bi)).1.stack.mem =
      bjMemUpdate (bjMemUpdate s.stack.mem (bjIdx (s.stack.wr + 1))
        (bjBranchStackIn s bi).pushData)
        (bjIdx s.stack.wr)
        ⟨(bjBranchStackIn s bi).pushData.reconPC, (bjBranchStackIn s bi).pushData.reconPC,
          (bjBranchStackIn s bi).threadMask⟩ := by
    rw [hs1]
  have hs1_rd : (bjSysStep s (.branch bi)).1.stack.rd = s.stack.wr + 1 := by
    rw [hs1]
  have hs2_mem : (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.stack.mem =
      (bjSysStep s (.branch bi)).1.stack.mem := by
    rw [hs2]
  have hs2_mem' : (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.stack.mem =
      bjMemUpdate (bjMemUpdate s.stack.mem (bjIdx (s.stack.wr + 1))
        (bjBranchStackIn s bi).pushData)
        (bjIdx s.stack.wr)
        ⟨(bjBranchStackIn s bi).pushData.reconPC, (bjBranchStackIn s bi).pushData.reconPC,
          (bjBranchStackIn s bi).threadMask⟩ := by
    rw [hs2_mem]; exact hs1_mem
  have hs2_rd : (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.stack.rd =
      (bjSysStep s (.branch bi)).1.stack.rd - 1 := by
    rw [hs2]
  have hs2_rd' : (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.stack.rd =
      s.stack.wr + 1 - 1 := by
    rw [hs2_rd, hs1_rd]
  -- 两个写入索引不同（wr 与 wr+1 在合法契约下不撞）
  have hne : bjIdx s.stack.wr ≠ bjIdx (s.stack.wr + 1) := by
    intro h
    have hv : s.stack.wr.toNat % depth = (s.stack.wr + 1).toNat % depth := by
      have hc := congrArg Fin.val h
      simpa [bjIdx] using hc
    rw [hovf, Nat.mod_eq_of_lt (by omega : s.stack.wr.toNat < depth),
        Nat.mod_eq_of_lt hwr] at hv
    omega
  have hrd : s.stack.wr + 1 - 1 = s.stack.wr := BitVec.add_sub_cancel _ _
  -- 两次 join 的 tmask 更新展开
  have htm1 : (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.tmask
      = bjStackNewMask (bjSysStep s (.branch bi)).1.stack := by
    show (if bjStackJump (bjSysStep s (.branch bi)).1.stack (bjJoinIn pc1) then
            bjStackNewMask (bjSysStep s (.branch bi)).1.stack
          else (bjSysStep s (.branch bi)).1.tmask) = _
    rw [if_pos hj1']
  have htm2 : (bjSysStep (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1
      (.join pc2)).1.tmask
      = bjStackNewMask (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.stack := by
    show (if bjStackJump (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.stack
              (bjJoinIn pc2) then
            bjStackNewMask (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.stack
          else (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.tmask) = _
    rw [if_pos hj2']
  constructor
  · -- 第二次 join：读 RPC 项（bjIdx wr），newMask = 分支前 threadMask
    rw [htm2]
    show ((bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.stack.mem
          (bjIdx (bjSysStep (bjSysStep s (.branch bi)).1 (.join pc1)).1.stack.rd)).newMask
        = s.tmask
    rw [hs2_rd', hs2_mem', hrd, bjMemUpdate_self]
    rfl
  · -- 第一次 join：读路径项（bjIdx (wr+1)），newMask = pushentry.newMask
    rw [htm1]
    show ((bjSysStep s (.branch bi)).1.stack.mem
          (bjIdx (bjSysStep s (.branch bi)).1.stack.rd)).newMask
        = (bjPushentry bi).newMask
    rw [hs1_rd, hs1_mem, bjMemUpdate_of_ne _ _ _ _ hne, bjMemUpdate_self]
    rfl

/-- T3 下溢安全：空栈（wr_ptr = 0）上 pop 不改变任何状态（:43-44, :57-59）。 -/
theorem bjT3_underflow_safe {depth nT : Nat} [NeZero depth]
    (s : BjStackState depth nT) (i : BjStackIn nT)
    (hwr : s.wr = 0) (hp : i.push = false) :
    bjStackStep s i = s := by
  simp [bjStackStep, bjStackJump, bjCanPop, hp, hwr]

/-- T4 掩码划分：if_mask 与 else_mask 不相交且拼回 mask_init（:141-142）。
    用字面 BitVec 32（bv_decide 看不穿 abbrev，先 obtain 拆结构再投影规约）。 -/
theorem bjT4_mask_partition (bi : BjBranchIn 32) :
    bjIfMask bi &&& bjElseMask bi = 0 ∧
    bjIfMask bi ||| bjElseMask bi = bi.maskInit := by
  obtain ⟨v, m, pb, pe, pr⟩ := bi
  simp only [bjIfMask, bjElseMask]
  constructor <;> bv_decide

/-- T5 push 优先：push 与 pop 同拍时行为 = 仅 push（when/elsewhen，:48-57）。 -/
theorem bjT5_push_priority {depth nT : Nat} [NeZero depth]
    (s : BjStackState depth nT) (i : BjStackIn nT) (hp : i.push = true) :
    bjStackStep s i = bjStackStep s { i with pop := false } := by
  simp [bjStackStep, hp]

/- ---- 公理审计（T1-T5 应仅剩 Lean 标准公理；测试节 native_decide 会引入
       Lean.ofReduceBool，属预期，见 AGENTS.md 已知踩坑） ---- -/

#print axioms bjT1_ptr_conserve
#print axioms bjT2_mask_restore
#print axioms bjT3_underflow_safe
#print axioms bjT4_mask_partition
#print axioms bjT5_push_priority

end Ventus.SIMT
