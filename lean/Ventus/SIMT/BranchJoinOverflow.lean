/- ========================================================================= -/
/-                  SIMT/BranchJoinOverflow.lean                             -/
/-  bug 报告 I-2（branch_join_stack 溢出无防护）的形式化证据                  -/
/-                                                                           -/
/-  依赖：Ventus.SIMT.BranchJoin（branch_join.scala 的逐行模型，见该文件头）。  -/
/-                                                                           -/
/- ======================== 溢出机制与槽位演算 ============================== -/
/-  depth_stack = num_thread = 32（pipe.scala:129），每次分化 push 占 2 项    -/
/-  （RPC 项写 slot wr，路径项写 slot wr+1，然后 rd := wr+1, wr := wr+2）。   -/
/-  第 k 级（0 起）push 前 wr = 2k，写槽位 2k、2k+1：                         -/
/-    第 1 级（k=0）：槽 0（RPC）、槽 1（路径）                               -/
/-    第 16 级（k=15）：槽 30、31                                             -/
/-    第 17 级（k=16）：写指针 32、33 → mod 32 = 槽 0、1                      -/
/-  ⇒ 第 17 级 push 恰好覆盖第 1 级的 RPC 项与路径项。                        -/
/-  指针位宽 log2Ceil(33) = 6（0..63）：17 次 push 后 wr = 34，指针本身       -/
/-  **没有**回绕——指针忠实记录"已压 34 项"，损坏完全来自 Mem(32) 越界，       -/
/-  与指针溢出无关。                                                          -/
/-                                                                           -/
/- ======================== 建模语义说明（任务要求 3） ====================== -/
/-  Chisel/FIRRTL 中 Mem 越界读写行为未定义：越界读返回未定值，越界写被忽略   -/
/-  或行为依赖后端。本模型（BranchJoin.lean D4）把 Mem 索引取 `ptr % depth`， -/
/-  即确定性别名——这是"最温和"的具体化：它等价于越界写被静默重定向到栈底。   -/
/-  真实硬件行为只会更糟不会更好（读出的 X 值在后端可实现为任意比特）。       -/
/-  因此本文件以 mod 语义演示的错乱是真实损坏的下界。                         -/
/-                                                                           -/
/- ======================== 可达性警告（必须阅读） ========================= -/
/-  本文件的 push 轨迹每级都喂 maskInit = 0xFFFFFFFF，这**违反**流水线的      -/
/-  mask 纪律：pipe.scala:366 使 vbranch 的 mask_init = 指令掩码 ∧            -/
/-  simt_stack.out_mask（⊆ thread_masks[wid] 当前活跃掩码），而               -/
/-  branch_join.scala:249-256 在 divOccur 时把 thread_masks 更新为所走路径    -/
/-  掩码；takeif 恒选**小**边（:145，takeif ⟺ ifCnt < elseCnt），故          -/
/-  |taken| ≤ |mask_init|/2。两条推论：                                       -/
/-  (a) 无 pop 的连续 push 链上活跃掩码每级至少减半：32→16→8→4→2，            -/
/-      最多 5 级（taken-path 嵌套，每级栈占 2 项）；                         -/
/-  (b) 逐线程剥离式深层嵌套只能发生在 pushed（大边）路径上，而 pushed 路径   -/
/-      要等 taken 路径到 join、**先弹出路径项**（:57-59）才开始执行——        -/
/-      每级净占 1 项而非 2 项。31 级剥离的最深时刻栈占用 = 30（外层 RPC 项） -/
/-      + 2（最深级两项）= 32 = depth_stack，**恰好不溢出**。                 -/
/-  报告 I-2 的原分析（"每级保留 2 项 ⇒ 最多 16 级；剥离可达 31 级需 62 项"） -/
/-  把两种互斥的嵌套成本叠加了：(a) 的成本配 (b) 的深度。正确结论：最坏栈需求  -/
/-  恰好是 num_thread = 32 项，栈是精确定尺寸的，合法执行下 wr_ptr ≤ 32 恒     -/
/-  成立、永不越界（形式化该不变量是后续波次的工作）。                         -/
/-  因此本文件见证的是**机制与无防护事实**：栈无满检测、无 stall、无异常，     -/
/-  一旦驱动序列违反 mask 纪律（如未来微架构改动破坏 pipe.scala:366 的 ∧），  -/
/-  溢出静默发生。建议 I-2 改判为"机制属实、当前不可达（栈恰好定尺寸）"，      -/
/-  防护建议（满检测/断言）作为健壮性加固保留。                               -/
/- ========================================================================= -/

import Ventus.SIMT.BranchJoin

namespace Ventus.SIMT

open Ventus.Base

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 理想（无界）栈语义：对照组                                              -/
/-    与 bjSysStep 相同的转移规则，唯一区别是栈为无界 List（head = 栈顶），   -/
/-    无深度限制、无别名。                                                    -/
/- ========================================================================= -/

structure BjoIdealState where
  stk   : List (BjEntry 32)
  tmask : BitVec 32

def bjoIdealInit : BjoIdealState := ⟨[], 0xFFFFFFFF⟩

def bjoIdealStep (s : BjoIdealState) (e : BjEvent 32) : BjoIdealState × BjOut 32 :=
  match e with
  | .nop => (s, bjOutDefault)
  | .branch bi =>
      let div := bjDivOccur bi
      let tk  := bjTakeif bi
      let pe  := bjPushentry bi
      let rpc : BjEntry 32 := ⟨pe.reconPC, pe.reconPC, s.tmask⟩
      let stk' := if div then pe :: rpc :: s.stk else s.stk
      let tm' := if div then (if tk then bjIfMask bi else bjElseMask bi) else s.tmask
      let fc  := (!tk) || bjElseOnly bi
      ({ stk := stk', tmask := tm' },
       { complete := tk, fetchValid := fc, fetchJump := fc,
         fetchPC := if fc then bi.PCbranch else 0,
         popJump := false, popPC := 0, popMask := 0 })
  | .join pc =>
      match s.stk with
      | [] =>
        (s, { complete := false, fetchValid := true, fetchJump := false, fetchPC := 0,
              popJump := false, popPC := 0, popMask := 0 })
      | top :: rest =>
        if top.reconPC == pc then
          ({ stk := rest, tmask := top.newMask },
           { complete := false, fetchValid := true, fetchJump := true, fetchPC := top.jumpPC,
             popJump := true, popPC := top.jumpPC, popMask := top.newMask })
        else
          (s, { complete := false, fetchValid := true, fetchJump := false, fetchPC := 0,
                popJump := false, popPC := 0, popMask := 0 })

def bjoIdealRun (s : BjoIdealState) (es : List (BjEvent 32)) : BjoIdealState :=
  es.foldl (fun st e => (bjoIdealStep st e).1) s

/- ========================================================================= -/
/- 2. 17 级嵌套分化的 push 轨迹（真实参数 depth=32, nT=32）                   -/
/-    每级：valuMask=1（if=1 线程，else=31 线程，divOccur=1，takeif=true）。  -/
/-    注意：maskInit 恒为全 1，自第 2 级起违反 mask 纪律（见文件头警告）——  -/
/-    这是机制演示，不是合法内核轨迹。                                        -/
/- ========================================================================= -/

def bjoReconPC  (k : Nat) : BitVec 32 := BitVec.ofNat 32 (0x1000 + 4 * k)
def bjoPCbranch (k : Nat) : BitVec 32 := BitVec.ofNat 32 (0x4000 + 4 * k)
def bjoPCexec   (k : Nat) : BitVec 32 := BitVec.ofNat 32 (0x0100 + 4 * k)

def bjoBranch (k : Nat) : BjBranchIn 32 :=
  { valuMask := 1, maskInit := 0xFFFFFFFF,
    PCbranch := bjoPCbranch k, PCexecute := bjoPCexec k, PCreconv := bjoReconPC k }

/-- 17 级 push（第 1..17 级 = k=0..16）。 -/
def bjoPushTrace : List (BjEvent 32) := (List.range 17).map (fun k => .branch (bjoBranch k))

/-- 32 次有效 join：依次弹第 17..2 级（k=16..1）的路径项与 RPC 项。
    弹出顺序与两个模型一致：path_16, rpc_16, path_15, rpc_15, …, path_1, rpc_1。 -/
def bjoPopTrace : List (BjEvent 32) :=
  (List.range 16).flatMap (fun i => [.join (bjoReconPC (16 - i)), .join (bjoReconPC (16 - i))])

/-- 初始状态（真实参数）：栈空，thread_mask = 全 1（RegInit ~0）。 -/
def bjoInit : BjSysState 32 32 := { stack := bjStackInit 32 32, tmask := 0xFFFFFFFF }

def bjoStateAfterPush : BjSysState 32 32 := bjRun bjoInit bjoPushTrace
def bjoStateAfterPop  : BjSysState 32 32 := bjRun bjoInit (bjoPushTrace ++ bjoPopTrace)

def bjoConcreteFinal := bjSysStep bjoStateAfterPop (.join (bjoReconPC 0))
def bjoIdealAfterPop  := bjoIdealRun bjoIdealInit (bjoPushTrace ++ bjoPopTrace)
def bjoIdealFinal     := bjoIdealStep bjoIdealAfterPop (.join (bjoReconPC 0))

/- ========================================================================= -/
/- 3. 证据定理                                                                -/
/- ========================================================================= -/

/-- 槽位演算（纯数值）：第 17 级（k=16）push 写指针 32、33，对 32 取模得槽 0、1。 -/
theorem bjoT0_slot_math : 2 * 16 % 32 = 0 ∧ (2 * 16 + 1) % 32 = 1 := by decide

/-- 指针未回绕：17 次 push 后 wr_ptr = 34（6 位可表示，无计数器溢出）。 -/
theorem bjoT1_wr_unwrapped : bjoStateAfterPush.stack.wr = 34 := by
  native_decide

/-- 模型中的 Mem 索引别名：指针 32、33 映射到槽 0、1。 -/
theorem bjoT2_slot_alias :
    (bjIdx (32 : BitVec (bjPtrWidth 32))).val = 0 ∧
    (bjIdx (33 : BitVec (bjPtrWidth 32))).val = 1 := by
  native_decide

/-- 覆盖前：第 1 级 push 后，槽 0 = 第 1 级 RPC 项、槽 1 = 第 1 级路径项。 -/
theorem bjoT3a_slots_before :
    (bjRun bjoInit [.branch (bjoBranch 0)]).stack.mem ⟨0, by decide⟩
      = ⟨bjoReconPC 0, bjoReconPC 0, 0xFFFFFFFF⟩ ∧
    (bjRun bjoInit [.branch (bjoBranch 0)]).stack.mem ⟨1, by decide⟩
      = ⟨bjoReconPC 0, bjoPCbranch 0, 0xFFFFFFFE⟩ := by
  native_decide

/-- 覆盖后：17 次 push 后，槽 0、1 已被第 17 级的 RPC 项与路径项覆盖
    （第 17 级 push 时 threadMask = 1：第 2 级起每级 tmask 已被更新为所走的
    单线程 if 掩码）。 -/
theorem bjoT3b_slots_after :
    bjoStateAfterPush.stack.mem ⟨0, by decide⟩ = ⟨bjoReconPC 16, bjoReconPC 16, 1⟩ ∧
    bjoStateAfterPush.stack.mem ⟨1, by decide⟩ = ⟨bjoReconPC 16, bjoPCbranch 16, 0xFFFFFFFE⟩ := by
  native_decide

/-- 中间状态对齐：32 次 join 后，具体模型 wr=2、rd=1（指向槽 1）；
    理想栈剩 2 项（第 1 级的路径项与 RPC 项）。 -/
theorem bjoT4_mid :
    bjoStateAfterPop.stack.wr = 2 ∧ bjoStateAfterPop.stack.rd = 1 ∧
    bjoIdealAfterPop.stk.length = 2 := by
  native_decide

/-- 核心见证：第 1 级的汇合 join（PC = reconPC 0）——
    具体模型：槽 1 已被第 17 级路径项覆盖，reconPC 不匹配 → **不弹栈、不跳转、
    汇合丢失**（fallthrough，掩码停留在 1 线程）；无满检测、无异常。
    理想栈：TOS = 第 1 级路径项 → 弹栈并跳 PC_branch 0、恢复 31 线程 else 掩码。 -/
theorem bjoT5_witness_lost_join :
    bjoConcreteFinal.2.popJump = false ∧ bjoConcreteFinal.2.fetchJump = false ∧
    bjoIdealFinal.2.popJump = true ∧ bjoIdealFinal.2.popPC = bjoPCbranch 0 ∧
    bjoIdealFinal.2.popMask = 0xFFFFFFFE := by
  native_decide

/-- 幽灵弹栈：同一状态下向第 17 级的 reconPC 发 join——
    具体模型：槽 1 里残留的第 17 级路径项**再次匹配** → 虚假弹栈、
    虚假跳回 PC_branch 16（已汇合过的路径被幽灵重入）；
    理想栈：TOS 是第 1 级路径项（reconPC 0 ≠ reconPC 16）→ 不弹栈。 -/
theorem bjoT6_witness_ghost_pop :
    (bjSysStep bjoStateAfterPop (.join (bjoReconPC 16))).2.popJump = true ∧
    (bjSysStep bjoStateAfterPop (.join (bjoReconPC 16))).2.popPC = bjoPCbranch 16 ∧
    (bjoIdealStep bjoIdealAfterPop (.join (bjoReconPC 16))).2.popJump = false := by
  native_decide

#print axioms bjoT5_witness_lost_join
#print axioms bjoT6_witness_ghost_pop

end Ventus.SIMT
