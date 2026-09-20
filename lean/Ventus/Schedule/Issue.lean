/- ========================================================================= -/
/-                     Schedule/Issue.lean                                    -/
/-  发射级路由（issue.scala）的 Lean 4 模型、测试与证明                         -/
/-                                                                           -/
/-  核心交付：RRArbiter 非 Irrevocable（RRArbiter.lean rra3_not_stable）的      -/
/-  剩余例化点核销：issue.scala:189-190（XVDualIssue 的 arb_x/arb_v）与         -/
/-  :224-232（IssueV2 的九个 RRArbiter）经全仓 grep 核实**均无例化**（死代码），-/
/-  唯一活的 Issue 类（pipe.scala:74-75 issueX/issueV）是纯组合路由；           -/
/-  ibuffer.scala:64-65 的 rrarbit_x/v（活）下游只按 fire 采样 ⇒ 免疫。         -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    pipeline/issue.scala（Issue :40-143 活；arbiter_o2m :146-166、            -/
/-      XVDualIssue :168-203、IssueV2 :205-316 均无例化，死代码）               -/
/-  例化点核实（全仓 grep Module(new ...)）：                                  -/
/-    Issue ← pipe.scala:74-75（issueX 走 x 通道、issueV 走 v 通道）；          -/
/-    XVDualIssue / IssueV2 / arbiter_o2m 无任何例化。                          -/
/-    活连线（pipe.scala:371-401）：issueV.out_vALU→valu、out_LSU→lsu、         -/
/-    out_SIMT→simt_stack.branch_ctl、out_SFU→sfu、out_MUL→mul、out_TC→tc、     -/
/-    out_vFPU→fpu；issueX.out_sALU→alu、out_CSR→csrfile、                      -/
/-    out_warpscheduler→warp_sche.warp_control；各自另一实例的同名单元          -/
/-    ready 全绑 false（:375-401）——通道侧别分类必须一致，否则死锁（见 Q5）。 -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. Issue:54 的 Queue.apply(io.in, 0) 与 IssueV2:234 的 Queue.apply(_, 0) -/
/-      均为零深度队列 = 纯组合直连（chisel v6.4.0 Decoupled.scala Queue.apply -/
/-      的 entries==0 分支），模型中不出现。Issue 因此是纯组合模块。            -/
/-  D2. 只建模 valid/ready/路由选择子；bits 全是 inputBuf.bits 的直通           -/
/-      （issue.scala:57-85），valid 门控保证未选中通道的 bits 不被消费。       -/
/-      CtrlSigs 只取路由相关 10 字段（tc/sfu/fp/csr.orR/mul/mem/isvec/barrier/ -/
/-      simt_stack/simt_stack_op；csr 为 UInt(2.W) 取其 orR，simt_stack_op 是   -/
/-      Bool，:120/:293 的 `=== 0.U` 即 = false）。                            -/
/-  D3. Issue 的路由链（:98-139）优先级序：tc > sfu > fp > csr > mul > mem >   -/
/-      isvec > barrier > sALU（否则分支）。isvec 分支内按 simt_stack/op 细分： -/
/-      ss=1,op=0 → vALU+SIMT 双发（beqv，:119-124）；ss=1,op≠0 → 仅 SIMT；    -/
/-      ss=0 → 仅 vALU。                                                       -/
/-  D4. 死代码（arbiter_o2m/XVDualIssue/IssueV2）仍建模并给出关键契约定理，     -/
/-      定理前缀 issO2m/iss（XVDualIssue 共享 iss 前缀的分裂定理）/issV2，      -/
/-      目的：若被复活，其协议缺陷（Q4/Q6）有据可查。                          -/
/-  D5. IssueV2 的路由链（:245-272）与 Issue 同优先级序，但 isvec 类全进        -/
/-      arb_vALU（vALU/SIMT 合并仲裁，en 编码 :292-300 区分；:311-315 拆出）。  -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1. IssueV2 vALU/SIMT 合并仲裁的就绪耦合（:315）：arb_vALU.io.out.ready =  -/
/-      out_vALU.ready && out_SIMT.ready——即使 en=01（仅 vALU），出队也要求    -/
/-      SIMT 就绪。SIMT 单元（simt_stack branch_ctl）若在空闲时拉低 ready，    -/
/-      vALU-only 事务被无谓阻塞（性能）甚至死锁（若 ready 依赖自身 valid）。  -/
/-      死代码，记录在案。（活代码 Issue 的 beqv 双发也有同类耦合，但那是      -/
/-      协议要求的同时消费，见定理 iss_dual_valid_coupled。）                  -/
/-  Q2. arbiter_o2m（:146-166）的 out(j).valid 由 out(j).ready 反推，不看      -/
/-      in.valid（:155-159）——in.valid=0 且下游 ready 时 out(j).fire=1，下游   -/
/-      将消费假数据（valid/ready 反接）；:152 的 `stall := in.ready` 命名也     -/
/-      反常（stall=可接收）。死代码，记录在案防复活。                         -/
/-  Q3. Issue 路由链与 ibuffer2issue 的 inst_is_vec（ibuffer.scala:66-80）在    -/
/-      两种控制组合下分类不一致（定理 iss_classify_agree 给出精确判据）：      -/
/-      D1 = csr∧(mul∨mem)（无 tc/sfu/fp）时 Issue 路由到 CSR（x 侧）而        -/
/-      inst_is_vec 判为 v 侧；D2 = isvec∧barrier（其余全 0）时 Issue 路由到   -/
/-      vALU/SIMT（v 侧）而 inst_is_vec 判为 x 侧。后果：D2 类指令会被送       -/
/-      issueX，而 issueX 的 out_vALU/out_SIMT ready 绑死 false                 -/
/-      （pipe.scala:375,383）→ 永久停顿（死锁）。现有译码表不可译出这两种     -/
/-      组合（barrier 三行 BARRIER/BARRIERSUB/ENDPRG 的 isvec 全为 N，          -/
/-      DecodeUnit.scala:481-483；csr 行不带 mul/mem），故当前不可达；          -/
/-      属译码表演化时的地雷，建议在译码侧加断言。                              -/
/-  Q4.（写回侧记录见 Writeback.lean Q1-Q3。）                                  -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Ventus.Base.Handshake
import Ventus.Schedule.RRArbiter
import Std.Tactic.BVDecide

namespace Ventus.Schedule

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 路由控制字段子集与端口枚举                                                -/
/- ========================================================================= -/

/-- CtrlSigs 的路由相关字段子集（D2；csr 已取 orR，simt_stack_op 为 Bool） -/
structure IssCtrl where
  tc : Bool
  sfu : Bool
  fp : Bool
  csrOrR : Bool
  mul : Bool
  mem : Bool
  isvec : Bool
  barrier : Bool
  simt_stack : Bool
  simt_stack_op : Bool
deriving DecidableEq

/-- Issue 的十个输出端口（issue.scala:43-52） -/
inductive IssPort where
  | TC | SFU | vFPU | CSR | MUL | LSU | SIMT | vALU | ws | sALU
deriving DecidableEq

/- ========================================================================= -/
/- 2. Issue 路由模型（issue.scala:98-139，活代码）                              -/
/- ========================================================================= -/

/-- 路由目标端口集（1 个；beqv 双发时为 [vALU, SIMT]）。
    严格按 :98-139 的 if-elsewhen 链优先级（D3）。 -/
def issRoute (c : IssCtrl) : List IssPort :=
  if c.tc then [.TC]                              -- :98-100
  else if c.sfu then [.SFU]                       -- :101-103
  else if c.fp then [.vFPU]                       -- :104-106
  else if c.csrOrR then [.CSR]                    -- :107-109
  else if c.mul then [.MUL]                       -- :110-113
  else if c.mem then [.LSU]                       -- :114-117
  else if c.isvec then                            -- :118
    if c.simt_stack then                          -- :119
      if !c.simt_stack_op then [.vALU, .SIMT]     -- :120-124（op===0：beqv 双发）
      else [.SIMT]                                -- :125-128（SIMT only）
    else [.vALU]                                  -- :129-132（vALU only）
  else if c.barrier then [.ws]                    -- :133-135
  else [.sALU]                                    -- :136-139

/-- beqv 双发端口判定 -/
def issIsDualPort : IssPort → Bool
  | .vALU | .SIMT => true
  | _ => false

/-- 输出 valid（:87-96 默认 false；选中分支 := inputBuf.valid；
    双发时 :122-123 两路 valid 都被对方 ready 门控） -/
def issOutValid (c : IssCtrl) (v : Bool) (r : IssPort → Bool) (p : IssPort) : Bool :=
  if issRoute c = [.vALU, .SIMT]
  then v && r .vALU && r .SIMT && issIsDualPort p
  else v && (issRoute c).any (fun t => decide (p = t))

/-- inputBuf.ready（:97 默认 false；选中分支 := 目标 ready；
    双发 :124 := beqv_ready = SIMT.ready && vALU.ready） -/
def issInReady (c : IssCtrl) (r : IssPort → Bool) : Bool :=
  match issRoute c with
  | [.vALU, .SIMT] => r .vALU && r .SIMT
  | [t] => r t
  | _ => false

/-- 输入 fire = valid && ready -/
def issInFire (c : IssCtrl) (v : Bool) (r : IssPort → Bool) : Bool :=
  v && issInReady c r

/-- 路由形状：要么双发，要么单目标 -/
theorem issRoute_shape (c : IssCtrl) :
    issRoute c = [.vALU, .SIMT] ∨ ∃ t, issRoute c = [t] := by
  unfold issRoute
  repeat' split
  all_goals first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩

/-- 逐分支路由规约：tc 优先 -/
theorem iss_route_tc (c : IssCtrl) (h : c.tc = true) : issRoute c = [.TC] := by
  simp [issRoute, h]

theorem iss_route_sfu (c : IssCtrl) (h1 : c.tc = false) (h2 : c.sfu = true) :
    issRoute c = [.SFU] := by simp [issRoute, h1, h2]

theorem iss_route_fp (c : IssCtrl) (h1 : c.tc = false) (h2 : c.sfu = false)
    (h3 : c.fp = true) : issRoute c = [.vFPU] := by simp [issRoute, h1, h2, h3]

theorem iss_route_csr (c : IssCtrl) (h1 : c.tc = false) (h2 : c.sfu = false)
    (h3 : c.fp = false) (h4 : c.csrOrR = true) : issRoute c = [.CSR] := by
  simp [issRoute, h1, h2, h3, h4]

theorem iss_route_mul (c : IssCtrl) (h1 : c.tc = false) (h2 : c.sfu = false)
    (h3 : c.fp = false) (h4 : c.csrOrR = false) (h5 : c.mul = true) :
    issRoute c = [.MUL] := by simp [issRoute, h1, h2, h3, h4, h5]

theorem iss_route_mem (c : IssCtrl) (h1 : c.tc = false) (h2 : c.sfu = false)
    (h3 : c.fp = false) (h4 : c.csrOrR = false) (h5 : c.mul = false)
    (h6 : c.mem = true) : issRoute c = [.LSU] := by
  simp [issRoute, h1, h2, h3, h4, h5, h6]

theorem iss_route_dual (c : IssCtrl) (h1 : c.tc = false) (h2 : c.sfu = false)
    (h3 : c.fp = false) (h4 : c.csrOrR = false) (h5 : c.mul = false)
    (h6 : c.mem = false) (h7 : c.isvec = true) (h8 : c.simt_stack = true)
    (h9 : c.simt_stack_op = false) : issRoute c = [.vALU, .SIMT] := by
  simp [issRoute, h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem iss_route_simt (c : IssCtrl) (h1 : c.tc = false) (h2 : c.sfu = false)
    (h3 : c.fp = false) (h4 : c.csrOrR = false) (h5 : c.mul = false)
    (h6 : c.mem = false) (h7 : c.isvec = true) (h8 : c.simt_stack = true)
    (h9 : c.simt_stack_op = true) : issRoute c = [.SIMT] := by
  simp [issRoute, h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem iss_route_valu (c : IssCtrl) (h1 : c.tc = false) (h2 : c.sfu = false)
    (h3 : c.fp = false) (h4 : c.csrOrR = false) (h5 : c.mul = false)
    (h6 : c.mem = false) (h7 : c.isvec = true) (h8 : c.simt_stack = false) :
    issRoute c = [.vALU] := by simp [issRoute, h1, h2, h3, h4, h5, h6, h7, h8]

theorem iss_route_ws (c : IssCtrl) (h1 : c.tc = false) (h2 : c.sfu = false)
    (h3 : c.fp = false) (h4 : c.csrOrR = false) (h5 : c.mul = false)
    (h6 : c.mem = false) (h7 : c.isvec = false) (h8 : c.barrier = true) :
    issRoute c = [.ws] := by simp [issRoute, h1, h2, h3, h4, h5, h6, h7, h8]

theorem iss_route_salu (c : IssCtrl) (h1 : c.tc = false) (h2 : c.sfu = false)
    (h3 : c.fp = false) (h4 : c.csrOrR = false) (h5 : c.mul = false)
    (h6 : c.mem = false) (h7 : c.isvec = false) (h8 : c.barrier = false) :
    issRoute c = [.sALU] := by simp [issRoute, h1, h2, h3, h4, h5, h6, h7, h8]

/-- beqv 双发端口判定的等价形式 -/
theorem issIsDualPort_eq_true {p : IssPort} (h : issIsDualPort p = true) :
    p = .vALU ∨ p = .SIMT := by
  revert h
  cases p <;> simp [issIsDualPort]

/-- ISS1 valid 路由正确性：任何 valid 的端口都在路由结果中 -/
theorem iss_valid_routed (c : IssCtrl) (v : Bool) (r : IssPort → Bool) (p : IssPort)
    (hp : issOutValid c v r p = true) :
    (issRoute c = [.vALU, .SIMT] ∧ (p = .vALU ∨ p = .SIMT)) ∨
      (∃ t, issRoute c = [t] ∧ p = t) := by
  by_cases hd : issRoute c = [.vALU, .SIMT]
  · left
    refine ⟨hd, ?_⟩
    unfold issOutValid at hp
    rw [if_pos hd] at hp
    rw [Bool.and_eq_true] at hp
    obtain ⟨hp, hpd⟩ := hp
    exact issIsDualPort_eq_true hpd
  · right
    rcases issRoute_shape c with hd2 | ⟨t, ht⟩
    · exact absurd hd2 hd
    · refine ⟨t, ht, ?_⟩
      unfold issOutValid at hp
      rw [if_neg hd, ht] at hp
      simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true,
        decide_eq_true_eq] at hp
      exact hp.2

/-- ISS2 互斥：两个不同端口同时 valid ⟹ 必为 beqv 双发，且恰是 {vALU, SIMT} -/
theorem iss_mutex (c : IssCtrl) (v : Bool) (r : IssPort → Bool) (p q : IssPort)
    (hp : issOutValid c v r p = true) (hq : issOutValid c v r q = true)
    (hpq : p ≠ q) :
    issRoute c = [.vALU, .SIMT] ∧
      ((p = .vALU ∧ q = .SIMT) ∨ (p = .SIMT ∧ q = .vALU)) := by
  rcases iss_valid_routed c v r p hp with ⟨hd, hp'⟩ | ⟨t, ht, hpt⟩
  · rcases iss_valid_routed c v r q hq with ⟨-, hq'⟩ | ⟨t', ht', hqt'⟩
    · refine ⟨hd, ?_⟩
      rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
      · exact absurd rfl hpq
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hpq
    · rw [ht'] at hd
      simp at hd
  · rcases iss_valid_routed c v r q hq with ⟨hd, -⟩ | ⟨t', ht', hqt'⟩
    · rw [ht] at hd
      simp at hd
    · subst hpt
      subst hqt'
      rw [ht] at ht'
      simp at ht'
      exact absurd ht' hpq

/-- ISS3 双发耦合（Q1 的活代码对应物，:122-123）：beqv 双发时两路 valid
    都被双方 ready 门控——SIMT 不就绪则 vALU.valid 也为 0（即使 vALU.ready=1） -/
theorem iss_dual_valid_coupled (c : IssCtrl) (v : Bool) (r : IssPort → Bool)
    (hd : issRoute c = [.vALU, .SIMT]) :
    issOutValid c v r .vALU = (v && r .vALU && r .SIMT) ∧
      issOutValid c v r .SIMT = (v && r .vALU && r .SIMT) := by
  unfold issOutValid
  simp only [if_pos hd]
  simp [issIsDualPort]

/-- ISS4 in.ready 规约：单目标 = 目标 ready；双发 = 双方 ready -/
theorem iss_inReady_single (c : IssCtrl) (r : IssPort → Bool) (t : IssPort)
    (ht : issRoute c = [t]) : issInReady c r = r t := by
  simp [issInReady, ht]

theorem iss_inReady_dual (c : IssCtrl) (r : IssPort → Bool)
    (hd : issRoute c = [.vALU, .SIMT]) :
    issInReady c r = (r .vALU && r .SIMT) := by
  simp [issInReady, hd]

/- ========================================================================= -/
/- 3. Issue 路由数值回归测试（全部 `by decide`）                                -/
/- ========================================================================= -/

section IssRouteTests

/-- 全 false 控制字 -/
def issCtrl0 : IssCtrl :=
  { tc := false, sfu := false, fp := false, csrOrR := false, mul := false,
    mem := false, isvec := false, barrier := false,
    simt_stack := false, simt_stack_op := false }

def issRdyAll : IssPort → Bool := fun _ => true
def issRdyNone : IssPort → Bool := fun _ => false

-- R1 默认路由 sALU；valid/ready 传递
example : issRoute issCtrl0 = [.sALU] := by decide
example : issOutValid issCtrl0 true issRdyAll .sALU = true := by decide
example : issOutValid issCtrl0 true issRdyAll .vALU = false := by decide
example : issInReady issCtrl0 issRdyAll = true := by decide
example : issInReady issCtrl0 issRdyNone = false := by decide
example : issInFire issCtrl0 true issRdyAll = true := by decide

-- R2 优先级：tc 压过 mem/fp
example : issRoute { issCtrl0 with tc := true, mem := true, fp := true } = [.TC] := by decide
-- R3 csr 在 mul/mem 之前
example : issRoute { issCtrl0 with csrOrR := true, mem := true } = [.CSR] := by decide
-- R4 mem 在 isvec 之前
example : issRoute { issCtrl0 with mem := true, isvec := true } = [.LSU] := by decide
-- R5 isvec 三分支
example : issRoute { issCtrl0 with isvec := true } = [.vALU] := by decide
example : issRoute { issCtrl0 with isvec := true, simt_stack := true, simt_stack_op := true }
    = [.SIMT] := by decide
example : issRoute { issCtrl0 with isvec := true, simt_stack := true }
    = [.vALU, .SIMT] := by decide
-- R6 barrier
example : issRoute { issCtrl0 with barrier := true } = [.ws] := by decide

-- R7 双发的 valid 耦合（Q1 活代码版）：SIMT 不就绪则两路 valid 全 0
def issCtrlBeqv : IssCtrl := { issCtrl0 with isvec := true, simt_stack := true }
def issRdyNoSimt : IssPort → Bool := fun p => !(p == IssPort.SIMT)
example : issOutValid issCtrlBeqv true issRdyNoSimt .vALU = false := by decide
example : issOutValid issCtrlBeqv true issRdyNoSimt .SIMT = false := by decide
example : issInReady issCtrlBeqv issRdyNoSimt = false := by decide
example : issOutValid issCtrlBeqv true issRdyAll .vALU = true := by decide
example : issOutValid issCtrlBeqv true issRdyAll .SIMT = true := by decide

-- R8 单目标反压不串台：sALU 不就绪只影响 sALU
def issRdyNoSAlu : IssPort → Bool := fun p => !(p == IssPort.sALU)
example : issInReady issCtrl0 issRdyNoSAlu = false := by decide
example : issInReady { issCtrl0 with fp := true } issRdyNoSAlu = true := by decide

end IssRouteTests

/- ========================================================================= -/
/- 4. 分类一致性：Issue 路由侧别 vs inst_is_vec（ibuffer.scala:66-80，活代码）  -/
/- ========================================================================= -/

/-- Issue 路由的通道侧别：v 侧 = 向量执行单元（TC/SFU/vFPU/MUL/LSU/vALU/SIMT），
    x 侧 = CSR/warpscheduler/sALU。与 issRoute 同优先级序的布尔化。 -/
def issRouteSide (c : IssCtrl) : Bool :=
  if c.tc then true
  else if c.sfu then true
  else if c.fp then true
  else if c.csrOrR then false
  else if c.mul then true
  else if c.mem then true
  else if c.isvec then true
  else if c.barrier then false
  else false

/-- inst_is_vec（ibuffer.scala:66-80 / issue.scala:174-188，两处同构）：
    (tc||fp||mul||sfu||mem) → v；(csr.orR||barrier) → x；isvec → v；否则 x -/
def issIsVec (c : IssCtrl) : Bool :=
  if c.tc || c.fp || c.mul || c.sfu || c.mem then true
  else if c.csrOrR || c.barrier then false
  else c.isvec

/-- ISS5 分类一致性判据（Q3）：两种分类一致 ⟺ 两个分歧判别式均不成立。
    D1 = csr∧(mul∨mem) 且无 tc/sfu/fp（Issue 判 x 侧、inst_is_vec 判 v 侧）；
    D2 = isvec∧barrier 且其余全 0（Issue 判 v 侧、inst_is_vec 判 x 侧）。
    现有译码表不可译出这两种组合（见文件头 Q3），故当前一致。 -/
theorem iss_classify_agree (c : IssCtrl) :
    issIsVec c = issRouteSide c ↔
      ¬((c.csrOrR && !c.tc && !c.sfu && !c.fp && (c.mul || c.mem)) ||
        (!c.tc && !c.sfu && !c.fp && !c.csrOrR && !c.mul && !c.mem &&
          c.isvec && c.barrier)) := by
  obtain ⟨tc, sfu, fp, csr, mul, mem, isvec, barrier, ss, sop⟩ := c
  cases tc <;> cases sfu <;> cases fp <;> cases csr <;> cases mul <;> cases mem <;>
    cases isvec <;> cases barrier <;> simp [issIsVec, issRouteSide]

-- 分歧判别式的数值佐证（Q3 的两个地雷形态）
example : issRoute { issCtrl0 with csrOrR := true, mem := true } = [.CSR] := by decide
example : issIsVec { issCtrl0 with csrOrR := true, mem := true } = true := by decide
example : issRoute { issCtrl0 with isvec := true, barrier := true } = [.vALU] := by decide
example : issIsVec { issCtrl0 with isvec := true, barrier := true } = false := by decide

/- ========================================================================= -/
/- 5. XVDualIssue（issue.scala:168-203，死代码）的按类分裂                      -/
/- ========================================================================= -/

/-- 分裂无丢不重（issue.scala:192-200，与 ibuffer.scala:81-87 同构）：
    输入 i 的 fire ⟺ 按 inst_is_vec 恰好进入一个仲裁器并 fire -/
theorem iss_split_fire_iff (isvec inValid arbXready arbVready : Bool) :
    (inValid && (if isvec then arbVready else arbXready)) =
      ((inValid && !isvec && arbXready) || (inValid && isvec && arbVready)) := by
  cases isvec <;> cases inValid <;> simp

/-- 分裂侧别一致：inst_is_vec 的 x/v 判定与 Issue 的端口侧别在现有译码
    可达控制字上一致（ISS5 的推论形态，逐 Bool 穷举） -/
theorem iss_split_side (c : IssCtrl) :
    issIsVec c = issRouteSide c ∨
      (c.csrOrR && !c.tc && !c.sfu && !c.fp && (c.mul || c.mem)) = true ∨
      (!c.tc && !c.sfu && !c.fp && !c.csrOrR && !c.mul && !c.mem &&
        c.isvec && c.barrier) = true := by
  obtain ⟨tc, sfu, fp, csr, mul, mem, isvec, barrier, ss, sop⟩ := c
  cases tc <;> cases sfu <;> cases fp <;> cases csr <;> cases mul <;> cases mem <;>
    cases isvec <;> cases barrier <;> simp [issIsVec, issRouteSide]

/- ========================================================================= -/
/- 6. IssueV2（issue.scala:205-316，死代码）                                    -/
/- ========================================================================= -/

/-- IssueV2 的路由目标仲裁器（:245-272，与 Issue 同优先级序；
    isvec 类全进 arb_vALU，由 en 区分 vALU/SIMT） -/
def issV2Route (c : IssCtrl) : IssPort :=
  if c.tc then .TC                                -- :245-247
  else if c.sfu then .SFU                         -- :248-250
  else if c.fp then .vFPU                         -- :251-253
  else if c.csrOrR then .CSR                      -- :254-256
  else if c.mul then .MUL                         -- :257-259
  else if c.mem then .LSU                         -- :260-262
  else if c.isvec then .vALU                      -- :263-265（合并仲裁）
  else if c.barrier then .ws                      -- :266-268
  else .sALU                                      -- :269-272

/-- vALU/SIMT 使能编码（:292-300）：en(0)=vALU 使能，en(1)=SIMT 使能；
    ss=1,op=0 → "b11"；ss=1,op≠0 → "b10"；ss=0 → "b01" -/
def issV2En (c : IssCtrl) : BitVec 2 :=
  if c.simt_stack then (if c.simt_stack_op then 2#2 else 3#2) else 1#2

/-- IssueV2 输出 valid（:311,:313） -/
def issV2OutVAluValid (arbValid : Bool) (en : BitVec 2) : Bool := arbValid && en.getLsbD 0
def issV2OutSIMTValid (arbValid : Bool) (en : BitVec 2) : Bool := arbValid && en.getLsbD 1

/-- IssueV2 合并仲裁出队就绪（:315）：不看 en——Q1 耦合停顿的根源 -/
def issV2ArbReady (vAluReady simtReady : Bool) : Bool := vAluReady && simtReady

/-- ISS6 en 编码正确性：bit0 = vALU 使能（非 SIMT-only），bit1 = SIMT 使能 -/
theorem issV2_en_bit0 (c : IssCtrl) :
    (issV2En c).getLsbD 0 = !(c.simt_stack && c.simt_stack_op) := by
  cases hs : c.simt_stack <;> cases ho : c.simt_stack_op <;> simp [issV2En, hs, ho]

theorem issV2_en_bit1 (c : IssCtrl) :
    (issV2En c).getLsbD 1 = c.simt_stack := by
  cases hs : c.simt_stack <;> cases ho : c.simt_stack_op <;> simp [issV2En, hs, ho]

/-- ISS7 Issue 与 IssueV2 的路由一致性：非双发时 IssueV2 的目标仲裁器 =
    Issue 的目标端口（SIMT-only 除外——它进合并仲裁器 vALU，由 en=10 区分） -/
theorem issV2_route_agree (c : IssCtrl) :
    issRoute c = [issV2Route c] ∨
      (issRoute c = [.vALU, .SIMT] ∧ issV2Route c = .vALU) ∨
      (issRoute c = [.SIMT] ∧ issV2Route c = .vALU) := by
  obtain ⟨tc, sfu, fp, csr, mul, mem, isvec, barrier, ss, sop⟩ := c
  cases tc <;> cases sfu <;> cases fp <;> cases csr <;> cases mul <;> cases mem <;>
    cases isvec <;> cases barrier <;> cases ss <;> cases sop <;> decide

/-- ISS8 耦合停顿 quirk（Q1，:315）：en=01（仅 vALU）时出队仍要求 SIMT.ready -/
theorem issV2_valu_only_needs_simt_ready (simtReady : Bool) :
    issV2ArbReady true simtReady = simtReady := rfl

/-- ISS8' 对比：若按 en 门控（本应有的写法），en=01 时只需 vALU.ready -/
theorem issV2_valu_only_would_suffice (simtReady : Bool) :
    (true && (!(1#2 : BitVec 2).getLsbD 1 || simtReady)) = true := rfl

-- IssueV2 数值回归测试
example : issV2Route issCtrl0 = .sALU := by decide
example : issV2Route issCtrlBeqv = .vALU := by decide
example : issV2En issCtrlBeqv = 3#2 := by decide
example : issV2En { issCtrl0 with isvec := true, simt_stack := true, simt_stack_op := true }
    = 2#2 := by decide
example : issV2En { issCtrl0 with isvec := true } = 1#2 := by decide
example : issV2OutSIMTValid true (issV2En { issCtrl0 with isvec := true }) = false := by decide

/- ========================================================================= -/
/- 7. arbiter_o2m（issue.scala:146-166，死代码）                                -/
/- ========================================================================= -/

/-- out(j).valid：:153 默认全 false，:155-159 升序 when 循环 last-connect-wins
    ⇒ out(j).valid = out(j).ready && (j 之后无 ready)。**不看 in.valid**（Q2）。 -/
def issO2mValid {n : Nat} (rdy : Nat → Bool) (j : Fin n) : Bool :=
  rdy j.val && (rraFindNat rdy (j.val + 1) (n - (j.val + 1))).isNone

/-- in.ready = 任一 out ready（:161-164）；:152 的 stall := in.ready -/
def issO2mInReady {n : Nat} (rdy : Nat → Bool) : Bool :=
  (rraFindNat rdy 0 n).isSome

/-- ISS9 o2m 互斥：至多一个 out 有效 -/
theorem issO2m_mutex {n : Nat} (rdy : Nat → Bool) (i j : Fin n)
    (hi : issO2mValid rdy i = true) (hj : issO2mValid rdy j = true) :
    i = j := by
  unfold issO2mValid at hi hj
  rw [Bool.and_eq_true] at hi hj
  obtain ⟨hri, hni⟩ := hi
  obtain ⟨hrj, hnj⟩ := hj
  by_cases h : i.val = j.val
  · exact Fin.ext h
  · rcases Nat.lt_or_gt_of_ne h with hij | hji
    · exfalso
      cases hf : rraFindNat rdy (i.val + 1) (n - (i.val + 1)) with
      | some k => rw [hf] at hni; contradiction
      | none =>
        have hf' := rraFindNat_none_spec hf j.val (by omega) (by omega)
        rw [hf'] at hrj
        contradiction
    · exfalso
      cases hf : rraFindNat rdy (j.val + 1) (n - (j.val + 1)) with
      | some k => rw [hf] at hnj; contradiction
      | none =>
        have hf' := rraFindNat_none_spec hf i.val (by omega) (by omega)
        rw [hf'] at hri
        contradiction

/-- ISS10 o2m valid 反接 quirk（Q2）：in.valid=false 时，只要有 ready 的端口，
    最高号 ready 端口的 out.fire = 1——下游消费假数据 -/
theorem issO2m_fire_without_valid {n : Nat} (rdy : Nat → Bool) (j : Fin n)
    (hr : rdy j.val = true)
    (hnone : ∀ k, j.val < k → k < n → rdy k = false) :
    issO2mValid rdy j && rdy j.val = true := by
  have hf : rraFindNat rdy (j.val + 1) (n - (j.val + 1)) = none :=
    rraFindNat_none_of_spec (fun k h1 h2 => hnone k (by omega) (by omega))
  have hv : issO2mValid rdy j = true := by
    unfold issO2mValid
    rw [Bool.and_eq_true]
    exact ⟨hr, by simp [hf]⟩
  simp [hv, hr]

-- o2m 数值回归测试
example : issO2mValid (n := 3) (fun k => k == 1 || k == 2) (⟨2, by decide⟩ : Fin 3) = true := by decide
example : issO2mValid (n := 3) (fun k => k == 1 || k == 2) (⟨1, by decide⟩ : Fin 3) = false := by decide
example : issO2mValid (n := 3) (fun _ => false) (⟨0, by decide⟩ : Fin 3) = false := by decide
example : issO2mInReady (n := 3) (fun k => k == 2) = true := by decide
example : issO2mInReady (n := 3) (fun _ => false) = false := by decide

/- ========================================================================= -/
/- 8. RRArbiter 例化点核销                                                     -/
/-                                                                           -/
/-  (a) issue.scala:189-190（XVDualIssue arb_x/arb_v）、:224-232（IssueV2 九个） -/
/-      ——全仓无例化（死代码），rra3_not_stable 的非 Irrevocable 性不可达。     -/
/-      若复活：下游必须只按 fire 采样 bits（Q1/Q2 另有协议缺陷需先修）。       -/
/-  (b) ibuffer.scala:64-65（rrarbit_x/v，活代码，n=num_warp=8）：              -/
/-      下游 = operand_collector 的 controlX/V（pipe.scala:288-289），          -/
/-      经 instDemux 纯组合分配到 collectorUnit；collectorUnit 仅在             -/
/-      control.fire 时锁存控制字（operandCollector.scala:144,184-185），       -/
/-      scoreb 的 if_ctrl/if_fire 也用 fire 门控（pipe.scala:238,242-243）。    -/
/-      反压期间 chosen/bits 可变（rra3_not_stable 的机制：新 warp 解除阻塞     -/
/-      后 valid 上升可抢占），但没有任何消费者按 Irrevocable 假设锁存，        -/
/-      故无害。ISS11 钉死关键的 fire 完整性。                                 -/
/- ========================================================================= -/

/-- ISS11 fire 完整性（ibuffer2issue，活代码）：out.fire 时被消费的恰是
    chosen 输入且该输入同拍 fire（grant 与 chosen 对齐，rra1_choice_granted）。
    即非 Irrevocable 只影响"反压期间的 bits 变化"，不影响 fire 拍的数据正确性 -/
theorem iss_ib2iss_fire_integrity {n : Nat} (hn : 0 < n) (v : BitVec n) (lg : Fin n)
    (r : Bool) (hv : rraOutValid hn v lg = true) :
    v.getLsbD (rraChoice hn v lg).val && rraInReady hn v lg r (rraChoice hn v lg) = r := by
  have hv' : v.getLsbD (rraChoice hn v lg).val = true := hv
  have hg := rra1_choice_granted hn v lg hv'
  simp [rraInReady, hv', hg]

/-- ISS12 fire 时的数据归属：out.bits = 被 fire 输入的 bits（组合直通 :56） -/
theorem iss_ib2iss_bits_of_fire {n : Nat} (hn : 0 < n) {α : Type}
    (bits : Fin n → α) (v : BitVec n) (lg : Fin n) :
    rraOutBits hn bits v lg = bits (rraChoice hn v lg) := rfl

-- ibuffer2issue 规模的数值佐证（n=8=num_warp）：反压期间新请求改变 chosen
example : rraChoice (by decide : 0 < 8) 0b00000001#8 ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
example : rraChoice (by decide : 0 < 8) 0b00000101#8 ⟨0, by decide⟩ = ⟨2, by decide⟩ := by decide

/- ========================================================================= -/
/- 9. 公理审计                                                                -/
/- ========================================================================= -/

#print axioms issRoute_shape
#print axioms iss_valid_routed
#print axioms iss_mutex
#print axioms iss_dual_valid_coupled
#print axioms iss_classify_agree
#print axioms iss_split_fire_iff
#print axioms issV2_route_agree
#print axioms issO2m_mutex
#print axioms issO2m_fire_without_valid
#print axioms iss_ib2iss_fire_integrity

end Ventus.Schedule
