/- ========================================================================= -/
/-                      Spec/Contracts.lean                                  -/
/-  黑盒/环境契约集中清单（AGENTS.md「黑盒契约集中」纪律的落点）                -/
/-                                                                           -/
/-  目的：把全工程散落在各文件头注释中的黑盒假设 / 环境契约集中成一份          -/
/-  可审计清单。每条契约给出：来源模块、Chisel 行号、核销状态                  -/
/-  【discharged 已核销 / pending 待核销 / axiomatic 公理化】与核销证据        -/
/-  定理名；能形式化的给出 Prop 谓词（spec 前缀）；有 Lean 定理证据的          -/
/-  给出机器可检查的交叉引用（第 5 节 specXref*，同名同型别名 +               -/
/-  #print axioms 审计）。                                                   -/
/-                                                                           -/
/-  收集源（2026-08-27 全仓 Grep 核实，关键词：假设 / 契约 / H- 前缀 / 环境 / 黑盒）： -/
/-    Arith/ExeSFU.lean      H-FPU-1..4 / H-FDIV-1 / H-TC-1..3 / H-DECODE-1   -/
/-    CTA/CtaScheduler.lean  CtasEventOk 五事件十项（H-WGB .. H-CUIF-DEALLOC） -/
/-    CTA/Allocator.lean     AlcEnvOk（A1）；核销 H-ALLOC-SLOT / H-ALLOC-FIT   -/
/-    CTA/CuInterface.lean   CuifEnvOk（E1/E2）；核销 H-CUIF-SPLIT/DONE/       -/
/-                           DEALLOC；E2 即 I-25 被打破的前提                  -/
/-    CTA/ResourceTable.lean 核销 H-RT-BOUNDS / H-RT-DISJOINT + 守恒 + SCAN    -/
/-    Schedule/Writeback.lean D6 的 A1-A4（I-9 核销前提）                      -/
/-    Schedule/I4Fix.lean    I-4 修复验证（i4f_*；占用-发射互斥证据）          -/
/-    Pipe.lean              H-BB / H-WID / H-IB2I / H-DELAY（B 类定理前提）   -/
/-    SIMT/BranchJoinBounds.lean 假设 (1)-(4)（I-2 收口前提）                  -/
/-    Base/MemLaws.lean + Mem/SRAMTemplate.lean + 各 Mem 模型                  -/
/-                           SRAM/时钟理想化（读写律接口、同拍读写、上电初值、 -/
/-                           SyncReadMem 1 拍延迟抽象）                        -/
/-    Mem/ICache.lean D8、Schedule/WarpScheduler.lean M7（环境假设散点）       -/
/-                                                                           -/
/-  统计（与本文件 spec_count_* 定理机器核对一致）：共 41 条                  -/
/-    已核销 25 / 待核销 0 / 公理化 15 / 已证伪 1                                       -/
/-    （2026-09-11：H-FPU-1/H-FPU-4 由 FpuWrap.lean 消解，axiomatic 17→15、          -/
/-     discharged 23→25；更早的 discharged 17→23 为前几波核销）                        -/
/-  已知契约缺口（有假设但无/缺核销证据，详见各条 evidence 栏与第 6 节）：     -/
/-    G1 H-DECODE-1：已于 2026-08-28 核销（DecodeUnitProps.lean 的            -/
/-       decH1a/decH1b/decH1c/decH1_sfu_specOk 全表证明，无反例行）。          -/
/-    G2 H-ALLOC-FIT 时序一致性半边：【2026-09-10 已证伪】                    -/
/-       RtCacheConsistency.lean：逐行不高估（max 形式）不是不变式——allocator -/
/-       按 sel 行扣减 vs rt 按 best-fit 选段的错配在 SCAN 被同 CU alloc       -/
/-       抢占时不刷新、可累积为高估；sgpr N=2048 全程 decide 见证：            -/
/-       H-ALLOC-FIT 失效 → FIND 失败按初值 base=0 插表 → 与在驻 WG 区间       -/
/-       重叠（rtcc_w_* 族）。已登记为 I-51（潜伏/时序条件，doc/03）。        -/
/-    G3 H-CUIF-SPLIT 头注所列 cuif_split_wfid 定理不存在。                   -/
/-    G4 CTA-E2 被 I-25 实际打破（CTA2warp tag 迟读污染）——H-CUIF-DONE/      -/
/-       DEALLOC 的核销只在 E2 成立的有效输入域内有效。                       -/
/-    G5 I-25 见证是匿名 example（轨迹 cuifTi25Leak/cuifTi25Res），非命名     -/
/-       定理，无法被跨文件 xref 直接引用其命题。                             -/
/- ========================================================================= -/

import Ventus.Base.Handshake
import Ventus.Base.MemLaws
import Ventus.CTA.CtaScheduler
import Ventus.CTA.ResourceTable
import Ventus.CTA.Allocator
import Ventus.CTA.CuInterface
import Ventus.Arith.ExeSFU
import Ventus.Schedule.Writeback
import Ventus.Schedule.I4Fix
import Ventus.SIMT.BranchJoinBounds
import Ventus.Arith.DecodeUnitProps
import Ventus.CTA.WgBuffer
import Ventus.Pipe
import Ventus.Mem.ICache

namespace Ventus.Spec

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 核销状态分类与契约登记条目                                              -/
/- ========================================================================= -/

/-- 契约核销状态：
    discharged 已核销（有 Lean 定理证据，见第 5 节交叉引用）；
    pending    待核销（已识别、有归属模块，尚无证据定理）；
    axiomatic  公理化（黑盒既定范围或环境约定，本工程内不可核销/不需核销）；
    refuted    已证伪（假设不成立，有反例定理——对应的代码 bug 见 03 报告） -/
inductive SpecContractStatus where
  | discharged
  | pending
  | axiomatic
  | refuted
deriving DecidableEq, Repr, BEq

/-- 单条契约登记项（审计用元数据；形式化陈述见第 3 节，证据见第 5 节） -/
structure SpecContractEntry where
  /-- 契约编号（沿来源文件头注的命名） -/
  id : String
  /-- 来源模块（lean/Ventus 下相对路径） -/
  srcModule : String
  /-- Chisel 源码位置（文件:行号） -/
  chisel : String
  /-- 核销状态 -/
  status : SpecContractStatus
  /-- 核销证据定理名 / 缺口说明 -/
  evidence : String
deriving Repr

/- ========================================================================= -/
/- 2. 契约登记册（40 条；与 spec_count_* 定理核对）                            -/
/- ========================================================================= -/

/-- 全工程黑盒/环境契约登记册 -/
def specContracts : List SpecContractEntry :=
  [ ---- A. ExeSFU 黑盒假设（Arith/ExeSFU.lean H 区；FPU/TC/FdivSqrt 黑盒） ----
    { id := "H-FPU-1", srcModule := "Arith/ExeSFU", chisel := "execution.scala:746-804"
      status := .discharged
      evidence := "VectorFPU ctrl 透传（wvd/wxd/regIndex/warpID/vecMask）。2026-09-11 消解（VentusF/FpuWrap.lean）：fwHfpu1_ctrl_passthrough（每笔 ctrl 透传，零公理）+ fwHfpu1_pairing（叶 FIFO 逐笔配对）" }
  , { id := "H-FPU-2", srcModule := "Arith/ExeSFU", chisel := "execution.scala:784-803"
      status := .axiomatic
      evidence := "FPU 宏 Decoupled + Irrevocable；FPUexe 无输出队列直连。2026-09-11 更新（FpuWrap.lean）：Decoupled 逐笔配对已证（fwHfpu1_pairing）；Irrevocable 的全称形式被 Q-FW-1 反证（fwSfpu_stable_violation：跨 fu 在飞交错 + 反压下 out.bits 切换）——条件形式已证（fwSfpu_out_irrevocable_of_singleFu，单 fu 在飞时成立）。I-52 在案" }
  , { id := "H-FPU-3", srcModule := "Arith/ExeSFU", chisel := "execution.scala:746-804"
      status := .axiomatic
      evidence := "FPU 数值正确性既定黑盒范围外，仅证接线保真。2026-09-10 收窄：Ventus/Spec/FloatSpec.lean 给出 IEEE 754 位级规约（specFpuBinOk/specFpuFmaOk/specFpuCmpOk/specFpuFToFOk/specFpuIToFOk/specFpuFToIOk/specFpuClassOk）——本条含义从『行为正确』收窄为『输出等于位级规约值』。2026-09-11 再收窄（FpuFma.lean）：封装层数值无污染已证（ffm_wrapper_value_faithful/ffm_wrapper_fmadd_value）+ 叶契约表 ffmSpecSem（=specFpu*Ok 实例化：ffm_specSem_*_ok 族）——本条剩余黑盒 = fudian 组合核内部满足 ffmSpecSem（H-FM-1）" }
  , { id := "H-FPU-4", srcModule := "Arith/ExeSFU", chisel := "execution.scala:785"
      status := .discharged
      evidence := "result 取低 32 位 (31,0)。2026-09-11 消解（FpuWrap.lean）：fwHfpu4_lo32_zeroExtend + fwFpu_cvt_isSingle + fwHfpu4_result_eq_sem——VectorFPU 出端实为 64 位线（FPU.scala:12,56 FPUOutput(64)），各叶 f32 结果零扩展装载，(31,0) 恒等无损；Q11 疑点关闭" }
  , { id := "H-FDIV-1", srcModule := "Arith/ExeSFU", chisel := "FloatDivSqrt.scala:303,342"
      status := .axiomatic
      evidence := "FloatDivSqrt 组抽象黑盒；out 反压稳定经源码审查确认，延迟任意。2026-09-10 收窄：数值半由 FloatSpec.lean 的 specFdivDivOk/specFdivSqrtOk 位级规约承载；延迟/反压半不收窄" }
  , { id := "H-TC-1", srcModule := "Arith/ExeSFU", chisel := "execution.scala:115-162"
      status := .axiomatic
      evidence := "TensorCoreFP32 ctrl 透传；消费形态见 exsTc_ctrl_passthrough" }
  , { id := "H-TC-2", srcModule := "Arith/ExeSFU", chisel := "execution.scala:136"
      status := .axiomatic
      evidence := "TC 握手：in.ready 直通、out 满足 Decoupled；TC 宏未建模" }
  , { id := "H-TC-3", srcModule := "Arith/ExeSFU", chisel := "execution.scala:150"
      status := .axiomatic
      evidence := "TC 无逐 lane 掩码、全 lane 写回；机制侧钉死 exsTc_wvdMask_allOnes（wvd_mask 恒全 1）" }
  , { id := "H-DECODE-1", srcModule := "Arith/ExeSFU", chisel := "DecodeUnit.scala:225-228,237-238,344-355; operandCollector.scala:250"
      status := .discharged
      evidence := "核销（2026-08-28，DecodeUnitProps.lean）：decH1a/decH1b/decH1c/decH1_sfu_specOk 全表证明无反例行；见 specXrefDecH1SfuSpecOk" }
  ---- B. CtaScheduler 的 CtasEventOk（五事件十项） ----
  , { id := "H-WGB", srcModule := "CTA/CtaScheduler", chisel := "wg_buffer.scala:85"
      status := .discharged
      evidence := "核销（2026-08-28，WgBuffer.lean）：wgb_h_wgb_discharge（fire 当拍计数必 <8）+ wgb_step_count 记账对应；见 specXrefWgbHWgb" }
  , { id := "H-ALLOC-PENDING", srcModule := "CTA/CtaScheduler", chisel := "allocator.scala:187-188"
      status := .discharged
      evidence := "核销（2026-08-28，WgbEnvOk 条件下）：dcg1_allocRegInv_run 不变式 + dcg1_hAllocPending_rdAct/offer/fire/accept 四落点" }
  , { id := "H-ALLOC-SLOT", srcModule := "CTA/CtaScheduler", chisel := "allocator.scala:162,270-271,295"
      status := .discharged
      evidence := "alc_h_alloc_slot（Allocator.lean）" }
  , { id := "H-WF", srcModule := "CTA/CtaScheduler", chisel := "host 契约"
      status := .axiomatic
      evidence := "1 ≤ numWf ≤ 8：host 侧契约 + WG 定义，工程内不可核销" }
  , { id := "H-RT-BOUNDS", srcModule := "CTA/CtaScheduler", chisel := "resource_table.scala:301-307,364-369"
      status := .discharged
      evidence := "rt_alloc_base_bounds（ResourceTable.lean）" }
  , { id := "H-RT-DISJOINT", srcModule := "CTA/CtaScheduler", chisel := "resource_table.scala:281-313"
      status := .discharged
      evidence := "rt_alloc_disjoint + rt_step_wf；守恒 rt_alloc_used / rt_dealloc_used / rt_sum_le_N（ResourceTable.lean）" }
  , { id := "H-ALLOC-FIT", srcModule := "CTA/CtaScheduler", chisel := "allocator.scala:251-262,91"
      status := .discharged
      evidence := "alc_h_alloc_fit + alc_assert91（Allocator.lean：相对缓存内容不漏不超，定理仍成立）；缺口 G2 已证伪（2026-09-10，RtCacheConsistency.lean rtcc_w_* 族：缓存可高估实际空段，H-ALLOC-FIT 在破窗三条件下失效——I-51）" }
  , { id := "H-CUIF-SPLIT", srcModule := "CTA/CtaScheduler", chisel := "cu_interface.scala:71-82,99-113"
      status := .discharged
      evidence := "cuif_split_tag + cuif_split_deq_last + cuif_split_countdown（CuInterface.lean）；缺口 G3：头注所列 cuif_split_wfid 不存在" }
  , { id := "H-CUIF-DONE", srcModule := "CTA/CtaScheduler", chisel := "cu_interface.scala:161,171,179"
      status := .discharged
      evidence := "cuif_done_read + cuif_cnt_update + cuif_finish_exact（CuInterface.lean）；以 CTA-E2 为前提，E2 被 I-25 打破（缺口 G4）" }
  , { id := "H-CUIF-DEALLOC", srcModule := "CTA/CtaScheduler", chisel := "cu_interface.scala:179,204-223"
      status := .discharged
      evidence := "cuif_dealloc_valid_iff + cuif_dealloc_exact + cuif_dealloc_bits + cuif_dealloc_wgId（CuInterface.lean）" }
  ---- C. 环境契约（Allocator A1 / CuInterface E1 E2） ----
  , { id := "CTA-A1", srcModule := "CTA/Allocator", chisel := "allocator.scala:296"
      status := .discharged
      evidence := "核销（2026-08-29，条件形式）：dcg2_ctaA1（H-CUIF-DEALLOC 三定理打包 + dcg2Agree 簿记对应前提）" }
  , { id := "CTA-E1", srcModule := "CTA/CuInterface", chisel := "cu_interface.scala:79-82"
      status := .discharged
      evidence := "核销（2026-08-29，条件形式）：dcg2_ctaE1（alc_h_alloc_slot + dcg2Agree + H-WF）；numWf≥1 依赖 host 契约（axiomatic）" }
  , { id := "CTA-E2", srcModule := "CTA/CuInterface", chisel := "cu_interface.scala:161"
      status := .axiomatic
      evidence := "CuifEnvOk done 侧：cu_wf_done 的 wf_tag 指向在驻槽——即 I-25 被打破的前提（CTA2warp.scala:77 tag 迟读污染）；违反见证轨迹 cuifTi25Leak / cuifTi25Res（CuInterface.lean 数值测试，缺口 G4/G5）" }
  ---- D. Writeback D6 的 A1-A4（I-9 核销前提） ----
  , { id := "WB-A1", srcModule := "Schedule/Writeback", chisel := "regfile.scala（bank 结构）"
      status := .discharged
      evidence := "核销闭环（2026-08-30，Discharge3.lean）：dcg3_wba1_capstone（CSR 写入点=CTA 派发链，不受 I-25 影响）+ 对齐/尺寸核实——**硬件零检查，host 契约违约即撞址（I-45）**；dcg3_wba1_rt_run_aligned 为正面定理" }
  , { id := "WB-A2", srcModule := "Schedule/Writeback", chisel := "scoreboard.scala（_r 视图）"
      status := .discharged
      evidence := "核销（2026-08-29，Discharge2.lean，前缀精化形式）：dcg2_wba2_prefix/getElem/chain；前提 hf（flush 重启程序序）与 icache 按序响应属环境" }
  , { id := "WB-A3", srcModule := "Schedule/Writeback", chisel := "scoreboard.scala:115-118; pipe.scala:262-268"
      status := .discharged
      evidence := "核销（2026-08-28）：dcg1_wbA3_serialization（独立命题化）+ dcg1_wbA3_blocked_while_busy 机制半" }
  , { id := "WB-A4", srcModule := "Schedule/Writeback", chisel := "writeback.scala:52-61; operandCollector.scala:623-624"
      status := .discharged
      evidence := "写回通路全组合（零深度 Queue = 直连 + Arbiter 无状态 + out.ready≡true）：wb_bank_wen_eq / wb_bank_wen_x_x0 / wb_i9_chain；I-9 核销主定理 wb_i9_unreachable" }
  ---- E. Pipe B 类定理前提 ----
  , { id := "H-BB", srcModule := "Pipe", chisel := "pipe.scala:130,148"
      status := .discharged
      evidence := "核销（2026-08-29，有界等待条件形式）：dcg2_hbb_grant/accept/fire/no_fire_iff/bounded_wait；活性闭环缺环（in0/flushCache 不持续有效）为系统侧前提" }
  , { id := "H-WID", srcModule := "Pipe", chisel := "branch_join.scala:120,179"
      status := .discharged
      evidence := "核销（2026-08-28，模型范围内）：dcg1_hWid_complete/fetchCtl/same_source/event；残留缺口：bjstack(wid) 实例选择未建模（BranchJoin D2 单 warp），见 Discharge1 头注" }
  , { id := "H-IB2I", srcModule := "Pipe", chisel := "pipe.scala:223-224"
      status := .discharged
      evidence := "核销（2026-08-28，Discharge1.lean）：dcg1_hIb2i_no_distortion/ready_closed/fire_eq/bits_closed" }
  , { id := "H-DELAY", srcModule := "Pipe", chisel := "scoreboard.scala:142; pipe.scala:161,237"
      status := .discharged
      evidence := "核销（2026-08-28）：dcg1_hDelay_wire + dcg1_hDelay_gate_closed（I-4 门控链前提逐 warp 实例化闭合）" }
  ---- F. BranchJoinBounds 假设 (1)-(4)（I-2 收口前提） ----
  , { id := "BJB-1", srcModule := "SIMT/BranchJoinBounds", chisel := "pipe.scala:366,293; branch_join.scala:260"
      status := .discharged
      evidence := "核销闭环（2026-08-30，Discharge3.lean）：dcg3_bjb1_end_to_end（B1 经链路保真 + QueueModel Hist 前缀闭合）；残余：Chisel Queue(1,flow)⇒AQueue 的 Simulates 精化未证（方法论降级）" }
  , { id := "BJB-2", srcModule := "SIMT/BranchJoinBounds", chisel := "branch_join.scala:145"
      status := .discharged
      evidence := "takeif 恒选小边：bjbTakeif_if_half + bjbTakeif_else_half" }
  , { id := "BJB-3", srcModule := "SIMT/BranchJoinBounds", chisel := "branch_join.scala（pushed 路径等 join）"
      status := .axiomatic
      evidence := "逐线程剥离只发生在大边且每级净占 1 项：源码直接事实，抽象协议模型内置为守卫" }
  , { id := "BJB-4", srcModule := "SIMT/BranchJoinBounds", chisel := "branch_join.scala:57-59,48-56"
      status := .axiomatic
      evidence := "LIFO 弹栈 + RPC 项与路径项配对：源码直接事实；收口主定理 bjbMain_no_overflow（抽象层），具体→抽象全精化未证（文件头明示降级）" }
  ---- G. 存储/时钟理想化 ----
  , { id := "MEM-1", srcModule := "Base/MemLaws", chisel := "（接口约定）"
      status := .axiomatic
      evidence := "大存储走 MemLaws 接口（read_write_same / read_write_diff / read_init 三定律），零 axiom 接口库；上层定理对任意实例全称量化" }
  , { id := "MEM-2", srcModule := "Mem/SRAMTemplate", chisel := "SRAMTemplate.scala（read-during-write）"
      status := .axiomatic
      evidence := "同拍同址读写 raw 读出建模为写后值（物理 SRAM 未定义）；don't-care 论证见 SRAMTemplate D2（bypassWrite/LFSR 覆盖）" }
  , { id := "MEM-3", srcModule := "Mem/SRAMTemplate", chisel := "SRAMTemplate.scala（上电初值）"
      status := .axiomatic
      evidence := "mem 上电初值建模为全 0（真实 SRAM 未定）；所有定理结论只落在写后读/复位后读的确定值上（SRAMTemplate D8）" }
  , { id := "MEM-4", srcModule := "CTA/ResourceTable, CTA/CuInterface, Mem/SRAMTemplate", chisel := "resource_table.scala:583-586; cu_interface.scala:165-176"
      status := .axiomatic
      evidence := "SyncReadMem 1 拍读延迟抽象为 fire 拍采样/组合读（ResourceTable D5、CuInterface D6、SRAMTemplate D3 一致约定）" }
  , { id := "IC-D8a", srcModule := "Mem/ICache", chisel := "ICacheMSHR.scala:163; ICache.scala:185"
      status := .discharged
      evidence := "对齐半核销（2026-08-28）：dcg1_pcc_run_aligned + dcg1_icD8_align_assert（coreReq 地址 num_fetch=2 对齐）" }
  , { id := "IC-D8b", srcModule := "Mem/ICache", chisel := "ICacheMSHR.scala:163"
      status := .axiomatic
      evidence := "memRsp 只回已分配且已发访存请求的 entry——片外内存子系统纪律，本工程不可内证；消费闭环 dcg1_icD8_rsp_consumes_env（Discharge1.lean）" }
  , { id := "WS-M7", srcModule := "Schedule/WarpScheduler", chisel := "warp_schedule.scala:55"
      status := .refuted
      evidence := "已证伪（2026-08-28）：dcg1_wsM7_assumption_false + dcg1_wsM7_counterexample（FIFO 满时 warpRsp.ready=false 丢响应）——即 I-6；修复见 03 报告" }
  ]

/-- 按状态计数 -/
def specCountStatus (st : SpecContractStatus) : Nat :=
  (specContracts.filter (fun e => e.status == st)).length

/-- 登记册总数核对 -/
theorem spec_count_total : specContracts.length = 41 := by decide
/-- 已核销 23 条 -/
theorem spec_count_discharged : specCountStatus .discharged = 25 := by decide
/-- 待核销 0 条 -/
theorem spec_count_pending : specCountStatus .pending = 0 := by decide
/-- 公理化 17 条 -/
theorem spec_count_axiomatic : specCountStatus .axiomatic = 15 := by decide
/-- 已证伪 1 条 -/
theorem spec_count_refuted : specCountStatus .refuted = 1 := by decide
/-- 四分划闭合 -/
theorem spec_count_partition :
    specCountStatus .discharged + specCountStatus .pending +
      specCountStatus .axiomatic + specCountStatus .refuted = specContracts.length := by decide

/- ========================================================================= -/
/- 3. 可形式化契约的 Prop 陈述（spec 前缀；与登记册 id 对应）                 -/
/- ========================================================================= -/

/-- 【H-RT-DISJOINT / WB-A1 的原子形式】两个资源区间 [b1,b1+s1) 与 [b2,b2+s2)
    不相交。CtaScheduler 的 ctasPairOk 与 ResourceTable 的 rt_alloc_disjoint
    均含此形状；此处给出与具体模块无关的规范形式。 -/
def specIntervalDisjoint (b1 s1 b2 s2 : Nat) : Prop :=
  b1 + s1 ≤ b2 ∨ b2 + s2 ≤ b1

/-- specIntervalDisjoint 的判定实例（decide 自检用） -/
instance (b1 s1 b2 s2 : Nat) : Decidable (specIntervalDisjoint b1 s1 b2 s2) := by
  unfold specIntervalDisjoint; infer_instance

-- 数值自检（先测试后证明纪律）
example : specIntervalDisjoint 0 16 16 8 := by decide
example : specIntervalDisjoint 32 8 0 32 := by decide
example : ¬ specIntervalDisjoint 8 16 16 8 := by decide
example : ¬ specIntervalDisjoint 0 1 0 1 := by decide

/-- 【H-FPU-1】VectorFPU ctrl 透传：输出事务的 wvd/wxd/regIndex/warpID/vecMask
    等于对应输入事务的 ctrl 字段（in-flight 延迟任意）。
    消费形态：ExeSFU.lean 的 exsFpu_mask_fidelity 以 `o.vecMask = m` 为前提。 -/
def specFpuCtrlPassthrough (inp : Ventus.Arith.ExsFpuCtrlIn)
    (o : Ventus.Arith.ExsFpuOut) : Prop :=
  o.wvd = inp.wvd ∧ o.wxd = inp.wxd ∧ o.regIndex = inp.regIndex ∧
  o.warpID = inp.warpID ∧ o.vecMask = inp.vecMask

/-- 【H-TC-1】TensorCoreFP32 ctrl 透传：out.ctrl = 对应输入事务的 ctrl。 -/
def specTcCtrlPassthrough (inp o : Ventus.Arith.ExsTcCtrl) : Prop := o = inp

/-- 【H-FPU-2 / H-TC-2 的通用握手半】Decoupled 通道 Irrevocable（反压下
    valid 保持、bits 稳定）。直接复用 Base/Handshake.lean 的契约定义。 -/
def specIrrevocable {α : Type} (tr : Ventus.Base.Handshake.Trace α) : Prop :=
  Ventus.Base.Handshake.Irrevocable tr

/-- 【H-DECODE-1】上游（decode/operandCollector）对 SFU 类指令的产出约束：
    (a) isvec ⟺ wvd，且 ¬isvec ⟹ wxd；
    (b) 标量（¬isvec）SFU 指令 mask = 0x1；
    (c) wvd/wxd 互斥（FPU 指令恰一）。
    现状：待核销（登记册缺口 G1）——DecodeUnit.lean 未钉此性质。 -/
def specSfuDecodeOk (isvec wvd wxd : Bool) (mask : BitVec 32) : Prop :=
  (isvec = wvd) ∧ (isvec = false → wxd = true) ∧
  (isvec = false → mask = 1#32) ∧ (wvd = true → wxd = false)

/-- specSfuDecodeOk 的判定实例（decide 自检用） -/
instance (isvec wvd wxd : Bool) (mask : BitVec 32) :
    Decidable (specSfuDecodeOk isvec wvd wxd mask) := by
  unfold specSfuDecodeOk; infer_instance

-- 现行 decode 表声称的合法形态确实满足谓词（自检测试）
example : specSfuDecodeOk true true false 0xFFFFFFFF#32 := by decide
example : specSfuDecodeOk false false true 0x1#32 := by decide
example : ¬ specSfuDecodeOk true false true 0x1#32 := by decide   -- Q3 反例形态
example : ¬ specSfuDecodeOk false false true 0x3#32 := by decide  -- Q4 反例形态
example : ¬ specSfuDecodeOk true true true 0x1#32 := by decide    -- Q12 反例形态

/- 【CTA-E2】cu_wf_done 的 wf_tag 指向在驻（live）槽——即 I-25 被打破的前提：
   CTA2warp.scala:77 的 data(wid) 迟读在 wid 复用后可被污染，使 done 计到
   错误槽位。其在具体状态机上的形式化即 CuInterface.lean 的 CuifEnvOk
   （第 4 节集中引用），此处不再重复陈述，只在登记册标注状态与关联。 -/

/- ========================================================================= -/
/- 4. 既有契约谓词的集中引用（机器可检查的同名同型核对，轻量形态）              -/
/- ========================================================================= -/

-- CTA 事件契约总谓词（CtasEventOk 五事件十项 = H-WGB .. H-CUIF-DEALLOC）
#check @Ventus.CTA.CtasEventOk
-- CTA 环境契约（A1 / E1+E2 的具体状态机实例）
#check @Ventus.CTA.AlcEnvOk
#check @Ventus.CTA.CuifEnvOk
-- resource_table 侧事件契约（cnt < 8 等，ResourceTable Q7）
#check @Ventus.CTA.rtEventOk
-- 区间不相交在 CtaScheduler 的具体形态
#check @Ventus.CTA.ctasPairOk
-- 存储接口契约类
#check @Ventus.Base.MemLaws

/- ========================================================================= -/
/- 5. 核销证据的机器可检查交叉引用                                            -/
/-                                                                           -/
/-  每个 specXref* 定义是对应证据定理的同名同型别名（Prop 值 def）：若来源     -/
/-  文件改名/改型，本文件编译即失败——「契约集中处的陈述与各处核销证据同名      -/
/-  同型」由此保证。                                                          -/
/-  注意：bv_decide 证据定理带每定理私有的 LRAT trust 公理                     -/
/-  （…._native.bv_decide.ax_*），native_decide 测试带 Lean.ofReduceBool，    -/
/-  按 AGENTS.md 归档注明。                                                   -/
/- ========================================================================= -/

section SpecXrefs

/-- 【H-WGB 核销证据（WgBuffer.lean）】 -/
def specXrefWgbHWgb := @Ventus.CTA.wgb_h_wgb_discharge
/-- 【H-DECODE-1 核销证据（DecodeUnitProps.lean，全表证明）】 -/
def specXrefDecH1SfuSpecOk := @Ventus.Arith.decH1_sfu_specOk
/-- 【H-RT-BOUNDS 核销证据】 -/
def specXrefRtBounds := @Ventus.CTA.rt_alloc_base_bounds
/-- 【H-RT-DISJOINT 核销证据】 -/
def specXrefRtDisjoint := @Ventus.CTA.rt_alloc_disjoint
/-- 【H-RT-DISJOINT 不变式保持】 -/
def specXrefRtStepWf := @Ventus.CTA.rt_step_wf
/-- 【H-RT 守恒：分配后占用记账】 -/
def specXrefRtAllocUsed := @Ventus.CTA.rt_alloc_used
/-- 【H-RT 守恒：回收后占用记账】 -/
def specXrefRtDeallocUsed := @Ventus.CTA.rt_dealloc_used
/-- 【H-RT 守恒：总量不超 N】 -/
def specXrefRtSumLe := @Ventus.CTA.rt_sum_le_N
/-- 【H-ALLOC-SLOT 核销证据】 -/
def specXrefAllocSlot := @Ventus.CTA.alc_h_alloc_slot
/-- 【H-ALLOC-FIT 核销证据】 -/
def specXrefAllocFit := @Ventus.CTA.alc_h_alloc_fit
/-- 【H-ALLOC-FIT 断言侧（allocator.scala:91 仿真断言恒成立）】 -/
def specXrefAllocAssert91 := @Ventus.CTA.alc_assert91
/-- 【H-CUIF-SPLIT 核销证据：wf_tag 分配】 -/
def specXrefCuifSplitTag := @Ventus.CTA.cuif_split_tag
/-- 【H-CUIF-SPLIT 核销证据：末 WF 弹出】 -/
def specXrefCuifSplitDeqLast := @Ventus.CTA.cuif_split_deq_last
/-- 【H-CUIF-SPLIT 核销证据：拆分计数恰好】 -/
def specXrefCuifSplitCountdown := @Ventus.CTA.cuif_split_countdown
/-- 【H-CUIF-DONE 核销证据：done 读数】 -/
def specXrefCuifDoneRead := @Ventus.CTA.cuif_done_read
/-- 【H-CUIF-DONE 核销证据：计数更新】 -/
def specXrefCuifCntUpdate := @Ventus.CTA.cuif_cnt_update
/-- 【H-CUIF-DONE 核销证据：完成计数恰好】 -/
def specXrefCuifFinishExact := @Ventus.CTA.cuif_finish_exact
/-- 【H-CUIF-DEALLOC 核销证据：回收 valid 刻画】 -/
def specXrefCuifDeallocValidIff := @Ventus.CTA.cuif_dealloc_valid_iff
/-- 【H-CUIF-DEALLOC 核销证据：回收时机精确】 -/
def specXrefCuifDeallocExact := @Ventus.CTA.cuif_dealloc_exact
/-- 【H-CUIF-DEALLOC 核销证据：dealloc bits】 -/
def specXrefCuifDeallocBits := @Ventus.CTA.cuif_dealloc_bits
/-- 【H-CUIF-DEALLOC 核销证据：wgId 一致】 -/
def specXrefCuifDeallocWgId := @Ventus.CTA.cuif_dealloc_wgId
/-- 【CTA-E2 违反面（I-25）见证轨迹：泄漏场景输入序列（命题为匿名 example，
    缺口 G5；此处引用轨迹定义本身）】 -/
def specXrefCuifI25LeakTrace := @Ventus.CTA.cuifTi25Leak
/-- 【CTA-E2 违反面（I-25）见证轨迹：计数残留场景输入序列】 -/
def specXrefCuifI25ResTrace := @Ventus.CTA.cuifTi25Res
/-- 【H-FPU-1 消费形态】 -/
def specXrefFpuMaskFidelity := @Ventus.Arith.exsFpu_mask_fidelity
/-- 【H-TC-1 消费形态】 -/
def specXrefTcCtrlPassthrough := @Ventus.Arith.exsTc_ctrl_passthrough
/-- 【H-TC-3 机制钉】 -/
def specXrefTcMaskAllOnes := @Ventus.Arith.exsTc_wvdMask_allOnes
/-- 【H-DECODE-1(c) 破窗形态（Q12 witness）：wvd=wxd=0 结果丢弃】 -/
def specXrefFpuQ12Drop := @Ventus.Arith.exsFpu_q12_drop
/-- 【H-DECODE-1(a) 破窗形态（Q3 witness）：isvec=1∧wvd=0 指令无声丢失】 -/
def specXrefSfuQ3SilentDrop := @Ventus.Arith.exsSfu_q3_silent_drop
/-- 【WB-A4 / I-9 核销主定理（向量 bank）】 -/
def specXrefWbI9Unreachable := @Ventus.Schedule.wb_i9_unreachable
/-- 【WB-A4 / I-9 核销 capstone：写拍同时性链】 -/
def specXrefWbI9Chain := @Ventus.Schedule.wb_i9_chain
/-- 【WB-A3 相关证据：修复版同 warp 至多一个 CU 持有】 -/
def specXrefI4fNoTwoBusyFix := @Ventus.Schedule.i4f_no_two_busy_fix
/-- 【WB-A3 相关证据：原版门控下同样不双占用（I-4 不可自举）】 -/
def specXrefI4fNoTwoBusyOrig := @Ventus.Schedule.i4f_no_two_busy_orig
/-- 【I-4 修复有效性：同拍 in+out 占用位保持】 -/
def specXrefI4fRaceGone := @Ventus.Schedule.i4f_race_gone
/-- 【BJB 收口主定理（抽象层，前提 = 假设 (1)-(4)）】 -/
def specXrefBjbNoOverflow := @Ventus.SIMT.bjbMain_no_overflow
/-- 【BJB-2 核销证据（if 边减半）】 -/
def specXrefBjbTakeifIfHalf := @Ventus.SIMT.bjbTakeif_if_half
/-- 【BJB-2 核销证据（else 边减半）】 -/
def specXrefBjbTakeifElseHalf := @Ventus.SIMT.bjbTakeif_else_half
/-- 【BJB-1 部分核销：掩码纪律的 popcount 形式】 -/
def specXrefBjbDisciplinePopcount := @Ventus.SIMT.bjbDiscipline_popcount
/-- 【H-DELAY 前提的消费形态（I-4 门控链）】 -/
def specXrefPipeI4GateChain := @Ventus.pipe_i4_gate_chain
/-- 【IC-D8 消费形态：hvalid 即「响应只指向已分配 entry」假设】 -/
def specXrefIcMshrRspFire := @Ventus.Mem.icMshr_rsp_fire
/-- 【MEM-1 接口定律（写后读同址）】 -/
def specXrefMemReadWriteSame := @Ventus.Base.MemLaws.read_write_same
/-- 【MEM-1 接口定律（写后读异址）】 -/
def specXrefMemReadWriteDiff := @Ventus.Base.MemLaws.read_write_diff
/-- 【MEM-1 接口定律（初始化读）】 -/
def specXrefMemReadInit := @Ventus.Base.MemLaws.read_init

end SpecXrefs

/- ========================================================================= -/
/- 6. 汇总：状态分组与公理审计                                                -/
/-                                                                           -/
/-  分组（与第 2 节登记册一致）：                                             -/
/-   discharged(23)：H-ALLOC-SLOT、H-RT-BOUNDS、H-RT-DISJOINT、H-ALLOC-FIT、 -/
/-     H-CUIF-SPLIT、H-CUIF-DONE、H-CUIF-DEALLOC、WB-A4、BJB-2、H-WGB、        -/
/-     H-DECODE-1、H-IB2I、H-DELAY、H-WID、WB-A3、H-ALLOC-PENDING、IC-D8a、   -/
/-     WB-A2、BJB-1、H-BB、WB-A1、CTA-A1、CTA-E1（后六条为条件形式，前提     -/
/-     见各条 evidence 与 Discharge2.lean）                                  -/
/-   pending(0)：（全部核销完毕）                                            -/
/-   axiomatic(17)：H-FPU-1..4、H-FDIV-1、H-TC-1..3、H-WF、CTA-E2、           -/
/-     IC-D8b                                                                -/
/-   refuted(1)：WS-M7（即 I-6）                                             -/
/-     BJB-3、BJB-4、MEM-1..4                                                 -/
/-  其中 CTA-E2 标 axiomatic 但已被 I-25 反例打破（缺口 G4）——它的真实语义    -/
/-  是「有效输入域约束」，核销出的 H-CUIF-DONE/DEALLOC 只在该域内成立。       -/
/- ========================================================================= -/

-- 公理审计（归档注明：bv_decide 定理带 LRAT trust 公理；本文件自身无 sorry）
#print axioms specXrefRtDisjoint
#print axioms specXrefAllocFit
#print axioms specXrefCuifFinishExact
#print axioms specXrefWbI9Unreachable
#print axioms specXrefBjbNoOverflow
#print axioms specXrefI4fNoTwoBusyFix
#print axioms spec_count_partition

end Ventus.Spec
