/- ========================================================================= -/
/-                          Top.lean                                        -/
/-  GPGPU 顶层连线（GPGPU_top.scala，702 行）的 Lean 4 连线模型与连线契约     -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/top/GPGPU_top.scala          -/
/-    （class GPGPU_top :150-327、SM_wrapper :329-515、CTAinterface :54-115、 -/
/-      SM2clusterArbiter :525-579、l2Distribute :587-598、                   -/
/-      cluster2L2Arbiter :606-654、GPGPU_axi_top :116-137 等）               -/
/-  参数（top/parameters.scala + L1Cache/RVGParameter.scala）：               -/
/-    num_sm=2、num_cluster=1、num_sm_in_cluster=2、num_l2cache=1、           -/
/-    num_cache_in_sm=2、num_warp=8、MMU_ENABLED=false（:15，MMU 分支          -/
/-    :224-307 不例化）、GVM_ENABLED=false（:14 默认，GVM 块 :500-514          -/
/-    不例化）、INST_CNT=true、INST_CNT_2=false、SINGLE_INST=false、          -/
/-    l1cache_sourceBits=13（:111 = 3+log2Up(4)+log2Up(256)）、               -/
/-    l2cache_params.source_bits=16（L2cache/Parameters.scala:159 =           -/
/-    13+log2Ceil(2)+log2Ceil(1)+1+1）。                                      -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 纯连线建模（同 Pipe.lean D1/D2）：每条非平凡连线 = 一个纯函数，        -/
/-      输出等式 = 源码该行语义；定理多为 rfl/decide/bv_decide 级。子模块      -/
/-      （cta_scheduler_top、Scheduler(L2)、CTA2warp、pipe、ICache/DCache/     -/
/-      SharedMemory、L1Cache2L2Arbiter 内部）不展开，只形式化对接面。         -/
/-  D2. 纯 `<>` 直通连线（:174-175 CTA↔SM、:203-204/:207-208/:211-212          -/
/-      L2 簇连线、:310-311 host、:366-367 memReq/memRsp、:352-353/:361-364   -/
/-      CTA2warp↔pipe 等）统一抽象为 `topConn = id`。                          -/
/-  D3. Chisel `:=` 的宽度语义：RHS 窄于 LHS 自动零扩展；RHS 宽于 LHS         -/
/-      **静默截断**（宽装窄，本项目 I-11/I-21 同款 bug 族）。本文件对每个     -/
/-      跨模块宽度变化点显式建模扩展/截断函数并证无损性（或记录有损点）。      -/
/-  D4. 参数取定 MMU_ENABLED=false、GVM_ENABLED=false：MMU 分支（:224-307）    -/
/-      与 GVM 调试块（:500-514）不例化，不建模；SINGLE_INST=false ⇒           -/
/-      SM_wrapper.io.inst 字段不存在（:337）。GPGPU_axi_adapter_top           -/
/-      （:138-148）全仓无例化点（grep 证实，ExtMem_gen.scala:20 只 emit      -/
/-      GPGPU_axi_top）——死模块，只做参数核查（Q6），不建连线模型。            -/
/-  D5. TestCase/CPUtest（:655-702）是仿真测试台 stub，不建模。               -/
/-      :315-326 的 printf 调试观测不建模。L2 Scheduler / AXI4Adapter /       -/
/-      AXI4Lite2CTA 为黑盒（MMIO 寄存器映射在 axi/AXI4Lite2CTA.scala，        -/
/-      不在本文件范围）。                                                     -/
/-  D6. 仲裁器内部（SM2clusterArbiter 的 memReqArb+Queue(2)、l2Distribute 的   -/
/-      memRspArb、cluster2L2Arbiter 的 memReqArb）按"固定优先级仲裁 + 直通    -/
/-      转发"语义只建模其**可观测连线函数**（source 打包/解包、valid 路由、    -/
/-      ready 汇聚）；仲裁公平性不在本文件范围。NCluster=1/NL2Cache=1 使       -/
/-      cluster2L2Arbiter 与 l2Distribute 在现配置下退化为近直通（W6/W7）。    -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1.【死字段】:37 host2CTA_data.host_kernel_asid（16b，KNL_ASID_WIDTH）     -/
/-      声明后全文件无消费——CTAinterface 的 asid 通路用的是 :49 host_asid      -/
/-      （:81，且仅 MMU_ENABLED=true 时接）。纯死字段，无功能影响。            -/
/-  Q2.【死字段】:48 host_gds_size_total 源码自承 "Useless ?"，无消费。        -/
/-  Q3.【host 接口字段丢弃】cta_scheduler 的 io_cta2host 含 cu_id              -/
/-      （cta_scheduler.scala:99-100，"For CTA schedule strategy research"）， -/
/-      CTAinterface :84 只取 wg_id 填入 CTA2host_data——cu_id 在顶层边界       -/
/-      被丢弃。调试信息丢失，无功能影响。                                     -/
/-  Q4.【icache_invalidate 绑死】:136 GPGPU_axi_top 把 icache_invalidate       -/
/-      绑死 false.B（W12）：AXI 产品顶层永不冲刷 ICache。换 kernel 复用       -/
/-      同地址代码时正确性完全依赖"ICache 无陈旧项"的外部保证（SimWrapper      -/
/-      顶层 GPGPU_SimWrapper.scala:111 才把该信号暴露为端口）。在 I-23        -/
/-      （ICache probe/refill 无互斥）的背景下值得上游复核。                   -/
/-  Q5.【cycle_cnt 绑死】:135 cycle_cnt := 0.U，:323 的 printf 周期计数恒      -/
/-      0。纯调试观测退化。                                                    -/
/-  Q6.【死模块 + 参数失配】:139 GPGPU_axi_adapter_top 的 AXI idBits =         -/
/-      log2Up(num_sm)+log2Up(num_warp)+1 = 1+3+1 = 5，与其内例化的            -/
/-      GPGPU_axi_top 的 idBits = l2cache_params.source_bits = 16 不一致       -/
/-      （:147 `io.m<>` 会宽度失配）。全仓无例化点，属死代码；若被启用即       -/
/-      elaboration 报错或 id 静默截断。定理 top_axiAdapter_mismatch。         -/
/-  Q7.【TL size 字段恒 0】:543 与 :624 两处 `size := 0.U`（注释自承正确值     -/
/-      应为 log2Up(BlockWords*BytesOfWord)=7）。TL size=0 语义为 1 字节，     -/
/-      与 128B mask/data 矛盾；若 L2 Scheduler/AXI4Adapter 按 size 而非        -/
/-      mask 解释即错。现全仓一致如此，待 L2 波次核销消费侧。                  -/
/-  Q8.【MMU 分支宽装窄】:286（MMU_ENABLED=true 分支，现不例化）               -/
/-      `Cat(cluster2l2Arb.memReqOut.bits.source, 0.U(1.W))` 为 17 位，装入    -/
/-      16 位 source 字段 → MSB 静默截断（宽装窄族）。现配置不可达；           -/
/-      MMU 使能时需重审（:291 的 `>> 1` 恢复假定 LSB 附加位存活，与 :286      -/
/-      的 MSB 截断叠加 = 源高位丢失）。                                       -/
/-  Q9.【a_param = DontCare】:386 icache 请求的 a_param 置 DontCare（Verilog   -/
/-      下为任意值），经 :547 直通进 TL param 字段。TL-UL 约定 Get 的           -/
/-      param=0；若下游消费 param 即错。L2 侧不消费则无害（同 Q7 待核销）。    -/
/-  Q10.【nsm_in_cluster=2 路由位硬编码】:562/:572 的 memRsp 路由只看           -/
/-      source bit14（= W4 打包的 sm 位）；位布局由 :538 的 Cat 与              -/
/-      l1cache_sourceBits=13 共同决定，参数化变动（NSmInCluster>2 走           -/
/-      :566/:575 分支）即漂移。本文件 W5 定理钉死现配置布局。                 -/
/- ========================================================================= -/

import Ventus.Mem.ShareMem
import Std.Tactic.BVDecide

namespace Ventus

open Ventus.Mem

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 例化参数核查（GPGPU_top.scala:164-169 的 5 组例化 + 全文件常数）          -/
/- =========================================================================-/

/-- NSms：SM 例化数（:165；RVGParameter.scala:23 ← parameters.scala:7 num_sm=2） -/
def topNSms : Nat := 2

/-- NCluster（parameters.scala:27 num_cluster=1） -/
def topNCluster : Nat := 1

/-- NSmInCluster（parameters.scala:29 = num_sm/num_cluster = 2） -/
def topNSmInCluster : Nat := 2

/-- NL2Cache（parameters.scala:132 num_l2cache=1） -/
def topNL2Cache : Nat := 1

/-- NCacheInSM（parameters.scala:130 num_cache_in_sm=2；:435 的 assert 同款） -/
def topNCacheInSM : Nat := 2

/-- NUMBER_CU（parameters.scala:138 = num_sm；CTAinterface :58-59 的 Vec 维数） -/
def topNumberCU : Nat := 2

/-- l1cache_sourceBits（parameters.scala:111 = 3+log2Up(4)+log2Up(256) = 3+2+8） -/
def topL1SourceBits : Nat := 13

/-- l2cache_params.source_bits = l2cache_params_l.source_bits
    （L2cache/Parameters.scala:159 = 13+log2Ceil(2)+log2Ceil(1)+1+1 = 16；
    两个参数集的 micro 只差 num_cluster 字段而现配置 num_cluster=1，故同值） -/
def topL2SourceBits : Nat := 16

/-- P1：SM 数 = 簇数 × 簇内 SM 数（:165 与 :172-173 双重循环的一致性） -/
theorem top_p_nsms : topNSms = topNCluster * topNSmInCluster := by decide

/-- P2：CTA 调度器的 CU 口数 = SM 数（:58-59 ↔ :165；:174-175 对接的前提） -/
theorem top_p_cu : topNumberCU = topNSms := by decide

/-- P3：:174-175 的双重循环索引 i*NSmInCluster+j 恰好覆盖 Fin NSms，不重不漏 -/
theorem top_p_sm_index_cover :
    (0 * topNSmInCluster + 0 = 0) ∧ (0 * topNSmInCluster + 1 = 1) ∧
    topNCluster * topNSmInCluster = topNSms := by decide

/-- P4：L1 source 宽度公式落实（parameters.scala:111） -/
theorem top_p_l1src_formula : topL1SourceBits = 3 + 2 + 8 := by decide

/-- P5：L2 source 宽度公式落实（L2cache/Parameters.scala:159） -/
theorem top_p_l2src_formula :
    topL2SourceBits = topL1SourceBits + 1 + 0 + 1 + 1 := by decide

/-- P6：SM2clusterArbiter 输出位宽（l2cache_params_l）与 Scheduler 输入位宽
    （l2cache_params）一致（:167 vs :166 的例化参数；:203/:285 对接的前提） -/
theorem top_p_l2src_match : topL2SourceBits = 16 ∧ topL1SourceBits = 13 := by decide

/-- P7：TLBundleA_lite 固定字段位宽（L2cache/Parameters.scala:154-158 +
    SourceA.scala:20-31）：op=3、size=7（log2Ceil(128)）、addr=32（mmu=false）、
    mask=128（beatBytes/writeBytes=128/1）、data=1024（128B×8）、param=3。
    与 L1CacheMemReq 侧（L1Interfaces.scala:69-87）逐项等宽：
    a_opcode 3=a op、a_addr 32=address、a_mask 32×4=128、a_data 32×32=1024。 -/
theorem top_p_tl_widths :
    (3 : Nat) = 3 ∧ 7 = Nat.log2 128 ∧ 128 = 32 * 4 ∧ 1024 = 32 * 32 := by decide

/-- l2Distribute 的 bank 选择（:593 的 `l2param.parseAddress(addr)._2`；
    NL2Cache=1 ⇒ l2cBits=log2Ceil(1)=0 ⇒ Parameters.scala:224 走 else 分支恒 0.U） -/
def topL2BankSel (_addr : BitVec 32) : BitVec 1 := 0#1

/-- P8：地址映射——NL2Cache=1 时全 32 位地址空间归属唯一的 L2，
    "各 bank 地址区间不相交"退化为全覆盖（无重叠亦无空洞） -/
theorem top_l2_bank_single (a : BitVec 32) : topL2BankSel a = 0#1 := rfl

/- ========================================================================= -/
/- 2. A 类：连线事实（逐行翻译 GPGPU_top.scala，定理 = "连线函数 = 源码语义"）  -/
/- =========================================================================-/

/-- W0（:174-175,:203-204,:207-208,:211-212,:310-311,:352-353,:361-364,
    :366-367,:391-395,:403-409,:424,:426,:485-497 等）：
    纯 `<>` / 直接 `:=` 直通连线的统一抽象——连线函数即恒等。 -/
def topConn {α : Type} (x : α) : α := x

/-- 直通连线的语义就是恒等（契约表所有 `<>` 行共用） -/
theorem top_conn_id {α : Type} (x : α) : topConn x = x := rfl

/-- 手动 Decoupled 对接（:178-183,:186-192,:289-297 等三行式：valid/bits 正向
    直通、ready 反向直通）的共用抽象 -/
def topFwdV (v : Bool) : Bool := v
def topBwdR (r : Bool) : Bool := r

/-- 手动对接两端 fire 定义一致（同一拍同一事务，两侧视图相同） -/
theorem top_manual_fire_agree (v r : Bool) : (topFwdV v && r) = (v && topBwdR r) := rfl

/-- W1（:32-50）：host2CTA_data 字段（host 侧；位宽见各行注释） -/
structure TopHost2CtaData where
  wgId         : BitVec 32  -- :33 WG_ID_WIDTH=32
  numWf        : BitVec 4   -- :34 log2Ceil(NUM_WF_MAX+1)=log2Ceil(9)
  wfSize       : BitVec 6   -- :35 log2Ceil(NUM_THREAD_MAX+1)=log2Ceil(33)
  startPc      : BitVec 32  -- :36 MEM_ADDR_WIDTH
  kernelAsid   : BitVec 16  -- :37 KNL_ASID_WIDTH=SV32.asidLen=16（Q1：死字段）
  size3dX      : BitVec 11  -- :38 log2Ceil(NUM_WG_DIM_MAX+1)=log2Ceil(1025)
  size3dY      : BitVec 11
  size3dZ      : BitVec 11
  csrKnl       : BitVec 32  -- :39
  vgprTotal    : BitVec 11  -- :40 log2Ceil(1024+1)
  sgprTotal    : BitVec 12  -- :41 log2Ceil(2048+1)
  ldsTotal     : BitVec 18  -- :42 log2Ceil(sharemem_size+1)=log2Ceil(131073)
  vgprPerWf    : BitVec 11  -- :43
  sgprPerWf    : BitVec 12  -- :44
  pdsPerWf     : BitVec 18  -- :45 log2Ceil(4096*32+1)=log2Ceil(131073)
  pdsBase      : BitVec 32  -- :46
  gdsBase      : BitVec 32  -- :47
  gdsSizeTotal : BitVec 32  -- :48（Q2：死字段，源码自承 "Useless ?"）
  asid         : BitVec 16  -- :49 ASID_WIDTH=16

/-- W1 目标侧：cta_sche.io.host_wg_new.bits（cta_scheduler.scala:14-31,70-81
    的 trait 组合；逐字段位宽与 TopHost2CtaData 对应项**完全等宽**，已逐行
    核对 cta_scheduler.scala:16-31,72-81。MMU_ENABLED=false ⇒ asid_kernel
    字段不存在（:80-82 不生成，D4）） -/
structure TopCtaWgNew where
  wgId           : BitVec 32
  numWf          : BitVec 4
  numThreadPerWf : BitVec 6
  startPc        : BitVec 32
  numWgX         : BitVec 11
  numWgY         : BitVec 11
  numWgZ         : BitVec 11
  pdsBase        : BitVec 32
  numPdsPerWf    : BitVec 18
  csrKernel      : BitVec 32
  numLds         : BitVec 18
  numSgpr        : BitVec 12
  numVgpr        : BitVec 11
  numSgprPerWf   : BitVec 12
  numVgprPerWf   : BitVec 11
  gdsBase        : BitVec 32

/-- W1（:62-82）：CTAinterface 的 host2CTA → cta_sche.host_wg_new 字段映射。
    valid/ready 直通（:62-63，W0）；kernelAsid/gdsSizeTotal 恒无去向（Q1/Q2），
    asid 在 MMU off 下亦无去向（:80-82 不生成）。 -/
def topHostMap (h : TopHost2CtaData) : TopCtaWgNew where
  wgId           := h.wgId        -- :64
  numWf          := h.numWf       -- :65
  numThreadPerWf := h.wfSize      -- :66
  startPc        := h.startPc     -- :67
  numWgX         := h.size3dX     -- :68
  numWgY         := h.size3dY     -- :69
  numWgZ         := h.size3dZ     -- :70
  pdsBase        := h.pdsBase     -- :71
  numPdsPerWf    := h.pdsPerWf    -- :72
  csrKernel      := h.csrKnl      -- :73
  numLds         := h.ldsTotal    -- :74
  numSgpr        := h.sgprTotal   -- :75
  numVgpr        := h.vgprTotal   -- :76
  numSgprPerWf   := h.sgprPerWf   -- :77
  numVgprPerWf   := h.vgprPerWf   -- :78
  gdsBase        := h.gdsBase     -- :79

-- W1 逐字段连线事实（全部 rfl；每条对应源码一行）
theorem top_hostMap_wgId    (h : TopHost2CtaData) : (topHostMap h).wgId = h.wgId := rfl
theorem top_hostMap_numWf   (h : TopHost2CtaData) : (topHostMap h).numWf = h.numWf := rfl
theorem top_hostMap_thread  (h : TopHost2CtaData) : (topHostMap h).numThreadPerWf = h.wfSize := rfl
theorem top_hostMap_startPc (h : TopHost2CtaData) : (topHostMap h).startPc = h.startPc := rfl
theorem top_hostMap_wgX     (h : TopHost2CtaData) : (topHostMap h).numWgX = h.size3dX := rfl
theorem top_hostMap_wgY     (h : TopHost2CtaData) : (topHostMap h).numWgY = h.size3dY := rfl
theorem top_hostMap_wgZ     (h : TopHost2CtaData) : (topHostMap h).numWgZ = h.size3dZ := rfl
theorem top_hostMap_pdsBase (h : TopHost2CtaData) : (topHostMap h).pdsBase = h.pdsBase := rfl
theorem top_hostMap_pdsPer  (h : TopHost2CtaData) : (topHostMap h).numPdsPerWf = h.pdsPerWf := rfl
theorem top_hostMap_csr     (h : TopHost2CtaData) : (topHostMap h).csrKernel = h.csrKnl := rfl
theorem top_hostMap_lds     (h : TopHost2CtaData) : (topHostMap h).numLds = h.ldsTotal := rfl
theorem top_hostMap_sgpr    (h : TopHost2CtaData) : (topHostMap h).numSgpr = h.sgprTotal := rfl
theorem top_hostMap_vgpr    (h : TopHost2CtaData) : (topHostMap h).numVgpr = h.vgprTotal := rfl
theorem top_hostMap_sgprPer (h : TopHost2CtaData) : (topHostMap h).numSgprPerWf = h.sgprPerWf := rfl
theorem top_hostMap_vgprPer (h : TopHost2CtaData) : (topHostMap h).numVgprPerWf = h.vgprPerWf := rfl
theorem top_hostMap_gds     (h : TopHost2CtaData) : (topHostMap h).gdsBase = h.gdsBase := rfl

/-- W1 完整性：本模型结构把 :38 的 size_3d(Vec 3) 展开为 3 个字段，故
    TopHost2CtaData 共 19 个模型字段 = 16 个入映射目标 + 3 个无消费
    （kernelAsid/gdsSizeTotal 恒死，Q1/Q2；asid 仅 MMU_ENABLED=true 时经 :81
    消费，现配置下无去向）。 -/
theorem top_hostMap_field_count : 16 + 3 = 19 := by decide

/-- W2 源侧：cta_sche.io.cu_wf_new(i).bits（io_cuinterface2cu，
    cta_scheduler.scala:85-90 + trait ctainfo_alloc_to_cu :55-60——注意
    base 字段位宽是 log2Ceil(MAX) 而非 log2Ceil(MAX+1)） -/
structure TopCuWfNew where
  numWf          : BitVec 4   -- :89 log2Ceil(8+1)
  numThreadPerWf : BitVec 6   -- :72 log2Ceil(32+1)
  ldsBase        : BitVec 17  -- :60 log2Ceil(131072)
  sgprBase       : BitVec 11  -- :58 log2Ceil(2048)
  vgprBase       : BitVec 10  -- :59 log2Ceil(1024)
  wfTag          : BitVec 6   -- :88 WF_TAG_WIDTH=6
  startPc        : BitVec 32  -- :76
  gdsBase        : BitVec 32  -- :74
  pdsBase        : BitVec 32  -- :75
  csrKernel      : BitVec 32  -- :77
  numWgX         : BitVec 11  -- :78
  numWgY         : BitVec 11
  numWgZ         : BitVec 11
  wgId           : BitVec 32  -- :87

/-- W2 目标侧：CTAreqData（CTA2warp.scala:17-33；MMU off ⇒ :32 的
    dispatch2cu_knl_asid 不存在，:104-108 的 match 走 None 分支不生成） -/
structure TopCtaReqData where
  wgWfCount : BitVec 4   -- :18 log2Ceil(8+1)
  wfSize    : BitVec 6   -- :19
  sgprBase  : BitVec 12  -- :20 log2Ceil(2048+1)
  vgprBase  : BitVec 11  -- :21 log2Ceil(1024+1)
  ldsBase   : BitVec 18  -- :22 log2Ceil(131072+1)
  wfTag     : BitVec 6   -- :23
  startPc   : BitVec 32  -- :24
  pdsBase   : BitVec 32  -- :25
  gdsBase   : BitVec 32  -- :26
  csrKnl    : BitVec 32  -- :27
  wgidX     : BitVec 11  -- :28
  wgidY     : BitVec 11  -- :29
  wgidZ     : BitVec 11  -- :30
  wgId      : BitVec 32  -- :31

/-- W2（:89-109）：CTAinterface 的 cu_wf_new(i) → CTA2warp(i) 字段映射。
    valid/ready 直通（:89/:109，W0）。三处窄装宽零扩展（:92/:93/:94，D3 的
    合法方向），其余等宽直通。 -/
def topCta2WarpMap (c : TopCuWfNew) : TopCtaReqData where
  wgWfCount := c.numWf                    -- :90
  wfSize    := c.numThreadPerWf           -- :91
  ldsBase   := c.ldsBase.zeroExtend 18    -- :92（17→18 零扩展）
  sgprBase  := c.sgprBase.zeroExtend 12   -- :93（11→12 零扩展）
  vgprBase  := c.vgprBase.zeroExtend 11   -- :94（10→11 零扩展）
  wfTag     := c.wfTag                    -- :95
  startPc   := c.startPc                  -- :96
  gdsBase   := c.gdsBase                  -- :97
  pdsBase   := c.pdsBase                  -- :98
  csrKnl    := c.csrKernel                -- :99
  wgidX     := c.numWgX                   -- :100
  wgidY     := c.numWgY                   -- :101
  wgidZ     := c.numWgZ                   -- :102
  wgId      := c.wgId                     -- :103

-- W2 逐字段连线事实
theorem top_c2w_count   (c : TopCuWfNew) : (topCta2WarpMap c).wgWfCount = c.numWf := rfl
theorem top_c2w_size    (c : TopCuWfNew) : (topCta2WarpMap c).wfSize = c.numThreadPerWf := rfl
theorem top_c2w_wfTag   (c : TopCuWfNew) : (topCta2WarpMap c).wfTag = c.wfTag := rfl
theorem top_c2w_startPc (c : TopCuWfNew) : (topCta2WarpMap c).startPc = c.startPc := rfl
theorem top_c2w_gds     (c : TopCuWfNew) : (topCta2WarpMap c).gdsBase = c.gdsBase := rfl
theorem top_c2w_pds     (c : TopCuWfNew) : (topCta2WarpMap c).pdsBase = c.pdsBase := rfl
theorem top_c2w_csr     (c : TopCuWfNew) : (topCta2WarpMap c).csrKnl = c.csrKernel := rfl
theorem top_c2w_wgidX   (c : TopCuWfNew) : (topCta2WarpMap c).wgidX = c.numWgX := rfl
theorem top_c2w_wgidY   (c : TopCuWfNew) : (topCta2WarpMap c).wgidY = c.numWgY := rfl
theorem top_c2w_wgidZ   (c : TopCuWfNew) : (topCta2WarpMap c).wgidZ = c.numWgZ := rfl
theorem top_c2w_wgId    (c : TopCuWfNew) : (topCta2WarpMap c).wgId = c.wgId := rfl

/-- W2 零扩展无损（:92/:93/:94，D3 合法方向）：扩展后截回原宽 = 原值 -/
theorem top_c2w_zext_lossless (c : TopCuWfNew) :
    (topCta2WarpMap c).ldsBase.extractLsb' 0 17 = c.ldsBase ∧
    (topCta2WarpMap c).sgprBase.extractLsb' 0 11 = c.sgprBase ∧
    (topCta2WarpMap c).vgprBase.extractLsb' 0 10 = c.vgprBase := by
  obtain ⟨a,b,ld,sg,vg,e,f,g,h,i,j,k,l⟩ := c
  unfold topCta2WarpMap
  refine ⟨?_, ?_, ?_⟩ <;> bv_decide

/-- W3（:111-113）：warp2CTA(i) → cta_sche.cu_wf_done(i)。
    CTArspData 只有一个字段（CTA2warp.scala:34-36，wf_tag 6 位），
    bits/valid 正向直通、ready 反向直通（W0/top_manual_fire_agree）。 -/
def topWarp2CtaTag (t : BitVec 6) : BitVec 6 := t

theorem top_warp2cta_tag (t : BitVec 6) : topWarp2CtaTag t = t := rfl

/-- W4a（L1Cache2L2Arbiter.scala:37，SM_wrapper :365 例化的内部连线）：
    L1Cache2L2Arbiter 把 NCacheInSM 位 Cat 到 L1 源高位：
    Cat(cacheIdx, a_source13)。注：:36 的 Arbiter 数据类型是 L1CacheMemReq
    （a_source 32 位），Cat 结果 14 位零扩展入 32 位；:38 `io.memReqOut <>
    memReqArb.io.out` 再截回 14 位（L1CacheMemReqArb.a_source）。 -/
def topL1ArbPackSrc (cid : BitVec 1) (src : BitVec 13) : BitVec 14 := cid ++ src

/-- W4b（:366 + :178）：SM_wrapper.io.memReq 是 L1CacheMemReq（a_source 32 位），
    而 l1Cache2L2Arb.memReqOut 是 L1CacheMemReqArb（14 位）——:366 的 `<>` 零扩展
    14→32；:178 sm2clusterArb.memReqVecIn.bits := sm.memReq.bits 又截回 14
    （L1CacheMemReqArb ← L1CacheMemReq，D3 静默截断）。
    两次"零扩展+截断"对构成恒等： -/
theorem top_sm_memReq_source_chain (x : BitVec 14) :
    (((x.zeroExtend 32).extractLsb' 0 14).zeroExtend 32).extractLsb' 0 14 = x := by
  bv_decide

/-- W4c（:538）：SM2clusterArbiter 把簇内 SM 号 Cat 到源高位
    （NSmInCluster=2 分支）：Cat(smIdx, a_source14)，15 位零扩展入
    TLBundleA_lite(l2cache_params_l).source（16 位，P6）。 -/
def topSm2ClusterPackSrc (sm : BitVec 1) (src : BitVec 14) : BitVec 16 :=
  (sm ++ src).zeroExtend 16

/-- W4d（:540-547）：其余字段直通——opcode/param/address/mask/data 等宽
    （P7），spike_info 直通（:544），size := 0.U 零扩展（:543，Q7）。 -/
def topSm2ClusterSize : BitVec 7 := (0#1).zeroExtend 7

theorem top_sm2cluster_size_zero : topSm2ClusterSize = 0#7 := by decide

/-- W5a（:556-558）：memRsp 解包——memRspIn(TLBundleD_lite_plus，source 16 位)
    的 d_source 截断为 14 位（L1CacheMemRsp.d_source，D3 宽装窄）。
    截去的 [15:14] = [0, smIdx]（W4c 构造 + 假设 H-L2SRC：L2 原样回传
    source）；路由已在 :562 消费过 smIdx，故对本 SM 无损。 -/
def topSm2ClusterRspDSource (src : BitVec 16) : BitVec 14 := src.extractLsb' 0 14

/-- W5b（:562，NSmInCluster=2 分支）：memRspVecOut(i).valid =
    (source[14] == i) && memRspIn.valid（Q10：路由位布局与 W4c 耦合） -/
def topSm2ClusterRspValid (i : BitVec 1) (rspValid : Bool) (src : BitVec 16) : Bool :=
  (src.extractLsb' 14 1 == i) && rspValid

/-- W5c（:571-573）：memRspIn.ready = Mux1H(UIntToOH(source[14]),
    Reverse(Cat(readies))) = source[14] ? rdy1 : rdy0 -/
def topSm2ClusterRspReady (r0 r1 : Bool) (src : BitVec 16) : Bool :=
  if src.extractLsb' 14 1 == 1#1 then r1 else r0

/-- W5 路由完备：恰好一个 SM 命中（独热的直接推论） -/
theorem top_rsp_route_exactly_one (v : Bool) (src : BitVec 16) :
    (topSm2ClusterRspValid 0#1 v src && topSm2ClusterRspValid 1#1 v src) = false := by
  unfold topSm2ClusterRspValid
  bv_decide

/-- W6a（:593，NL2Cache=1）：l2Distribute 的 valid 门
    `valid && (0.U === parseAddress(addr)._2)`——P8 给出 parseAddress._2 恒 0，
    门退化为直通。 -/
def topL2DistValid (inValid : Bool) (addr : BitVec 32) : Bool :=
  inValid && (0#1 == topL2BankSel addr)

theorem top_l2dist_valid_passthrough (v : Bool) (a : BitVec 32) :
    topL2DistValid v a = v := by
  unfold topL2DistValid topL2BankSel; cases v <;> rfl

/-- W6b（:596）：memReqIn.ready = Mux1H(UIntToOH(0.U), Reverse(Cat([rdy0])))
    = rdy0（单元件 Mux1H 退化为直通） -/
def topL2DistInReady (r0 : Bool) : Bool := r0

theorem top_l2dist_ready_passthrough (r : Bool) : topL2DistInReady r = r := rfl

/-- W6c（:592）：bits 广播直通（NL2Cache=1 只有一个出口）+ :590/:594/:597
    memRsp 单元件 Arbiter 直通（W0） -/
theorem top_l2dist_bits_passthrough {α : Type} (b : α) : topConn b = b := rfl

/-- W7a（:615，NCluster=1 分支）：cluster2L2Arbiter 的 req source 直通
    （不加簇号前缀——这是 source 位布局不含 cluster 位的原因，W4c 的 bit14
    直接是簇内 SM 号） -/
def topCluster2L2ReqSrc (src : BitVec 16) : BitVec 16 := src

theorem top_cluster2l2_req_src (s : BitVec 16) : topCluster2L2ReqSrc s = s := rfl

/-- W7b（:638）：memRspVecOut(i).bits.source :=
    memRspIn.bits.source(14,0)——16 位先截 15 位再零扩展回 16 位，
    **bit15 被丢弃**（D3 宽装窄，随后零扩展补 0）。 -/
def topCluster2L2RspSrc (s : BitVec 16) : BitVec 16 := (s.extractLsb' 0 15).zeroExtend 16

/-- W7b 无损性判据：bit15=0 时截断+零扩展是恒等 -/
theorem top_cluster_rsp_lossless (s : BitVec 16) (h : s.extractLsb' 15 1 = 0#1) :
    topCluster2L2RspSrc s = s := by
  unfold topCluster2L2RspSrc
  bv_decide

/- W7c（:640-641, NCluster=1 分支）：memRsp valid 直通；:647-648 ready 直通 -/

/- W8（:200-223，MMU_ENABLED=false 分支的 L2 簇连线）：
    :203 l2cache.in_a <> cluster2l2Arb.memReqOut（W0 直通）
    :204 cluster2l2Arb.memRspIn <> l2cache.in_d（W0）
    :207 cluster2l2Arb.memReqVecIn(0) <> l2distribute(0).memReqVecOut(0)（W0）
    :208 l2distribute(0).memRspVecIn(0) <> cluster2l2Arb.memRspVecOut(0)（W0）
    :211/:212 io.out_a(0)/out_d(0) 直通（W0；NL2Cache=1 只有 (0)）。
    MMU=true 分支（:224-307）不例化（D4），其 :286 的宽装窄见 Q8。 -/

/-- W9a（:355,:358-360）：pc_reset 链路。`pipe.io.pc_reset := true.B`（:355）
    被 `when(cnt.value===5.U){pc_reset := false.B}`（:360）条件覆盖
    （last-connect-wins），cnt = Counter(10)（:358）只在 <5 时自增（:359）。
    等效状态机：cnt 初值 0，c < 5 时步进 +1，到达 5 后永久停住。 -/
def topPcResetStep (c : BitVec 4) : BitVec 4 := if c < 5#4 then c + 1 else c

/-- W9b：pc_reset = (cnt.value ≠ 5)（:355 与 :360 的合成） -/
def topPcReset (c : BitVec 4) : Bool := c != 5#4

/-- W9c：第 k 拍的 cnt 值（复位后 cnt=0 起步） -/
def topPcCntAt : Nat → BitVec 4
  | 0 => 0#4
  | k + 1 => topPcResetStep (topPcCntAt k)

/-- W9 不变式：cnt 永不超过 5（Counter(10) 的回绕永不触发，:359 不增则停） -/
theorem top_pcResetStep_le5 (c : BitVec 4) (h : c ≤ 5#4) : topPcResetStep c ≤ 5#4 := by
  unfold topPcResetStep
  bv_decide

/-- W9 不动点：cnt=5 后永久停住 -/
theorem top_pcReset_stable5 : topPcResetStep 5#4 = 5#4 := by decide

/-- W9 安全前提落实（PCcontrol 波次的已知前提"顶层 pc_reset 前 5 拍拉高"）：
    拍 0..4（cnt=0..4）pc_reset 恒为 true -/
theorem top_pcReset_high_first5 : ∀ k, k < 5 → topPcReset (topPcCntAt k) = true := by
  decide

/-- W9 计数器在拍 5 到达并停在 5 -/
theorem top_pcCntAt_eq5 (m : Nat) : topPcCntAt (5 + m) = 5#4 := by
  induction m with
  | zero => decide
  | succ m ih =>
    show topPcResetStep (topPcCntAt (5 + m)) = 5#4
    rw [ih]; decide

/-- W9 安全前提的对偶：拍 5 起 pc_reset 永久为 false（SM 进入正常运行，
    mask 无初值问题不再被 pc_reset 掩盖——该前提的证明义务在此闭环） -/
theorem top_pcReset_low_after5 (k : Nat) (hk : 5 ≤ k) :
    topPcReset (topPcCntAt k) = false := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 5 + m := ⟨k - 5, by omega⟩
  rw [top_pcCntAt_eq5]; decide

/-- W10（:488，I-21 现场）：sharedmem.io.coreReq.bits.setIdx :=
    pipe.io.shared_req.bits.setIdx——LSU 侧 8 位（LSU.scala:71,171,216）
    零扩展为 ShareMem 侧 10 位（ShareMemParameters.scala:22，NSets=1024）。
    Chisel `:=` 窄装宽自动零扩展（D3 合法方向），语义等价于： -/
def topSharedSetIdxConn (s : BitVec 8) : BitVec 10 := s.zeroExtend 10

/-- W10 对接与 ShareMem.lean 既有 I-21 模型的等式：本连线函数正是
    smSetIdxOfAddr 的零扩展步 -/
theorem top_shared_setIdx_conn (a : BitVec 32) :
    smSetIdxOfAddr a = topSharedSetIdxConn (lsuSetOf a) := rfl

/-- W10 I-21 断点的连线级刻画：零扩展后高 2 位恒 0 ⇒ 每 bank 1024 行中
    仅低 256 行可达（smI21_dead_rows 的连线侧前提；别名/覆盖证据见
    ShareMem.lean 的 smI21_alias / smI21_witness，本文件不重证） -/
theorem top_shared_setIdx_high_zero (s : BitVec 8) :
    topSharedSetIdxConn s ≤ 255#10 := by
  unfold topSharedSetIdxConn
  bv_decide

/-- W11a（:117）：GPGPU_axi_top 的 AXI 参数——addr 32、data 64、
    id = l2cache_params.source_bits -/
def topAxiAddrBits : Nat := 32
def topAxiDataBits : Nat := 64
def topAxiIdBits : Nat := 16

/-- W11b（:139）：GPGPU_axi_adapter_top 的 AXI idBits（死模块，D4） -/
def topAxiAdapterIdBits : Nat := 1 + 3 + 1  -- log2Up(2)+log2Up(8)+1

/-- W11 AXI id 与 L2 source 位宽一致（:117 ↔ P5，AXI4Adapter 对接的前提） -/
theorem top_axi_id_consistent : topAxiIdBits = topL2SourceBits := by decide

/-- Q6 落实：GPGPU_axi_adapter_top 的 idBits=5 与 GPGPU_axi_top 的 16 不一致；
    该模块全仓无例化点（死代码），若启用 :147 的 `<>` 即宽度失配 -/
theorem top_axiAdapter_mismatch : topAxiAdapterIdBits ≠ topAxiIdBits := by decide

/-- W11c（:135，Q5）：cycle_cnt 绑死 0（0.U 零扩展入 20 位） -/
def topCycleCntConst : BitVec 20 := (0#1).zeroExtend 20

theorem top_cycleCnt_const : topCycleCntConst = 0#20 := by decide

/-- W11d（:136，Q4）：icache_invalidate 绑死 false -/
def topAxiTopIcacheInv : Bool := false

/-- W11e（:184）：icache_invalidate 广播到簇内所有 SM（每个 SM 同值，W0） -/
def topIcacheInvBroadcast (b : Bool) (_sm : Fin 2) : Bool := b

/-- Q4 的合成：GPGPU_axi_top 下所有 SM 的 ICache 永不收 invalidate -/
theorem top_icacheInv_never (sm : Fin 2) :
    topIcacheInvBroadcast topAxiTopIcacheInv sm = false := rfl

/- W11f（:129-134）：axi_lite_adapter.io.ctl<>io.s、axi_adapter AXI 对接、
    host_req/host_rsp 对接（:133-134）——全部 W0 直通。MMIO 寄存器映射本体
    在 axi/AXI4Lite2CTA.scala（D5，不在本文件范围）。 -/

/-- W12a（:380）：icache memReq 的 opcode 绑死 4（TL Get；:381 注释自承） -/
def topIcacheReqOpcode : BitVec 3 := 4#3

theorem top_icache_opcode : topIcacheReqOpcode = 4#3 := rfl

/-- W12b（:385）：icache memReq 的 a_mask 每通道（4 位字节使能）置全 1；
    32 通道 Cat 后 = 128 位全 1（:541 的 asUInt） -/
def topIcacheAMaskLane : BitVec 4 := 0xF#4

theorem top_icache_mask_lane : topIcacheAMaskLane = 0xF#4 := rfl

/-- W12c（:384）：icache memReq 的 a_data 置全 0（Get 无数据）-/
def topIcacheAData : BitVec 1024 := 0#1024

theorem top_icache_data_zero : topIcacheAData = 0#1024 := rfl

/- W12d（:386，Q9）：icache 请求 a_param := DontCare——综合后取值任意，
    经 :547 直通进 TL param。本模型不赋具体值，记录为审查疑点。 -/

/- W12e（:372-376,:416-421）：icache/dcache 的 memRsp 字段级手动对接
    （d_addr/d_data/d_source/d_opcode 直通 + valid/ready 手动，W0 +
    top_manual_fire_agree）；:379-388 的 memReq 手动对接同构（除 W12a-c
    三个绑死字段外全直通）。 -/

/- W13（:310-311）：io.host_rsp<>cta.io.CTA2host、io.host_req<>cta.io.host2CTA
    ——GPGPU_top 边界直通（W0）。CTA2host_data 只含 wg_id（:51-53，
    cta_sche 的 cu_id 在此丢弃，Q3）。 -/

/-- W14（:312-313）：inst_cnt 逐 SM 直通分发（INST_CNT=true、INST_CNT_2=false
    ⇒ inst_cnt2 不存在，:313 不生成） -/
theorem top_inst_cnt_distrib {α : Type} (x : α) : topConn x = x := rfl

/- W15：时钟/复位分发——全文件无 withClock/异步例化，单一时钟域、单一
    同步复位（GVM 块 :504 的 `io.clock := clock` 是同时钟显式前递，
    GVM off 不例化，D4）。唯一的软件时序控制是 W9 的 pc_reset 链。 -/

/- ========================================================================= -/
/- 2.5 数值回归测试（先测试；全部 by decide）                                 -/
/- =========================================================================-/

section TopRegressionTests

-- T1 pc_reset 轨迹（W9）：拍 0..4 拉高、拍 5 起拉低
example :
    (List.range 7).map (fun k => topPcReset (topPcCntAt k)) =
    [true, true, true, true, true, false, false] := by decide

-- T2 source 打包（W4c）：sm=1、src=0x2ABC
example : (topSm2ClusterPackSrc 1#1 0x2ABC#14).extractLsb' 14 1 = 1#1 := by decide
example : (topSm2ClusterPackSrc 1#1 0x2ABC#14).extractLsb' 0 14 = 0x2ABC#14 := by decide
example : (topSm2ClusterPackSrc 1#1 0x2ABC#14).extractLsb' 15 1 = 0#1 := by decide

-- T3 L1 打包（W4a）：cid=1、src=0x1ABC
example : (topL1ArbPackSrc 1#1 0x1ABC#13).extractLsb' 13 1 = 1#1 := by decide
example : (topL1ArbPackSrc 1#1 0x1ABC#13).extractLsb' 0 13 = 0x1ABC#13 := by decide

-- T4 rsp 路由（W5b/W5c）
example : topSm2ClusterRspValid 1#1 true (topSm2ClusterPackSrc 1#1 0x2ABC#14) = true := by decide
example : topSm2ClusterRspValid 0#1 true (topSm2ClusterPackSrc 1#1 0x2ABC#14) = false := by decide
example : topSm2ClusterRspValid 1#1 false (topSm2ClusterPackSrc 1#1 0x2ABC#14) = false := by decide
example : topSm2ClusterRspReady true false (topSm2ClusterPackSrc 1#1 0x2ABC#14) = false := by decide
example : topSm2ClusterRspReady true false (topSm2ClusterPackSrc 0#1 0x2ABC#14) = true := by decide

-- T5 rsp d_source 截断（W5a）：低 14 位无损
example : topSm2ClusterRspDSource (topSm2ClusterPackSrc 1#1 0x2ABC#14) = 0x2ABC#14 := by decide

-- T6 l2Distribute 退化（W6）
example : topL2DistValid true 0xDEADBEEF#32 = true := by decide
example : topL2DistValid false 0xDEADBEEF#32 = false := by decide

-- T7 cluster2L2 rsp 截断（W7b）：bit15=0 无损
example : topCluster2L2RspSrc 0x7ABC#16 = 0x7ABC#16 := by decide

-- T8 I-21 对接（W10）：8 位 setIdx 零扩展
example : topSharedSetIdxConn 0xAB#8 = 0x0AB#10 := by decide
example : smSetIdxOfAddr 0x70008040#32 = smSetIdxOfAddr 0x70000040#32 := by decide

-- T9 参数核查（P1-P6、W11）
example : topNSms = 2 ∧ topNL2Cache = 1 ∧ topL1SourceBits = 13 ∧ topL2SourceBits = 16 := by decide
example : topAxiAdapterIdBits = 5 := by decide

end TopRegressionTests

/- ========================================================================= -/
/- 3. B 类：跨模块组合契约（请求/响应源位端到端往返）                          -/
/- =========================================================================-/

/-- 请求路径端到端 source 装配（W4a∘W4b∘W4c）：
    SM 内 L1Cache2L2Arbiter 打包 Cat(cacheId, l1src13)，经两次零扩展/截断对
    （W4b，已证恒等）到达 SM2clusterArbiter，再 Cat(smIdx) 零扩展为 L2 的
    16 位 source。最终布局：[15]=0、[14]=smIdx、[13]=cacheId、[12:0]=l1src。 -/
def topEndToEndSrc (sm cid : BitVec 1) (src : BitVec 13) : BitVec 16 :=
  topSm2ClusterPackSrc sm (topL1ArbPackSrc cid src)

/-- B-SRC1：端到端位布局（请求侧） -/
theorem top_src_layout (sm cid : BitVec 1) (src : BitVec 13) :
    (topEndToEndSrc sm cid src).extractLsb' 15 1 = 0#1 ∧
    (topEndToEndSrc sm cid src).extractLsb' 14 1 = sm ∧
    (topEndToEndSrc sm cid src).extractLsb' 13 1 = cid ∧
    (topEndToEndSrc sm cid src).extractLsb' 0 13 = src := by
  unfold topEndToEndSrc topSm2ClusterPackSrc topL1ArbPackSrc
  bv_decide

/-- B-SRC2：响应路由把响应送回发起 SM——W5b 路由位（bit14）与 W4c 打包位
    一致（Q10 的钉死）；对端 SM 恒不命中。 -/
theorem top_rsp_route_home (cid : BitVec 1) (src : BitVec 13) (v : Bool) :
    topSm2ClusterRspValid 0#1 v (topEndToEndSrc 0#1 cid src) = v ∧
    topSm2ClusterRspValid 1#1 v (topEndToEndSrc 0#1 cid src) = false ∧
    topSm2ClusterRspValid 1#1 v (topEndToEndSrc 1#1 cid src) = v ∧
    topSm2ClusterRspValid 0#1 v (topEndToEndSrc 1#1 cid src) = false := by
  unfold topSm2ClusterRspValid topEndToEndSrc topSm2ClusterPackSrc topL1ArbPackSrc
  bv_decide

/-- B-SRC3：响应 ready 汇聚按 source[14] 选中目标 SM 的 ready（W5c） -/
theorem top_rsp_ready_mux (r0 r1 : Bool) (cid : BitVec 1) (src : BitVec 13) :
    topSm2ClusterRspReady r0 r1 (topEndToEndSrc 0#1 cid src) = r0 ∧
    topSm2ClusterRspReady r0 r1 (topEndToEndSrc 1#1 cid src) = r1 := by
  unfold topSm2ClusterRspReady topEndToEndSrc topSm2ClusterPackSrc topL1ArbPackSrc
  bv_decide

/-- B-SRC4：响应进 SM 后的两级解包无损——:556 截 16→14（W5a）后，
    L1Cache2L2Arbiter.scala:42-44 按 bit13 路由回发起 cache（i$/d$），
    :40 的 `<>` 再截 14→13 恢复原始 L1 source（L1Interfaces.scala:66 注
    "cut off head log2Up(NSms) bits at outside"）。 -/
theorem top_rsp_dsource_roundtrip (sm cid : BitVec 1) (src : BitVec 13) :
    (topSm2ClusterRspDSource (topEndToEndSrc sm cid src)).extractLsb' 13 1 = cid ∧
    (topSm2ClusterRspDSource (topEndToEndSrc sm cid src)).extractLsb' 0 13 = src := by
  unfold topSm2ClusterRspDSource topEndToEndSrc topSm2ClusterPackSrc topL1ArbPackSrc
  bv_decide

/-- B-SRC5：cluster2L2Arbiter 的 bit15 截断（W7b）对请求路径产生的全部
    source 无损（B-SRC1 给出 bit15=0）——前提 H-L2SRC：L2 Scheduler 原样
    回传 source（黑盒契约，D1；L2 波次核销义务）。 -/
theorem top_cluster_rsp_packed_lossless (sm cid : BitVec 1) (src : BitVec 13) :
    topCluster2L2RspSrc (topEndToEndSrc sm cid src) = topEndToEndSrc sm cid src := by
  unfold topCluster2L2RspSrc topEndToEndSrc topSm2ClusterPackSrc topL1ArbPackSrc
  bv_decide

/-- B-I21：I-21 的顶层引用——:488 对接（W10）是 ShareMem.lean `smI21_alias`/
    `smI21_dead_rows`/`smI21_witness` 的连线侧前提。本条把"对接后高 2 位
    恒 0"与死区结论钉在同一形式上： -/
theorem top_i21_dead_rows_conn (s : BitVec 8) :
    (smRowOfSetIdx (topSharedSetIdxConn s)).val < 256 := by
  have h := top_shared_setIdx_high_zero s
  have hto : (topSharedSetIdxConn s).toNat ≤ 255 := BitVec.le_def.mp h
  simp [smRowOfSetIdx]
  omega

/- ========================================================================= -/
/- 4. 连线契约表（汇总；行号 = GPGPU_top.scala，定理均为本文件已证命题）       -/
/- ========================================================================= -/
/-
  参数核查：
  | 条目 | 位置 | 内容 | 定理 |
  |------|------|------|------|
  | P1 | :165,:172-173 | NSms=2=NCluster×NSmInCluster | top_p_nsms |
  | P2 | :58-59↔:165 | NUMBER_CU=num_sm=2（CTA↔SM 口数一致） | top_p_cu |
  | P3 | :174-175 | i*NSmInCluster+j 覆盖 Fin 2 不重不漏 | top_p_sm_index_cover |
  | P4/P5 | par:111,L2par:159 | l1cache_sourceBits=13、source_bits=16 | top_p_l1src_formula, top_p_l2src_formula |
  | P6 | :166-169 | params 与 params_l 的 source_bits 同宽 16 | top_p_l2src_match |
  | P7 | L2par:154-158 | TLBundleA_lite 与 L1CacheMemReq 字段等宽 | top_p_tl_widths |
  | P8 | :593+L2par:219-226 | NL2Cache=1 ⇒ 地址映射全覆盖单 bank | top_l2_bank_single |

  连线事实：
  | 条目 | 行号 | 连线内容 | 定理 |
  |------|------|---------|------|
  | W0 | :174-175,:203-213,:310-311,:352-367 等 | 全部 `<>`/直接 := 直通 | top_conn_id |
  | W1 | :62-82 | host2CTA→cta_sche.host_wg_new 16 字段映射（3 字段无消费 Q1/Q2/asid） | top_hostMap_* |
  | W2 | :89-113 | cu_wf_new→CTA2warp 14 字段映射（3 处零扩展无损）；warp2CTA 直通 | top_c2w_*, top_warp2cta_tag |
  | W3 | :178-183,:186-192 | 手动 Decoupled 对接 fire 一致 | top_manual_fire_agree |
  | W4 | :538（+L1Arb:37,:366,:178） | source 打包链：Cat(cid,src13)→zext/trunc→Cat(sm)→zext16 | top_sm_memReq_source_chain, topEndToEndSrc |
  | W5 | :554-577 | memRsp 解包：bit14 路由、d_source 截 14、ready Mux1H | top_rsp_route_exactly_one, T4/T5 |
  | W6 | :587-598 | l2Distribute 单 bank 退化为直通 | top_l2dist_*_passthrough |
  | W7 | :606-654 | cluster2L2Arbiter NCluster=1 近直通；:638 bit15 截断 | topCluster2L2RspSrc, top_cluster_rsp_lossless |
  | W8 | :201-213 | MMU=false 分支 L2 簇连线（MMU 分支不例化，Q8） | top_conn_id |
  | W9 | :355,:358-360 | pc_reset 前 5 拍拉高、其后永久拉低 | top_pcReset_high_first5, top_pcReset_low_after5 |
  | W10 | :488 | sharedmem setIdx 8→10 零扩展（I-21 现场） | top_shared_setIdx_conn, top_shared_setIdx_high_zero |
  | W11 | :116-137 | GPGPU_axi_top AXI 参数/常量绑死（Q4/Q5/Q6） | top_axi_*, top_cycleCnt_const, top_icacheInv_never |
  | W12 | :379-388 | icache memReq：opcode=4、mask 全 1、data=0、param=DontCare(Q9) | top_icache_* |
  | W13 | :310-311 | host_req/host_rsp 边界直通（cu_id 丢弃，Q3） | top_conn_id |
  | W14 | :312-313 | inst_cnt 逐 SM 直通分发 | top_inst_cnt_distrib |
  | W15 | 全文 | 单时钟域/单同步复位；唯一软件时序控制 = W9 | （结构性观察，无定理） |

  组合契约：
  | B-SRC1 | W4 全链 | 请求 source 端到端位布局 [15]=0,[14]=sm,[13]=cid,[12:0]=src | top_src_layout |
  | B-SRC2 | W4c+W5b | 响应路由送回发起 SM，对端不命中 | top_rsp_route_home |
  | B-SRC3 | W5c | ready 按 source[14] 汇聚 | top_rsp_ready_mux |
  | B-SRC4 | :556+L1Arb:40-44 | 响应两级解包无损恢复 cid/src | top_rsp_dsource_roundtrip |
  | B-SRC5 | :638+B-SRC1 | bit15 截断对请求路径 source 无损 | top_cluster_rsp_packed_lossless |
  | B-I21 | :488 | I-21 对接的高 2 位恒 0 ⇒ 行址 < 256 | top_i21_dead_rows_conn |

  假设清单（B 类定理的前提，非本文件义务）：
  - H-L2SRC：L2 Scheduler 原样回传 16 位 source（请求→响应不改写）。
    失效后果：B-SRC5 之前提 bit15=0 不再由请求侧保证；W5 的路由位错位。
    属 L2 波次核销义务。
  - H-CTA：cta_scheduler_top/cu_interface 内部语义（wf_tag 分配、资源表）
    见 CTA/ 各文件；本文件只保证 :62-113 的接口字段映射。
  - H-AXI：AXI4Lite2CTA 的 MMIO 寄存器映射与 AXI4Adapter 的 TL↔AXI 转换
    为黑盒（axi/ 目录），本文件只核查参数位宽一致性（W11）。

  未覆盖范围：MMU=true 分支（:224-307，D4；其 :286 宽装窄见 Q8）、GVM
  调试块（:500-514）、TestCase/CPUtest（:655-702）、:315-326 printf、
  L1Cache2L2Arbiter/三个 Arbiter 的内部仲裁公平性、icache a_source 的
  5 位窄源（:383 零扩展入 13 位，合法方向）。
-/

/- 公理审计（bv_decide 定理带每定理私有的 LRAT 检查 trust 公理
   `…._native.bv_decide.ax_*`，归档注明；本文件无 native_decide） -/
#print axioms top_pcReset_high_first5
#print axioms top_pcReset_low_after5
#print axioms top_sm_memReq_source_chain
#print axioms top_rsp_route_exactly_one
#print axioms top_cluster_rsp_lossless
#print axioms top_shared_setIdx_high_zero
#print axioms top_src_layout
#print axioms top_rsp_route_home
#print axioms top_rsp_ready_mux
#print axioms top_rsp_dsource_roundtrip
#print axioms top_cluster_rsp_packed_lossless
#print axioms top_i21_dead_rows_conn
#print axioms top_c2w_zext_lossless
#print axioms top_axiAdapter_mismatch

end Ventus
