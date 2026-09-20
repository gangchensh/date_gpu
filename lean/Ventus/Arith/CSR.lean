/- ========================================================================= -/
/-                     Arith/CSR.lean                                        -/
/-  CSR 文件（CSRFile / CSRexe）的 Lean 4 模型（WP5 收尾件）                   -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/pipeline/CSR.scala          -/
/-    （CSR 地址/操作码常量在 17-86 行；CSRFile 在 87-318 行；                -/
/-      CSRexe 在 320-372 行）                                                -/
/-  例化点：pipe.scala:126 `csrfile=Module(new CSRexe())`，每 SM 一个 CSRexe， -/
/-  内含 num_warp=8 个 CSRFile（每 warp 一份 CSR 状态，CSR.scala:337）。      -/
/-  参数取 parameters.scala 默认值：xLen=32、num_warp=8、num_thread=32、      -/
/-  depth_warp=3、depth_thread=5、WF_COUNT_WIDTH=4、WAVE_ITEM_WIDTH=10、      -/
/-  TAG_WIDTH=6、SGPR_ID_WIDTH+1=12、VGPR_ID_WIDTH+1=11、                     -/
/-  WG_SIZE_X/Y/Z_WIDTH=11、LDS_ID_WIDTH=17、LDS_BASE=0x70000000。           -/
/-  ctrl.csr 为 2 位（scoreboard.scala:27，Scoreboard 波次已核实）。          -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 无初值寄存器：wg_wf_count、wf_size_dispatch、knl_base、wg_id、        -/
/-      wf_tag_dispatch（CSR.scala:161-165）与 sgpr_base_dispatch、           -/
/-      vgpr_base_dispatch（:174-175）均为 `Reg` 而非 `RegInit`，上电后、      -/
/-      首次 CTA 下发前读出为未定值（X）。Lean 模型取 0 作为任意初值，         -/
/-      相关定理均不依赖该选择（见 Q4）。                                      -/
/-  D2. VLMAX（:197）是 Reg 但全模块无任何写通路，恒为 num_thread=32，        -/
/-      建模为常量 csrVLMAX。vtype 的组成寄存器 VILL/VMA/VTA/VSEW/VLMUL        -/
/-      与 vstart/vcsr/vl/vlenb/vxrm/vxsat 同样无任何写通路（死状态），        -/
/-      建模为状态字段以保真，csrStep 不更新它们，定理 csr_step_dead_vcsr      -/
/-      钉死其不变性。                                                       -/
/-  D3. 宽度对齐（Chisel 隐式零扩展处显式化）：                               -/
/-      - CTA 域 wf_size 为 6 位（log2Ceil(33)），寄存器 10 位                -/
/-        （WAVE_ITEM_WIDTH），赋值零扩展；                                   -/
/-      - wg_wf_count 4 位、wf_tag 6 位、wg_id_x/y/z 11 位读视图零扩展       -/
/-        到 32 位；                                                         -/
/-      - lds_base := Cat(LDS_BASE(31,18), lds_18bit)（:304），LDS_BASE      -/
/-        低 18 位全 0，故 = 0x70000000 ||| zext32(lds)，引理 csrLdsCat_eq   -/
/-        钉死该等价；                                                       -/
/-      - lsu_tid = wf_tag_dispatch * num_thread（:315）：6bit×6bit 截       -/
/-        12bit 再零扩展到 32 位；tag ≤ 63 时积 ≤ 2016 < 4096 无截断，        -/
/-        等价于 zext32(tag) <<< 5（定理 csr_lsu_tid_mul）。                 -/
/-  D4. CSRexe 的 result 队列（Queue(WriteScalarCtrl,1,pipe=true)，:356）     -/
/-      内部不建模，只建模反压关系 io.in.ready = enq.ready && !CTA2csr.valid  -/
/-      （:359）与 enq.bits 的组合内容（:361-365）；握手/队列精化契约由       -/
/-      Ventus/Base/Handshake.lean 与 QueueModel.lean 另管。                 -/
/-  D5. 每 warp 一个 CSRFile 实例；CSRexe 的 wid 路由建模为                   -/
/-      `Fin 8 → CsrState` 上的逐 warp 输入派生（csrPerWarpInput）：          -/
/-      写使能 = fire && (wid == k)，CTA 使能 = ctaValid && (ctaWid == k)     -/
/-      （:338-344 先广播 false，:354-355 再对选中 warp 覆盖，last-connect    -/
/-      wins）。                                                             -/
/-  D6. csr_rdata 为组合读（:254 Lookup，默认 0），写回数据 wdata 默认取      -/
/-      csr_rdata（:211-212），仅在 wen 且 custom_signal_0/isvec 时被改       -/
/-      写（:259,:263）。读改写（W/S/C）的 csr_wdata（:217-223）基于写前      -/
/-      的 csr_rdata 计算，单拍内写不反馈到读，建模与此一致。                -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1（I 类嫌疑，功能）：isvec 写分支（:262-264）只把写回数据改成            -/
/-      min(AVL,VLMAX)，不更新 vl 或任何寄存器；且 vl/vstart/vcsr/vlenb/      -/
/-      vxrm/vxsat 的地址（:45-51 定义）根本不在读表（:225-252）中。后果：    -/
/-      vsetvl 类指令的写回值正确（min 语义），但 vl 恒 0 且软件无法读出，    -/
/-      vstart/vcsr 等向量 CSR 是死状态。若上游软件/测试依赖读 vl 会得到 0。  -/
/-      定理 csr_vl_dead、csr_isvec_no_state 钉死现状。                       -/
/-  Q2（I 类嫌疑，功能）：fcsr（0x003）在读表（:235）但写链（:265-294）无     -/
/-      对应分支 → csrrw/csrrs fcsr 被静默丢弃。RISC-V 要求写 fcsr 同时更     -/
/-      新 frm 与 fflags 两个字段；Ventus 只支持单独写 frm/fflags 地址。      -/
/-      定理 csr_fcsr_write_ignored 钉死现状。                                -/
/-  Q3（I 类嫌疑）：写链未覆盖的可读地址（threadid、wg_wf_count、             -/
/-      wf_size_dispatch、knl_base、wg_id、wf_tag_dispatch、lds_base、        -/
/-      pds_base、wg_id_x/y/z、vtype，即全部 CTA 下发寄存器与 vtype）的写     -/
/-      被静默忽略，且无任何非法指令异常（mtvec 恒 0，:104，无 trap 支持）。  -/
/-      RISC-V 对只读 CSR 写要求抛异常；此处约定为"写无效"。                  -/
/-  Q4：七个 Reg 无 RegInit（见 D1），CTA 下发前读出未定值。实际流水线中      -/
/-      warp 被调度前必先完成 CTA 下发（warp_schedule 协议），风险可控，      -/
/-      但仿真/验证环境读到 X 可能造成 X 传播。                               -/
/-  Q5：vtype 恒 0x10（VSEW=2 其余 0，:192-196,203），VLMAX 恒 32；           -/
/-      vstart/vcsr/vl/vlenb 寄存器存在但既不可读也不可写（死状态，:198-204）。-/
/-  Q6：custom_signal_0 分支（:258-261）写 rpc := csr_input 且                -/
/-      wdata := csr_input——忽略 CSR.S/C 的读改写语义，写回值是输入而非       -/
/-      CSR 旧值（非标准 CSRRW 语义）。疑为 setrpc 定制指令有意为之，         -/
/-      pipe.scala:139-143 的 printf 佐证其调试用途。                         -/
/-  Q7：CSR.S/C 读改写基于 32 位 csr_rdata；对 frm（3 位）/fflags（5 位）     -/
/-      等窄寄存器，读出的高位为 0，rmw 结果取低位写回，语义自洽（定理        -/
/-      csr_frm_write_low3、csr_fflags_write_mask 钉死）。                    -/
/-  Q8：mip/mie/mstatus 可写位位置符合 RISC-V（MIE/MPIE 位 3/7，xTIP 位 7、   -/
/-      xSIP 位 3、xEIP 位 11）；MPP 恒 3（M 态），其余位恒 0。               -/
/-  Q9：misa/mvendorid/marchid/mimpid/mhartid/mcycle/minstret 等地址在        -/
/-      常量表（:57-83）中定义但未进读表 → 读出 0。misa 读 0 严格违反         -/
/-      RISC-V（应含 MXL 与扩展位），GPU 场景大概率无消费者。                 -/
/-  Q10（CSRexe）：CTA2csr.valid 当拍 io.in.ready=0（:359），阻止 CSR 指      -/
/-      令与 CTA 下发同拍竞争。写链与 CTA 链更新的寄存器不相交（写链：        -/
/-      csr_print/fflags/frm/mstatus/mip/mie/mscratch/mepc/mcause/mtval/      -/
/-      rpc；CTA 链：wf_count/wf_size/sgpr/vgpr/wf_tag/lds/pds/knl/           -/
/-      wg_id_x/y/z/wg_id/threadid），此反压保守但安全。                      -/
/-  Q11（CSRexe）：8 个 CSRFile 广播同一 ctrl/in1，写/CTA 使能按 wid 独热     -/
/-      选择；lsu_*、simt_rpc、rm 按 wid 动态索引组合读出、无锁存             -/
/-      （:349-352,:368-370）——消费者（LSU 等）需在 wid 稳定期间采样，        -/
/-      pipe.scala:136-138 直连 lsu.io.csr_wid 满足此用法。                   -/
/- ========================================================================= -/

import Ventus.Base.Defs
import Std.Tactic.BVDecide

namespace Ventus.Arith

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 操作码与地址常量（CSR.scala:17-86）                                     -/
/- ========================================================================= -/

def csrOpN : BitVec 2 := 0  -- :18 not CSR operation
def csrOpW : BitVec 2 := 1  -- :19 write
def csrOpS : BitVec 2 := 2  -- :20 set
def csrOpC : BitVec 2 := 3  -- :21 clear

-- float csr（:24-26）
def csrAddrFflags : BitVec 12 := 0x001
def csrAddrFrm    : BitVec 12 := 0x002
def csrAddrFcsr   : BitVec 12 := 0x003
-- Vector csr（:45-51；仅 vtype 进读表，其余读出 0，见 Q1/Q5）
def csrAddrVstart : BitVec 12 := 0x008
def csrAddrVxsat  : BitVec 12 := 0x009
def csrAddrVxrm   : BitVec 12 := 0x00A
def csrAddrVcsr   : BitVec 12 := 0x00F
def csrAddrVl     : BitVec 12 := 0xC20
def csrAddrVtype  : BitVec 12 := 0xC21
def csrAddrVlenb  : BitVec 12 := 0xC22
-- thread csr（:29-42）
def csrAddrThreadid       : BitVec 12 := 0x800
def csrAddrWgWfCount      : BitVec 12 := 0x801
def csrAddrWfSizeDispatch : BitVec 12 := 0x802
def csrAddrKnlBase        : BitVec 12 := 0x803
def csrAddrWgId           : BitVec 12 := 0x804
def csrAddrWfTagDispatch  : BitVec 12 := 0x805
def csrAddrLdsBaseDispatch : BitVec 12 := 0x806
def csrAddrPdsBaseaddr    : BitVec 12 := 0x807
def csrAddrWgIdX          : BitVec 12 := 0x808
def csrAddrWgIdY          : BitVec 12 := 0x809
def csrAddrWgIdZ          : BitVec 12 := 0x80A
def csrAddrCsrPrint       : BitVec 12 := 0x80B
def csrAddrRpc            : BitVec 12 := 0x80C
-- Machine-level csr（:57-83；仅 mstatus/mie/mtvec/mscratch/mepc/mcause/mtval/mip 进读表）
def csrAddrMstatus  : BitVec 12 := 0x300
def csrAddrMisa     : BitVec 12 := 0x301
def csrAddrMie      : BitVec 12 := 0x304
def csrAddrMtvec    : BitVec 12 := 0x305
def csrAddrMscratch : BitVec 12 := 0x340
def csrAddrMepc     : BitVec 12 := 0x341
def csrAddrMcause   : BitVec 12 := 0x342
def csrAddrMtval    : BitVec 12 := 0x343
def csrAddrMip      : BitVec 12 := 0x344
def csrAddrMcycle   : BitVec 12 := 0xB00

/-- LDS 基址超参（parameters.scala:136） -/
def csrLdsBaseConst : BitVec 32 := 0x70000000

/-- VLMAX = num_thread = 32（:197；Reg 但无写通路，见 D2） -/
def csrVLMAX : BitVec 32 := 32

/- ========================================================================= -/
/- 2. CSRFile 状态（CSR.scala:107-204）                                       -/
/- ========================================================================= -/

/-- 单 warp 的 CSRFile 全部寄存器状态。无初值的字段见 D1/Q4。 -/
structure CsrState where
  -- mip/mie 中断位（:107-126），仅 bit3/7/11 可写
  mtip : Bool
  msip : Bool
  meip : Bool
  mtie : Bool
  msie : Bool
  meie : Bool
  -- mstatus（:128-145），仅 MIE(bit3)/MPIE(bit7) 可写，MPP 恒 3
  mie : Bool
  mpie : Bool
  -- 机器陷入寄存器（:148-157）
  mscratch : BitVec 32
  mepc     : BitVec 32
  mcause   : BitVec 32
  mtval    : BitVec 32
  -- 线程消息寄存器（:160-172）
  threadid       : BitVec 32
  wgWfCount      : BitVec 4   -- WF_COUNT_WIDTH = log2Ceil(8+1)
  wfSizeDispatch : BitVec 10  -- WAVE_ITEM_WIDTH
  knlBase        : BitVec 32  -- MEM_ADDR_WIDTH
  wgId           : BitVec 32
  wfTagDispatch  : BitVec 6   -- TAG_WIDTH = 3+3
  ldsBaseDispatch : BitVec 32
  pdsBaseaddr    : BitVec 32
  wgIdX : BitVec 11           -- WG_SIZE_X_WIDTH = log2Ceil(1025)
  wgIdY : BitVec 11
  wgIdZ : BitVec 11
  csrPrint : BitVec 32
  rpc      : BitVec 32
  -- 调度基址（:174-175）
  sgprBase : BitVec 12        -- SGPR_ID_WIDTH+1 = 11+1
  vgprBase : BitVec 11        -- VGPR_ID_WIDTH+1 = 10+1
  -- 浮点 CSR（:181-189）
  nv : Bool
  dz : Bool
  of : Bool
  uf : Bool
  nx : Bool
  frm : BitVec 3
  -- 向量 CSR（:192-204，全部死状态，见 D2/Q5）
  vill : Bool
  vma  : Bool
  vta  : Bool
  vsew : BitVec 3
  vlmul : BitVec 3
  vstart : BitVec 32
  vxsat : Bool
  vxrm : BitVec 2
  vcsr  : BitVec 32
  vl    : BitVec 32
  vlenb : BitVec 32
deriving DecidableEq

/-- 复位初值（RegInit 部分按源码；无 RegInit 的字段取 0，见 D1） -/
def csrInit : CsrState where
  mtip := false; msip := false; meip := false
  mtie := false; msie := false; meie := false
  mie := false; mpie := false
  mscratch := 0; mepc := 0; mcause := 0; mtval := 0
  threadid := 0
  wgWfCount := 0        -- Reg 无初值（Q4）
  wfSizeDispatch := 0   -- Reg 无初值（Q4）
  knlBase := 0          -- Reg 无初值（Q4）
  wgId := 0             -- Reg 无初值（Q4）
  wfTagDispatch := 0    -- Reg 无初值（Q4）
  ldsBaseDispatch := 0; pdsBaseaddr := 0
  wgIdX := 0; wgIdY := 0; wgIdZ := 0
  csrPrint := 0; rpc := 0
  sgprBase := 0         -- Reg 无初值（Q4）
  vgprBase := 0         -- Reg 无初值（Q4）
  nv := false; dz := false; of := false; uf := false; nx := false
  frm := 0
  vill := false; vma := false; vta := false
  vsew := 2;            -- :195 only support e32
  vlmul := 0;           -- :196 only support LMUL=1
  vstart := 0; vxsat := false; vxrm := 0; vcsr := 0; vl := 0; vlenb := 0

/- ========================================================================= -/
/- 3. 组合读视图（CSR.scala:125-126,145,186,188,203 的 Cat 与 :225-254 读表） -/
/- ========================================================================= -/

/-- mstatus 读视图（:145）：MPP=3 → 0x1800；仅 bit3(MIE)/bit7(MPIE) 可变 -/
def csrMstatusVal (s : CsrState) : BitVec 32 :=
  0x1800#32 ||| (if s.mpie then 0x80#32 else 0#32) ||| (if s.mie then 0x8#32 else 0#32)

/-- mip 读视图（:125）：MEIP bit11、MTIP bit7、MSIP bit3，其余恒 0 -/
def csrMipVal (s : CsrState) : BitVec 32 :=
  (if s.meip then 0x800#32 else 0#32) ||| (if s.mtip then 0x80#32 else 0#32) |||
  (if s.msip then 0x8#32 else 0#32)

/-- mie 读视图（:126）：同 mip 布局 -/
def csrMieVal (s : CsrState) : BitVec 32 :=
  (if s.meie then 0x800#32 else 0#32) ||| (if s.mtie then 0x80#32 else 0#32) |||
  (if s.msie then 0x8#32 else 0#32)

/-- fflags 读视图（:186）：NV bit4、DZ bit3、OF bit2、UF bit1、NX bit0 -/
def csrFflagsVal (s : CsrState) : BitVec 32 :=
  (if s.nv then 0x10#32 else 0#32) ||| (if s.dz then 0x8#32 else 0#32) |||
  (if s.of then 0x4#32 else 0#32) ||| (if s.uf then 0x2#32 else 0#32) |||
  (if s.nx then 0x1#32 else 0#32)

/-- fcsr 读视图（:188）：Cat(0(24), frm, fflags) -/
def csrFcsrVal (s : CsrState) : BitVec 32 :=
  (BitVec.zeroExtend 32 s.frm <<< 5#32) ||| csrFflagsVal s

/-- vtype 读视图（:203）：VILL bit31、VMA bit7、VTA bit6、VSEW bit5:3、VLMUL bit2:0 -/
def csrVtypeVal (s : CsrState) : BitVec 32 :=
  (if s.vill then 0x80000000#32 else 0#32) ||| (if s.vma then 0x80#32 else 0#32) |||
  (if s.vta then 0x40#32 else 0#32) ||| (BitVec.zeroExtend 32 s.vsew <<< 3#32) |||
  BitVec.zeroExtend 32 s.vlmul

/-- CSR 组合读（:254 `Lookup(csr_addr, 0.U, csrFile)`，读表在 :225-252）。
    未进读表的地址（vstart/vl/misa/mcycle/...）读出 0（Q1/Q9）。 -/
def csrRead (s : CsrState) (addr : BitVec 12) : BitVec 32 :=
  if addr == csrAddrMstatus then csrMstatusVal s                    -- :226
  else if addr == csrAddrMie then csrMieVal s                       -- :227
  else if addr == csrAddrMtvec then 0#32                            -- :228（:104 恒 0）
  else if addr == csrAddrMscratch then s.mscratch                   -- :229
  else if addr == csrAddrMepc then s.mepc                           -- :230
  else if addr == csrAddrMcause then s.mcause                       -- :231
  else if addr == csrAddrMtval then s.mtval                         -- :232
  else if addr == csrAddrMip then csrMipVal s                       -- :233
  else if addr == csrAddrFrm then BitVec.zeroExtend 32 s.frm        -- :234
  else if addr == csrAddrFcsr then csrFcsrVal s                     -- :235
  else if addr == csrAddrFflags then csrFflagsVal s                 -- :236
  else if addr == csrAddrVtype then csrVtypeVal s                   -- :237
  else if addr == csrAddrThreadid then s.threadid                   -- :239
  else if addr == csrAddrWgWfCount then BitVec.zeroExtend 32 s.wgWfCount      -- :240
  else if addr == csrAddrWfSizeDispatch then BitVec.zeroExtend 32 s.wfSizeDispatch -- :241
  else if addr == csrAddrKnlBase then s.knlBase                     -- :242
  else if addr == csrAddrWgId then s.wgId                           -- :243
  else if addr == csrAddrWfTagDispatch then BitVec.zeroExtend 32 s.wfTagDispatch -- :244
  else if addr == csrAddrLdsBaseDispatch then s.ldsBaseDispatch     -- :245
  else if addr == csrAddrPdsBaseaddr then s.pdsBaseaddr             -- :246
  else if addr == csrAddrWgIdX then BitVec.zeroExtend 32 s.wgIdX    -- :247
  else if addr == csrAddrWgIdY then BitVec.zeroExtend 32 s.wgIdY    -- :248
  else if addr == csrAddrWgIdZ then BitVec.zeroExtend 32 s.wgIdZ    -- :249
  else if addr == csrAddrCsrPrint then s.csrPrint                   -- :250
  else if addr == csrAddrRpc then s.rpc                             -- :251
  else 0#32

/- ========================================================================= -/
/- 4. 写数据与写回数据（CSR.scala:206-223,255）                               -/
/- ========================================================================= -/

/-- 写使能（:216）：ctrl.csr.orR & io.write -/
def csrWen (op : BitVec 2) (write : Bool) : Bool := (op != 0#2) && write

/-- 读改写（:217-223 MuxLookup）：W→直写，S→置位，C→清位，N/其他→0（不可达，
    因 wen 要求 op ≠ 0） -/
def csrWdata (op : BitVec 2) (rdata input : BitVec 32) : BitVec 32 :=
  if op == csrOpW then input
  else if op == csrOpS then rdata ||| input
  else if op == csrOpC then rdata &&& ~~~input
  else 0#32

/-- 写回数据 wb_wxd_rd（:210-212,257-264）：默认 csr_rdata；
    wen 且 custom_signal_0 → csr_input（:259，Q6）；
    wen 且 isvec → min(AVL, VLMAX)（:263，Q1） -/
def csrWbWxdRd (s : CsrState) (op : BitVec 2) (addr : BitVec 12) (in1 : BitVec 32)
    (write custom0 isvec : Bool) : BitVec 32 :=
  if csrWen op write && custom0 then in1
  else if csrWen op write && isvec then
    (if BitVec.ult in1 csrVLMAX then in1 else csrVLMAX)
  else csrRead s addr

/- ========================================================================= -/
/- 5. 输入与单拍状态转移（CSR.scala:257-313）                                 -/
/- ========================================================================= -/

/-- CSRFile 单拍输入。cta* 为 CTA2csr.bits.CTAdata 各字段（CTA2warp.scala:18-31，
    宽度按源码：wf_size 6 位、lds 18 位、wf_tag 6 位） -/
structure CsrInputs where
  csrOp   : BitVec 2        -- ctrl.csr（scoreboard.scala:27，2 位）
  addr    : BitVec 12       -- ctrl.inst(31,20)（:206）
  in1     : BitVec 32       -- io.in1（:207）
  write   : Bool            -- io.write
  custom0 : Bool            -- ctrl.custom_signal_0
  isvec   : Bool            -- ctrl.isvec
  ctaValid : Bool           -- io.CTA2csr.valid
  ctaWfCount : BitVec 4     -- dispatch2cu_wg_wf_count
  ctaWfSize  : BitVec 6     -- dispatch2cu_wf_size_dispatch（log2Ceil(33)）
  ctaSgprBase : BitVec 12
  ctaVgprBase : BitVec 11
  ctaLdsBase  : BitVec 18   -- log2Ceil(sharemem_size+1)
  ctaWfTag    : BitVec 6    -- dispatch2cu_wf_tag_dispatch（TAG_WIDTH）
  ctaPdsBase  : BitVec 32
  ctaKnlBase  : BitVec 32
  ctaWgidX    : BitVec 11
  ctaWgidY    : BitVec 11
  ctaWgidZ    : BitVec 11
  ctaWgId     : BitVec 32

/-- LDS 基址拼接（:304）：Cat(LDS_BASE(31, LDS_ID_WIDTH+1), lds_18bit)，
    LDS_ID_WIDTH = log2Ceil(131072) = 17 -/
def csrLdsCat (x : BitVec 18) : BitVec 32 :=
  (BitVec.zeroExtend 32 (csrLdsBaseConst.extractLsb' 18 14) <<< 18#32) |||
  BitVec.zeroExtend 32 x

/-- 单拍状态转移：先 CSR 写链（:257-295），后 CTA 下发链（:296-313）。
    两链更新的寄存器不相交（Q10），顺序无语义影响。 -/
def csrStep (s : CsrState) (i : CsrInputs) : CsrState :=
  let rdata := csrRead s i.addr
  let w := csrWdata i.csrOp rdata i.in1
  let s1 :=
    if csrWen i.csrOp i.write then
      if i.custom0 then { s with rpc := i.in1 }                          -- :258-261
      else if i.isvec then s                                             -- :262-264（Q1：不写任何寄存器）
      else if i.addr == csrAddrCsrPrint then { s with csrPrint := w }    -- :265-266
      else if i.addr == csrAddrFflags then                               -- :267-272
        { s with nx := w.getLsbD 0, uf := w.getLsbD 1, of := w.getLsbD 2, dz := w.getLsbD 3, nv := w.getLsbD 4 }
      else if i.addr == csrAddrFrm then { s with frm := w.extractLsb' 0 3 } -- :273-274
      else if i.addr == csrAddrMstatus then                              -- :275-277
        { s with mie := w.getLsbD 3, mpie := w.getLsbD 7 }
      else if i.addr == csrAddrMip then                                  -- :278-281
        { s with mtip := w.getLsbD 7, msip := w.getLsbD 3, meip := w.getLsbD 11 }
      else if i.addr == csrAddrMie then                                  -- :282-285
        { s with mtie := w.getLsbD 7, msie := w.getLsbD 3, meie := w.getLsbD 11 }
      else if i.addr == csrAddrMscratch then { s with mscratch := w }    -- :286-287
      else if i.addr == csrAddrMepc then { s with mepc := w }            -- :288-289
      else if i.addr == csrAddrMcause then { s with mcause := w }        -- :290-291
      else if i.addr == csrAddrMtval then { s with mtval := w }          -- :292-293
      else s                                                             -- Q2/Q3：静默忽略
    else s
  if i.ctaValid then                                                     -- :296-313
    { s1 with
      wgWfCount := i.ctaWfCount                                          -- :298
      wfSizeDispatch := BitVec.zeroExtend 10 i.ctaWfSize                 -- :299（6→10 零扩展）
      sgprBase := i.ctaSgprBase                                          -- :300
      vgprBase := i.ctaVgprBase                                          -- :301
      wfTagDispatch := BitVec.zeroExtend 6 (i.ctaWfTag.extractLsb' 0 3)   -- :302（低 depth_warp=3 位，零扩展到 TAG_WIDTH=6）
      ldsBaseDispatch := csrLdsCat i.ctaLdsBase                          -- :304
      pdsBaseaddr := i.ctaPdsBase                                        -- :305
      knlBase := i.ctaKnlBase                                            -- :306
      wgIdX := i.ctaWgidX                                                -- :307
      wgIdY := i.ctaWgidY                                                -- :308
      wgIdZ := i.ctaWgidZ                                                -- :309
      wgId := i.ctaWgId                                                  -- :310
      threadid := BitVec.zeroExtend 32 (i.ctaWfTag.extractLsb' 0 3) <<< 5#32 } -- :312（<<depth_thread）
  else s1

/-- 多拍运行 -/
def csrRun (s : CsrState) (ins : List CsrInputs) : CsrState := ins.foldl csrStep s

/- ========================================================================= -/
/- 6. 输出（CSR.scala:176-177,189,214,315-317）                               -/
/- ========================================================================= -/

def csrOutFrm (s : CsrState) : BitVec 3 := s.frm                        -- :189
def csrOutSgprBase (s : CsrState) : BitVec 12 := s.sgprBase             -- :176
def csrOutVgprBase (s : CsrState) : BitVec 11 := s.vgprBase             -- :177
def csrOutSimtRpc (s : CsrState) : BitVec 32 := s.rpc                   -- :214
/-- lsu_tid = wf_tag_dispatch * num_thread（:315），等价性见 D3 -/
def csrOutLsuTid (s : CsrState) : BitVec 32 :=
  BitVec.zeroExtend 32 s.wfTagDispatch <<< 5#32
def csrOutLsuPds (s : CsrState) : BitVec 32 := s.pdsBaseaddr            -- :316
def csrOutLsuNumw (s : CsrState) : BitVec 32 :=
  BitVec.zeroExtend 32 s.wgWfCount                                      -- :317

/- ========================================================================= -/
/- 7. CSRexe：num_warp=8 个 CSRFile 的 wid 路由（CSR.scala:320-372）          -/
/- ========================================================================= -/

/-- warp 数量（parameters.scala:8） -/
def csrNumWarp : Nat := 8

/-- 派生第 k 个 warp 的 CSRFile 输入（:338-344 广播 + :354-355 独热覆盖）。
    广播时 write=false.B、CTA2csr.valid=false.B，随后仅选中 warp 被覆盖。 -/
def csrPerWarpInput (i : CsrInputs) (fire : Bool) (wid ctaWid : BitVec 3)
    (k : BitVec 3) : CsrInputs :=
  { i with write := fire && (wid == k), ctaValid := i.ctaValid && (ctaWid == k) }

/-- CSRexe 单拍：每个 warp 独立 step -/
def csrExeStep (f : Fin 8 → CsrState) (fire : Bool) (wid ctaWid : BitVec 3)
    (i : CsrInputs) : Fin 8 → CsrState :=
  fun k => csrStep (f k) (csrPerWarpInput i fire wid ctaWid (BitVec.ofNat 3 k.val))

/-- in.ready（:359）：队列 enq.ready 且 CTA 下发不占拍（Q10） -/
def csrExeInReady (enqReady : Bool) (ctaValid : Bool) : Bool := enqReady && !ctaValid

/-- enq.bits.wb_wxd_rd（:364）：取选中 warp 的组合写回数据 -/
def csrExeWbWxdRd (f : Fin 8 → CsrState) (wid : Fin 8) (i : CsrInputs) : BitVec 32 :=
  csrWbWxdRd (f wid) i.csrOp i.addr i.in1 i.write i.custom0 i.isvec

/-- lsu/simt/rm 动态索引读出（:349-352,:368-370） -/
def csrExeLsuTid (f : Fin 8 → CsrState) (wid : Fin 8) : BitVec 32 := csrOutLsuTid (f wid)
def csrExeLsuPds (f : Fin 8 → CsrState) (wid : Fin 8) : BitVec 32 := csrOutLsuPds (f wid)
def csrExeLsuNumw (f : Fin 8 → CsrState) (wid : Fin 8) : BitVec 32 := csrOutLsuNumw (f wid)
def csrExeSimtRpc (f : Fin 8 → CsrState) (wid : Fin 8) : BitVec 32 := csrOutSimtRpc (f wid)
def csrExeRm (f : Fin 8 → CsrState) (rmWid : Fin 8) : BitVec 3 := (f rmWid).frm
def csrExeSgprBase (f : Fin 8 → CsrState) (k : Fin 8) : BitVec 12 := (f k).sgprBase
def csrExeVgprBase (f : Fin 8 → CsrState) (k : Fin 8) : BitVec 11 := (f k).vgprBase

/- ========================================================================= -/
/- 8. 数值回归测试（先测试；全部 `by decide`）                                -/
/- ========================================================================= -/

section CsrRegressionTests

/-- 空输入（一拍内无任何事件） -/
def csrInNop : CsrInputs where
  csrOp := 0#2; addr := 0#12; in1 := 0#32
  write := false; custom0 := false; isvec := false
  ctaValid := false
  ctaWfCount := 0#4; ctaWfSize := 0#6; ctaSgprBase := 0#12; ctaVgprBase := 0#11
  ctaLdsBase := 0#18; ctaWfTag := 0#6; ctaPdsBase := 0#32; ctaKnlBase := 0#32
  ctaWgidX := 0#11; ctaWgidY := 0#11; ctaWgidZ := 0#11; ctaWgId := 0#32

/-- CSR 指令写输入（write=true、custom0/isvec/ctaValid 默认 false） -/
def csrInWrite (op : BitVec 2) (addr : BitVec 12) (v : BitVec 32) : CsrInputs :=
  { csrInNop with csrOp := op, addr := addr, in1 := v, write := true }

/-- CTA 下发输入 -/
def csrInCta (tag : BitVec 6) (lds : BitVec 18) (wfCount : BitVec 4) (wfSize : BitVec 6)
    (sgpr : BitVec 12) (vgpr : BitVec 11) (pds knl : BitVec 32)
    (x y z : BitVec 11) (wgid : BitVec 32) : CsrInputs :=
  { csrInNop with
    ctaValid := true
    ctaWfCount := wfCount
    ctaWfSize := wfSize
    ctaSgprBase := sgpr
    ctaVgprBase := vgpr
    ctaLdsBase := lds
    ctaWfTag := tag
    ctaPdsBase := pds
    ctaKnlBase := knl
    ctaWgId := wgid
    ctaWgidX := x
    ctaWgidY := y
    ctaWgidZ := z }

-- T1 复位读出：mstatus = 0x1800（MPP=3），mip/mie/mtvec/frm/fflags/fcsr = 0
example : csrRead csrInit csrAddrMstatus = 0x1800#32 := by decide
example : csrRead csrInit csrAddrMip = 0#32 := by decide
example : csrRead csrInit csrAddrMie = 0#32 := by decide
example : csrRead csrInit csrAddrMtvec = 0#32 := by decide
example : csrRead csrInit csrAddrFrm = 0#32 := by decide
example : csrRead csrInit csrAddrFflags = 0#32 := by decide
example : csrRead csrInit csrAddrFcsr = 0#32 := by decide

-- T2 复位读出：vtype = 0x10（VSEW=2，:195）；vl/vstart/vcsr/vlenb/misa/mcycle
--    及未定义地址读出 0（Q1/Q9）
example : csrRead csrInit csrAddrVtype = 0x10#32 := by decide
example : csrRead csrInit csrAddrVl = 0#32 := by decide
example : csrRead csrInit csrAddrVstart = 0#32 := by decide
example : csrRead csrInit csrAddrVcsr = 0#32 := by decide
example : csrRead csrInit csrAddrVlenb = 0#32 := by decide
example : csrRead csrInit csrAddrVxsat = 0#32 := by decide
example : csrRead csrInit csrAddrVxrm = 0#32 := by decide
example : csrRead csrInit csrAddrMisa = 0#32 := by decide
example : csrRead csrInit csrAddrMcycle = 0#32 := by decide
example : csrRead csrInit 0xFFF#12 = 0#32 := by decide

-- T3 mscratch 的 W/S/C 读改写（:217-223,286-287）
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrMscratch 0xDEADBEEF#32))
    csrAddrMscratch = 0xDEADBEEF#32 := by decide
example : csrRead (csrStep (csrStep csrInit (csrInWrite csrOpW csrAddrMscratch 0x00FF00FF#32))
    (csrInWrite csrOpS csrAddrMscratch 0x0F0F0000#32)) csrAddrMscratch = 0x0FFF00FF#32 := by decide
example : csrRead (csrStep (csrStep csrInit (csrInWrite csrOpW csrAddrMscratch 0xFFFFFFFF#32))
    (csrInWrite csrOpC csrAddrMscratch 0x0F0F0F0F#32)) csrAddrMscratch = 0xF0F0F0F0#32 := by decide
-- 写当拍写回数据 = 写前旧值（D6）
example : csrWbWxdRd csrInit csrOpW csrAddrMscratch 0xDEADBEEF#32 true false false = 0#32 := by decide

-- T4 mepc/mcause/mtval/csr_print 直写往返
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrMepc 0x1234#32))
    csrAddrMepc = 0x1234#32 := by decide
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrMcause 0xABCD#32))
    csrAddrMcause = 0xABCD#32 := by decide
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrMtval 0x55#32))
    csrAddrMtval = 0x55#32 := by decide
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrCsrPrint 0x77#32))
    csrAddrCsrPrint = 0x77#32 := by decide

-- T5 mstatus：仅 bit3/bit7 可写（:275-277），写全 1 得 0x1800|0x88=0x1888
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrMstatus 0xFFFFFFFF#32))
    csrAddrMstatus = 0x1888#32 := by decide
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrMstatus 0x8#32))
    csrAddrMstatus = 0x1808#32 := by decide
-- CSR.C 清 MIE 位：0x1888 清 0x8 → 0x1880
example : csrRead (csrStep (csrStep csrInit (csrInWrite csrOpW csrAddrMstatus 0xFFFFFFFF#32))
    (csrInWrite csrOpC csrAddrMstatus 0x8#32)) csrAddrMstatus = 0x1880#32 := by decide

-- T6 mip/mie：仅 bit3/7/11 可写，写全 1 得 0x888（:278-285）
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrMip 0xFFFFFFFF#32))
    csrAddrMip = 0x888#32 := by decide
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrMie 0xFFFFFFFF#32))
    csrAddrMie = 0x888#32 := by decide

-- T7 frm：只取低 3 位（:274）；写 0xFF → frm=7；fcsr 高 24 位恒 0
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrFrm 0xFF#32))
    csrAddrFrm = 7#32 := by decide
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrFrm 0xFF#32))
    csrAddrFcsr = 0xE0#32 := by decide

-- T8 fflags：只取低 5 位（:267-272）；位序 NX..NV；S/C 读改写
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrFflags 0x1F#32))
    csrAddrFflags = 0x1F#32 := by decide
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrFflags 0xFFFFFFFF#32))
    csrAddrFflags = 0x1F#32 := by decide
example : csrRead (csrStep (csrStep csrInit (csrInWrite csrOpW csrAddrFflags 0x1F#32))
    (csrInWrite csrOpC csrAddrFflags 0x5#32)) csrAddrFflags = 0x1A#32 := by decide
-- fflags 与 frm 联合读出 fcsr：frm=5、fflags=0x12 → 0xA0|0x12 = 0xB2
example : csrRead (csrStep (csrStep csrInit (csrInWrite csrOpW csrAddrFrm 5#32))
    (csrInWrite csrOpW csrAddrFflags 0x12#32)) csrAddrFcsr = 0xB2#32 := by decide

-- T9 Q2 钉死：写 fcsr 被静默忽略（frm/fflags 均不变）
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrFcsr 0xFF#32))
    csrAddrFcsr = 0#32 := by decide

-- T10 Q3 钉死：写只读地址（threadid/knl_base/vtype/rpc 以外的 CTA 寄存器）被忽略
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrThreadid 0xFF#32))
    csrAddrThreadid = 0#32 := by decide
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrKnlBase 0xFF#32))
    csrAddrKnlBase = 0#32 := by decide
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrVtype 0xFF#32))
    csrAddrVtype = 0x10#32 := by decide
example : csrRead (csrStep csrInit (csrInWrite csrOpW csrAddrWgIdX 0xFF#32))
    csrAddrWgIdX = 0#32 := by decide

-- T11 Q1 钉死：写 vl 地址被忽略；vl 恒 0
example : (csrStep csrInit (csrInWrite csrOpW csrAddrVl 0xFF#32)).vl = 0#32 := by decide

-- T12 op=N（csr=0）时即使 write=true 也不写（:216 wen）
example : csrStep csrInit (csrInWrite csrOpN csrAddrMscratch 0xFF#32) = csrInit := by decide

-- T13 custom_signal_0（:258-261，Q6）：rpc 写入原始输入，写回数据也是输入
example : (csrStep csrInit
    { csrInWrite csrOpW csrAddrRpc 0xCAFE#32 with custom0 := true }).rpc = 0xCAFE#32 := by decide
example : csrWbWxdRd csrInit csrOpW csrAddrRpc 0xCAFE#32 true true false = 0xCAFE#32 := by decide
example : csrRead (csrStep csrInit
    { csrInWrite csrOpW csrAddrRpc 0xCAFE#32 with custom0 := true }) csrAddrRpc = 0xCAFE#32 := by decide
-- custom0 优先于 isvec 与地址译码（:258 在 :262 之前）
example : (csrStep csrInit
    { csrInWrite csrOpW csrAddrMscratch 0xBEEF#32 with custom0 := true, isvec := true }).mscratch
    = 0#32 := by decide

-- T14 isvec 写回数据 = min(AVL, VLMAX=32)（:263）；且不写任何寄存器（Q1）
example : csrWbWxdRd csrInit csrOpW csrAddrVl 100#32 true false true = 32#32 := by decide
example : csrWbWxdRd csrInit csrOpW csrAddrVl 10#32 true false true = 10#32 := by decide
example : csrWbWxdRd csrInit csrOpW csrAddrVl 32#32 true false true = 32#32 := by decide
example : csrStep csrInit { csrInWrite csrOpW csrAddrVl 100#32 with isvec := true }
    = csrInit := by decide

-- T15 CTA 下发（:296-313）：tag=0b101101（45）→ wfTag=5、threadid=5<<5=160
def csrS1 : CsrState := csrStep csrInit
  (csrInCta 0b101101#6 0x12345#18 5#4 32#6 0x40#12 0x20#11 0x80000000#32 0x40000000#32
    1#11 2#11 3#11 0x1234#32)

example : csrS1.wfTagDispatch = 5#6 := by decide
example : csrS1.threadid = 160#32 := by decide
example : csrOutLsuTid csrS1 = 160#32 := by decide      -- lsu_tid = tag*num_thread（:315）
example : csrS1.ldsBaseDispatch = 0x70012345#32 := by decide  -- Cat(LDS_BASE(31,18), lds)（:304）
example : csrS1.knlBase = 0x40000000#32 := by decide
example : csrS1.pdsBaseaddr = 0x80000000#32 := by decide
example : csrOutLsuPds csrS1 = 0x80000000#32 := by decide
example : csrOutLsuNumw csrS1 = 5#32 := by decide       -- wg_wf_count 零扩展（:317）
example : csrOutSgprBase csrS1 = 0x40#12 := by decide
example : csrOutVgprBase csrS1 = 0x20#11 := by decide
example : csrS1.wgIdX = 1#11 ∧ csrS1.wgIdY = 2#11 ∧ csrS1.wgIdZ = 3#11 := by decide
example : csrS1.wgId = 0x1234#32 := by decide
example : csrS1.wfSizeDispatch = 32#10 := by decide     -- 6→10 零扩展
-- CTA 下发寄存器可读（:239-249）
example : csrRead csrS1 csrAddrThreadid = 160#32 := by decide
example : csrRead csrS1 csrAddrKnlBase = 0x40000000#32 := by decide
example : csrRead csrS1 csrAddrWfTagDispatch = 5#32 := by decide
example : csrRead csrS1 csrAddrLdsBaseDispatch = 0x70012345#32 := by decide

-- T16 同拍 CSR 写 + CTA 下发：两链寄存器不相交，都生效（Q10）
example : csrRead (csrStep csrInit
    { csrInWrite csrOpW csrAddrMscratch 0x99#32 with ctaValid := true, ctaKnlBase := 0x5555#32 })
    csrAddrMscratch = 0x99#32 := by decide
example : (csrStep csrInit
    { csrInWrite csrOpW csrAddrMscratch 0x99#32 with ctaValid := true, ctaKnlBase := 0x5555#32 }).knlBase
    = 0x5555#32 := by decide

-- T17 CSRexe 反压（:359）：CTA 下发当拍 in.ready=0
example : csrExeInReady true false = true := by decide
example : csrExeInReady true true = false := by decide
example : csrExeInReady false false = false := by decide

-- T18 CSRexe wid 路由（:354-355）：仅 wid=2 的 warp 被写
def csrF0 : Fin 8 → CsrState := fun _ => csrInit
def csrExeS1 : Fin 8 → CsrState :=
  csrExeStep csrF0 true 2#3 7#3 (csrInWrite csrOpW csrAddrMscratch 0x42#32)

example : (csrExeS1 ⟨2, by decide⟩).mscratch = 0x42#32 := by decide
example : (csrExeS1 ⟨0, by decide⟩).mscratch = 0#32 := by decide
example : (csrExeS1 ⟨3, by decide⟩).mscratch = 0#32 := by decide

end CsrRegressionTests

/- ========================================================================= -/
/- 9. 规约定理（后证明）                                                      -/
/- ========================================================================= -/

/-- 展开 CSR 模型全部定义的标准 simp 集；decide 配置折叠字面量地址比较。
    （bv_decide 看不穿 def，须先展开） -/
macro "csr_unfold" : tactic =>
  `(tactic| simp (config := { decide := true }) only [
    ite_true, ite_false,
    csrRead, csrStep, csrWdata, csrWen, csrWbWxdRd, csrMstatusVal, csrMipVal, csrMieVal,
    csrFflagsVal, csrFcsrVal, csrVtypeVal, csrLdsCat, csrLdsBaseConst, csrVLMAX,
    csrOutLsuTid, csrOutLsuNumw, csrOutLsuPds, csrOutFrm, csrOutSimtRpc,
    csrOutSgprBase, csrOutVgprBase,
    csrOpN, csrOpW, csrOpS, csrOpC,
    csrAddrFflags, csrAddrFrm, csrAddrFcsr, csrAddrVstart, csrAddrVxsat, csrAddrVxrm,
    csrAddrVcsr, csrAddrVl, csrAddrVtype, csrAddrVlenb, csrAddrThreadid, csrAddrWgWfCount,
    csrAddrWfSizeDispatch, csrAddrKnlBase, csrAddrWgId, csrAddrWfTagDispatch,
    csrAddrLdsBaseDispatch, csrAddrPdsBaseaddr, csrAddrWgIdX, csrAddrWgIdY, csrAddrWgIdZ,
    csrAddrCsrPrint, csrAddrRpc, csrAddrMstatus, csrAddrMisa, csrAddrMie, csrAddrMtvec,
    csrAddrMscratch, csrAddrMepc, csrAddrMcause, csrAddrMtval, csrAddrMip, csrAddrMcycle,
    csrInNop, csrInWrite, csrInCta])

set_option hygiene false in
/-- 写链 if 树的逐条件拆分宏（hygiene false：捕获使用处的 `i`）。
    条件顺序严格对应 csrStep 写链（CSR.scala:258-293）；
    每个叶子用给定 tactic 收尾（叶子上结构投影均可 rfl/simp 闭合）。
    注：不用 `split` 是因为其内部 simp 的 maxSteps=100000 上限在 40 字段
    结构 x 12 分支的大目标上必然爆掉（实测），by_cases+if_pos/if_neg 可控。 -/
macro "csr_tree_cases" leaf:tactic : tactic => `(tactic| (
  by_cases hw : csrWen i.csrOp i.write = true
  · rw [if_pos hw]
    by_cases hc : i.custom0 = true
    · rw [if_pos hc]; $leaf
    · rw [if_neg hc]
      by_cases hv : i.isvec = true
      · rw [if_pos hv]; $leaf
      · rw [if_neg hv]
        by_cases h1 : (i.addr == csrAddrCsrPrint) = true
        · rw [if_pos h1]; $leaf
        · rw [if_neg h1]
          by_cases h2 : (i.addr == csrAddrFflags) = true
          · rw [if_pos h2]; $leaf
          · rw [if_neg h2]
            by_cases h3 : (i.addr == csrAddrFrm) = true
            · rw [if_pos h3]; $leaf
            · rw [if_neg h3]
              by_cases h4 : (i.addr == csrAddrMstatus) = true
              · rw [if_pos h4]; $leaf
              · rw [if_neg h4]
                by_cases h5 : (i.addr == csrAddrMip) = true
                · rw [if_pos h5]; $leaf
                · rw [if_neg h5]
                  by_cases h6 : (i.addr == csrAddrMie) = true
                  · rw [if_pos h6]; $leaf
                  · rw [if_neg h6]
                    by_cases h7 : (i.addr == csrAddrMscratch) = true
                    · rw [if_pos h7]; $leaf
                    · rw [if_neg h7]
                      by_cases h8 : (i.addr == csrAddrMepc) = true
                      · rw [if_pos h8]; $leaf
                      · rw [if_neg h8]
                        by_cases h9 : (i.addr == csrAddrMcause) = true
                        · rw [if_pos h9]; $leaf
                        · rw [if_neg h9]
                          by_cases h10 : (i.addr == csrAddrMtval) = true
                          · rw [if_pos h10]; $leaf
                          · rw [if_neg h10]; $leaf
  · rw [if_neg hw]; $leaf))

-- ---- W1 读改写（:217-223） ----

theorem csrWdata_w (r x : BitVec 32) : csrWdata csrOpW r x = x := by
  csr_unfold

theorem csrWdata_s (r x : BitVec 32) : csrWdata csrOpS r x = r ||| x := by
  csr_unfold

theorem csrWdata_c (r x : BitVec 32) : csrWdata csrOpC r x = r &&& ~~~x := by
  csr_unfold

theorem csrWdata_n (r x : BitVec 32) : csrWdata csrOpN r x = 0#32 := by
  csr_unfold

-- ---- W2 读视图位规约（:125-126,145,186,188,203） ----

/-- mstatus：MIE=bit3、MPIE=bit7、MPP=3（bit11/12 恒 1），bit0/bit31 恒 0 -/
theorem csr_read_mstatus_bits (s : CsrState) :
    (csrRead s csrAddrMstatus).getLsbD 3 = s.mie ∧
    (csrRead s csrAddrMstatus).getLsbD 7 = s.mpie ∧
    (csrRead s csrAddrMstatus).getLsbD 11 = true ∧
    (csrRead s csrAddrMstatus).getLsbD 12 = true ∧
    (csrRead s csrAddrMstatus).getLsbD 0 = false ∧
    (csrRead s csrAddrMstatus).getLsbD 31 = false := by
  csr_unfold; bv_decide

/-- mip：MSIP=bit3、MTIP=bit7、MEIP=bit11，bit0 恒 0 -/
theorem csr_read_mip_bits (s : CsrState) :
    (csrRead s csrAddrMip).getLsbD 3 = s.msip ∧
    (csrRead s csrAddrMip).getLsbD 7 = s.mtip ∧
    (csrRead s csrAddrMip).getLsbD 11 = s.meip ∧
    (csrRead s csrAddrMip).getLsbD 0 = false := by
  csr_unfold; bv_decide

/-- mie：MSIE=bit3、MTIE=bit7、MEIE=bit11，bit0 恒 0 -/
theorem csr_read_mie_bits (s : CsrState) :
    (csrRead s csrAddrMie).getLsbD 3 = s.msie ∧
    (csrRead s csrAddrMie).getLsbD 7 = s.mtie ∧
    (csrRead s csrAddrMie).getLsbD 11 = s.meie ∧
    (csrRead s csrAddrMie).getLsbD 0 = false := by
  csr_unfold; bv_decide

/-- fflags：NX=bit0、UF=bit1、OF=bit2、DZ=bit3、NV=bit4，bit5 及以上恒 0 -/
theorem csr_read_fflags_bits (s : CsrState) :
    (csrRead s csrAddrFflags).getLsbD 0 = s.nx ∧
    (csrRead s csrAddrFflags).getLsbD 1 = s.uf ∧
    (csrRead s csrAddrFflags).getLsbD 2 = s.of ∧
    (csrRead s csrAddrFflags).getLsbD 3 = s.dz ∧
    (csrRead s csrAddrFflags).getLsbD 4 = s.nv ∧
    (csrRead s csrAddrFflags).getLsbD 5 = false := by
  csr_unfold; bv_decide

/-- fcsr：bit4:0=fflags、bit7:5=frm、bit8 恒 0 -/
theorem csr_read_fcsr_bits (s : CsrState) :
    (csrRead s csrAddrFcsr).getLsbD 0 = s.nx ∧
    (csrRead s csrAddrFcsr).getLsbD 4 = s.nv ∧
    (csrRead s csrAddrFcsr).getLsbD 5 = s.frm.getLsbD 0 ∧
    (csrRead s csrAddrFcsr).getLsbD 6 = s.frm.getLsbD 1 ∧
    (csrRead s csrAddrFcsr).getLsbD 7 = s.frm.getLsbD 2 ∧
    (csrRead s csrAddrFcsr).getLsbD 8 = false := by
  csr_unfold; bv_decide

/-- vtype：VILL=bit31、VMA=bit7、VTA=bit6、VSEW=bit5:3、VLMUL=bit2:0 -/
theorem csr_read_vtype_bits (s : CsrState) :
    (csrRead s csrAddrVtype).getLsbD 31 = s.vill ∧
    (csrRead s csrAddrVtype).getLsbD 7 = s.vma ∧
    (csrRead s csrAddrVtype).getLsbD 6 = s.vta ∧
    (csrRead s csrAddrVtype).extractLsb' 3 3 = s.vsew ∧
    (csrRead s csrAddrVtype).extractLsb' 0 3 = s.vlmul := by
  csr_unfold; bv_decide

-- ---- W3 读改写回环（write → 下拍 read） ----

theorem csr_mscratch_rw (s : CsrState) (v : BitVec 32) :
    csrRead (csrStep s (csrInWrite csrOpW csrAddrMscratch v)) csrAddrMscratch = v := by
  csr_unfold

theorem csr_mscratch_rs (s : CsrState) (v : BitVec 32) :
    csrRead (csrStep s (csrInWrite csrOpS csrAddrMscratch v)) csrAddrMscratch
      = s.mscratch ||| v := by
  csr_unfold

theorem csr_mscratch_rc (s : CsrState) (v : BitVec 32) :
    csrRead (csrStep s (csrInWrite csrOpC csrAddrMscratch v)) csrAddrMscratch
      = s.mscratch &&& ~~~v := by
  csr_unfold

theorem csr_mepc_rw (s : CsrState) (v : BitVec 32) :
    csrRead (csrStep s (csrInWrite csrOpW csrAddrMepc v)) csrAddrMepc = v := by
  csr_unfold

theorem csr_mcause_rw (s : CsrState) (v : BitVec 32) :
    csrRead (csrStep s (csrInWrite csrOpW csrAddrMcause v)) csrAddrMcause = v := by
  csr_unfold

theorem csr_mtval_rw (s : CsrState) (v : BitVec 32) :
    csrRead (csrStep s (csrInWrite csrOpW csrAddrMtval v)) csrAddrMtval = v := by
  csr_unfold

theorem csr_print_rw (s : CsrState) (v : BitVec 32) :
    csrRead (csrStep s (csrInWrite csrOpW csrAddrCsrPrint v)) csrAddrCsrPrint = v := by
  csr_unfold

-- ---- W4 写掩码（只读位不受写影响，:267-285） ----

/-- mstatus 写掩码：结果 = 0x1800 | (v & 0x88)，即仅 bit3/bit7 可写 -/
theorem csr_mstatus_write_mask (s : CsrState) (v : BitVec 32) :
    csrRead (csrStep s (csrInWrite csrOpW csrAddrMstatus v)) csrAddrMstatus
      = 0x1800#32 ||| (v &&& 0x88#32) := by
  csr_unfold; bv_decide

/-- mip 写掩码：仅 bit3/7/11 可写 -/
theorem csr_mip_write_mask (s : CsrState) (v : BitVec 32) :
    csrRead (csrStep s (csrInWrite csrOpW csrAddrMip v)) csrAddrMip = v &&& 0x888#32 := by
  csr_unfold; bv_decide

/-- mie 写掩码：仅 bit3/7/11 可写 -/
theorem csr_mie_write_mask (s : CsrState) (v : BitVec 32) :
    csrRead (csrStep s (csrInWrite csrOpW csrAddrMie v)) csrAddrMie = v &&& 0x888#32 := by
  csr_unfold; bv_decide

/-- frm 写掩码：只取低 3 位（Q7） -/
theorem csr_frm_write_low3 (s : CsrState) (v : BitVec 32) :
    csrRead (csrStep s (csrInWrite csrOpW csrAddrFrm v)) csrAddrFrm = v &&& 7#32 := by
  csr_unfold; bv_decide

/-- fflags 写掩码：只取低 5 位（Q7） -/
theorem csr_fflags_write_mask (s : CsrState) (v : BitVec 32) :
    csrRead (csrStep s (csrInWrite csrOpW csrAddrFflags v)) csrAddrFflags = v &&& 0x1F#32 := by
  csr_unfold; bv_decide

/-- 窄寄存器上的 CSR.S 读改写（Q7）：frm' = (zext(frm) | v) & 7 -/
theorem csr_frm_set_narrow (s : CsrState) (v : BitVec 32) :
    csrRead (csrStep s (csrInWrite csrOpS csrAddrFrm v)) csrAddrFrm
      = (BitVec.zeroExtend 32 s.frm ||| v) &&& 7#32 := by
  csr_unfold; bv_decide

-- ---- W5 写无效路径（钉死 Q1/Q2/Q3） ----

/-- Q2：写 fcsr 被静默忽略（写链无 fcsr 分支），状态不变 -/
theorem csr_fcsr_write_ignored (s : CsrState) (v : BitVec 32) :
    csrStep s (csrInWrite csrOpW csrAddrFcsr v) = s := by
  csr_unfold

/-- Q3：写 threadid（CTA 下发寄存器）被静默忽略 -/
theorem csr_threadid_write_ignored (s : CsrState) (v : BitVec 32) :
    csrStep s (csrInWrite csrOpW csrAddrThreadid v) = s := by
  csr_unfold

/-- Q3：写 vtype 被静默忽略 -/
theorem csr_vtype_write_ignored (s : CsrState) (v : BitVec 32) :
    csrStep s (csrInWrite csrOpW csrAddrVtype v) = s := by
  csr_unfold

/-- Q1：写 vl 地址被静默忽略（vl 不可写） -/
theorem csr_vl_write_ignored (s : CsrState) (v : BitVec 32) :
    csrStep s (csrInWrite csrOpW csrAddrVl v) = s := by
  csr_unfold

/-- Q1：vl 地址不在读表，读出恒 0 -/
theorem csr_vl_read_zero (s : CsrState) : csrRead s csrAddrVl = 0#32 := by
  csr_unfold

/-- Q1：isvec 分支（wen 且非 custom0 且 isvec）不写任何寄存器，状态不变 -/
theorem csr_isvec_no_state (s : CsrState) (i : CsrInputs)
    (hc : i.custom0 = false) (hv : i.isvec = true) (hcta : i.ctaValid = false) :
    csrStep s i = s := by
  cases hw : csrWen i.csrOp i.write <;> simp [csrStep, hc, hv, hcta, hw]

/-- Q6：custom_signal_0 分支只写 rpc（值为原始输入，非读改写结果） -/
theorem csr_custom0_rpc (s : CsrState) (i : CsrInputs)
    (hwen : csrWen i.csrOp i.write = true) (hc : i.custom0 = true)
    (hcta : i.ctaValid = false) :
    csrStep s i = { s with rpc := i.in1 } := by
  simp [csrStep, hwen, hc, hcta]

-- ---- W6 写回数据（:210-212,257-264） ----

/-- 非写拍（wen=0）写回数据 = csr_rdata -/
theorem csr_wb_default (s : CsrState) (op : BitVec 2) (addr : BitVec 12) (v : BitVec 32)
    (write custom0 isvec : Bool) (hw : csrWen op write = false) :
    csrWbWxdRd s op addr v write custom0 isvec = csrRead s addr := by
  simp [csrWbWxdRd, hw]

/-- wen 且 custom0：写回数据 = 输入（Q6） -/
theorem csr_wb_custom0 (s : CsrState) (op : BitVec 2) (addr : BitVec 12) (v : BitVec 32)
    (write custom0 isvec : Bool) (hw : csrWen op write = true) (hc : custom0 = true) :
    csrWbWxdRd s op addr v write custom0 isvec = v := by
  simp [csrWbWxdRd, hw, hc]

/-- wen 且 isvec（非 custom0）：写回数据 = min(AVL, VLMAX)（Q1） -/
theorem csr_wb_isvec_min (s : CsrState) (op : BitVec 2) (addr : BitVec 12) (v : BitVec 32)
    (write isvec : Bool) (hw : csrWen op write = true) (hv : isvec = true) :
    csrWbWxdRd s op addr v write false isvec
      = (if BitVec.ult v csrVLMAX then v else csrVLMAX) := by
  simp [csrWbWxdRd, hw, hv]

-- ---- W7 寄存器组隔离（Q10：写链与 CTA 链不相交） ----

/-- 无 CTA 下发时，写链不触碰 CTA 下发寄存器 -/
theorem csr_write_preserves_cta_regs (s : CsrState) (i : CsrInputs)
    (hcta : i.ctaValid = false) :
    (csrStep s i).knlBase = s.knlBase ∧ (csrStep s i).wgWfCount = s.wgWfCount ∧
    (csrStep s i).threadid = s.threadid ∧ (csrStep s i).wfTagDispatch = s.wfTagDispatch ∧
    (csrStep s i).sgprBase = s.sgprBase ∧ (csrStep s i).vgprBase = s.vgprBase ∧
    (csrStep s i).ldsBaseDispatch = s.ldsBaseDispatch ∧
    (csrStep s i).pdsBaseaddr = s.pdsBaseaddr := by
  simp only [csrStep, hcta, Bool.false_eq_true, ite_false]
  csr_tree_cases (exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- CTA 下发不触碰写链寄存器（此处以 mscratch/mstatus 位/frm/fflags 位为例） -/
theorem csr_cta_preserves_write_regs (s : CsrState) (i : CsrInputs)
    (hcta : i.ctaValid = true) (hw : i.write = false) :
    (csrStep s i).mscratch = s.mscratch ∧ (csrStep s i).mie = s.mie ∧
    (csrStep s i).mpie = s.mpie ∧ (csrStep s i).frm = s.frm ∧
    (csrStep s i).nx = s.nx ∧ (csrStep s i).csrPrint = s.csrPrint := by
  simp only [csrStep, hw, csrWen, Bool.and_false, Bool.false_eq_true, ite_false]
  (repeat' split) <;> simp

/-- D2/Q5：向量 CSR 状态是死状态，csrStep 从不更新 -/
theorem csr_step_dead_vcsr (s : CsrState) (i : CsrInputs) :
    (csrStep s i).vsew = s.vsew ∧ (csrStep s i).vlmul = s.vlmul ∧
    (csrStep s i).vill = s.vill ∧ (csrStep s i).vma = s.vma ∧
    (csrStep s i).vta = s.vta ∧ (csrStep s i).vstart = s.vstart ∧
    (csrStep s i).vl = s.vl ∧ (csrStep s i).vcsr = s.vcsr ∧
    (csrStep s i).vlenb = s.vlenb ∧ (csrStep s i).vxrm = s.vxrm ∧
    (csrStep s i).vxsat = s.vxsat := by
  simp only [csrStep]
  by_cases hcta : i.ctaValid = true
  · rw [if_pos hcta]
    csr_tree_cases (exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  · rw [if_neg hcta]
    csr_tree_cases (exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

-- ---- W8 CTA 下发出参（:296-313,315-317） ----

/-- threadid = tag 低 3 位零扩展后左移 depth_thread=5（:312） -/
theorem csr_cta_threadid (s : CsrState) (i : CsrInputs)
    (hcta : i.ctaValid = true) (hw : i.write = false) :
    (csrStep s i).threadid
      = BitVec.zeroExtend 32 (i.ctaWfTag.extractLsb' 0 3) <<< 5#32 := by
  simp [csrStep, csrWen, hcta, hw]

/-- wf_tag_dispatch = tag 低 3 位零扩展到 6 位（:302） -/
theorem csr_cta_wftag (s : CsrState) (i : CsrInputs)
    (hcta : i.ctaValid = true) (hw : i.write = false) :
    (csrStep s i).wfTagDispatch = BitVec.zeroExtend 6 (i.ctaWfTag.extractLsb' 0 3) := by
  simp [csrStep, csrWen, hcta, hw]

/-- lds_base 拼接引理（:304，D3）：Cat(LDS_BASE(31,18), x) = 0x70000000 | zext(x) -/
theorem csrLdsCat_eq (x : BitVec 18) :
    csrLdsCat x = 0x70000000#32 ||| BitVec.zeroExtend 32 x := by
  simp only [csrLdsCat, csrLdsBaseConst]; bv_decide

/-- lsu_tid 的乘法形式（:315，D3）：移位 = ×32 -/
theorem csr_lsu_tid_mul (s : CsrState) :
    csrOutLsuTid s = BitVec.zeroExtend 32 s.wfTagDispatch * 32#32 := by
  simp only [csrOutLsuTid]; bv_decide

/-- lsu_tid 上界：tag < 64 → lsu_tid < 2048，32 位无截断（D3 论证钉死） -/
theorem csr_lsu_tid_bound (s : CsrState) :
    BitVec.ult (csrOutLsuTid s) 2048#32 = true := by
  simp only [csrOutLsuTid]; bv_decide

-- ---- W9 CSRexe wid 路由（:338-355,359） ----

/-- 空拍不变性：write=false 且 ctaValid=false 时状态不变 -/
theorem csrStep_nop (s : CsrState) (i : CsrInputs)
    (hw : i.write = false) (hcta : i.ctaValid = false) :
    csrStep s i = s := by
  simp [csrStep, csrWen, hw, hcta]

/-- wid 未选中的 warp 状态不变（:354-355 独热使能） -/
theorem csrExe_untouched (f : Fin 8 → CsrState) (fire : Bool) (wid ctaWid : BitVec 3)
    (i : CsrInputs) (k : Fin 8)
    (h1 : (wid == BitVec.ofNat 3 k.val) = false)
    (h2 : (ctaWid == BitVec.ofNat 3 k.val) = false) :
    csrExeStep f fire wid ctaWid i k = f k := by
  simp only [csrExeStep, csrPerWarpInput, h1, h2, Bool.and_false]
  apply csrStep_nop <;> rfl

/-- wid 选中的 warp 获得 write=fire 的输入 -/
theorem csrExe_touched (f : Fin 8 → CsrState) (ctaWid : BitVec 3)
    (i : CsrInputs) (k : Fin 8) (wid : BitVec 3)
    (hk : wid = BitVec.ofNat 3 k.val) :
    csrExeStep f true wid ctaWid i k
      = csrStep (f k) { i with
          write := true
          ctaValid := i.ctaValid && (ctaWid == BitVec.ofNat 3 k.val) } := by
  subst hk
  simp [csrExeStep, csrPerWarpInput]

/- ========================================================================= -/
/- 10. 公理审计（关键定理；bv_decide 会引入每个定理私有的 LRAT 检查           -/
/-     trust 公理，形如 `…._native.bv_decide.ax_…`，归档时注明）              -/
/- ========================================================================= -/

#print axioms csrWdata_s
#print axioms csr_read_mstatus_bits
#print axioms csr_read_fcsr_bits
#print axioms csr_mscratch_rw
#print axioms csr_mstatus_write_mask
#print axioms csr_frm_set_narrow
#print axioms csr_fcsr_write_ignored
#print axioms csr_vl_write_ignored
#print axioms csr_isvec_no_state
#print axioms csr_custom0_rpc
#print axioms csr_write_preserves_cta_regs
#print axioms csr_step_dead_vcsr
#print axioms csr_cta_threadid
#print axioms csrLdsCat_eq
#print axioms csr_lsu_tid_mul
#print axioms csrExe_untouched

end Ventus.Arith
