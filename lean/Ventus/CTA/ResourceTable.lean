/- ========================================================================= -/
/-                      CTA/ResourceTable.lean                                -/
/-  CTA 资源表（resource_table.scala）的 Lean 4 模型：WG 槽位资源链表、        -/
/-  分配基址生成（FIND）、摘除（DEALLOC）、空段扫描（SCAN/rtcache）            -/
/-                                                                           -/
/-  Chisel 源码对照：                                                         -/
/-    opengpgpu/original/ventus-gpgpu/ventus/src/cta/resource_table.scala     -/
/-    （io_rtram :61-74；resource_table_handler :76-572——ALLOC 查找            -/
/-    :241-407、WRITE :344-385、DEALLOC :412-444、SCAN :449-517、             -/
/-    OUTPUT :522-525；resource_table_ram :574-615；                          -/
/-    resource_table_top :620-877）                                           -/
/-  参数（top/parameters.scala）：NUM_CU=2 (:167)、NUM_WG_SLOT=8 (:169)、      -/
/-    NUM_LDS_MAX=131072 (:180, 2^17)、NUM_SGPR_MAX=2048 (:181, 2^11)、       -/
/-    NUM_VGPR_MAX=1024 (:182, 2^10)、RESOURCE_TABLE.NUM_RESULT=2 (:195)、    -/
/-    DEBUG=true (:197)。resource_table_top 以默认 NUM_CU_PER_GROUP=1 例化    -/
/-    （cta_scheduler.scala:119）⇒ NUM_HANDLER=2、每 handler 绑定 1 个 rtram。-/
/-                                                                           -/
/-  本文件核销 CtaScheduler.lean 黑盒契约中的：                               -/
/-    H-RT-BOUNDS   （rt_alloc_base_bounds：分配区间在界内）                  -/
/-    H-RT-DISJOINT （rt_alloc_disjoint / rt_step_wf：活跃分配两两不交）      -/
/-  外加分配-回收守恒（rt_alloc_used / rt_dealloc_used / rt_sum_le_N）与      -/
/-  rtcache 一致性（rtScan_max / rt_scan_ge_iff / rt_find_of_scan）。          -/
/-                                                                           -/
/- ======================== 建模决策 / 对 Chisel 的偏离点 ==================== -/
/-  D1. 单 handler+rtram 对、对资源总量 N 参数化建模。lds/sgpr/vgpr 三路       -/
/-      handler 同构且互不共享状态（:660-665 各自独立例化）；NUM_CU_PER_GROUP -/
/-      =1 时 handler↔rtram 一一绑定（:677-679 注释），top 层只剩路由连线。   -/
/-      DecoupledIO_1_to_3（utils.scala:113-146）保证三路各自恰好收到一次     -/
/-      同一 alloc/dealloc（ign 位门控 dealloc，:785-795），属 utils 范畴。   -/
/-  D2. FIND/SCAN 的 3 级流水（:282-299, :458-467）抽象为对段 0..cnt 的       -/
/-      顺序 fold。论证：流水的第 3 级是**组合**计算（:300-311），其输入      -/
/-      （init/finish/valid 标志与 addr1/addr2 读数据）恰是"段 i 的           -/
/-      边界"，逐拍打拍不改变每个段被判定一次、判定式相同的语义；             -/
/-      fsm_a_cnt 从 0 计到 cnt（:313, :400）恰好覆盖 cnt+1 个段，            -/
/-      结果在离开 FIND 前全部落寄存器（:306-311 是寄存器赋值）。              -/
/-      时序/握手（ready/valid、CONNECT 状态、抢占 :137-145/:403）抽象为      -/
/-      事件：alloc 完成 = WRITE_OUTPUT 的链表写入+baseaddr 输出，            -/
/-      dealloc = fsm_d==1 的摘除写入。                                       -/
/-  D3. 地址/尺寸用 Nat（同 CtaScheduler D3）：在 RtWf 不变式下所有地址        -/
/-      < N ≤ 2^17，硬件位宽 log2Ceil(N)（地址）/log2Ceil(N+1)（尺寸）足够。  -/
/-      唯一的回绕点由 rt_bw_* 系列定理在位向量层面钉死：空表段长              -/
/-      (N-1) - (~0) ≡ N (mod 2^(log2 N+1))（:302-304）与哨兵 +1 ≡ 0         -/
/-      （:302, :307）；addr2 写入 base+size-1 不截断（rt_bw_addr2_fits）。  -/
/-  D4. Chisel 的 DontCare 建模为"保持旧值"：仅出现于尾节点的 next、          -/
/-      头节点的 prev、cnt=0 时的 head/tail（:271-274, :337-338 与             -/
/-      dealloc 的 fsm_d_next/fsm_d_prev）——这些位次在 RtWf 下永不被读        -/
/-      （遍历只走 cnt 步即停），本文件的 wf 保持定理即为该结论的形式化。     -/
/-  D5. resource_table_ram 的 SyncReadMem（:583-586）读延迟 1 拍抽象为        -/
/-      状态上的组合读；rtram 写使能由 io.en（:576 起）门控，事件模型中       -/
/-      handler 选中的那张表就是操作对象。valid/wgid 调试阵列（:605-613）     -/
/-      与 DEBUG 断言（:323, :373, :385, :436-437, :613）不建模，             -/
/-      其对应性质由定理承担。                                                -/
/-  D6. wgsize=0 的 alloc 不插表、输出 base=0（:352-369 的 !(wgsize===0.U)   -/
/-      门控 + :400 跳过扫描 + :270/:336 的 found_addr 清零）。               -/
/-  D7. sort3（utils.scala:53-95，注释称 out(0) 最大）在建模中以 max/mid      -/
/-      数学描述；位级正确性由 rt_sort3_*（bv_decide，12bit 抽查）钉死。      -/
/-      SCAN 只用到 out(0)/out(1)（:478-484 丢弃 out(2)）。                   -/
/-  D8. NUM_RT_RESULT=2 ⇒ rtcache 只保留最大两段；本文件证明                  -/
/-      rtcache(0) = 最大空段长（rt_scan_max）。                              -/
/-                                                                           -/
/- ======================== 源码审查疑点（上报主会话） ======================= -/
/-  Q1【I 类候选，轻微】:429-430 `rtram_dealloc.addr2.wr.en := false.B`       -/
/-      重复两行，dealloc 簇的 addr1.wr.en 从未驱动（:170 WireInit DontCare   -/
/-      兜底）；同理 SCAN 簇（:171）的全部 wr.en 从未驱动，经 :172-178 的     -/
/-      MUX 在 SCAN 态直连 io.rtram_data。功能正确性依赖 firtir 把 DontCare   -/
/-      常量化为 0 的惯例——语义上是"设计者对写使能断都不在乎"，但写入是       -/
/-      有副作用的。建议补上 `rtram_scan.*.wr.en := false.B` 与               -/
/-      `rtram_dealloc.addr1.wr.en := false.B`。                             -/
/-  Q2【III 类，整洁】:246 `fsm_a_found_ok` 是死信号（:315 赋值后无任何       -/
/-      读者），:314 注释说"pipeline 下一拍出结果"靠的其实是 :400 的           -/
/-      fsm_a_cnt > cnt 条件。无功能影响。                                    -/
/-  Q3【核对无误】:385 assert（head_flag ↔ found_addr==0）：选中段是段 0       -/
/-      ⇒ base=lo=0 ✓；base=0 ⇒ 段 0 或空表初值 ⇒ head_flag=true ✓。          -/
/-  Q4【I 类后果面定量，接 CtaScheduler Q4】H-ALLOC-FIT 缺位即链表腐蚀：      -/
/-      若不存在 ≥wgsize 的空段且 cnt>0，found_* 保持初值（addr=0、           -/
/-      head=tail=true，:268-276），WRITE 把新节点以 addr1=0/addr2=wgsize-1   -/
/-      插为头+尾并 cnt+1（:352-369），旧节点成为孤儿且区间重叠。             -/
/-      DEBUG 断言 :323 只在仿真抓。本文件 T7（rtFull/rtCorrupt）给出具体 witness。-/
/-  Q5【跨模块，接 CtaScheduler Q4】SCAN/OUTPUT 可被同 CU 的 alloc 抢占       -/
/-      （:137-138 alloc.ready 含 SCAN/OUTPUT，:560/:567 直接跳转）⇒ 被抢     -/
/-      的 rtcache_update 丢弃；随后 ALLOC→SCAN→OUTPUT 会补发反映最新状态     -/
/-      的扫描。窗口期内 allocator 的 rtcache 是旧值——H-ALLOC-FIT 的          -/
/-      时序一致性属 allocator 侧债务（rt 侧职责：每次 OUTPUT 的内容都准确，  -/
/-      本文件 rt_scan_ge_iff / rt_find_of_scan 核销此半）。                   -/
/-  Q6【I-11 触发面证据】sgpr 路 N=2048，rt 输出 base ∈ [0, N-wgsize] 任意    -/
/-      值均合法，≥1024 完全可能：T8（rtI11）给出 base=1792 的               -/
/-      witness（单节点占 [0,1792)，再分 256 ⇒ gap 恰在 1792）。rt 侧无任何   -/
/-      <1024 的限制 ⇒ collector 侧若按 10bit 处理 sgpr base 必回绕，         -/
/-      触发面覆盖"低区被占后的任意大 base 分配"。vgpr 路 N=1024 ⇒            -/
/-      base ≤ 1023，不涉及。                                                -/
/-  Q7【边界，契约承担】cnt 宽 log2Ceil(9)=4bit，cnt=8 时再 alloc 得 cnt=9     -/
/-      不溢出寄存器但超出 NUM_WG_SLOT 语义（链表遍历前提崩溃）。依赖          -/
/-      allocator 的 H-ALLOC-SLOT（无空槽则不分配），本模型契约                -/
/-      rtEventOk 以 cnt < 8 显式承担。                                       -/
/-  Q8【契约外行为】dealloc 目标不在链表中时（H-CUIF-DEALLOC 保证不发生，    -/
/-      DEBUG 断言 :436-437 守仿真），硬件按 prev/next[wgslot] 的野值写坏     -/
/-      相邻节点；本模型此时步进为"不变"（rtFindSlot = none），差异仅在       -/
/-      契约不可达区域。                                                      -/
/- ========================================================================= -/

import Std.Tactic.BVDecide

namespace Ventus.CTA

set_option linter.unusedVariables false

/- ========================================================================= -/
/- 1. 参数与位宽保真                                                           -/
/- ========================================================================= -/

def rtNUM_WG_SLOT : Nat := 8          -- parameters.scala:169
def rtNUM_LDS : Nat := 131072         -- :180, sharemem_size = 2^17
def rtNUM_SGPR : Nat := 2048          -- :181, 256*num_warp = 2^11
def rtNUM_VGPR : Nat := 1024          -- :182, 128*num_warp = 2^10
def rtNUM_RT_RESULT : Nat := 2        -- :195

/-- RT-BW1a 空表段长回绕（:302-304）：12bit 下 (2047) - (~0=4095) ≡ 2048 = N。
    FIND/SCAN 对空表算出的段长经回绕恰好等于整个资源——Nat 模型直接取 N 的合法依据。 -/
theorem rt_bw_empty_size_sgpr : (2047#12 - 4095#12) = 2048#12 := by decide
/-- RT-BW1b vgpr 路同型（11bit） -/
theorem rt_bw_empty_size_vgpr : (1023#11 - 2047#11) = 1024#11 := by decide
/-- RT-BW1c lds 路同型（18bit） -/
theorem rt_bw_empty_size_lds : (131071#18 - 262143#18) = 131072#18 := by decide

/-- RT-BW2 段首哨兵 +1 回绕（:302 的 addr1 := ~0，:307 的 found_addr := addr1+1）：
    12bit 下 4095+1 ≡ 0，即"段 0 的基址 = 0"。Nat 模型 rtGapLo 0 = 0 的合法依据。 -/
theorem rt_bw_sentinel_succ_sgpr : (4095#12 + 1#12) = 0#12 := by decide
theorem rt_bw_sentinel_succ_vgpr : (2047#11 + 1#11) = 0#11 := by decide
theorem rt_bw_sentinel_succ_lds : (262143#18 + 1#18) = 0#18 := by decide

/-- RT-BW3 addr2 写入不截断（:369：addr2 := base+size-1，log2Ceil(N) 位）：
    在界内（base+size ≤ N）且非空（1 ≤ size）时结果 < N，N 为 2 的幂故装得下。 -/
theorem rt_bw_addr2_fits (N base size : Nat) (hbs : base + size ≤ N) (hs : 1 ≤ size) :
    base + size - 1 < N := by omega

/-- RT-BW4 基址本身不截断（:98 baseaddr.addr 为 log2Ceil(N) 位）：非空分配 base < N。 -/
theorem rt_bw_base_fits (N base size : Nat) (hbs : base + size ≤ N) (hs : 1 ≤ size) :
    base < N := by omega

/-  sort3（utils.scala:53-95）位级抽查：12bit（sgpr 尺寸宽度）。
    Mux1H 在独热时等价于优先级选择；独热性一并验证。 -/
def rtSort3Circ (a b c : BitVec 12) : BitVec 12 × BitVec 12 × BitVec 12 :=
  let cmp0 := a > b  -- res(0)(0)
  let cmp1 := b > c  -- res(1)(0)
  let cmp2 := c > a  -- res(2)(0)
  let r00 := cmp0; let r01 := !cmp2
  let r10 := cmp1; let r11 := !cmp0
  let r20 := cmp2; let r21 := !cmp1
  let out0 := if r00 && r01 then a
              else if r10 && r11 then b
              else if r20 && r21 then c
              else a   -- !(res(0)(0)||res(1)(0)||res(2)(0)) 的默认支（全相等时命中）
  let out1 := if (r00 ^^ r01) then a
              else if (r10 ^^ r11) then b
              else if (r20 ^^ r21) then c
              else 0#12
  let out2 := if !r00 && !r01 then a
              else if !r10 && !r11 then b
              else if !r20 && !r21 then c
              else a   -- utils.scala:86 的第四条件（全相等时命中，输出 in(0)）
  (out0, out1, out2)

/-- RT-SORT3-1 独热性：out0 的选择条件至多一个为真（Mux1H 合法） -/
theorem rt_sort3_onehot0 (a b c : BitVec 12) :
    ¬ ((a > b) && !(c > a) && ((b > c) && !(a > b))) ∧
    ¬ ((a > b) && !(c > a) && ((c > a) && !(b > c))) ∧
    ¬ ((b > c) && !(a > b) && ((c > a) && !(b > c))) := by
  bv_decide

/-- RT-SORT3-2 功能正确：out0 = max，out1 = median（= 两两 min 的 max） -/
theorem rt_sort3_out (a b c : BitVec 12) :
    (rtSort3Circ a b c).1 = (if b ≤ a then if c ≤ a then a else c else if c ≤ b then b else c) ∧
    (rtSort3Circ a b c).2.1 =
      (let mab := if a ≤ b then a else b
       let mbc := if b ≤ c then b else c
       let mac := if a ≤ c then a else c
       if mbc ≤ mab then if mac ≤ mab then mab else mac
       else if mac ≤ mbc then mbc else mac) := by
  unfold rtSort3Circ
  bv_decide

/- ========================================================================= -/
/- 2. 资源表 RAM 抽象状态与链表遍历                                            -/
/- ========================================================================= -/

/-- rtram 的抽象状态（io_rtram :61-74 + resource_table_ram :574-615）。
    prev/next/addr1/addr2 是 SyncReadMem，cnt/head/tail 是寄存器。
    地址用 Nat（D3）；槽位号 Fin 8（NUM_WG_SLOT=8）。 -/
structure RtRam where
  cnt : Nat                      -- 链表中 WG 数（:68, :580）
  head : Fin 8                   -- 链表首槽（:69, :581）
  tail : Fin 8                   -- 链表尾槽（:70, :582）
  next : Fin 8 → Fin 8           -- 按资源地址序的后继指针（:64, :584）
  prev : Fin 8 → Fin 8           -- 前驱指针（:63, :583）
  addr1 : Fin 8 → Nat            -- 各 WG 的基址（:65, :585）
  addr2 : Fin 8 → Nat            -- 各 WG 的末址（:66, :586）

/-- 从 head 沿 next 走 i 步（硬件 FIND/SCAN 的遍历，:289-294/:459-464） -/
def rtWalk (next : Fin 8 → Fin 8) (hd : Fin 8) : Nat → Fin 8
  | 0 => hd
  | (i+1) => next (rtWalk next hd i)

/-- 本 ram 的链表遍历 -/
def RtRam.walk (ram : RtRam) (i : Nat) : Fin 8 := rtWalk ram.next ram.head i

/-- 链表良构不变式：遍历 cnt 步内地址严格升序、区间在界内、prev 与 next 互逆、
    tail 指向末节点。head ≡ walk 0 由定义保证。 -/
structure RtWf (ram : RtRam) (N : Nat) : Prop where
  npos : 0 < N
  cntLe : ram.cnt ≤ rtNUM_WG_SLOT
  bounds : ∀ i, i < ram.cnt →
    ram.addr1 (ram.walk i) ≤ ram.addr2 (ram.walk i) ∧ ram.addr2 (ram.walk i) < N
  sorted : ∀ i, i + 1 < ram.cnt → ram.addr2 (ram.walk i) < ram.addr1 (ram.walk (i+1))
  prevOk : ∀ i, i + 1 < ram.cnt → ram.prev (ram.walk (i+1)) = ram.walk i
  tailOk : 0 < ram.cnt → ram.walk (ram.cnt - 1) = ram.tail

@[simp] theorem rtWalk_zero (next hd) : rtWalk next hd 0 = hd := rfl
@[simp] theorem rtWalk_succ (next hd i) : rtWalk next hd (i+1) = next (rtWalk next hd i) := rfl

/-- 单点更新（建模 rtram 的写口） -/
def rtSet (f : Fin 8 → α) (a : Fin 8) (v : α) : Fin 8 → α :=
  fun x => if x = a then v else f x

@[simp] theorem rtSet_eq (f : Fin 8 → α) (a : Fin 8) (v : α) : rtSet f a v a = v := by
  simp [rtSet]

@[simp] theorem rtSet_ne (f : Fin 8 → α) {a x : Fin 8} (h : x ≠ a) (v : α) :
    rtSet f a v x = f x := by simp [rtSet, h]

/-- addr1 沿链表严格递增（跨度形式，便于归纳） -/
theorem rt_addr1_strict_aux (ram : RtRam) (N : Nat) (hwf : RtWf ram N) :
    ∀ d i, i + d + 1 < ram.cnt → ram.addr1 (ram.walk i) < ram.addr1 (ram.walk (i+d+1))
  | 0, i, h => by
    have hb := (hwf.bounds i (by omega)).1
    have hs := hwf.sorted i h
    have e : i + 0 + 1 = i + 1 := rfl
    rw [e]
    omega
  | d+1, i, h => by
    have ih := rt_addr1_strict_aux ram N hwf d i (by omega)
    have hb := (hwf.bounds (i+d+1) (by omega)).1
    have hs := hwf.sorted (i+d+1) (by omega)
    have e : i + (d+1) + 1 = i + d + 1 + 1 := rfl
    rw [e]
    omega

/-- addr1 严格单调（一般形式） -/
theorem rt_addr1_strict (ram : RtRam) (N : Nat) (hwf : RtWf ram N) {i j : Nat}
    (hij : i < j) (hj : j < ram.cnt) : ram.addr1 (ram.walk i) < ram.addr1 (ram.walk j) := by
  have h := rt_addr1_strict_aux ram N hwf (j - i - 1) i (by omega)
  have e : i + (j - i - 1) + 1 = j := by omega
  rw [e] at h
  exact h

/-- addr1 单调（≤ 形式） -/
theorem rt_addr1_mono (ram : RtRam) (N : Nat) (hwf : RtWf ram N) {i j : Nat}
    (hij : i ≤ j) (hj : j < ram.cnt) : ram.addr1 (ram.walk i) ≤ ram.addr1 (ram.walk j) := by
  rcases Nat.eq_or_lt_of_le hij with h | h
  · rw [h]; exact Nat.le_refl _
  · exact Nat.le_of_lt (rt_addr1_strict ram N hwf h hj)

/-- 跨节点：前者的末址 < 后者的基址 -/
theorem rt_addr2_lt_addr1 (ram : RtRam) (N : Nat) (hwf : RtWf ram N) {i j : Nat}
    (hij : i < j) (hj : j < ram.cnt) : ram.addr2 (ram.walk i) < ram.addr1 (ram.walk j) := by
  have hs := hwf.sorted i (by omega)
  have hm := rt_addr1_mono ram N hwf (show i + 1 ≤ j by omega) hj
  omega

/-- 遍历在 cnt 步内单射（节点互不相同）——H-RT-DISJOINT 与指针手术正确性的支点 -/
theorem rt_walk_inj (ram : RtRam) (N : Nat) (hwf : RtWf ram N) {i j : Nat}
    (hi : i < ram.cnt) (hj : j < ram.cnt) (h : ram.walk i = ram.walk j) : i = j := by
  rcases Nat.lt_trichotomy i j with h1 | h1 | h1
  · exact absurd (rt_addr1_strict ram N hwf h1 hj) (by rw [h]; exact Nat.lt_irrefl _)
  · exact h1
  · exact absurd (rt_addr1_strict ram N hwf h1 hi) (by rw [h]; exact Nat.lt_irrefl _)

/- ========================================================================= -/
/- 3. 空段（gap）定义与基本性质                                                -/
/-    段 i（0 ≤ i ≤ cnt）：链表第 i-1 个节点之后、第 i 个节点之前的空闲区间   -/
/-    对应硬件 :301-304：addr1 = 段首-1（段 0 取哨兵 ~0），addr2 = 段末       -/
/- ========================================================================= -/

/-- 段 i 的基址（含）：段 0 为 0，否则为前节点末址+1 -/
def rtGapLo (ram : RtRam) (i : Nat) : Nat :=
  if i = 0 then 0 else ram.addr2 (ram.walk (i-1)) + 1

/-- 段 i 的末址（不含）：段 cnt 为 N，否则为后节点基址 -/
def rtGapHi (ram : RtRam) (N i : Nat) : Nat :=
  if i = ram.cnt then N else ram.addr1 (ram.walk i)

/-- 段 i 的长度（硬件 :304 的 addr2-addr1；回绕等价性见 rt_bw_*） -/
def rtGapSize (ram : RtRam) (N i : Nat) : Nat := rtGapHi ram N i - rtGapLo ram i

@[simp] theorem rtGapLo_zero (ram : RtRam) : rtGapLo ram 0 = 0 := by simp [rtGapLo]

theorem rtGapLo_succ (ram : RtRam) (i : Nat) :
    rtGapLo ram (i+1) = ram.addr2 (ram.walk i) + 1 := by
  simp [rtGapLo]

theorem rtGapHi_of_lt (ram : RtRam) (N : Nat) {i : Nat} (h : i < ram.cnt) :
    rtGapHi ram N i = ram.addr1 (ram.walk i) := by simp [rtGapHi, Nat.ne_of_lt h]

theorem rtGapHi_cnt (ram : RtRam) (N : Nat) : rtGapHi ram N ram.cnt = N := by simp [rtGapHi]

/-- 段非负：基址 ≤ 末址（减法是真实减法） -/
theorem rt_gapLo_le_hi (ram : RtRam) (N : Nat) (hwf : RtWf ram N) {i : Nat}
    (hi : i ≤ ram.cnt) : rtGapLo ram i ≤ rtGapHi ram N i := by
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    simp [rtGapLo]
  · by_cases hc : i = ram.cnt
    · subst hc
      have hb := (hwf.bounds (ram.cnt - 1) (by omega)).2
      simp [rtGapLo, rtGapHi, Nat.ne_of_gt h0]
      omega
    · have hb := hwf.sorted (i-1) (by omega)
      have e : i - 1 + 1 = i := by omega
      rw [e] at hb
      simp [rtGapLo, rtGapHi, hc, Nat.ne_of_gt h0]
      omega

/-- cnt > 0 时任何空段严格小于 N（至少一个节点占了 ≥1 个地址）——
    FIND 成功性论证的关键（:268-276 初值 found_size=N 会被任何真实空段击败） -/
theorem rt_gapSize_lt_N (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    (hcnt : 0 < ram.cnt) {i : Nat} (hi : i ≤ ram.cnt) :
    rtGapSize ram N i < N := by
  have hle := rt_gapLo_le_hi ram N hwf hi
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    have hc : ¬ (0 = ram.cnt) := by omega
    have hb := hwf.bounds 0 (by omega)
    simp only [rtGapSize, rtGapHi, hc, ↓reduceIte, rtGapLo, ↓reduceIte, Nat.sub_zero]
    omega
  · by_cases hc : i = ram.cnt
    · subst hc
      have hb := (hwf.bounds (ram.cnt - 1) (by omega)).2
      have h0' : ¬ (ram.cnt = 0) := by omega
      simp only [rtGapSize, rtGapHi, ↓reduceIte, rtGapLo, h0', ↓reduceIte]
      omega
    · have hb := (hwf.bounds i (by omega)).2
      have hb1 := (hwf.bounds i (by omega)).1
      simp only [rtGapSize, rtGapHi, hc, ↓reduceIte, rtGapLo, Nat.ne_of_gt h0, ↓reduceIte]
      omega
/- ========================================================================= -/
/- 4. FIND：最小适配空段查找（:241-341 的顺序 fold 抽象，D2）                  -/
/- ========================================================================= -/

/-- FIND 的累加器：当前最优段（长、基址、段号）+ 是否已选中过真实段。
    对应 fsm_a_found_size/addr/ptr/head_flag/tail_flag（:247-253）：
    fk=i 与 head_flag=(i=0)、tail_flag=(i=cnt) 等价（段号唯一确定两标志）。 -/
structure RtAcc where
  fsize : Nat
  faddr : Nat
  fk : Nat
  upd : Bool

/-- FIND 的单步更新（:305-311）：段 i 能容下且比当前最优小 ⇒ 改选段 i -/
def rtFindStep (ram : RtRam) (N wgsize : Nat) (acc : RtAcc) (i : Nat) : RtAcc :=
  if wgsize ≤ rtGapSize ram N i ∧ rtGapSize ram N i < acc.fsize then
    ⟨rtGapSize ram N i, rtGapLo ram i, i, true⟩ else acc

/-- 从段 i 起、再走 fuel 步的 fold（硬件 fsm_a_cnt 从 0 计到 cnt，:313/:400） -/
def rtFindGo (ram : RtRam) (N wgsize : Nat) : Nat → Nat → RtAcc → RtAcc
  | 0, _, acc => acc
  | (f+1), i, acc => rtFindGo ram N wgsize f (i+1) (rtFindStep ram N wgsize acc i)

/-- 完整 FIND：段 0..cnt 共 cnt+1 个段；初值 = "整张表"假设（:268-276） -/
def rtFind (ram : RtRam) (N wgsize : Nat) : RtAcc :=
  rtFindGo ram N wgsize (ram.cnt + 1) 0 ⟨N, 0, 0, false⟩

theorem rtFindGo_zero (ram : RtRam) (N wgsize i : Nat) (acc : RtAcc) :
    rtFindGo ram N wgsize 0 i acc = acc := rfl

theorem rtFindGo_succ (ram : RtRam) (N wgsize f i : Nat) (acc : RtAcc) :
    rtFindGo ram N wgsize (f+1) i acc =
      rtFindGo ram N wgsize f (i+1) (rtFindStep ram N wgsize acc i) := rfl

/-- 累加器良好性：处理完 processed 个段后，upd 记录的是一个真实段的信息；
    未 upd 时保持初值 fsize=N。 -/
def rtAccOk (ram : RtRam) (N wgsize processed : Nat) (acc : RtAcc) : Prop :=
  acc.fsize ≤ N ∧
  (acc.upd = false → acc.fsize = N) ∧
  (acc.upd = true → acc.fk < processed ∧ acc.faddr = rtGapLo ram acc.fk ∧
    acc.fsize = rtGapSize ram N acc.fk ∧ wgsize ≤ acc.fsize)

theorem rtFindGo_ok (ram : RtRam) (N wgsize : Nat) (hwf : RtWf ram N) :
    ∀ f i acc, i + f ≤ ram.cnt + 1 → rtAccOk ram N wgsize i acc →
      rtAccOk ram N wgsize (i + f) (rtFindGo ram N wgsize f i acc)
  | 0, i, acc, _, hacc => by
      rw [rtFindGo_zero]
      exact hacc
  | (f+1), i, acc, hside, hacc => by
    have hi : i ≤ ram.cnt := by omega
    have hstep : rtAccOk ram N wgsize (i+1) (rtFindStep ram N wgsize acc i) := by
      obtain ⟨hN, hfalse, htrue⟩ := hacc
      unfold rtFindStep
      by_cases hc : wgsize ≤ rtGapSize ram N i ∧ rtGapSize ram N i < acc.fsize
      · rw [if_pos hc]
        refine ⟨?_, by simp, ?_⟩
        · by_cases hic : i = ram.cnt
          · subst hic
            simp [rtGapSize, rtGapHi]
          · have hb := (hwf.bounds i (by omega)).1
            have hb2 := (hwf.bounds i (by omega)).2
            simp only [rtGapSize, rtGapHi, hic, ↓reduceIte]
            omega
        · intro _
          exact ⟨Nat.lt_succ_self i, rfl, rfl, hc.1⟩
      · rw [if_neg hc]
        refine ⟨hN, hfalse, ?_⟩
        intro hup
        obtain ⟨h1, h2, h3, h4⟩ := htrue hup
        exact ⟨Nat.lt_succ_of_lt h1, h2, h3, h4⟩
    rw [rtFindGo_succ]
    have hrec := rtFindGo_ok ram N wgsize hwf f (i+1) (rtFindStep ram N wgsize acc i)
      (by omega) hstep
    have e : i + 1 + f = i + (f + 1) := by omega
    rw [e] at hrec
    exact hrec

/-- RT-F1 FIND 结果的良好性（整体版） -/
theorem rtFind_ok (ram : RtRam) (N wgsize : Nat) (hwf : RtWf ram N) :
    rtAccOk ram N wgsize (ram.cnt + 1) (rtFind ram N wgsize) := by
  have hinit : rtAccOk ram N wgsize 0 ⟨N, 0, 0, false⟩ :=
    ⟨Nat.le_refl N, fun _ => rfl, fun h => by simp at h⟩
  have h := rtFindGo_ok ram N wgsize hwf (ram.cnt + 1) 0 ⟨N, 0, 0, false⟩ (by omega) hinit
  rw [Nat.zero_add] at h
  exact h

/-- RT-F2 选中段的完整信息（upd=true 时） -/
theorem rtFind_upd (ram : RtRam) (N wgsize : Nat) (hwf : RtWf ram N)
    (h : (rtFind ram N wgsize).upd = true) :
    (rtFind ram N wgsize).fk ≤ ram.cnt ∧
    (rtFind ram N wgsize).faddr = rtGapLo ram (rtFind ram N wgsize).fk ∧
    (rtFind ram N wgsize).fsize = rtGapSize ram N (rtFind ram N wgsize).fk ∧
    wgsize ≤ (rtFind ram N wgsize).fsize := by
  have hok := rtFind_ok ram N wgsize hwf
  obtain ⟨_, _, htrue⟩ := hok
  obtain ⟨h1, h2, h3, h4⟩ := htrue h
  exact ⟨Nat.lt_succ_iff.mp h1, h2, h3, h4⟩

/-- fold 保持 upd=true -/
theorem rtFindGo_upd_mono (ram : RtRam) (N wgsize : Nat) :
    ∀ f i acc, acc.upd = true → (rtFindGo ram N wgsize f i acc).upd = true
  | 0, _, _, h => by rw [rtFindGo_zero]; exact h
  | (f+1), i, acc, h => by
    rw [rtFindGo_succ]
    apply rtFindGo_upd_mono ram N wgsize f (i+1)
    unfold rtFindStep
    by_cases hc : wgsize ≤ rtGapSize ram N i ∧ rtGapSize ram N i < acc.fsize
    · rw [if_pos hc]
    · rw [if_neg hc]; exact h

/-- RT-F3 FIND 成功性：存在能容下的空段且表非空 ⇒ 必选中某个真实段
    （:262-267 注释承诺"一定能找到"的实现依据；前提是 allocator 的 H-ALLOC-FIT） -/
theorem rtFindGo_success (ram : RtRam) (N wgsize : Nat) (hwf : RtWf ram N)
    (hcnt : 0 < ram.cnt) :
    ∀ f i acc, i + f ≤ ram.cnt + 1 → (acc.upd = false → acc.fsize = N) →
      (∃ j, i ≤ j ∧ j < i + f ∧ wgsize ≤ rtGapSize ram N j) →
      (rtFindGo ram N wgsize f i acc).upd = true
  | 0, i, acc, _, _, hex => by
    obtain ⟨j, hj0, hj1, _⟩ := hex
    omega
  | (f+1), i, acc, hside, hacc, hex => by
    by_cases hup : acc.upd = true
    · rw [rtFindGo_succ]
      apply rtFindGo_upd_mono
      unfold rtFindStep
      by_cases hc : wgsize ≤ rtGapSize ram N i ∧ rtGapSize ram N i < acc.fsize
      · rw [if_pos hc]
      · rw [if_neg hc]; exact hup
    · have hup' : acc.upd = false := by
        cases hb : acc.upd with
        | false => rfl
        | true => exact absurd hb hup
      have hfN := hacc hup'
      by_cases hc : wgsize ≤ rtGapSize ram N i ∧ rtGapSize ram N i < acc.fsize
      · -- 本步更新 ⇒ upd 单调保持
        rw [rtFindGo_succ]
        apply rtFindGo_upd_mono
        unfold rtFindStep
        rw [if_pos hc]
      · -- 本步不更新 ⇒ 拟合段必在 i+1 之后（j=i 时步进条件必真，矛盾）
        obtain ⟨j, hj0, hj1, hj2⟩ := hex
        have hj : i < j := by
          rcases Nat.eq_or_lt_of_le hj0 with h | h
          · subst h
            exfalso
            apply hc
            have hlt : rtGapSize ram N i < N :=
              rt_gapSize_lt_N ram N hwf hcnt (by omega)
            exact ⟨hj2, by omega⟩
          · exact h
        rw [rtFindGo_succ]
        have hstep : rtFindStep ram N wgsize acc i = acc := by
          unfold rtFindStep
          rw [if_neg hc]
        rw [hstep]
        apply rtFindGo_success ram N wgsize hwf hcnt f (i+1) acc (by omega) hacc
        exact ⟨j, by omega, by omega, hj2⟩

/-- RT-F3' 整体版：存在拟合空段 ⇒ FIND 必有所获（cnt=0 时初值即正解，见 rtFind_empty） -/
theorem rtFind_success (ram : RtRam) (N wgsize : Nat) (hwf : RtWf ram N)
    (hcnt : 0 < ram.cnt)
    (hex : ∃ j, j ≤ ram.cnt ∧ wgsize ≤ rtGapSize ram N j) :
    (rtFind ram N wgsize).upd = true := by
  obtain ⟨j, hj0, hj1⟩ := hex
  apply rtFindGo_success ram N wgsize hwf hcnt (ram.cnt + 1) 0 ⟨N, 0, 0, false⟩
    (by omega) (fun _ => rfl)
  exact ⟨j, by omega, by omega, hj1⟩

/-- 空表的 FIND 保持初值（段 0 长度 = N 不严格小于初值 N，:269-276 注释的
    "unless rtram.cnt==0 and the initial assumption is correct"） -/
theorem rtFind_empty (ram : RtRam) (N wgsize : Nat) (hcnt : ram.cnt = 0) :
    rtFind ram N wgsize = ⟨N, 0, 0, false⟩ := by
  have hsz : rtGapSize ram N 0 = N := by simp [rtGapSize, rtGapHi, rtGapLo, hcnt]
  show rtFindGo ram N wgsize (ram.cnt + 1) 0 ⟨N, 0, 0, false⟩ = ⟨N, 0, 0, false⟩
  rw [hcnt]
  show rtFindGo ram N wgsize 1 0 ⟨N, 0, 0, false⟩ = ⟨N, 0, 0, false⟩
  rw [rtFindGo_succ, rtFindGo_zero]
  unfold rtFindStep
  simp only [hsz]
  rw [if_neg (by omega)]


/-- 段末上界：rtGapHi ≤ N -/
theorem rtGapHi_le_N (ram : RtRam) (N : Nat) (hwf : RtWf ram N) {i : Nat}
    (hi : i ≤ ram.cnt) : rtGapHi ram N i ≤ N := by
  by_cases hc : i = ram.cnt
  · simp [rtGapHi, hc]
  · have hic : i < ram.cnt := by omega
    simp only [rtGapHi, hc, ↓reduceIte]
    have hb := hwf.bounds i hic
    omega

/-- walk 0 = head（定义展开） -/
theorem rtRam_walk_zero (ram : RtRam) : ram.walk 0 = ram.head := rfl

/-- walk (i+1) = next (walk i)（定义展开） -/
theorem rtRam_walk_succ (ram : RtRam) (i : Nat) :
    ram.walk (i+1) = ram.next (ram.walk i) := rfl

/- ========================================================================= -/
/- 5. 指针手术：ALLOC 的插入（WRITE :344-385）与 DEALLOC 的摘除（:412-444）    -/
/-    DontCare 位次按 D4 建模为"保持旧值"                                     -/
/- ========================================================================= -/

/-- ALLOC 的链表插入：slot 插到段 k（walk(k-1) 与 walk k 之间），
    区间 [base, base+size-1]（:352-369 的全部写口；k=0 ↔ head_flag，
    k=cnt ↔ tail_flag，写口条件 :352-363 逐行对应） -/
def rtInsert (ram : RtRam) (slot : Fin 8) (base size k : Nat) : RtRam where
  cnt := ram.cnt + 1                                                     -- :356-357
  head := if k = 0 then slot else ram.head                               -- :352-353
  tail := if k = ram.cnt then slot else ram.tail                         -- :354-355
  next := rtSet (if 0 < k then rtSet ram.next (ram.walk (k-1)) slot else ram.next)  -- :361-363
            slot (if k < ram.cnt then ram.walk k else ram.next slot)
  prev := rtSet (if k < ram.cnt then rtSet ram.prev (ram.walk k) slot else ram.prev) -- :358-360
            slot (if 0 < k then ram.walk (k-1) else ram.prev slot)
  addr1 := rtSet ram.addr1 slot base                                     -- :364-366
  addr2 := rtSet ram.addr2 slot (base + size - 1)                        -- :367-369

@[simp] theorem rtInsert_cnt (ram : RtRam) (slot : Fin 8) (base size k : Nat) :
    (rtInsert ram slot base size k).cnt = ram.cnt + 1 := rfl

@[simp] theorem rtInsert_head (ram : RtRam) (slot : Fin 8) (base size k : Nat) :
    (rtInsert ram slot base size k).head = if k = 0 then slot else ram.head := rfl

@[simp] theorem rtInsert_tail (ram : RtRam) (slot : Fin 8) (base size k : Nat) :
    (rtInsert ram slot base size k).tail = if k = ram.cnt then slot else ram.tail := rfl

theorem rtInsert_addr1 (ram : RtRam) (slot : Fin 8) (base size k : Nat) :
    (rtInsert ram slot base size k).addr1 = rtSet ram.addr1 slot base := rfl

theorem rtInsert_addr2 (ram : RtRam) (slot : Fin 8) (base size k : Nat) :
    (rtInsert ram slot base size k).addr2 = rtSet ram.addr2 slot (base + size - 1) := rfl

theorem rtInsert_addr1_eq (ram : RtRam) (slot : Fin 8) (base size k : Nat) :
    (rtInsert ram slot base size k).addr1 slot = base := by
  rw [rtInsert_addr1, rtSet_eq]

theorem rtInsert_addr2_eq (ram : RtRam) (slot : Fin 8) (base size k : Nat) :
    (rtInsert ram slot base size k).addr2 slot = base + size - 1 := by
  rw [rtInsert_addr2, rtSet_eq]

theorem rtInsert_addr1_ne (ram : RtRam) {slot s : Fin 8} (h : s ≠ slot) (base size k : Nat) :
    (rtInsert ram slot base size k).addr1 s = ram.addr1 s := by
  rw [rtInsert_addr1, rtSet_ne _ h]

theorem rtInsert_addr2_ne (ram : RtRam) {slot s : Fin 8} (h : s ≠ slot) (base size k : Nat) :
    (rtInsert ram slot base size k).addr2 s = ram.addr2 s := by
  rw [rtInsert_addr2, rtSet_ne _ h]

/-- 插入后 next 的逐点刻画 -/
theorem rtInsert_next (ram : RtRam) (slot : Fin 8) (base size k : Nat) (s : Fin 8) :
    (rtInsert ram slot base size k).next s =
      if s = slot then (if k < ram.cnt then ram.walk k else ram.next slot)
      else if 0 < k ∧ s = ram.walk (k-1) then slot
      else ram.next s := by
  by_cases hs : s = slot
  · simp [rtInsert, rtSet, hs]
  · by_cases hk : 0 < k
    · by_cases hs2 : s = ram.walk (k-1)
      · simp [rtInsert, rtSet, hk, hs2]
      · simp [rtInsert, rtSet, hs, hk, hs2]
    · simp [rtInsert, rtSet, hs, hk]

/-- 插入后 prev 的逐点刻画 -/
theorem rtInsert_prev (ram : RtRam) (slot : Fin 8) (base size k : Nat) (s : Fin 8) :
    (rtInsert ram slot base size k).prev s =
      if s = slot then (if 0 < k then ram.walk (k-1) else ram.prev slot)
      else if k < ram.cnt ∧ s = ram.walk k then slot
      else ram.prev s := by
  by_cases hs : s = slot
  · simp [rtInsert, rtSet, hs]
  · by_cases hk : k < ram.cnt
    · by_cases hs2 : s = ram.walk k
      · simp [rtInsert, rtSet, hk, hs2]
      · simp [rtInsert, rtSet, hs, hk, hs2]
    · simp [rtInsert, rtSet, hs, hk]

/-- 插入后遍历：段号 k 之前不变（归纳） -/
theorem rtInsert_walk_lt (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    {slot : Fin 8} {base size k : Nat}
    (hk : k ≤ ram.cnt) (hnew : ∀ i, i < ram.cnt → ram.walk i ≠ slot) :
    ∀ i, i < k → (rtInsert ram slot base size k).walk i = ram.walk i := by
  intro i
  induction i with
  | zero =>
    intro hi
    rw [rtRam_walk_zero, rtRam_walk_zero, rtInsert_head, if_neg (by omega : ¬ k = 0)]
  | succ i ih =>
    intro hi
    have hi' : i < k := by omega
    have hic : i < ram.cnt := by omega
    rw [rtRam_walk_succ, rtRam_walk_succ, ih hi', rtInsert_next]
    have h1 : ¬ (ram.walk i = slot) := hnew i hic
    have h2 : ¬ (0 < k ∧ ram.walk i = ram.walk (k - 1)) := by
      intro hc
      obtain ⟨hk0, he⟩ := hc
      have hk1 : k - 1 < ram.cnt := by omega
      have hinj := rt_walk_inj ram N hwf hic hk1 he
      omega
    rw [if_neg h1, if_neg h2]

/-- 插入后遍历：段号 m+1 处是新节点（后继形式，供 defeq 展开） -/
theorem rtInsert_walk_eq_succ (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    {slot : Fin 8} {base size m : Nat}
    (hk : m + 1 ≤ ram.cnt) (hnew : ∀ i, i < ram.cnt → ram.walk i ≠ slot) :
    (rtInsert ram slot base size (m+1)).walk (m+1) = slot := by
  rw [rtRam_walk_succ,
    rtInsert_walk_lt ram N hwf (by omega) hnew m (Nat.lt_succ_self m), rtInsert_next]
  have h1 : ¬ (ram.walk m = slot) := hnew m (by omega)
  rw [if_neg h1, if_pos ⟨Nat.succ_pos m, rfl⟩]

/-- 插入后遍历：段号 k 处是新节点 -/
theorem rtInsert_walk_eq (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    {slot : Fin 8} {base size k : Nat}
    (hk : k ≤ ram.cnt) (hnew : ∀ i, i < ram.cnt → ram.walk i ≠ slot) :
    (rtInsert ram slot base size k).walk k = slot := by
  cases k with
  | zero =>
    rw [rtRam_walk_zero, rtInsert_head, if_pos rfl]
  | succ m => exact rtInsert_walk_eq_succ ram N hwf (by omega) hnew

/-- 插入后遍历：段号 k 之后顺延一位 -/
theorem rtInsert_walk_gt (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    {slot : Fin 8} {base size k : Nat}
    (hk : k ≤ ram.cnt) (hnew : ∀ i, i < ram.cnt → ram.walk i ≠ slot) :
    ∀ d, k + d < ram.cnt → (rtInsert ram slot base size k).walk (k+1+d) = ram.walk (k+d)
  | 0, hd => by
    have hkc : k < ram.cnt := by omega
    simp only [Nat.add_zero]
    rw [rtRam_walk_succ, rtInsert_walk_eq ram N hwf hk hnew, rtInsert_next,
      if_pos rfl, if_pos hkc]
  | d+1, hd => by
    have hd' : k + d < ram.cnt := by omega
    have e := rtInsert_walk_gt (base := base) (size := size) ram N hwf hk hnew d hd'
    have h2 : ¬ (0 < k ∧ ram.walk (k+d) = ram.walk (k - 1)) := by
      intro hc
      obtain ⟨hk0, he⟩ := hc
      have hk1 : k - 1 < ram.cnt := by omega
      have hinj := rt_walk_inj ram N hwf hd' hk1 he
      omega
    rw [show k + 1 + (d + 1) = (k + 1 + d) + 1 by omega, rtRam_walk_succ, e, rtInsert_next]
    have h1 : ¬ (ram.walk (k+d) = slot) := hnew _ hd'
    rw [if_neg h1, if_neg h2, show k + (d + 1) = (k + d) + 1 by omega, rtRam_walk_succ]

/-- RT-I2 插入保持良构（H-RT-BOUNDS/DISJOINT 在 alloc 方向的核心） -/
theorem rtInsert_wf (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    {slot : Fin 8} {base size k : Nat}
    (hk : k ≤ ram.cnt) (hnew : ∀ i, i < ram.cnt → ram.walk i ≠ slot)
    (hlo : rtGapLo ram k ≤ base) (hhi : base + size ≤ rtGapHi ram N k)
    (hsize : 1 ≤ size) (hcnt : ram.cnt < rtNUM_WG_SLOT) :
    RtWf (rtInsert ram slot base size k) N := by
  have hN := hwf.npos
  have h8 : rtNUM_WG_SLOT = 8 := rfl
  have hhiN : rtGapHi ram N k ≤ N := rtGapHi_le_N ram N hwf hk
  refine ⟨hN, by rw [rtInsert_cnt]; omega, ?_, ?_, ?_, ?_⟩
  · -- bounds：三段讨论（k 前 / k / k 后）
    intro i hi
    rw [rtInsert_cnt] at hi
    rcases Nat.lt_trichotomy i k with h | h | h
    · rw [rtInsert_walk_lt ram N hwf hk hnew i h]
      have hic : i < ram.cnt := by omega
      rw [rtInsert_addr1_ne ram (hnew i hic), rtInsert_addr2_ne ram (hnew i hic)]
      exact hwf.bounds i hic
    · subst h
      rw [rtInsert_walk_eq ram N hwf hk hnew, rtInsert_addr1_eq, rtInsert_addr2_eq]
      omega
    · have hd : k + (i - 1 - k) < ram.cnt := by omega
      have e := rtInsert_walk_gt (base := base) (size := size) ram N hwf hk hnew (i - 1 - k) hd
      have e2 : k + 1 + (i - 1 - k) = i := by omega
      have e3 : k + (i - 1 - k) = i - 1 := by omega
      rw [e2, e3] at e
      rw [e]
      have hic : i - 1 < ram.cnt := by omega
      rw [rtInsert_addr1_ne ram (hnew (i-1) hic), rtInsert_addr2_ne ram (hnew (i-1) hic)]
      exact hwf.bounds (i-1) hic
  · -- sorted
    intro i hi
    rw [rtInsert_cnt] at hi
    rcases Nat.lt_trichotomy (i+1) k with h | h | h
    · rw [rtInsert_walk_lt ram N hwf hk hnew (i+1) h,
        rtInsert_walk_lt ram N hwf hk hnew i (by omega)]
      have hi1 : i + 1 < ram.cnt := by omega
      have hic : i < ram.cnt := by omega
      rw [rtInsert_addr2_ne ram (hnew i hic), rtInsert_addr1_ne ram (hnew (i+1) hi1)]
      exact hwf.sorted i hi1
    · -- i+1 = k：旧节点 k-1 与新节点，用 hlo（段 k 基址 = addr2(walk(k-1))+1 ≤ base）
      have ei : i = k - 1 := by omega
      have hk0 : k ≠ 0 := by omega
      rw [h, rtInsert_walk_eq ram N hwf hk hnew,
        rtInsert_walk_lt ram N hwf hk hnew i (by omega)]
      have hic : i < ram.cnt := by omega
      rw [rtInsert_addr1_eq, rtInsert_addr2_ne ram (hnew i hic)]
      have hlo' : rtGapLo ram k = ram.addr2 (ram.walk (k-1)) + 1 := by
        simp [rtGapLo, hk0]
      rw [ei]
      omega
    · by_cases hik : i = k
      · -- i = k：新节点与旧节点 k，用 hhi（base+size ≤ 段 k 末址 = addr1(walk k)）
        rw [hik]
        have hkc : k < ram.cnt := by omega
        have e := rtInsert_walk_gt (base := base) (size := size) ram N hwf hk hnew 0 (by omega)
        simp only [Nat.add_zero] at e
        rw [e, rtInsert_walk_eq ram N hwf hk hnew,
          rtInsert_addr2_eq, rtInsert_addr1_ne ram (hnew k hkc)]
        have hhi' : rtGapHi ram N k = ram.addr1 (ram.walk k) := rtGapHi_of_lt ram N hkc
        omega
      · -- i > k：全部顺延旧值
        have hd : k + (i - 1 - k) < ram.cnt := by omega
        have e1 := rtInsert_walk_gt (base := base) (size := size) ram N hwf hk hnew (i - 1 - k) hd
        have e1a : k + 1 + (i - 1 - k) = i := by omega
        have e1b : k + (i - 1 - k) = i - 1 := by omega
        rw [e1a, e1b] at e1
        have hd2 : k + (i - k) < ram.cnt := by omega
        have e2 := rtInsert_walk_gt (base := base) (size := size) ram N hwf hk hnew (i - k) hd2
        have e2a : k + 1 + (i - k) = i + 1 := by omega
        have e2b : k + (i - k) = i := by omega
        rw [e2a, e2b] at e2
        rw [e1, e2]
        have hic : i - 1 < ram.cnt := by omega
        rw [rtInsert_addr2_ne ram (hnew (i-1) hic),
          rtInsert_addr1_ne ram (hnew i (by omega))]
        have hs := hwf.sorted (i-1) (by omega)
        have e4 : i - 1 + 1 = i := by omega
        rw [e4] at hs
        exact hs
  · -- prevOk
    intro i hi
    rw [rtInsert_cnt] at hi
    rcases Nat.lt_trichotomy (i+1) k with h | h | h
    · rw [rtInsert_walk_lt ram N hwf hk hnew (i+1) h,
        rtInsert_walk_lt ram N hwf hk hnew i (by omega),
        rtInsert_prev]
      have hi1 : i + 1 < ram.cnt := by omega
      have h1 : ¬ (ram.walk (i+1) = slot) := hnew (i+1) hi1
      have h2 : ¬ (k < ram.cnt ∧ ram.walk (i+1) = ram.walk k) := by
        intro hc
        obtain ⟨hkc, he⟩ := hc
        have hinj := rt_walk_inj ram N hwf hi1 hkc he
        omega
      rw [if_neg h1, if_neg h2]
      exact hwf.prevOk i hi1
    · -- i+1 = k：prev'(slot) = walk(k-1) = walk i
      rw [h, rtInsert_walk_eq ram N hwf hk hnew,
        rtInsert_walk_lt ram N hwf hk hnew i (by omega), rtInsert_prev]
      rw [if_pos rfl, if_pos (by omega : 0 < k)]
      have ei : k - 1 = i := by omega
      rw [ei]
    · by_cases hik : i = k
      · -- i = k：prev'(walk k) = slot
        rw [hik]
        have hkc : k < ram.cnt := by omega
        have e := rtInsert_walk_gt (base := base) (size := size) ram N hwf hk hnew 0 (by omega)
        simp only [Nat.add_zero] at e
        rw [e, rtInsert_walk_eq ram N hwf hk hnew, rtInsert_prev]
        have h1 : ¬ (ram.walk k = slot) := hnew k hkc
        rw [if_neg h1, if_pos ⟨hkc, rfl⟩]
      · -- i > k
        have hd : k + (i - k) < ram.cnt := by omega
        have e2 := rtInsert_walk_gt (base := base) (size := size) ram N hwf hk hnew (i - k) hd
        have e2a : k + 1 + (i - k) = i + 1 := by omega
        have e2b : k + (i - k) = i := by omega
        rw [e2a, e2b] at e2
        have hd1 : k + (i - 1 - k) < ram.cnt := by omega
        have e1 := rtInsert_walk_gt (base := base) (size := size) ram N hwf hk hnew (i - 1 - k) hd1
        have e1a : k + 1 + (i - 1 - k) = i := by omega
        have e1b : k + (i - 1 - k) = i - 1 := by omega
        rw [e1a, e1b] at e1
        rw [e2, e1, rtInsert_prev]
        have hic : i < ram.cnt := by omega
        have hkc : k < ram.cnt := by omega
        have h1 : ¬ (ram.walk i = slot) := hnew i hic
        have h2 : ¬ (k < ram.cnt ∧ ram.walk i = ram.walk k) := by
          intro hc
          obtain ⟨_, he⟩ := hc
          have hinj := rt_walk_inj ram N hwf hic hkc he
          omega
        rw [if_neg h1, if_neg h2]
        have hp := hwf.prevOk (i-1) (by omega)
        have e4 : i - 1 + 1 = i := by omega
        rw [e4] at hp
        exact hp
  · -- tailOk
    intro _
    rw [rtInsert_cnt]
    have e : ram.cnt + 1 - 1 = ram.cnt := by omega
    rw [e]
    by_cases hkc : k = ram.cnt
    · subst hkc
      rw [rtInsert_walk_eq ram N hwf (Nat.le_refl _) hnew, rtInsert_tail, if_pos rfl]
    · have hkc' : k < ram.cnt := by omega
      have hd : k + (ram.cnt - 1 - k) < ram.cnt := by omega
      have e1 := rtInsert_walk_gt (base := base) (size := size) ram N hwf hk hnew (ram.cnt - 1 - k) hd
      have e1a : k + 1 + (ram.cnt - 1 - k) = ram.cnt := by omega
      have e1b : k + (ram.cnt - 1 - k) = ram.cnt - 1 := by omega
      rw [e1a, e1b] at e1
      rw [e1, rtInsert_tail, if_neg hkc]
      exact hwf.tailOk (by omega)

/-- DEALLOC 的链表摘除（:417-428 的全部写口；k = slot 在链表中的位置）。
    硬件用 wgslot == head()/tail() 比较决定写口（:417/:420/:425/:427），
    在 RtWf 下 ⟺ k = 0 / k = cnt-1（rt_walk_inj + tailOk），本模型直接用 k。 -/
def rtRemove (ram : RtRam) (slot : Fin 8) (k : Nat) : RtRam where
  cnt := ram.cnt - 1                                                     -- :423-424
  head := if k = 0 then ram.next slot else ram.head                      -- :425-426
  tail := if k = ram.cnt - 1 then ram.prev slot else ram.tail            -- :427-428
  next := if 0 < k then rtSet ram.next (ram.prev slot) (ram.next slot) else ram.next  -- :417-419
  prev := if k + 1 < ram.cnt then rtSet ram.prev (ram.next slot) (ram.prev slot) else ram.prev  -- :420-422
  addr1 := ram.addr1                                                     -- 未动（:429-430 见 Q1）
  addr2 := ram.addr2

@[simp] theorem rtRemove_cnt (ram : RtRam) (slot : Fin 8) (k : Nat) :
    (rtRemove ram slot k).cnt = ram.cnt - 1 := rfl

@[simp] theorem rtRemove_head (ram : RtRam) (slot : Fin 8) (k : Nat) :
    (rtRemove ram slot k).head = if k = 0 then ram.next slot else ram.head := rfl

@[simp] theorem rtRemove_tail (ram : RtRam) (slot : Fin 8) (k : Nat) :
    (rtRemove ram slot k).tail = if k = ram.cnt - 1 then ram.prev slot else ram.tail := rfl

theorem rtRemove_addr1 (ram : RtRam) (slot : Fin 8) (k : Nat) :
    (rtRemove ram slot k).addr1 = ram.addr1 := rfl

theorem rtRemove_addr2 (ram : RtRam) (slot : Fin 8) (k : Nat) :
    (rtRemove ram slot k).addr2 = ram.addr2 := rfl

/-- 摘除后 next 的逐点刻画 -/
theorem rtRemove_next (ram : RtRam) (slot : Fin 8) (k : Nat) (s : Fin 8) :
    (rtRemove ram slot k).next s =
      if 0 < k ∧ s = ram.prev slot then ram.next slot else ram.next s := by
  by_cases hk : 0 < k
  · by_cases hs : s = ram.prev slot
    · simp [rtRemove, rtSet, hk, hs]
    · simp [rtRemove, rtSet, hk, hs]
  · simp [rtRemove, hk]

/-- 摘除后 prev 的逐点刻画 -/
theorem rtRemove_prev (ram : RtRam) (slot : Fin 8) (k : Nat) (s : Fin 8) :
    (rtRemove ram slot k).prev s =
      if k + 1 < ram.cnt ∧ s = ram.next slot then ram.prev slot else ram.prev s := by
  by_cases hk : k + 1 < ram.cnt
  · by_cases hs : s = ram.next slot
    · simp [rtRemove, rtSet, hk, hs]
    · simp [rtRemove, rtSet, hk, hs]
  · simp [rtRemove, hk]

/-- prev 指针与链表位置的一致（prevOk 的槽位形式） -/
theorem rt_prev_slot_eq (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    {slot : Fin 8} {k : Nat} (hk : k < ram.cnt) (hslot : ram.walk k = slot) (hk0 : 0 < k) :
    ram.prev slot = ram.walk (k-1) := by
  have hp := hwf.prevOk (k-1) (by omega)
  have e : k - 1 + 1 = k := by omega
  rw [e, hslot] at hp
  exact hp

/-- 摘除后遍历：k 之前不变 -/
theorem rtRemove_walk_lt (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    {slot : Fin 8} {k : Nat}
    (hk : k < ram.cnt) (hslot : ram.walk k = slot) :
    ∀ i, i < k → (rtRemove ram slot k).walk i = ram.walk i := by
  intro i
  induction i with
  | zero =>
    intro hi
    rw [rtRam_walk_zero, rtRam_walk_zero, rtRemove_head, if_neg (by omega : ¬ k = 0)]
  | succ i ih =>
    intro hi
    have hi' : i < k := by omega
    have hic : i < ram.cnt := by omega
    rw [rtRam_walk_succ, rtRam_walk_succ, ih hi', rtRemove_next]
    have h2 : ¬ (0 < k ∧ ram.walk i = ram.prev slot) := by
      intro hc
      obtain ⟨hk0, he⟩ := hc
      rw [rt_prev_slot_eq ram N hwf hk hslot hk0] at he
      have hk1 : k - 1 < ram.cnt := by omega
      have hinj := rt_walk_inj ram N hwf hic hk1 he
      omega
    rw [if_neg h2]

/-- 摘除后遍历：k 起整体前移 -/
theorem rtRemove_walk_ge (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    {slot : Fin 8} {k : Nat}
    (hk : k < ram.cnt) (hslot : ram.walk k = slot) :
    ∀ d, k + d < ram.cnt - 1 → (rtRemove ram slot k).walk (k+d) = ram.walk (k+d+1)
  | 0, hd => by
    cases k with
    | zero =>
      simp only [Nat.add_zero]
      rw [rtRam_walk_zero, rtRam_walk_succ, rtRemove_head, if_pos rfl, ← hslot]
    | succ m =>
      have hps : ram.prev slot = ram.walk m :=
        rt_prev_slot_eq ram N hwf hk hslot (Nat.succ_pos m)
      simp only [Nat.add_zero]
      rw [rtRam_walk_succ, rtRam_walk_succ,
        rtRemove_walk_lt ram N hwf hk hslot m (Nat.lt_succ_self m), rtRemove_next,
        if_pos ⟨Nat.succ_pos m, hps.symm⟩, ← hslot]
  | d+1, hd => by
    have hd' : k + d < ram.cnt - 1 := by omega
    have e := rtRemove_walk_ge ram N hwf hk hslot d hd'
    have h2 : ¬ (0 < k ∧ ram.walk (k+d+1) = ram.prev slot) := by
      intro hc
      obtain ⟨hk0, he⟩ := hc
      rw [rt_prev_slot_eq ram N hwf hk hslot hk0] at he
      have h1 : k + d + 1 < ram.cnt := by omega
      have hk1 : k - 1 < ram.cnt := by omega
      have hinj := rt_walk_inj ram N hwf h1 hk1 he
      omega
    rw [show k + (d + 1) + 1 = (k + d + 1) + 1 by omega]
    rw [show k + (d + 1) = (k + d) + 1 by omega]
    rw [rtRam_walk_succ, e, rtRemove_next, if_neg h2]
    exact (rtRam_walk_succ ram (k+d+1)).symm

/-- RT-R2 摘除保持良构 -/
theorem rtRemove_wf (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    {slot : Fin 8} {k : Nat}
    (hk : k < ram.cnt) (hslot : ram.walk k = slot) :
    RtWf (rtRemove ram slot k) N := by
  have hN := hwf.npos
  have h8 : rtNUM_WG_SLOT = 8 := rfl
  have hnext : ram.next slot = ram.walk (k+1) := by rw [← hslot]; rfl
  refine ⟨hN, by rw [rtRemove_cnt]; have := hwf.cntLe; omega, ?_, ?_, ?_, ?_⟩
  · -- bounds：地址数组未动，节点是旧节点的子序列
    intro i hi
    rw [rtRemove_cnt] at hi
    by_cases hik : i < k
    · rw [rtRemove_walk_lt ram N hwf hk hslot i hik, rtRemove_addr1, rtRemove_addr2]
      exact hwf.bounds i (by omega)
    · have hd : k + (i - k) < ram.cnt - 1 := by omega
      have e := rtRemove_walk_ge ram N hwf hk hslot (i - k) hd
      have e1 : k + (i - k) = i := by omega
      rw [e1] at e
      rw [e, rtRemove_addr1, rtRemove_addr2]
      exact hwf.bounds (i+1) (by omega)
  · -- sorted
    intro i hi
    rw [rtRemove_cnt] at hi
    rcases Nat.lt_trichotomy (i+1) k with h | h | h
    · rw [rtRemove_walk_lt ram N hwf hk hslot (i+1) h,
        rtRemove_walk_lt ram N hwf hk hslot i (by omega),
        rtRemove_addr1, rtRemove_addr2]
      exact hwf.sorted i (by omega)
    · -- i+1 = k：walk'(i)=walk(k-1)，walk'(k)=walk(k+1)，跨洞传递
      have ek : i + 1 = k := h
      have ei : i = k - 1 := by omega
      rw [ek]
      have hkc1 : k + 0 < ram.cnt - 1 := by omega
      have e1 := rtRemove_walk_ge ram N hwf hk hslot 0 hkc1
      simp only [Nat.add_zero] at e1
      rw [e1]
      have hik : i < k := by omega
      rw [rtRemove_walk_lt ram N hwf hk hslot i hik, rtRemove_addr1, rtRemove_addr2]
      have hb := (hwf.bounds k hk).1
      have hs1 := hwf.sorted (k-1) (by omega)
      have e1r : k - 1 + 1 = k := by omega
      rw [e1r] at hs1
      have hs2 := hwf.sorted k (by omega)
      rw [ei]
      omega
    · -- i+1 > k：两侧皆顺延旧值
      have hd1 : k + (i - k) < ram.cnt - 1 := by omega
      have e1 := rtRemove_walk_ge ram N hwf hk hslot (i - k) hd1
      have e1a : k + (i - k) = i := by omega
      rw [e1a] at e1
      have hd2 : k + (i + 1 - k) < ram.cnt - 1 := by omega
      have e2 := rtRemove_walk_ge ram N hwf hk hslot (i + 1 - k) hd2
      have e2a : k + (i + 1 - k) = i + 1 := by omega
      rw [e2a] at e2
      rw [e1, e2, rtRemove_addr1, rtRemove_addr2]
      exact hwf.sorted (i+1) (by omega)
  · -- prevOk
    intro i hi
    rw [rtRemove_cnt] at hi
    rcases Nat.lt_trichotomy (i+1) k with h | h | h
    · rw [rtRemove_walk_lt ram N hwf hk hslot (i+1) h,
        rtRemove_walk_lt ram N hwf hk hslot i (by omega),
        rtRemove_prev]
      have h2 : ¬ (k + 1 < ram.cnt ∧ ram.walk (i+1) = ram.next slot) := by
        intro hc
        obtain ⟨hkc, he⟩ := hc
        rw [hnext] at he
        have hinj := rt_walk_inj ram N hwf (by omega : i + 1 < ram.cnt)
          (by omega : k + 1 < ram.cnt) he
        omega
      rw [if_neg h2]
      exact hwf.prevOk i (by omega)
    · -- i+1 = k：prev'(walk(k+1)) = prev slot = walk(k-1) = walk'(i)
      have ek : i + 1 = k := h
      have ei : i = k - 1 := by omega
      rw [ek]
      have hkc1 : k + 0 < ram.cnt - 1 := by omega
      have e1 := rtRemove_walk_ge ram N hwf hk hslot 0 hkc1
      simp only [Nat.add_zero] at e1
      rw [e1, rtRemove_prev]
      have hk0 : 0 < k := by omega
      rw [if_pos ⟨by omega, hnext.symm⟩]
      rw [rt_prev_slot_eq ram N hwf hk hslot hk0, ei]
      have hik : k - 1 < k := by omega
      exact (rtRemove_walk_lt ram N hwf hk hslot (k-1) hik).symm
    · -- i+1 > k
      have hd1 : k + (i - k) < ram.cnt - 1 := by omega
      have e1 := rtRemove_walk_ge ram N hwf hk hslot (i - k) hd1
      have e1a : k + (i - k) = i := by omega
      rw [e1a] at e1
      have hd2 : k + (i + 1 - k) < ram.cnt - 1 := by omega
      have e2 := rtRemove_walk_ge ram N hwf hk hslot (i + 1 - k) hd2
      have e2a : k + (i + 1 - k) = i + 1 := by omega
      rw [e2a] at e2
      rw [e1, e2, rtRemove_prev]
      have h2 : ¬ (k + 1 < ram.cnt ∧ ram.walk (i+2) = ram.next slot) := by
        intro hc
        obtain ⟨hkc, he⟩ := hc
        rw [hnext] at he
        have hinj := rt_walk_inj ram N hwf (by omega : i + 2 < ram.cnt)
          (by omega : k + 1 < ram.cnt) he
        omega
      rw [if_neg h2]
      have hp := hwf.prevOk (i+1) (by omega)
      have e3 : i + 1 + 1 = i + 2 := by omega
      rw [e3] at hp
      exact hp
  · -- tailOk
    intro hcnt2
    rw [rtRemove_cnt] at hcnt2 ⊢
    by_cases hkc : k = ram.cnt - 1
    · -- 摘掉尾：tail' = prev slot = walk(k-1) = walk(cnt-2)
      rw [rtRemove_tail, if_pos hkc]
      have hk0 : 0 < k := by omega
      rw [rt_prev_slot_eq ram N hwf hk hslot hk0]
      have e : ram.cnt - 1 - 1 = k - 1 := by omega
      rw [e]
      have hik : k - 1 < k := by omega
      exact rtRemove_walk_lt ram N hwf hk hslot (k-1) hik
    · -- 摘掉中间：tail' = tail = walk(cnt-1)，walk'(cnt-2) = walk(cnt-1)
      rw [rtRemove_tail, if_neg hkc]
      have hd : k + (ram.cnt - 2 - k) < ram.cnt - 1 := by omega
      have e1 := rtRemove_walk_ge ram N hwf hk hslot (ram.cnt - 2 - k) hd
      have e1a : k + (ram.cnt - 2 - k) = ram.cnt - 2 := by omega
      rw [e1a] at e1
      have e : ram.cnt - 1 - 1 = ram.cnt - 2 := by omega
      rw [e, e1]
      have e2 : ram.cnt - 2 + 1 = ram.cnt - 1 := by omega
      rw [e2]
      exact hwf.tailOk (by omega)


/- ========================================================================= -/
/- 6. 占用总长与守恒                                                           -/
/- ========================================================================= -/

/-- 前 n 个节点的占用总长 Σ (addr2+1-addr1) -/
def rtSumSizes (ram : RtRam) : Nat → Nat
  | 0 => 0
  | (n+1) => rtSumSizes ram n + (ram.addr2 (ram.walk n) + 1 - ram.addr1 (ram.walk n))

theorem rtSumSizes_zero (ram : RtRam) : rtSumSizes ram 0 = 0 := rfl

theorem rtSumSizes_succ (ram : RtRam) (n : Nat) :
    rtSumSizes ram (n+1) =
      rtSumSizes ram n + (ram.addr2 (ram.walk n) + 1 - ram.addr1 (ram.walk n)) := rfl

/-- 占用单调 -/
theorem rtSumSizes_mono (ram : RtRam) (n : Nat) :
    rtSumSizes ram n ≤ rtSumSizes ram (n+1) := by
  rw [rtSumSizes_succ]; omega

/-- 占用单调（区间形式；注意避开 omega 对 `m - (k+1)` 形减法的盲点） -/
theorem rtSumSizes_mono_le (ram : RtRam) {a b : Nat} (h : a ≤ b) :
    rtSumSizes ram a ≤ rtSumSizes ram b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans ih (rtSumSizes_mono ram _)

/-- 前缀和不超过第 n 个节点的末址+1（地址升序 ⇒ 互不重叠的区间打包） -/
theorem rtSumSizes_le_addr2 (ram : RtRam) (N : Nat) (hwf : RtWf ram N) :
    ∀ n, n < ram.cnt → rtSumSizes ram (n+1) ≤ ram.addr2 (ram.walk n) + 1 := by
  intro n
  induction n with
  | zero =>
    intro hn
    rw [rtSumSizes_succ, rtSumSizes_zero]
    have hb := (hwf.bounds 0 hn).1
    omega
  | succ m ihm =>
    intro hn
    rw [rtSumSizes_succ]
    have ih := ihm (by omega)
    have hs := hwf.sorted m (by omega)
    have hb := (hwf.bounds (m+1) (by omega)).1
    omega

/-- RT-CONSERVE-0 不超分：占用总长 ≤ N -/
theorem rt_sum_le_N (ram : RtRam) (N : Nat) (hwf : RtWf ram N) :
    rtSumSizes ram ram.cnt ≤ N := by
  by_cases hc : ram.cnt = 0
  · rw [hc, rtSumSizes_zero]; exact Nat.zero_le N
  · have h := rtSumSizes_le_addr2 ram N hwf (ram.cnt - 1) (by omega)
    have e : ram.cnt - 1 + 1 = ram.cnt := by omega
    rw [e] at h
    have hb := (hwf.bounds (ram.cnt - 1) (by omega)).2
    omega

/-- RT-CONSERVE-1 分配守恒：插入后占用精确增加 size -/
theorem rt_alloc_used (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    {slot : Fin 8} {base size k : Nat}
    (hk : k ≤ ram.cnt) (hnew : ∀ i, i < ram.cnt → ram.walk i ≠ slot)
    (hsize : 1 ≤ size) :
    rtSumSizes (rtInsert ram slot base size k) (ram.cnt + 1) =
      rtSumSizes ram ram.cnt + size := by
  have aux : ∀ n, n ≤ ram.cnt + 1 →
      rtSumSizes (rtInsert ram slot base size k) n =
        rtSumSizes ram (if n ≤ k then n else n - 1) + (if n ≤ k then 0 else size) := by
    intro n
    induction n with
    | zero => intro _; simp [rtSumSizes]
    | succ m ihm =>
      intro hm
      rw [rtSumSizes_succ]
      have ihm' := ihm (by omega)
      rcases Nat.lt_trichotomy m k with h | h | h
      · -- m < k
        rw [rtInsert_walk_lt (base := base) (size := size) ram N hwf hk hnew m h]
        have hic : m < ram.cnt := by omega
        rw [rtInsert_addr1_ne ram (hnew m hic), rtInsert_addr2_ne ram (hnew m hic)]
        simp only [if_pos (show m ≤ k by omega)] at ihm'
        simp only [if_pos (show m + 1 ≤ k by omega)]
        rw [show rtSumSizes ram (m+1) =
            rtSumSizes ram m + (ram.addr2 (ram.walk m) + 1 - ram.addr1 (ram.walk m))
          from rtSumSizes_succ ram m]
        omega
      · -- m = k：新节点，size' = (base+size-1)+1-base = size
        subst h
        rw [rtInsert_walk_eq ram N hwf hk hnew,
          rtInsert_addr1_eq, rtInsert_addr2_eq]
        simp only [if_pos (Nat.le_refl m)] at ihm'
        simp only [if_neg (by omega : ¬ m + 1 ≤ m)]
        have e : m + 1 - 1 = m := by omega
        rw [e]
        omega
      · -- m > k：顺延旧节点
        have hd : k + (m - 1 - k) < ram.cnt := by omega
        have e1 := rtInsert_walk_gt (base := base) (size := size) ram N hwf hk hnew (m-1-k) hd
        have e1a : k + 1 + (m - 1 - k) = m := by omega
        have e1b : k + (m - 1 - k) = m - 1 := by omega
        rw [e1a, e1b] at e1
        rw [e1]
        have hic : m - 1 < ram.cnt := by omega
        rw [rtInsert_addr1_ne ram (hnew (m-1) hic), rtInsert_addr2_ne ram (hnew (m-1) hic)]
        simp only [if_neg (show ¬ m ≤ k by omega)] at ihm'
        simp only [if_neg (show ¬ m + 1 ≤ k by omega)]
        have e2 : m + 1 - 1 = m := by omega
        rw [e2]
        rw [show rtSumSizes ram m =
            rtSumSizes ram (m-1) + (ram.addr2 (ram.walk (m-1)) + 1 - ram.addr1 (ram.walk (m-1)))
          from by rw [show m = m - 1 + 1 by omega]; exact rtSumSizes_succ ram (m-1)]
        omega
  have h := aux (ram.cnt + 1) (Nat.le_refl _)
  simp only [if_neg (by omega : ¬ ram.cnt + 1 ≤ k)] at h
  have e : ram.cnt + 1 - 1 = ram.cnt := by omega
  rw [e] at h
  exact h

/-- RT-CONSERVE-2 回收守恒：摘除后占用精确减少被摘节点的尺寸 -/
theorem rt_dealloc_used (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    {slot : Fin 8} {k : Nat} (hk : k < ram.cnt) (hslot : ram.walk k = slot) :
    rtSumSizes (rtRemove ram slot k) (ram.cnt - 1) =
      rtSumSizes ram ram.cnt - (ram.addr2 slot + 1 - ram.addr1 slot) := by
  have aux : ∀ n, n ≤ ram.cnt - 1 →
      rtSumSizes (rtRemove ram slot k) n =
        if n ≤ k then rtSumSizes ram n
        else rtSumSizes ram k + (rtSumSizes ram (n+1) - rtSumSizes ram (k+1)) := by
    intro n
    induction n with
    | zero => intro _; simp [rtSumSizes]
    | succ m ihm =>
      intro hm
      rw [rtSumSizes_succ]
      have ihm' := ihm (by omega)
      rcases Nat.lt_trichotomy m k with h | h | h
      · rw [rtRemove_walk_lt ram N hwf hk hslot m h, rtRemove_addr1, rtRemove_addr2]
        simp only [if_pos (show m ≤ k by omega)] at ihm'
        simp only [if_pos (show m + 1 ≤ k by omega)]
        rw [rtSumSizes_succ]
        omega
      · -- m = k：越过被摘节点
        subst h
        have hkc1 : m + 0 < ram.cnt - 1 := by omega
        have e1 := rtRemove_walk_ge ram N hwf hk hslot 0 hkc1
        simp only [Nat.add_zero] at e1
        rw [e1, rtRemove_addr1, rtRemove_addr2]
        simp only [if_pos (Nat.le_refl m)] at ihm'
        simp only [if_neg (show ¬ m + 1 ≤ m by omega)]
        have hs1 := rtSumSizes_succ ram m
        have hs2 := rtSumSizes_succ ram (m+1)
        have hmono : rtSumSizes ram (m+1) ≤ rtSumSizes ram (m+1+1) := rtSumSizes_mono ram _
        omega
      · -- m > k
        have hd : k + (m - k) < ram.cnt - 1 := by omega
        have e1 := rtRemove_walk_ge ram N hwf hk hslot (m - k) hd
        have e1a : k + (m - k) = m := by omega
        rw [e1a] at e1
        rw [e1, rtRemove_addr1, rtRemove_addr2]
        simp only [if_neg (show ¬ m ≤ k by omega)] at ihm'
        simp only [if_neg (show ¬ m + 1 ≤ k by omega)]
        have hs2 := rtSumSizes_succ ram (m+1)
        have hmono : rtSumSizes ram (k+1) ≤ rtSumSizes ram (m+1) :=
          rtSumSizes_mono_le ram (by omega)
        omega
  have h := aux (ram.cnt - 1) (Nat.le_refl _)
  by_cases hkc : k = ram.cnt - 1
  · -- 摘的是尾节点
    simp only [if_pos (by omega : ram.cnt - 1 ≤ k)] at h
    have hs := rtSumSizes_succ ram (ram.cnt - 1)
    have e : ram.cnt - 1 + 1 = ram.cnt := by omega
    rw [e] at hs
    have hsk : ram.walk (ram.cnt - 1) = slot := hkc ▸ hslot
    rw [hsk] at hs
    omega
  · -- 摘的是中间节点
    simp only [if_neg (by omega : ¬ ram.cnt - 1 ≤ k)] at h
    have hs := rtSumSizes_succ ram k
    rw [hslot] at hs
    have e : ram.cnt - 1 + 1 = ram.cnt := by omega
    rw [e] at h
    have hmono : rtSumSizes ram (k+1) ≤ rtSumSizes ram ram.cnt :=
      rtSumSizes_mono_le ram (by omega)
    omega

/- ========================================================================= -/
/- 7. SCAN：rtcache 的最大两段（:449-517；NUM_RT_RESULT=2）                    -/
/- ========================================================================= -/

/-- SCAN 的 top-2 累加步（:478-480 的 sort3(0,0,size)/sort3(r0,r1,size) 取前二；
    sort3 的位级正确性见 rt_sort3_out） -/
def rtScanStep (acc : Nat × Nat) (sz : Nat) : Nat × Nat :=
  if acc.1 ≤ sz then (sz, acc.1) else if acc.2 ≤ sz then (acc.1, sz) else acc

def rtScanGo (ram : RtRam) (N : Nat) : Nat → Nat → Nat × Nat → Nat × Nat
  | 0, _, acc => acc
  | (f+1), i, acc => rtScanGo ram N f (i+1) (rtScanStep acc (rtGapSize ram N i))

/-- 完整 SCAN（:455 起 fsm_s_cnt 从 0 计到 cnt；初值 :474/:478 的 Mux(init,0,_)） -/
def rtScan (ram : RtRam) (N : Nat) : Nat × Nat := rtScanGo ram N (ram.cnt + 1) 0 (0, 0)

theorem rtScanGo_zero (ram : RtRam) (N i : Nat) (acc : Nat × Nat) :
    rtScanGo ram N 0 i acc = acc := rfl

theorem rtScanGo_succ (ram : RtRam) (N f i : Nat) (acc : Nat × Nat) :
    rtScanGo ram N (f+1) i acc = rtScanGo ram N f (i+1) (rtScanStep acc (rtGapSize ram N i)) := rfl

/-- 段 0..i+f-1 的最大空段长 -/
def rtGapMaxGo (ram : RtRam) (N : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | (f+1), i => max (rtGapSize ram N i) (rtGapMaxGo ram N f (i+1))

theorem rtGapMaxGo_zero (ram : RtRam) (N i : Nat) : rtGapMaxGo ram N 0 i = 0 := rfl

theorem rtGapMaxGo_succ (ram : RtRam) (N f i : Nat) :
    rtGapMaxGo ram N (f+1) i = max (rtGapSize ram N i) (rtGapMaxGo ram N f (i+1)) := rfl

theorem rtScanGo_fst (ram : RtRam) (N : Nat) :
    ∀ f i r0 r1, (rtScanGo ram N f i (r0, r1)).1 = max r0 (rtGapMaxGo ram N f i)
  | 0, i, r0, r1 => by rw [rtScanGo_zero, rtGapMaxGo_zero]; simp
  | (f+1), i, r0, r1 => by
    rw [rtScanGo_succ, rtGapMaxGo_succ]
    unfold rtScanStep
    by_cases h0 : r0 ≤ rtGapSize ram N i
    · rw [if_pos h0, rtScanGo_fst]
      rw [← Nat.max_assoc, Nat.max_eq_right h0]
    · rw [if_neg h0]
      by_cases h1 : r1 ≤ rtGapSize ram N i
      · rw [if_pos h1, rtScanGo_fst]
        rw [← Nat.max_assoc, Nat.max_eq_left (Nat.le_of_not_ge h0)]
      · rw [if_neg h1, rtScanGo_fst]
        rw [← Nat.max_assoc, Nat.max_eq_left (Nat.le_of_not_ge h0)]

/-- RT-SCAN-1 rtcache(0) = 全部空段的最大长度 -/
theorem rtScan_max (ram : RtRam) (N : Nat) :
    (rtScan ram N).1 = rtGapMaxGo ram N (ram.cnt + 1) 0 := by
  have h := rtScanGo_fst ram N (ram.cnt + 1) 0 0 0
  rw [Nat.zero_max] at h
  exact h

theorem rtGapMaxGo_ge (ram : RtRam) (N w : Nat) :
    ∀ f i j, i ≤ j → j < i + f → w ≤ rtGapSize ram N j → w ≤ rtGapMaxGo ram N f i := by
  intro f
  induction f with
  | zero => intro i j h0 h1 _; omega
  | succ f ih =>
    intro i j h0 h1 hw
    rw [rtGapMaxGo_succ]
    by_cases hj : j = i
    · subst hj; exact Nat.le_trans hw (Nat.le_max_left _ _)
    · exact Nat.le_trans (ih (i+1) j (by omega) (by omega) hw) (Nat.le_max_right _ _)

theorem rtGapMaxGo_mem (ram : RtRam) (N w : Nat) :
    ∀ f i, 0 < f → w ≤ rtGapMaxGo ram N f i →
      ∃ j, i ≤ j ∧ j < i + f ∧ w ≤ rtGapSize ram N j := by
  intro f
  induction f with
  | zero => intro i hf; omega
  | succ f ih =>
    intro i _ hw
    rw [rtGapMaxGo_succ] at hw
    by_cases h : w ≤ rtGapSize ram N i
    · exact ⟨i, Nat.le_refl _, by omega, h⟩
    · have hw' : w ≤ rtGapMaxGo ram N f (i+1) := by
        by_cases hab : rtGapMaxGo ram N f (i+1) ≤ rtGapSize ram N i
        · rw [Nat.max_eq_left hab] at hw; exact absurd hw h
        · rw [Nat.max_eq_right (Nat.le_of_not_ge hab)] at hw; exact hw
      by_cases hf : f = 0
      · subst hf
        rw [rtGapMaxGo_zero] at hw'
        have hw0 : w = 0 := by omega
        subst hw0
        exact absurd (Nat.zero_le _) h
      · obtain ⟨j, hj0, hj1, hj2⟩ := ih (i+1) (Nat.pos_of_ne_zero hf) hw'
        exact ⟨j, by omega, by omega, hj2⟩

/-- RT-SCAN-CONS rtcache 一致性：allocator 看到的 rtcache(0) ≥ size ⟺ rt 里确有能放下的空段
    （H-ALLOC-FIT 的 rt 侧机制核销：缓存永不高估） -/
theorem rt_scan_ge_iff (ram : RtRam) (N wgsize : Nat) :
    wgsize ≤ (rtScan ram N).1 ↔ ∃ i, i ≤ ram.cnt ∧ wgsize ≤ rtGapSize ram N i := by
  rw [rtScan_max]
  constructor
  · intro h
    obtain ⟨j, hj0, hj1, hj2⟩ := rtGapMaxGo_mem ram N wgsize (ram.cnt + 1) 0 (Nat.succ_pos _) h
    exact ⟨j, by omega, hj2⟩
  · intro h
    obtain ⟨j, hj0, hj1⟩ := h
    exact rtGapMaxGo_ge ram N wgsize (ram.cnt + 1) 0 j (by omega) (by omega) hj1

/-- RT-SCAN-FIND 一致性推论：缓存说放得下 ⇒ FIND 必找到（非空表） -/
theorem rt_find_of_scan (ram : RtRam) (N wgsize : Nat) (hwf : RtWf ram N)
    (hcnt : 0 < ram.cnt) (h : wgsize ≤ (rtScan ram N).1) :
    (rtFind ram N wgsize).upd = true :=
  rtFind_success ram N wgsize hwf hcnt ((rt_scan_ge_iff ram N wgsize).mp h)

/- ========================================================================= -/
/- 8. 事件模型与主定理（H-RT-BOUNDS / H-RT-DISJOINT 核销）                     -/
/- ========================================================================= -/

/-- 链表内查找槽位（dealloc 目标的定位；硬件直接用 prev/next[wgslot] 的读数） -/
def rtFindSlotGo (ram : RtRam) (slot : Fin 8) : Nat → Nat → Option Nat
  | 0, _ => none
  | (f+1), i => if ram.walk i = slot then some i else rtFindSlotGo ram slot f (i+1)

def rtFindSlot (ram : RtRam) (slot : Fin 8) : Option Nat := rtFindSlotGo ram slot ram.cnt 0

theorem rtFindSlotGo_zero (ram : RtRam) (slot : Fin 8) (i : Nat) :
    rtFindSlotGo ram slot 0 i = none := rfl

theorem rtFindSlotGo_succ (ram : RtRam) (slot : Fin 8) (f i : Nat) :
    rtFindSlotGo ram slot (f+1) i =
      if ram.walk i = slot then some i else rtFindSlotGo ram slot f (i+1) := rfl

theorem rtFindSlotGo_spec (ram : RtRam) (slot : Fin 8) :
    ∀ f i k, rtFindSlotGo ram slot f i = some k → i ≤ k ∧ k < i + f ∧ ram.walk k = slot
  | 0, _, _, h => by rw [rtFindSlotGo_zero] at h; simp at h
  | (f+1), i, k, h => by
    rw [rtFindSlotGo_succ] at h
    by_cases hi : ram.walk i = slot
    · rw [if_pos hi] at h
      simp at h
      subst h
      exact ⟨Nat.le_refl _, by omega, hi⟩
    · rw [if_neg hi] at h
      obtain ⟨h1, h2, h3⟩ := rtFindSlotGo_spec ram slot f (i+1) k h
      exact ⟨by omega, by omega, h3⟩

theorem rtFindSlotGo_none (ram : RtRam) (slot : Fin 8) :
    ∀ f i, rtFindSlotGo ram slot f i = none → ∀ j, i ≤ j → j < i + f → ram.walk j ≠ slot
  | 0, _, _, j, h0, h1 => by omega
  | (f+1), i, h, j, h0, h1 => by
    rw [rtFindSlotGo_succ] at h
    by_cases hi : ram.walk i = slot
    · rw [if_pos hi] at h; simp at h
    · rw [if_neg hi] at h
      by_cases hj : j = i
      · subst hj; exact hi
      · exact rtFindSlotGo_none ram slot f (i+1) h j (by omega) (by omega)

theorem rtFindSlot_spec (ram : RtRam) (slot : Fin 8) {k : Nat}
    (h : rtFindSlot ram slot = some k) : k < ram.cnt ∧ ram.walk k = slot := by
  obtain ⟨h1, h2, h3⟩ := rtFindSlotGo_spec ram slot ram.cnt 0 k h
  exact ⟨by omega, h3⟩

theorem rtFindSlot_none (ram : RtRam) (slot : Fin 8)
    (h : rtFindSlot ram slot = none) : ∀ j, j < ram.cnt → ram.walk j ≠ slot := by
  intro j hj
  exact rtFindSlotGo_none ram slot ram.cnt 0 h j (by omega) (by omega)

/-- rt 事件：alloc 完成（WRITE+baseaddr 输出）/ dealloc 完成（摘除） -/
inductive RtEvent where
  | alloc (slot : Fin 8) (wgsize : Nat)
  | dealloc (slot : Fin 8)

/-- 事件契约（外部前提：allocator 的 H-ALLOC-SLOT/H-ALLOC-FIT、
    cu_interface 的 H-CUIF-DEALLOC；逐条对应 CtaScheduler.lean 契约清单） -/
def rtEventOk (ram : RtRam) (N : Nat) : RtEvent → Prop
  | .alloc slot wgsize =>
      ram.cnt < rtNUM_WG_SLOT ∧                                  -- H-ALLOC-SLOT 有富余槽
      (∀ i, i < ram.cnt → ram.walk i ≠ slot) ∧                   -- H-ALLOC-SLOT 目标槽空闲
      (wgsize = 0 ∨ ∃ i, i ≤ ram.cnt ∧ wgsize ≤ rtGapSize ram N i)  -- H-ALLOC-FIT
  | .dealloc slot => ∃ k, k < ram.cnt ∧ ram.walk k = slot        -- H-CUIF-DEALLOC 只收在驻

/-- alloc 输出的基址（io.baseaddr.bits.addr，:393；wgsize=0 时 FIND 跳过、输出 0，D6） -/
def rtAllocBase (ram : RtRam) (N : Nat) (slot : Fin 8) (wgsize : Nat) : Nat :=
  if wgsize = 0 then 0 else (rtFind ram N wgsize).faddr

/-- 事件步进 -/
def rtStep (ram : RtRam) (N : Nat) (e : RtEvent) : RtRam :=
  match e with
  | .alloc slot wgsize =>
      if wgsize = 0 then ram      -- :352-369 的全部写口被 !(wgsize===0) 门控
      else rtInsert ram slot (rtFind ram N wgsize).faddr wgsize (rtFind ram N wgsize).fk
  | .dealloc slot =>
      match rtFindSlot ram slot with
      | some k => rtRemove ram slot k
      | none => ram               -- 契约不可达区域（Q8）

theorem rtStep_alloc (ram : RtRam) (N : Nat) (slot : Fin 8) (wgsize : Nat) :
    rtStep ram N (.alloc slot wgsize) =
      if wgsize = 0 then ram
      else rtInsert ram slot (rtFind ram N wgsize).faddr wgsize (rtFind ram N wgsize).fk := rfl

theorem rtStep_dealloc (ram : RtRam) (N : Nat) (slot : Fin 8) :
    rtStep ram N (.dealloc slot) =
      match rtFindSlot ram slot with
      | some k => rtRemove ram slot k
      | none => ram := rfl

/-- **H-RT-BOUNDS 核销**：契约内 alloc 的输出区间 [base, base+wgsize) 在界内 -/
theorem rt_alloc_base_bounds (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    (slot : Fin 8) (wgsize : Nat) (hok : rtEventOk ram N (.alloc slot wgsize)) :
    rtAllocBase ram N slot wgsize + wgsize ≤ N := by
  obtain ⟨hcnt8, hnew, hfit⟩ := hok
  unfold rtAllocBase
  by_cases hsize0 : wgsize = 0
  · rw [if_pos hsize0]; omega
  · rw [if_neg hsize0]
    obtain ⟨i, hi0, hi1⟩ := hfit.resolve_left hsize0
    by_cases hcnt0 : ram.cnt = 0
    · rw [rtFind_empty ram N wgsize hcnt0]
      show (0 : Nat) + wgsize ≤ N
      have hi : i = 0 := by omega
      subst hi
      have hsz : rtGapSize ram N 0 = N := by simp [rtGapSize, rtGapHi, rtGapLo, hcnt0]
      omega
    · have hup := rtFind_success ram N wgsize hwf (by omega) ⟨i, hi0, hi1⟩
      obtain ⟨hfk, haddr, hsize', hfit'⟩ := rtFind_upd ram N wgsize hwf hup
      have hle := rt_gapLo_le_hi ram N hwf hfk
      have hhi := rtGapHi_le_N ram N hwf hfk
      rw [hsize'] at hfit'
      have hfit'' : wgsize ≤ rtGapHi ram N (rtFind ram N wgsize).fk -
          rtGapLo ram (rtFind ram N wgsize).fk := hfit'
      rw [haddr]
      omega

/-- **H-RT-DISJOINT 核销（增量形式）**：契约内 alloc 的输出区间与所有在驻节点不交 -/
theorem rt_alloc_disjoint (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    (slot : Fin 8) (wgsize : Nat) (hok : rtEventOk ram N (.alloc slot wgsize))
    (hsize : wgsize ≠ 0) :
    ∀ j, j < ram.cnt →
      rtAllocBase ram N slot wgsize + wgsize ≤ ram.addr1 (ram.walk j) ∨
      ram.addr2 (ram.walk j) < rtAllocBase ram N slot wgsize := by
  obtain ⟨hcnt8, hnew, hfit⟩ := hok
  obtain ⟨i, hi0, hi1⟩ := hfit.resolve_left hsize
  intro j hj
  have hpos : 0 < ram.cnt := by omega
  have hup := rtFind_success ram N wgsize hwf hpos ⟨i, hi0, hi1⟩
  obtain ⟨hfk, haddr, hsize', hfit'⟩ := rtFind_upd ram N wgsize hwf hup
  have hle := rt_gapLo_le_hi ram N hwf hfk
  rw [hsize'] at hfit'
  have hfit'' : wgsize ≤ rtGapHi ram N (rtFind ram N wgsize).fk -
      rtGapLo ram (rtFind ram N wgsize).fk := hfit'
  unfold rtAllocBase
  rw [if_neg hsize, haddr]
  generalize hfk' : (rtFind ram N wgsize).fk = k
  rw [hfk'] at hfk hle hfit''
  rcases Nat.lt_or_ge j k with h | h
  · -- j 在选中段之前：addr2(walk j) ≤ addr2(walk(k-1)) < gapLo k
    right
    have hk0 : 0 < k := by omega
    have hlo' : rtGapLo ram k = ram.addr2 (ram.walk (k-1)) + 1 := by
      simp [rtGapLo, Nat.ne_of_gt hk0]
    have hk1 : k - 1 < ram.cnt := by omega
    have hmono : ram.addr2 (ram.walk j) ≤ ram.addr2 (ram.walk (k-1)) := by
      rcases Nat.eq_or_lt_of_le (show j ≤ k - 1 by omega) with he | he
      · rw [he]; exact Nat.le_refl _
      · have h1 := rt_addr2_lt_addr1 ram N hwf he hk1
        have h2 := (hwf.bounds (k-1) hk1).1
        omega
    omega
  · -- j 在选中段或之后：gapHi k = addr1(walk k) ≤ addr1(walk j)
    left
    have hkc : k < ram.cnt := by omega
    have hhi' : rtGapHi ram N k = ram.addr1 (ram.walk k) := rtGapHi_of_lt ram N hkc
    have hmono := rt_addr1_mono ram N hwf h hj
    omega

/-- RT-WF-DISJOINT 存量形式：良构链表的任意两节点区间不交 -/
theorem rt_wf_disjoint (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    {i j : Nat} (hi : i < ram.cnt) (hj : j < ram.cnt) (hij : i ≠ j) :
    ram.addr2 (ram.walk i) < ram.addr1 (ram.walk j) ∨
    ram.addr2 (ram.walk j) < ram.addr1 (ram.walk i) := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact Or.inl (rt_addr2_lt_addr1 ram N hwf h hj)
  · exact absurd h hij
  · exact Or.inr (rt_addr2_lt_addr1 ram N hwf h hi)

/-- RT-MAIN 不变式保持：契约内任意事件保持链表良构 -/
theorem rt_step_wf (ram : RtRam) (N : Nat) (hwf : RtWf ram N) (e : RtEvent)
    (hok : rtEventOk ram N e) : RtWf (rtStep ram N e) N := by
  cases e with
  | alloc slot wgsize =>
    obtain ⟨hcnt8, hnew, hfit⟩ := hok
    rw [rtStep_alloc]
    by_cases hsize0 : wgsize = 0
    · rw [if_pos hsize0]; exact hwf
    · rw [if_neg hsize0]
      obtain ⟨i, hi0, hi1⟩ := hfit.resolve_left hsize0
      by_cases hcnt0 : ram.cnt = 0
      · rw [rtFind_empty ram N wgsize hcnt0]
        show RtWf (rtInsert ram slot 0 wgsize 0) N
        have hi : i = 0 := by omega
        subst hi
        have hsz : rtGapSize ram N 0 = N := by simp [rtGapSize, rtGapHi, rtGapLo, hcnt0]
        have hhi : rtGapHi ram N 0 = N := by simp [rtGapHi, hcnt0]
        apply rtInsert_wf ram N hwf (by omega) hnew
        · simp [rtGapLo]
        · omega
        · omega
        · exact hcnt8
      · have hup := rtFind_success ram N wgsize hwf (by omega) ⟨i, hi0, hi1⟩
        obtain ⟨hfk, haddr, hsize', hfit'⟩ := rtFind_upd ram N wgsize hwf hup
        have hle := rt_gapLo_le_hi ram N hwf hfk
        rw [hsize'] at hfit'
        have hfit'' : wgsize ≤ rtGapHi ram N (rtFind ram N wgsize).fk -
            rtGapLo ram (rtFind ram N wgsize).fk := hfit'
        apply rtInsert_wf ram N hwf hfk hnew
        · exact Nat.le_of_eq haddr.symm
        · rw [haddr]; omega
        · omega
        · exact hcnt8
  | dealloc slot =>
    obtain ⟨k, hk, hslot⟩ := hok
    rw [rtStep_dealloc]
    cases hfs : rtFindSlot ram slot with
    | none =>
      show RtWf ram N
      exact absurd (hslot) (rtFindSlot_none ram slot hfs k hk)
    | some k' =>
      obtain ⟨hk', hslot'⟩ := rtFindSlot_spec ram slot hfs
      show RtWf (rtRemove ram slot k') N
      exact rtRemove_wf ram N hwf hk' hslot'

/-- RT-DEALLOC-NOTIN 回收即腾空：摘除后该槽不在链表中 -/
theorem rt_dealloc_notin (ram : RtRam) (N : Nat) (hwf : RtWf ram N)
    {slot : Fin 8} {k : Nat} (hk : k < ram.cnt) (hslot : ram.walk k = slot) :
    ∀ i, i < (rtRemove ram slot k).cnt → (rtRemove ram slot k).walk i ≠ slot := by
  intro i hi
  rw [rtRemove_cnt] at hi
  by_cases hik : i < k
  · rw [rtRemove_walk_lt ram N hwf hk hslot i hik]
    intro he
    have hinj := rt_walk_inj ram N hwf (by omega : i < ram.cnt) hk (he.trans hslot.symm)
    omega
  · have hd : k + (i - k) < ram.cnt - 1 := by omega
    have e := rtRemove_walk_ge ram N hwf hk hslot (i - k) hd
    have e1 : k + (i - k) = i := by omega
    rw [e1] at e
    rw [e]
    intro he
    have hinj := rt_walk_inj ram N hwf (by omega : i + 1 < ram.cnt) hk (he.trans hslot.symm)
    omega


/- ========================================================================= -/
/- 9. 数值回归测试（先测试后证明：硬件行为的可执行镜像）                        -/
/- ========================================================================= -/

section RtRegressionTests

/-- 空表（复位态：cnt=0 由 :580 RegInit 保证；head/tail 无初值但 cnt=0 下不可读，D4） -/
def rtEmpty : RtRam := ⟨0, 0, 0, id, id, fun _ => 0, fun _ => 0⟩

theorem rtEmpty_wf (N : Nat) (hN : 0 < N) : RtWf rtEmpty N := by
  have hc : rtEmpty.cnt = 0 := rfl
  refine ⟨hN, by decide, ?_, ?_, ?_, ?_⟩
  · intro i hi; omega
  · intro i hi; omega
  · intro i hi; omega
  · intro h; omega

-- T1：空表分配 A（slot 2, size 100）⇒ base=0，插入为唯一节点
def rtA : RtRam := rtStep rtEmpty rtNUM_SGPR (.alloc 2 100)

example : rtAllocBase rtEmpty rtNUM_SGPR 2 100 = 0 := by decide
example : rtA.cnt = 1 := by decide
example : rtA.walk 0 = 2 := by decide
example : rtA.head = 2 ∧ rtA.tail = 2 := by decide
example : rtA.addr1 2 = 0 ∧ rtA.addr2 2 = 99 := by decide

theorem rtA_wf : RtWf rtA rtNUM_SGPR :=
  rt_step_wf rtEmpty rtNUM_SGPR (rtEmpty_wf _ (by decide)) (.alloc 2 100) (by
    refine ⟨by decide, ?_, ?_⟩
    · intro i hi
      have hc : rtEmpty.cnt = 0 := rfl
      omega
    · right
      exact ⟨0, by decide, by decide⟩)

-- T2：再分配 B（slot 5, size 50）⇒ 尾段 [100, 2048)，base=100
def rtB : RtRam := rtStep rtA rtNUM_SGPR (.alloc 5 50)

example : rtAllocBase rtA rtNUM_SGPR 5 50 = 100 := by decide
example : rtB.cnt = 2 := by decide
example : rtB.walk 0 = 2 ∧ rtB.walk 1 = 5 := by decide
example : rtB.next 2 = 5 ∧ rtB.prev 5 = 2 := by decide
example : rtB.addr1 5 = 100 ∧ rtB.addr2 5 = 149 := by decide
example : rtB.head = 2 ∧ rtB.tail = 5 := by decide
example : rtSumSizes rtB 2 = 150 := by decide

theorem rtB_wf : RtWf rtB rtNUM_SGPR :=
  rt_step_wf rtA rtNUM_SGPR rtA_wf (.alloc 5 50) (by
    refine ⟨by decide, ?_, ?_⟩
    · intro i hi
      have hc : rtA.cnt = 1 := by decide
      have hi0 : i = 0 := by omega
      subst hi0
      decide
    · right
      exact ⟨1, by decide, by decide⟩)

-- T3：回收 A（slot 2，头节点）⇒ 链表前移
def rtC : RtRam := rtStep rtB rtNUM_SGPR (.dealloc 2)

example : rtFindSlot rtB 2 = some 0 := by decide
example : rtC.cnt = 1 := by decide
example : rtC.walk 0 = 5 := by decide
example : rtC.head = 5 ∧ rtC.tail = 5 := by decide
example : rtSumSizes rtC 1 = 50 := by decide     -- 回收精确（150 - 100）

theorem rtC_wf : RtWf rtC rtNUM_SGPR :=
  rt_step_wf rtB rtNUM_SGPR rtB_wf (.dealloc 2) (⟨0, by decide, by decide⟩)

-- T4：best-fit 检验——分配 C（slot 7, size 60）：段 0 = [0,100)（100 ≥ 60）
--     击败段 1 = [150,2048)（1898）⇒ base=0，插入为新头
def rtD : RtRam := rtStep rtC rtNUM_SGPR (.alloc 7 60)

example : rtAllocBase rtC rtNUM_SGPR 7 60 = 0 := by decide
example : rtD.cnt = 2 := by decide
example : rtD.walk 0 = 7 ∧ rtD.walk 1 = 5 := by decide
example : rtD.head = 7 ∧ rtD.tail = 5 := by decide
example : rtD.next 7 = 5 ∧ rtD.prev 5 = 7 := by decide
example : rtD.addr1 7 = 0 ∧ rtD.addr2 7 = 59 := by decide
example : rtSumSizes rtD 2 = 110 := by decide

theorem rtD_wf : RtWf rtD rtNUM_SGPR :=
  rt_step_wf rtC rtNUM_SGPR rtC_wf (.alloc 7 60) (by
    refine ⟨by decide, ?_, ?_⟩
    · intro i hi
      have hc : rtC.cnt = 1 := by decide
      have hi0 : i = 0 := by omega
      subst hi0
      decide
    · right
      exact ⟨0, by decide, by decide⟩)

-- T5：wgsize=0 不插表、输出 base=0（:352-369 门控 + :400 跳扫描，D6）
example : (rtStep rtD rtNUM_SGPR (.alloc 3 0)).cnt = rtD.cnt := by decide
example : (rtStep rtD rtNUM_SGPR (.alloc 3 0)).walk 0 = rtD.walk 0 ∧
    (rtStep rtD rtNUM_SGPR (.alloc 3 0)).walk 1 = rtD.walk 1 := by decide
example : rtAllocBase rtD rtNUM_SGPR 3 0 = 0 := by decide

-- T6：SCAN 结果（rtcache top-2）
example : (rtScan rtD rtNUM_SGPR).1 = 1898 := by decide   -- 段 [150,2048)
example : (rtScan rtD rtNUM_SGPR).2 = 40 := by decide     -- 段 [60,100)
example : (rtScan rtEmpty rtNUM_SGPR).1 = 2048 := by decide  -- 空表整段

-- T7【Q4 witness】H-ALLOC-FIT 缺位即链表腐蚀：全表被占（slot 0: [0,2047]）时
--    再要 512——FIND 无段可选保持初值，新节点以 base=0 插入，区间与在驻节点重叠
def rtFull : RtRam := ⟨1, 0, 0, id, id, fun _ => 0, fun _ => 2047⟩
def rtCorrupt : RtRam := rtStep rtFull rtNUM_SGPR (.alloc 1 512)

example : (rtFind rtFull rtNUM_SGPR 512).upd = false := by decide
example : rtCorrupt.cnt = 2 := by decide
example : rtCorrupt.addr1 1 = 0 ∧ rtCorrupt.addr2 1 = 511 := by decide
example : rtCorrupt.addr1 0 = 0 ∧ rtCorrupt.addr2 0 = 2047 := by decide
-- 重叠的直接证据：区间 [0,511] 与 [0,2047] 互含
example : rtCorrupt.addr1 1 ≤ rtCorrupt.addr2 0 ∧ rtCorrupt.addr1 0 ≤ rtCorrupt.addr2 1 := by decide
-- 契约本可拦下：任何段都放不下 512
example : ¬ rtEventOk rtFull rtNUM_SGPR (.alloc 1 512) := by
  intro h
  obtain ⟨h1, h2, h3⟩ := h
  have g0 : rtGapSize rtFull rtNUM_SGPR 0 = 0 := by decide
  have g1 : rtGapSize rtFull rtNUM_SGPR 1 = 0 := by decide
  rcases h3 with h0 | ⟨i, hi, hgi⟩
  · omega
  · have hc : rtFull.cnt = 1 := rfl
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · rw [g0] at hgi; omega
    · rw [g1] at hgi; omega

-- T8【Q6 / I-11 触发面证据】sgpr 路（N=2048）合法分配可给出任意高基址：
--    低区 [0,1792) 被占后再分 256 ⇒ base=1792 ≥ 1024（且贴满上界 1792+256=2048）
def rtI11 : RtRam := ⟨1, 3, 3, id, id, fun _ => 0, fun _ => 1791⟩   -- slot 3: [0, 1791]

example : rtAllocBase rtI11 rtNUM_SGPR 5 256 = 1792 := by decide
example : 1792 + 256 ≤ rtNUM_SGPR := by decide    -- H-RT-BOUNDS 贴边成立
example : ¬ (1792 < 1024) := by decide            -- collector 侧 10bit 处理必回绕

/-- 极端：size=1 时 base 可达 N-1=2047 -/
def rtI11max : RtRam := ⟨1, 3, 3, id, id, fun _ => 0, fun _ => 2046⟩  -- slot 3: [0, 2046]

example : rtAllocBase rtI11max rtNUM_SGPR 5 1 = 2047 := by decide

/-- I-11 对照：vgpr 路（N=1024）base 恒 ≤ 1023，不触发 -/
def rtV11 : RtRam := ⟨1, 3, 3, id, id, fun _ => 0, fun _ => 1022⟩

example : rtAllocBase rtV11 rtNUM_VGPR 5 1 = 1023 := by decide
example : 1023 < 1024 := by decide

end RtRegressionTests

/- ========================================================================= -/
/- 10. 公理审计                                                                -/
/-    结论：全部核心定理仅依赖标准公理 [propext, Quot.sound(, Classical.choice)]； -/
/-    rt_sort3_*（bv_decide）额外带 4.31 原生 LRAT 检查器的 trust 公理           -/
/-    `<thm>._native.bv_decide.ax_1_5`——与 CtaScheduler.lean 的                 -/
/-    ctas_tag_roundtrip 完全同类（项目已接受的 bv_decide 惯例）；               -/
/-    位宽引理 rt_bw_* 与全部测试用 decide，无额外公理。                         -/
/- ========================================================================= -/

#print axioms rt_alloc_base_bounds
#print axioms rt_alloc_disjoint
#print axioms rt_step_wf
#print axioms rt_alloc_used
#print axioms rt_dealloc_used
#print axioms rt_sum_le_N
#print axioms rtScan_max
#print axioms rt_scan_ge_iff
#print axioms rt_find_of_scan
#print axioms rt_dealloc_notin
#print axioms rt_sort3_out
#print axioms rt_bw_empty_size_sgpr

end Ventus.CTA
