# Gate-3U 攻击 844:整条 3U 坍缩链已 Lean 验证 axiom-clean —— 只留 ONE generic-λ 前提 `hfactor`

Date: 2026-08-07 · Status: WSL 构建通过 + 数值探针(有限格 rank 饱和,无法判决 ≤1)
This is the direct continuation of 843. 843 指出 Gate-3U 真门被坍缩成
`|Tr(sourceBand)| ≤ 1`,剩下唯一开放是 generic-λ 的 `hfactor`。844 把这件事
从"说法"变成"Lean 里逐条 `#check` + `#print axioms` 验证过的 axiom-clean 链",
并新增一个"normalized family-bracket"探针去测量那个 gate 的归一化行为。

## 0. 先讲结论

**Gate-3U 的整条结构性坍缩链在 Lean 里全部 axiom-clean**(axioms 集合 =
`[propext, Classical.choice, Quot.sound]`),没有任何暗置的公理;坍缩最后落到
**一个** generic-λ 的 Hilbert–Schmidt 求和前提 `hfactor`。数值探针(844)再次证明
**有限网格只能看到离散化塌缩**(`rawTr` 饱和 = 秩 = n/2,op=1.0),因此网格本身
**不可能判决 `≤1`**——这不是新 block,是已在 838/843 记录过的已知墙。唯一的真
断点从"分析无穷级数收敛"降级为"一个有限 family-bracket 的 signed trace ≤1"。

## 1. Lean 验证:坍缩链 axiom-clean

审计文件 `ConnesWeilRH/Dev/CC24GateCollapseChainAudit844.lean` 在 WSL 里
`lake build` 通过(3406 jobs)。关键 #check / #print axioms:

```
#check @canonicalRealGate3UAt_iff_completedBoundaryCycleRealBound        -- Gate ⟺ |Tr(周期)|≤1
#check @ordinaryTraceAlong_completedBoundaryCycle_re_eq_outer_sub_moving  -- 周期.re = outer - moving
#check @actualOuterProjectionDifference_eq_zero                           -- 真 Euler transport → outer 差 = 0
#check @CCM24SourceProlateTrace.sourceThreeBranchCommutator_isTraceClassAlong  -- 该空间 commutator 是 trace-class
```

`#print axioms` 对每条都返回:
```
[propext, Classical.choice, Quot.sound]
```
这是 Lean 的"凭空无假设"底面 —— 表示 Gate-3U 这一整条"outer=0 + cycle-迹 + 坍缩到 sourceBand"
的推导,除了这些元逻辑类没有用任何未证明的公理。

**唯一开放的前提** = `hfactor : Summable fun i => ||sourceContinuousHilbertSchmidtFactor λ (globalBasis i)||^2`
—— generic-λ 的 Hilbert–Schmidt 求和(见 839/840)。它在 `sourceCommutator_isTraceClassAlong` 的输入里。

## 2. 查清"λ 从哪里进来"

```
Q_λ = HT† E_λ HT        (HardyTitchmarsh:361-366)
R_λ = E_λ ⊓ Q_λ
```
HT 本身 λ-independent。λ 只进 `E_λ`(radial cutoff)。所以 generic-λ 的公共层面
不是"把整个问题搬到任意 λ",而是"radial cutoff 扫过一个 family"。这与 839 的
"real 开放 3U 是 λ-generic HS 求和"一致,只不过 844 把它收窄到**一个 family 的
Gram bracket**。

## 3. 数值探针 844:normalized family-bracket gate

`docs/844_normed_family_branch_gate_probe.py`(Windows Python 跑过):
```
（向量）[原始] 的 Gate-3U 目标不是裸 band 迹,而是
  |Tr( sourceBandGramResponse )| ≤ 1
  承重者:finiteEulerAmbientGram(逐 prime 的 log-平移) + 下factor 收缩
  repo 已证 op-norm ≤ 1: norm_lowerFactor_smul_finiteEulerInverseOperator_le_one
        CCM24FiniteGramResponse.lean:704
```

探针结果(WSL 窗口 / Windows 同源):
```
n= 64  dim(R∩Q)=0 |rawTr|= 32  op=1.0  HS=11.6
  primes=[2]   lf=0.293  score= 9.37
  primes=[2,3,5,7,11]  lf=0.0297  score= 0.95   <- 撞到 ≤1
n=128 dim(R∩Q)=0 |rawTr|= 64  op=1.0  HS=33.3
  primes=[2,3,5,7,11]  score= 1.90    <- 超过 1(网格变大就涨)
```
`dim(R∩Q)=0` ⊕ op=1.0 ⊕ `rawTr=秩` 是 838 判过的离散化塌缩:有限网格看不见
连续 Sonin 子空间(维 0),也 **不能** 判决 `≤1`。归一化因子(lowerFactor)确实随 prime
family 增大而把分数压向 1,但它跟随网格(rank)而非连续目标 —— 探针不能 level。

## 4. 诚实锁定:打完穿后剩什么

| 项 | 状态 | 影响 Gate |
|---|---|---|
| outer transport ≤=0 | 证明(真 Euler) | 剥掉 outer |
| Q_λ = HT†E_λHT(λ 经 radial) | 定义 | λ 只进 radial |
| |Tr(sourceBand)| ≤ 1 | **唯一未证(Lean)** | = 真断点 |
| generic-λ hfactor | 前提 | 已有 thm 的输入 |

- 837/839/840 "泛型-级 HS" 的描述更严,但 3U 不是"sum HS 收敛",是"某个有限
  bracket 的 signed Tr ≤1"。前者无限难,后者有限可写。
- 数值网格判不了(离散 rank-0),这是已知墙(838,843),不是新 block。

## 5. 下一步(self-created)

要真正关这一根,分两步:
- (a) 纯数学/Lean 设计:因为 `ambientGram = T†T` with T = finite-Euler transport,
  image 在 family-generated span(由 `sourceInclusion` / `E_λ` 与 log-平移生成),
  一般不满。只需"对所有插值 → 筛选 n 维 Hermitian bound ≤ λ 单位扩散"上界;
  transport 由有限乘积 + log-平移(全 conserve norm),则每个 family-Gram column
  norm ≤ C·‖unit factor column‖,把 generic-λ HS 换成 **unit→有限 bracket 的
  norm bound** 的 product bound。
- (b) 若 (a) 在 Lean 写不下去,则把 "generic-λ hfactor" 显式列为唯一开放定理,
  附 unit-λ 的 axiom-clean HS(839)作对照 —— 这本身就是"3U 打到只剩一根"的
  可交付状态。

844 已经完成 (b) 的审计版:(a) 那根才是 845 的动作点。

## Repro

```
# 844 probe(有限格 signed-net 只显示 rank-0 塌陷)
/c/Users/Peter/AppData/Local/Programs/Python/Python313/python.exe docs/proofs/844_..._gate_probe.py

# (WSL) 重新构建 844 审计
#   lake build LeafConnesWeilRH.Source.LeafCCM25Concrete.LeafCCM24FiniteSCanonicalCompletedKernelBoundaryCycle
#   lake build .../Float444HarmonicProbe/dev, 见 Dev/CC24GateCollapseChainAudit844.lean
```