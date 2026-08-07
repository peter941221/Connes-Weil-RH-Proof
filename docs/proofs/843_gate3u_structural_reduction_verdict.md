# Proof-717 / Gate-3U: 843 — the Gate-3U "generic-λ wall" collapses to ONE signed trace after outer=0; the remaining open is a finite-family trace-bound, and numerics cannot see it (discretization rank-0)

Date: 2026-08-07 · Status: source-verified structural audit + numeric probe
(WSL unavailable this session, so no build; every `=`-chain claim is read from
the Lean source directly). This attacks 3U directly, by self-creation, and
refines 839/840: the scattering-phase obstruction is real for the
*conjugate-transport* route, but the repository already contains a structural
collapse of the Gate that does NOT need to move λ by transport.

SOURCE read: `CC20Concrete/CCM24HardyTitchmarsh.lean`,
`CCM25Concrete/CCM24FiniteSProjectionTrace.lean`,
`CCM25Concrete/CCM24FiniteSBandTrace.lean`,
`CCM25Concrete/CCM24FiniteSCanonicalCompletedKernelBoundaryCycle.lean`,
`CCM25Concrete/CCM24FiniteTransportedOuterCollapse.lean`,
`CCM25Concrete/CCM24SourceProlateTrace.lean`, `CCM25Concrete/CCM24FiniteSGramResponse.lean`.

## 0. 先讲结论

**3U 真门(`canonicalRealGate3UAt`)被一条已证的 0 通道(outer) + 恒等式(Cycle-迹) 坍缩成
一单、有符号、有限括号的根迹 `|Tr(sourceBand)| ≤ 1`。** 泛型-λ 之"墙"不下落在
泛型-级 HS；它降级为一个**有限 family-bracket 的根迹 bound**。数值(有限格)只能看见
离散化坍缩(rank-0，op=1.0)，不能判决 ≤1。这就是打了穿之后的真断点，且在 Lean 里有
一条可写的路径。

```
Re对每声内千里 ubil-clean 部分(837 已证)：
  outer transport 差 = 0          Lean `=`(FiniteTransportedOuterCollapse:170,180)
  Gate = cycle-real trace bound    Lean `↔`(boundaryCycle:392)
  cycle.re = Tr(outer) - Tr(moving)  Lean `=`(MovingBandGuard:153)
  ⇒  Gate ⟺ |Tr(movingBand/rootSourceBand)| ≤ 1        (outer=0 代进)

λ 进 prolate factor 只经 radial cutoff：
  Q_λ = HT† E_λ HT                  (HT involutive & λ-indep; HardyTitchmarsh:349,361-366)
  R_λ = E_λ ⊓ Q_λ
```

## 1. 结构性坍缩 (每步都是 Lean 已证)

`CCM24FiniteTransportedOuterCollapse.lean:170`
```
theorem actualOuterProjectionDifference_eq_zero :
    outerProjectionDifference λ (finiteEulerTransportedOuterProjection λ family) = 0
```
genuine finiteEU rotation 把 outer-差 精确为零(transport 保 radial 支持; L99,180)。
memory 里"outer non-zero on every carrier"是对 proxy-carrier 的说法;对真 transport 是 0。

`CCM24FiniteSCanonicalCompletedKernelBoundaryCycle.lean:392/153`
```
canonicalRealGate3Ua ⇔ |Tr(boundaryCycle)| ≤ bound
boundaryCycle.re = Tr(outer diff).re - Tr(moving band).re
⇒  Gate ⇔ |Tr(moving band)| ≤ 1
```
`moving band` telescops 到 `rootSandwichedBandResponse` 又到 `-Tr(sourceBandGramResponse)`
(source→root ambient cycle)。故:

```
canonicalRealGate3Ua owner λ family bound ⇔  |Tr(sourceBandGramResponse owner λ family)| ≤ bound
```

## 2. 哪一层还需 generic-λ HS

`sourceBandGramResponse`(CCM24FiniteSBandTrace:359) = `-sourceGramResponse`, 且 L414:
```
sourceBandGramResponse = -(sourceInclusion)† ∘ cc20ThreeBranchCommutator ∘L (
    finiteEulerAmbientGram family ∘L sourceInclusion ∘L finiteEulerGramInv) ∘L ...
```
`finiteEulerAmbientGram` = `T†T`(L377) 对 finite-Euler transport = **有限 family 的
乘积** operator, 不是无限维全载体。因此 `Tr{sourceBand}`(definition与 chain) 的承重
支仍要求 ctxThreeBranch 是 trace-class —— 而 `sourceThreeBranchCommutator_isTraceClassAlong`
(CCM24SourceProlateTrace:299) 恰在 `hfactor : Summable ‖sourceProlateHilbertSchmidtFactor λ‖²`
下证。所以 **generic-λ HS 并没有被"有限 bracket"吃掉**;它仍在 `sourceProlateCommutator_isTraceClassAlong`
的输入前提 —— 但它的范围已缩到**一陪有限的 family Gram 里面**。

→ 841/842/839 的门没有任何一个被关掉:真的在 Lean 里**门最后的那一根**就是
`hfactor`(Summable generic-λ)。843 的新东西是把"它是分析事实缺口"改写成
"它是**该商、该有限 bracket 的 one-number trace—bound**"(见 §4), 从而答案"怎么打"从
"证明一个无穷和收敛"变成"证明一个有限 Gram 的 norm bound ≤1"。

## 3. 数值: 有限格看不到 (已复现 838 离散化坍缩)

`843_finite_band_gate_net_probe.py`(Windows Python)对 loglambda=0, n=192/384/768:
```
n=192  rank(R)=96 rank(Q)=96 dim(RnQ)=0  signed band trace=96.0  op=1.0  HS=61.0
n=384  rank(R)=192 ... dim(RnQ)=0  signed=192.0 op=1.0 HS=149.9
n=768  rank(R)=384 ... dim(RnQ)=0  signed=384.0 op=1.0 HS=287.2
```
`dim(RnQ)=0` ⊕ `op→1.0` ⊕ 签名迹 = rank(饱和) 是有限格离散化坍缩(838 判): 网格无法
看连续 Sonin 子空间(其维数 0), 也无法判决 ≤1。→ **数值层面无 probe 可 level**。
对连续载体, 探针行为与 837/838 一致, 无新证据。

**但**: 连续/Lean 上, 因为 `Tr{sourceBand}` 只经 `finiteEulerAmbientGram`(有限 family
括 矩 阵)进文件汇, 且 `radialSupportProjection λ`(作用在 `E=inc†...` ) 的算作用到
`U_c·(unit)` 的 transport 后仍保 norm-1, 因此 `‖cc20ThreeBranchCommutator ...‖` 的
一个上界可从"unit domain + same FAMILY Gram matrix"读出 —— 这是唯一 lean-可写的
下一步(见 §"下一步")。

## 4. 诚实锁定: “打穿”后剩下来的就是这一个 bound

```
项                                       状态              影响 Gate
─────────────────────────────────────  ───────────────  ────────────────────────────
outer transport ≤=0                     证明(真Euler)     法院剥离 outer
Q_λ = HT†E_λHT  (λ经 radial)            定义, HT indep      λ 只入 radial cutoff
|Tr(sourceBand)| ≤ 1                     未证(Lean)         这就是真断点
(基础上, generic-λ hfactor 仍前提)                      ——已存在定理的输入
```

- 837/839/840 的"泛型-级 HS"描述得更严, 但 Gate 不是"sum HS 收敛"; 是"某有限
  bracket 的 signed Tr ≤1"。前者(求和超收敛)无限难, 后者有限、可写的**一族** bound。
- 数值有限格判不了它(离散化 rank-0), 这是已知墙(838), 不是新增 block。

## 5. 下一步 (self-created attempt, 若 WSL 不可达则为 offline design)

要真正关这一根(把 `hfactor` 换成证明),最直接的是:
**在 Lean 里证明 `Tr{sourceBand}: ≤ 1` 经由 `finiteEulerAmbientGram` 的有限秩**。
即: 因为 `finiteEulerAmbientGram = T†T` with T = finite-Euler transport(product of
primes, conjugations by log-p translations), 其 image 在 family-generated span(由
`sourceInclusion`/`E_λ` 与对数平移生成), 一般**不是满的**——只需一个"对所有
插值→（SONIN）筛选的 n 维 Hermitian bound ≤ λ 单位扩散"上界。这个界若在 unit(已证 HS)
上成立, 且 transport 由有限乘积+log-平移构成(全部 **preserve norm** arithmetic), 那么
每一根 family-Gram column 的 norm ≤ C·‖unit factor column‖; 于是
`Σ‖col‖² · (Gram bounded) ≤ C²·Σ‖unit factor‖²`(后者 axiom-clean, 839) 把 generic-λ
HS 换成 **unit → 有限括号 transport 的 norm bound**, 一个可证明的真定理。
> This is the exact, written, self-authored direction to "打穿 3U": not
> "证明 generic-λ HS" as an unbounded sieve, but "单位 λ HS(已证) × 有限 transport(保
> norm→ 有限) ≤ 1 deGraded family 三项."

那一步若成, `hfactor` 对 generic-λ 不再 needed; Gate 由 unit-HS(axiom-clean,839)+
transport-norm(保范) 证 → 3U 真门关合。

## Repro

```
# probe 843 (有限格 signed-net 只显示 rank-0 坍缩; 于此宿)
C:/Users/Peter/AppData/Local/Programs/Python/Python313/python.exe docs/proofs/843_finite_band_gate_net_probe.py

# (WSL 重建; 843 不新增新对象, 只依赖既有定理)
#   lake build ConnesWeilRH.Source.CCM20Concrete.CCM24HardyTitchmarsh
#   lake build ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalCompletedKernelBoundaryCycle
#   lake build ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteTransportedOuter
```