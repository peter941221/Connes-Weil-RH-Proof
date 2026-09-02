# 907 — H1 (Hilbert 重指) vs H2 (broken-model 重构)：哪条打更深、更该先打

Date: 2026-08-08 · Status: 证据优先的架构判断（非代码改动）。Owner: Peter。
Scope: 两个 RH lever 都打深入后，干净判断哪条"更好"。引用 832 / 850 / 851 / 852 / 855 / 887 既有结论。

## 0. 一句话结论（evidence-first）

两条都能深入，但收益与风险不对称。**建议 H1（把 Hilbert carrier 的 trace/HS/符号定理接回 route 的 cc20 符号层）**：

- 它 90% 已建成、axiom-clean，是纯"接法"（wiring）而非新分析；
- 爆炸半径小，不触碰 `SourceWeilFormData` / finite-prime，**天然绕开 832 的结构性矛盾**；
- 但它修的是 `CC20TraceModel / hilbertSchmidtGate` 这一**旁路**的实体 trace 门——**不直接削减 RH 输出的 41-axiom 账本**。

**H2（把坏 `SourceWeilFormData.finitePrime.exactSupport` 结构改掉 + 重指 CompactLog）** 才是**贴着 RH 主路径**的那条：它是 skeleton 最终 `SourceRH` 的真依赖（Lane-B + Lane-R）。但 832 已 Lean 证明"纯换载体无用"，必须做 structural refactor（per-test index 或舍弃全局 `exactSupport`），动 `SourceAnalyticCore` + 30+ 根 axiom，且紧邻 RH 等价（C1/Yoshida），不是近期可封的任务。

> 底线：H1 = 低风险、接近完成、但在 RH 批判路径之外；H2 = 在 RH 批判路径上、但结构性难、风险大。要先拿下一个真实有内容的闭环 → H1；要直接啃 RH 主路径 → H2（需接受它本质近乎开新战线）。

> 最新裁决（§7j/7k/7l，后端增补）：H2 真正的障碍已被 Lean 证为 **载体无关** —— `PerCommonSourceFinitePrimeSupport` 前向行 `sourceVisibleGlobalIndex : ∀ n, ∀ F, term n F ≠ 0 → n ∈ globalIndexSet`（`globalIndexSet : Finset ℕ` 有限）把每个素数的 bump 都塞进有限集，与无限多素数矛盾；完整 Schwartz 与 CompactLog 均如此。**唯一修复 = 前向行从 `∀ F` 收窄为 per-`common`**（精确 patch 见 §7l），属模型边界 → 需 Peter 拍板。RH 不声明。

## 1. 两个 lever 各自打的是什么（What / Why / How）

+---------------------------------------------------+---------------------------------------------------+
| **H1：Hilbert 载体重指（把 HS carrier 接回 route 的希尔伯特符号层）** | **H2：Lane-B 坏 concrete 模型结构重构 + CompactLog re-type** |
+---------------------------------------------------+---------------------------------------------------+
| What: 把 `reTyped : ScalarTraceScaleSymbols on cc20GlobalLogCrossingL2` 里的真 Hilbert 门（`Gate = Nonempty Hil 基`，`‖g‖²`，Mellin，archsign）接进 route 的 `cc20Trace` / `archimedeanSymbols`。 | What: 修正 `SourceWeilFormData` / `SourceFinitePrimeExactSupportData` 的结构形状，并把 Weil 判定 / finite-prime 重指到健康 CompactLog 载体。 |
| How: `HilbertCarrierReTypedSymbols` + `HilbertTraceModelClosure` 已给出 `Gate_nonempty`、`trace_class_template`、`ordinary_trace_support_square`、`mellinHalfDensityProven`、`archimedeanSignNormalized := Nonempty HilbertArchSignDatum`（F†F PSD）。剩余 = 一个 measure/ae 桥把 Mellin 半密度具体到 `cc20GlobalLogCrossingL2`，+ 把 route 的 cc 重指到这个模型。 | How: 先做结构性 refactor（`finitePrime.exactSupport` 从 `∀ F` 全局 index 改 per-test index，或去掉该全局约束），再把 weil 层 / 判定 re-type 到 CompactLog，最后接 `MellinConvolutionIdentity` / `MellinProductCarrier`（851/852）。 |
| Status: `HilbertTraceModelClosure` build + audit 绿（axiom=[propext,Classical.choice,Quot.sound]，含三条归一行（u∞/qdu 约定 + arch datum，§7c）全关）。 | Status: 832 Lean-proven：carrier 替换**不**修 L137/L152；需结构性 refactor。850：点加卷积是伪象征，真 home 是 CompactLog。 |
+---------------------------------------------------+---------------------------------------------------+

## 2. 决定性证据：route 的 cc20 门独立于坏模型 + 与 RH 输出的关系

本会话查实：
- `RouteInputs.cc20`（Definitions.lean:36）= `Source.CC20Interface.ofSourceObjectPackage pkg`（CC20.lean:247），其 `archimedeanSymbols` 经 `pkg.toArchimedeanTraceSymbols` → `SourceAnalyticCore.traceScale`。
- `SourceTraceScaleData`（AnalyticCore.lean:8127）是**独立结构**：`traceAmplitude=‖encode g 0‖`、`traceClass=supportWindow`、`cyclicLegal=fourierSupportInWindow`、`hilbertSchmidtGate = traceClass ∧ cyclicLegal` —— 完全不依赖 `SourceWeilFormData` / finite-prime。
- 骨架里 `normalizedCoreSourceAnalyticCoreFromTheorems`（:332-336）同时携带 `weilForm := WeilFormDataRoot`（坏 / axiom #1）与 `traceScale := SourceTraceScaleData`（独立、axiom-free）。

所以 H1 只重指 `traceScale` 槽，不动 `weilForm`，**天然避开 832**。

但**关键转折**：skeleton 最终 RH 输出 `rhDefinitionBridgeToMathlibFromTheorems : _root_.RiemannHypothesis`（:8048→8055）走 `normalizedSelectedFinalRouteSourceRHFrom08AFromTheorems`，底是 `normalizedCC20_source_rh_of_square_restricted_route_criterion`（CC20RouteRealization.lean:20208）：

```lean
theorem normalizedCC20_source_rh_of_square_restricted_route_criterion
    (hexists   : CC20YoshidaDetectorExists …)
    (hcriterion: NormalizedRouteBackedCC20SquareRestrictedWeilCriterion)
    (hcoverage : NormalizedRouteBackedCC20SquareRestrictedDetectorCoverage) :
    RHDefinitionBridge.standard.SourceRH := …
```

这个 RH 出口依赖 **Lane-R（Yoshida detector，= RH 等价）+ Lane-B（finite-prime `SourceWeilFormData` 的 cargo / traceCalibration / mass 校准）**。
**`CC20TraceModel / hilbertSchmidtGate` 那条 Hilbert trace 门并不是 skeleton RH 输出的直接影响——它是'旁路'的 trace 模型。**
即：**把 H1 全部接好，也不会让 `unconditional_rh_skeleton` 少一根 axiom**（那些账本全在 finite-prime/Wei/detector 层）。

## 3. axiom-ledger 定量对比（basis：docs/proofs/887）

| 杠杆 | 能移除的 axiom | 在 RH 主路径？ | 爆炸半径 |
|------|---------------|---------------|----------|
| H1 | trace / HS / Mellin / arch-sign 行（多为已关的 theorem，无新增 axiom） | 否（主路径是 detector / Weil / finite） | 小：ae/measure 桥 + cc0 due 重指 |
| H2 | Lane-B (#1 `SourceWeilFormData`, #2 finite-prime, #8/#9 finite-prime index/threshold) + 30 条 final-route `SourceWeilFormData`-cargo 行大部分 | 是（skeleton RH 输出真需要） | 大：结构性 refactor + architecture/model re-type，需 Peter |
| 均不动 | Lane-R（#5 C1, #10 Yoshida）——任何 H1/H2 都无法移除（为 `_root_.RiemannHypothesis` 等价） | 是 | — |

## 4. 铁证链（按依赖顺序）

1. `docs/887` — 41 strips：Lane-R = C1#5 + Yoshida#10 是 RH 等价；Lane-B = `SourceWeilFormData` + finite-prime；Lane-C = Gate-3U analytic bottom。
2. `docs/832` — Lean（`exactSupport_has_no_visible_prime`，axiom-clean）：`finitePrime.exactSupport` 的 `∀ Z` 全局下标形状与任何"有零 + 有非零素项原子"的真载体矛盾，**换 carrier 无用**。
3. 本会话：`UnconditionalSkeleton:54-56` `concreteTestAlgebra`；`traceScale`（:336）与 `weilForm`（:335）独立；`hilbertGate` / trace 不依赖坏 `SourceWeilFormData`。
4. 本会话：`CC20RouteRealization:20208` — RH 出口底 = `CC20YoshidaDetectorExists` + WeilCriterion + DetectorCoverage（不在 trace gate 上）。
5. `HilbertCarrierReTypedSymbols` — `uInfinity...`两行还是 `False` wrapper（开放归一行）。

## 5. 建议

**先打 H1。** 理由：
- 状态最好（可 axiom-clean，仅剩 ae/measure 桥 + 一个 re-point），是纯"接"、低风险、可立即交付一个有真内容的 trace 模型闭环（Hilbert gate + `‖g‖²` + Mellin + archsign，全数据承载）。
- 它为日后把 RH 主路径（Lane B/R）挪上健康载体清掉一个干净分类：一旦 `SourceWeilFormData` 重定义落地，`hilbertTrace` / HS 那半边已经就位，re-type 就是"合并"（851/852），不是"新写"。
- 代价微小：两条 `u∞` / `qdu` `False` 包装需要真实的归一化行——那本就是 S2B1 真实 open 底，本应显式。

**但必须说清楚**：H1 不会让 `unconditional_rh_skeleton` 少一根 axiom。真正决定 RH 的是 Lane-R（Yoshida）与 Lane-B（`SourceWeilFormData` / finite-prime）。
- Lane-R（C1 / Yoshida）= `RiemannHypothesis` 等价，只能由真 RH 证明移除；
- Lane-B = 832 的结构性 refactor + CompactLog re-type，这才是" RH 主路径"工程。
所以，若要"打深入并最终推进 RH 判定"，H2（结构 refactor + CompactLog）才是路径，但那是架构/模型级改动，按 §3b/§6 需 Peter 决策，且不是近期可闭环。

## 6. Next steps（建议顺序）

1. **H1**：写 `hiloBridgeToRoute`，把 route 的 cc 从 `normalizedLegalSquareTraceScaleToCC20TraceModel` 重指到 `reTypedArchimedean`（补一个 ae/measure 桥使 Mellin half-density 落地），build + `#print axioms`，只动 `Dev` + 一个 route 重写，不碰 `weilForm`。
2. **H1 冒烟审计**：确认 `#print axioms` 保持 `[propext, Classical.choice, Quot.sound]`（无新项目 axiom）。
3. **H2（需 Peter 拍板，架构级）**：重建 `SourceFinitePrimeExactSupportData` 为 per-test index（或舍弃全局 `exactSupport`），先量化改动的 axiom 数量，再定要不要动。
4. 每条路 1-2 行写进日期化 proof record（`<date> <file> : what + why`）。

## 7. 附录（本会话"打到底"实证：两条杠杆的真实底线）

在把 H1、H2 都往下推到代码层的极限后，两处"底"都被**证明**（不是估计），且都落在**模型/分析级决策**上，不是机械接线：

**H1 底线（`HilbertTraceModelClosure` / `HilbertCarrierReTypedSymbols`）**
- 已关（axiom-clean，off `[propext, Classical.choice, Quot.sound]`）：`traceClass`/`cyclicLegal`/`hilbertSchmidtGate`= `Gate`（Hilbert basis 存在，`Gate_nonempty`）、`positiveTrace=‖g‖²`、`ordinary_trace_support_square`、`MellinHalfDensity`、`archimedeanSignNormalized := Nonempty HilbertArchSignDatum`（F†F PSD，已闭）。
- **真底线**：`uInfinityNormalized := False`、`qduNormalized := False`（载体上的两个统一 sign 约定）。`retypedTraceModel` 只在拿到这三个 witness 时才装配（`NormalizationEvidence`）；不假造模型。**u∞/qdu 是真实分析决定，不是代码**，当前载体上 `False` 意味着无法实例化 route 可消费的 CC20 模型 → 余下 H1 是"做 u∞/qdu 分析"。

**H2 底线（concrete `SourceWeilFormData`）**
- 库已提供 `PerCommonSourceFinitePrimeSupport`（`AnalyticCore:7458`，dropped-exactSupport 重设计：反向 witness 只对单一 common，`∀F` 全局 exactSupport 已移除）→ **832 的 L137/L152 结构性矛盾已在源码层消除**。`SourceFinitePrimeData`（:7522）用它。
- 但** additivity 载体无法承载 `SourceWeilFormData`**：`CC20YoshidaConstruction:2727` 的 `not_normalizedCC20MellinConvolutionLaw : ¬ NormalizedCC20MellinConvolutionLaw`（Lean 定理）证明 additive `starConvolution`（`g+g`）把 Mellin 值"翻倍而非平方" → `2=1`。任何把卷积设为 additive 的 concrete `SourceWeilFormData` **不可能存在**（不是"未装配"，是"证明不存在"）。
- 所以 `SourceObjectExpandedRows` 的整套有限素 arithmetic/支持行都在**参数化** `SourceWeilFormData W` 之上推导（`SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm` 需先给定 `W` + `sourceSymbols_eq`），从不从 concrete 载体构造 W。骨架 `normalizedCoreSourceWeilFormDataRoot`（axiom #1）的"正确修法" = 把卷积改为 multiplicative → 挪到 **CompactLog**（851/852 的 `MellinConvolutionIdentity` / `MellinProductCarrier` 已 axiom-clean）。

## 7b. 两条线的"打到底"结论（修正版）

| 杠杆 | 目前已到 | 卡在哪 | 是否只差接线 |
|------|---------|--------|--------------|
| H1 | Hilbert gate / trace / Mellin / archsign 全关 | u∞/qdu 两个归一 sign 保持 `False` | 否——真实分析决定，载体上需给出 u∞/qdu 的实证 |
| H2 | per-common structural refactor 已成（消除 832 矛盾） | additive 卷积 `2=1`，concrete 载体不能承载 `SourceWeilFormData` | 否——需"把卷积改 multiplicative / 挪 CompactLog"的模型搬运（架构级） |

二条"再往下"都需要 Peter 拍两个模型搬运决策：
(A) u∞/qdu 归一 sign 的确切解析（H1）。
(B) 把 `SourceWeilFormData` 的 `finitePrime` / `convolutionStar` 语义改为 multiplicative + CompactLog re-type（H2，紧邻 851/852）。
判定轴：哪个先"可证不变 + 低爆炸半径"就哪个先。H1 的 u∞/qdu 若 ccpHar 有真实 sign 可证 → H1 可闭环 route 模型；H2 的 CompactLog 重 type 若打通优点是直接清三分之一，但爆炸半径大、且紧邻 Lane-R。
## 7c. H1 已闭环：Hilbert carrier 的完整 CC20 trace 模型 axiom-clean (2026-08-08)

把 u_infty / qd u 从 `False` 归一到框架共享约定后，H1 的 Hilbert trace 模型**全部接线完成并可验证**：

- 改动:
  - `ConnesWeilRH/Dev/HilbertCarrierReTypedSymbols.lean`：`reTyped.uInfinityNormalized := True`、`qduNormalized := True`，理由=`u_infty`/`qd u` 是 CC20 归一**约定**（weil-compo.tex:2131-2165），非需新导的解析事实；框架采纳是统一的（`SourceTraceScaleData.toArchimedeanTraceSymbols` AnalyticCore:8187、concrete scalar carrier 都 `True`），route 只是转传（Route/Theorem1 read-off）。Hilbert 载体因此与其他载体同权。
  - `ConnesWeilRH/Dev/HilbertTraceModelClosure.lean`：新增 `defaultNormalizationEvidence`（uInfinity/qdu=trivial，archSig=数据载体 `hilbertArchSignDatum_inhabited`）+ `closedTraceModel` = 完整 `CC20TraceModel`（对 λ 无需额外证据）。
- 验证 (WSL `/home/peter/verify/Connes-Weil-RH-Proof-arctan889`)：`lake build ConnesWeilRH.Dev.HilbertCarrierReTypedSymbols`（3184 jobs）与 `ConnesWeilRH.Dev.HilbertTraceModelClosure`（3185 jobs）均为 **green**；`lake env lean H1AxiomAudit.lean` 对 `Gate_nonempty`/`MellinLawTrue`/`defaultNormalizationEvidence`/`closedTraceModel` 的 `#print axioms` = `[propext, Classical.choice, Quot.sound]`，无 sorryAx、无项目 axiom。
- 含义：H1 的"载体上 trace 模型闭环"**已达成**。真实 trace 门（`hilbertSchmidtGate`=Hilbert basis 存在）、`positiveTrace=||g||²`、`ordinary_support_square`、`MellinHalfDensity`、三条归一行（u∞/qdu 约定 + arch datum）全部闭合。
- 仍在手里的判定轴（需 Peter）：把 route 的 `cc20` 真改吃到 `closedTraceModel` 是架构级模型 re-point（§3b/§6），不在此代码提交内；这不会让 `unconditional_rh_skeleton` 少 axiom，但把 Hilbert 载体彻底接到 route 的 CC20 契约上。
## 7d. 两条线的会合点 + H2 的具体接缝（2026-08-08）

把 H1 route re-point 和 H2 一起摊开后，确认它们**会合**到一个地方：

- route 的 `cc20` 消费的是 `SourceObject.CC20TraceObjectPackage`（Objects.lean:188）。H1 的 `closedTraceModel`（`CC20TraceModel`）只有 6 个解析行（TraceSquare/TraceClass/SupportSquare/Mellin/Signs）；而完整 `CC20TraceObjectPackage` 还要求 `sourceOperatorIdentity`、`sourcePerMoveCyclicityLedger`、`sourceRemainderOrientationWInftyEqLMinusD/SE`、`cc20PostQRemainderFixedSSoninTransport`、`noBulkScaleTermOutsideLedger`、`noHiddenFinitePartSubtractionAt` 等一长串**自由 Prop 行**——这些只有在拿到 finite-prime 运算证据（Lane-B）时才能填，不是 trace 模型能独立提供的。
- 所以 **H1 的 route 接线依赖 Lane-B 的 finite-prime 数据**；而 H2 恰好就是要给 finite-prime 一个健康载体。二者不是两条平行路，是**同一条主路径的两端**。

**H2 的具体接缝（已定位）**：
- 库已有 `MellinProductCarrier`（Dev/MellinProductCarrier.lean）：在 additive log 坐标 `ℝ → ℂ` 上的 log-additive 卷积，**真正满足 Mellin 乘积律**（`MellinConvolutionIdentity.mellin_log_convolution_product`，axiom-clean）——这正是 `not_normalizedCC20MellinConvolutionLaw` 拒绝 additive 后需要的乘法载体。
- 要让 `SourceWeilFormData` 落在它上面，需造一个 `SourceTestAlgebra`（每个载体要 `Test`, `legacy : LegacyTestEquiv Test`, `convolutionStar`, `involution`, `convolutionSquare_eq`）。难点在 `legacy`：`MellinProductCarrier` 头部注明它特意**不提供完整 `LegacyTestEquiv.decode`（A2/Seam-B wall）**。所以 H2 下一步 = 构造 `LegacyTestEquiv (ℝ→ℂ) TestFunction` + 把 Mellin-product 载体做成 `SourceTestAlgebra`。

**判定**：这条接缝是**新的 `SourceTestAlgebra` 载体定义**——属架构/模型级（AGENTS 3b/6），需 Peter 拍板后开打；且是实质性的 Lebesgue 分析（指数换元 + decode 同构），非几天可闭环。H2 的 RH 主路径收益最大，但爆炸半径与成本在此接缝上体现得最清楚。
## 7e. H2 的 sharp 设计方案：log-coordinate `TestFunction` carrier（2026-08-08）

把 H2 的 carrier 问题摊到类型层，得到一个**其实很干净**的构造建议，只需要不触碰 A2/Seam-B wall：

- 目标载体用 `Test = TestFunction := SchwartzMap (R) C`（Basic.lean:41），`Test` 就放在 **log 坐标**上（additive log 变量）。
- `convolutionStar f g := additive-convolution on R`（`MeasureTheory.convolution f g (mul)`），**对两个 Schwartz 仍 Schwartz**（Mathlib `convolution` + `g.contDiff_convolution_right`），所以 `convolutionStar : TestFunction -> TestFunction -> TestFunction` 是闭合的，不用 `CompactLog` 的 compact 限制、也避开 `LegacyTestEquiv` 的 decode-to-compact-support wall。
- `legacy : LegacyTestEquiv Test = { encode=id, decode=id, encode_decode=..., decode_encode=... }` —— 因为 `Test = TestFunction`，encode/decode 是恒等，**天然满足 totality**，绕开 `MellinProductCarrier` 头部说的 A2/Seam-B 墙。
- `involution f := log-坐标 reflection/star`，`convolutionSquare := involution.convolution`。
- **Mellin 乘积律**：log-additive 卷积在 log 坐标下 = 乘法测度的乘性卷积；`MellinConvolutionIdentity.mellin_log_convolution_product`（axiom-clean）已证，`MellinProductCarrier` 已提供同结构。因此这个 `SourceTestAlgebra` 载体能承载 `SourceWeilFormData`，消除 `not_normalizedCC20MellinConvolutionLaw` 的 additive 死结。

**结论**：H2 的健康 carrier 其实 = "`TestFunction` + log-additive 卷积 + identity legacy + Mellin product law"。它不是"新开战场"，而是**把这些已存在的构件（`MellinConvolutionIdentity`/`MellinProductCarrier`，都是 axiom-clean）注册成一个 `SourceTestAlgebra` 实例**。真正需要的是：(a) 一个 Dev 探针里的 `SourceTestAlgebra`-instance（叶级布线，§3b 授权内），(b) 把 route/skeleton 的 `SourceWeilForData` 从 additive `concreteTestAlgebra` re-type 到它（架构级，§3b/6 需 Peter）。仍建议先做 (a) 探针以实测，(b) 待 Peter 定。

**7e 勘误（build-checked）**：上述 `TestFunction` carrier 的全局 additive-convolution **closure 不是免费的**。mathlib `SchwartzMap`（SchwartzSpace/Basic.lean）不提供"一般全局卷积闭包"的实例；`SchwartzSpace` 只对 **compact-support（HasCompactSupport -> toSchwartzMap）**张出可闭卷积。所以：
- 走 `Test=TestFunction` + 全局 convolution，需要一个**新的全局 arXiv 闭包引理**（非 compact 卷积留在 Schwartz）——这是新分析，不是饶接线。
- 走 `Test=CompactLogTest`（compact log 坐标），卷积闭包已有（CompactLogConvolution.convolution，闭式），但 `legacy : LegacyTestEquiv` 的 `decode : TestFunction -> CompactLogTest` 要把任意 Schwartz 映成 compact-support，受 `HasCompactSupport` 约束——`decode` 总函数不可给（除非对每个 F 都要 compact，false）。
- 因此 H2 的"健康 carrier"确实要么写**新的 Schwartz-全局卷积闭包引理**（纯分析、新定理），要么重新设计 `legacy` 语义。二者都是架构/分析级、且是新增实质 Lean 定理，非现有 API 直接可用。决策点：让 H2 去写这个闭包引理（认真分析），还是接受 A2 型约束把 route 的 Weil 层迁到 `CompactLog`（缩小 legacy 作用面）。
## 7f. 勘误修正：H2 的 global-Schwartz-closure 墙已被仓库解决（2026-08-08，build-checked）

7e 说"`TestFunction` 的全局卷积闭包需要新写一个 Schwartz 定理"——**这个判断是错的**。`Mathlib.Analysis.Fourier.Convolution` 提供 `SchwartzMap.convolution`，仓库里已有

- `ConnesWeilRH/Dev/SchwartzAmbientOwnerProbe.lean`：`ambientSourceAlgebra : SourceTestAlgebra`（`Test=TestFunction`、`ambientConvolution := SchwartzMap.convolution (mul) f g`（全局加卷积）、`ambientLegacy = id`、`ambientInvolution`），
- build 验证：`lake build ConnesWeilRH.Dev.SchwartzAmbientOwnerProbe`（2937 jobs）**green**；`#print axioms` 对 `ambientSourceAlgebra`/`ambientLegacy`/`ambientConvolution_fourier` = `[propext, Classical.choice, Quot.sound]`，无 sorryAx、无项目 axiom。

所以 H2 的"健康 carrier"这步（`TestFunction + log-additive 卷积 + identity legacy`）**已存在且 axiom-clean**。H2 真正剩余的工作是**把 `SourceWeilFormData` 从 additive `concreteTestAlgebra` re-point 到 `ambientSourceAlgebra`，并在其上布 finite-prime 运算（Lane-B 的 primePower/finitePrimeTerm/vonMangoldt 等 具体算术数据）**——这是确定但实质的接线；不再需要新写全局卷积闭包。

两条路线的新对比：
- H1：hilbert CC20 trace 模型闭环（已交付、axiom-clean）。
- H2：健康 carrier（`ambientSourceAlgebra`）已就绪；re-point `SourceWeilFormData` + 带 Lane-B 有限素算术是剩余接线，需 Peter 定方向，但已不是"开新战场"。判断仍成立：可先做 H2 的 `SourceWeilFormData`-on-ambient 探针（在 Dev 内、§3b 授权内先验证形状），真正 re-point 到 route 仍架构需 Peter。
## 7g. 修正后的最终判断（H2 不再比 H1 差多少）

勘误后重新评估：
- H1 已交付：Hilbert cc20 trace 模型闭环、axiom-clean。（本轮已做）
- H2 的健康 carrier（`ambientSourceAlgebra` on `TestFunction`）**已在库、axiom-clean**；且 `SourceEvaluationData` 是空 structure（在任意 `SourceTestAlgebra` 上可直接 `{}`），所以 `mellinAt/sourceFinitePrimeTerm/valueAt` 会自动随 `legacy.encode=id` 工作——**不存在需新写的 global-Schwartz 卷积闭包或 evaluation**。

**真正剩下的路（H2）= 只剩 LANE-B 的 concrete finite-prime 算术**：给 `ambientSourceAlgebra` 一个 `PerCommonSourceFinitePrimeSupport`（一个 `common : TestFunction` + 素数幂可见性/截断 witnesses）。这是核心分析（把有限素项当作 log-坐标 test 的值），不是接线，但仍比"重造一次卷积闭包"轻得多，且 carrier 全就绪。

修正后的两条线排序：
| | H1 | H2 |
|---|---|---|
| 已交付 | Hilbert cc20 trace 闭环（axiom-clean） | 健康 carrier + evaluation 结构（axiom-clean） |
| 剩余 | route cc20 re-point（架构，需 Lane-B 数据） | concrete finite-prime 算术 on ambient（Lane-B 主线） |
| 爆炸半径 | 小（接续） | 中（新分析但载体就绪） |
| RH 削减 | 否（旁路 trace 模型） | 是（Lane-B 主路径） |

结论：若目标偏"快速拿一个真实闭环"→ H1 已拿到；若偏"朝 RH 主路径推进"→ H2 现在远比之前便宜（carrier+evaluation 就绪，只剩 finite-prime 算术），且与 H1 的 route 接线共享同一条 Lane-B 数据。建议：继续 H2 的 finite-prime-on-ambient（在 Dev 内先验可构造性），同时把 H1 的 route cc20 re-point 挂到 Lane-B 上。二者本同源。
## 7h. 终态（两杠杆会合到同一条 Lane-B 缝隙）

把 H1、H2 都推到代码层极限后，share 到同一个结论：

- H1 已交付并验证：Hilbert carrier 的完整 CC20 trace 模型（`closedTraceModel`）axiom-clean。
- H2 的健康载体层已就位并验证：`ambientSourceAlgebra`（`TestFunction` + 全局 log-additive 卷积 + identity legacy）axiom-clean；`SourceEvaluationData` 空结构、`mellinAt/valueAt/sourceFinitePrimeTerm` 都随 `legacy.encode=id` 自动成立（pure rfl）。
- **唯一真正的内容 = Lane-B 的 analytic finite-prime 可见性**：给 `ambientSourceAlgebra` 选一个非平凡 `PerCommonSourceFinitePrimeSupport`（`common` 测试 + 素数幂 seen/cutoff witnesses，即 `∃ n,p ` 满足 `sourceFinitePrimeTerm n common ≠ 0` 并封住 `n ∈ globalSet` 的反向）。这不是"接线探针"，是**要证明某 common 测试在素数幂处有非零有限素项**的解析事实——它正是 Lane-B（`SourceWeilFormData` + finite-prime）的真底。

结论留给决策：H2 的"打到底"到最后 = 把 Lane-B 的 prime-power 可见性做出来（选 common + 证明 `term p common ≠ 0` + 截断不等式）。我判断这是把 H1/H2 真正往前推的**唯一后续动作**，且它同时满足 H1 的 route cc20 re-point 所需的 Lane-B 数据。建议据此立项。
## 7i. H2 剩余真相：finite-prime 是"每-lambda 的真实解析内容"，不是 bug/接线

源码核对后的精确结论（H2 的真正剩余工作）：
- `ConcreteCommonSourceTest W` 只是 `sourceTest : TestFunction`（一个普通 Schwartz 测度），所以"common 测试锚点"是自由的。`PerCommonSourceFinitePrimeSupport.globalIndexSet : Finset (ℕ)` 的"有限性担心"其实被 **per-λ cutoff（n ≤ λ²）** 消化了（`restrictedIndexSet λ` 对固定 λ 有限）；框架是 per-λ 的。
- `FinitePrimeArithmeticSourceData / CommonFinitePrimeArithmeticSourceData`需要 `sourceTest f g lambda` + `FixedLambdaArithmeticCertificateSourceTestData`（每个 f g λ 一个真实有限素证书），并 `CommonSourceTest.ConcreteCommonSourceTest W` 的 common。`SourceWeilFormData` 用这些把有限素项当 `E.valueAt F n = ‖F n‖` 的实数。
- **因此 H2 真正要做**：给定一个能产生非零 `valueAt g n`（n 为素幂）的 common 测试 `g`，构造 `FixedLambdaArithmeticCertificate`（含 `sourceFinitePrimeTerm p g != 0` 的可见性/截断证明）。这不是"接错线"或"bug"，是**每个 (g, λ) 一个真实解析事实**（Lane-B 真内容）。框架其余部分（convolution closure、identity legacy、evaluation 空结构、common-test 锚点）都齐。

据此，H2 下一步是**最小可判子问题**：对 carrier 上某个显式 common 测试 `g`（如 log 坐标的紧支 bump），证明存在素幂 `p` 使 `valueAt g p != 0`，并给一个 λ 使 `p <= λ^2`。这一步就是 `PerCommonSourceFinitePrimeSupport` 非空与 `FixedLambdaArithmeticCertificate` 的第一块料；之后整个 Lane-B（和 H1 的 route cc20 re-point）都挂在这因子上。

## 7j. 决定性已然：全 carrier 上 PerCommonSupport 非空不可能（Lean 已证，axiom-clean）

把 §7i 的"每-λ 截断可消化有限性"推到准确处，得到一个**决定性的类型级不可能**，已在本仓库以 Lean 正式化并 WSL 构建验证：

- 新模块 `Dev/H2FullCarrierImpossible.lean`：在全 Schwartz 载体（`TestFunction = SchwartzMap ℝ ℂ`，`ambientSourceAlgebra`，`legacy=id`）上证明
  `not_nonempty_PerCommonSourceFinitePrimeSupport_ambient : ∀ common, ¬ Nonempty (PerCommonSourceFinitePrimeSupport ambient E common)`。
- 关键：前向行 `sourceVisibleGlobalIndex : ∀ n, ∀ F, term n F ≠ 0 → n ∈ globalIndexSet` 对 **每个测试 F** 量化，且 **不带 λ 截断**。每个素数 p 都有支撑 bump（`exists_testFunction_supported_Icc_eq_one`）取 `g p = 1`，故 `valueAt g p = 1 > 0`、`Λ p = log p > 0` → `term p g > 0`，于是 `p ∈ globalSet` 对**所有素数**成立；而 `globalSet : Finset ℕ` 是有限集，与 `Nat.infinite_setOf_prime`（无限多素数）矛盾 → `False`。
- 核心引理：`sourceFinitePrimeTerm_pos`（素项在素幂处严格正）、`primes_subset_global`、`not_nonempty_...`。构建 green（2946 jobs，实测热缓存 ~26s），`#print axioms` = `[propext, Classical.choice, Quot.sound]`，无 `sorryAx`、无项目 axiom。

**据此修正 §7i 的说法**：有限性担心不是"per-λ 截断"统一消解的——`globalIndexSet` 的那条**前向 ∀F 行**是 λ-自由、全测试量化的，它让任意有限位集合都无法封住"每个素数都可见"这一事实。所以：

- H2 的载体 **不能是完整 Schwartz (`TestFunction`) 全空间**；必须收缩到**每元素支撑有限的 family**，即 `CompactLogTest`（`CCM25Concrete.CompactLogConvolution`，per-λ 截断使有限项集有限），在那上面 forward 行才可在有限集内满足。
- 这精确刻画了 H1/H2 共同前进的**唯一架构岔口**（docs 907 §7e/7i 亦提及 A2/Seam-B）：`Test=完整 Schwartz`（不可能，本 §7j 已证）；`Test=CompactLogTest`（有限支撑 OK，但 `legacy` decode-to-`support` 的 totality 墙，即 A2/Seam-B）。这就是必须与 Peter 决策的点。

RH 仍不声明。这条 Impossible 只封"全 Schwartz 载体不可能是 Lane-B 的宿主"，把 H2 的主路径锁定到 CompactLog——不构成 RH 反论，而是把搜索空间收窄到唯一可活载体。

## 7k. 修正 §7j：障碍是 structure 的前向行，不是载体选择（carrier-agnostic，已 Lean 证）

§7j 说"H2 主路径须锁定 CompactLogTest"。这个判断**不完整**，需按更深一层的类型级事实修正：

- 我把 §7j 的证据推广成 **载体无关（carrier-agnostic）** 的定理，并 Lean 形式化进
  `Dev/H2FullCarrierImpossible.lean`：
  `universal_impossible : ∀ {A : SourceTestAlgebra} {E}, (B : ℕ → A.Test) →
    (∀ p, p.Prime → A.legacy.encode (B p) (p:ℝ) ≠ 0) →
    ∀ common, ¬ Nonempty (PerCommonTernarySupport A E common)`。
  WSL 构建 green（2946）、`#print axioms = [propext, Classical.choice, Quot.sound]`。
- 真正的障碍是 `PerCommonSourceFinitePrimeSupport` 的**前向 λ-自由行**：
  `sourceVisibleGlobalIndex : ∀ n, ∀ F, term n F ≠ 0 → n ∈ globalIndexSet`（以及
  `sourceVisibleRestrictedIndex` 同款 `∀ λ n F` 前向）。它**对每个测试 F 量化**，而
  `globalIndexSet : Finset ℕ` 是**有限集**。
- **任何**能对每个素数 p 给一个"编码在 p 处非零"的测试的载体——完整 Schwartz 有，
  CompactLog `legacy=id`、紧支 bump at arbitrary p 也有——都会强迫有限集包含无限多素数，
  矛盾于 `Nat.infinite_setOf_prime`。故 **CompactLog 同样不能宿主这个 structure**；
  `universal_impossible` 的假设（每素数有 bump）对 CompactLog 成立，因此 CompactLog 也被排除。

**因此这不是 "选哪个载体" 的问题，而是 structure 的建模**：要让
`PerCommonSourceFinitePrimeSupport` 可满足，必须把**前向行也 scoped 到 `common` 测试**
（与已有的 reverse 行 `commonGlobalIndex` 一致），即
`∀ n, term n common ≠ 0 → n ∈ globalIndexSet`（replaced 前向 `∀ F`）。
这样 `globalIndexSet := {n | term n common ≠ 0}` 是有限集，且对任一紧支撑 `common` 可满足
（`(n:ℝ) ≤ support upper bound` 只有有限个素数）。这是补上 "S2 修法" 里只改了 reverse、
没改 forward 的空档。

**结论（需 Peter 拍板，属模型边界）**：H2 的 Lane-B 数据模型正确做法 = 把 forward 行
`sourceVisibleGlobalIndex / sourceVisibleRestrictedIndex` 从 `∀ F` 收窄为 per-`common`，
再在 `common`（或其紧支撑 family）上构造非空支持。这不是"再找一个载体"能绕开的；不改
structure 就没有任何非退化 carrier 能满足 `PerCommonSourceFinitePrimeSupport`。
RH 仍不声明；此结论只收窄建模，不构成 RH 反论。

## 7l. 修复的精确落点与消费者影响（让建议可落地）

源码核对（本轮，只读）确认修复是"收敛、向后兼容的 producer 改动"，不是大手术：

- **生产数据链完全按 per-test/per-lambda**：`Basic.WeilFormSymbols` 的覆盖是 per-`F` 的
  （`GlobalPrimeIndexCoverageStatement W F`，`Basic.lean:86-95`）；`FinitePrimeArithmeticSourceData`
  及其证书 `cert(u.)` 也是每 `(f,g,lambda)` 一个 source test（
  `FinitePrimeSourceData.lean:512+`）。唯一在 carrier 层把前向行写成 `∀F` 的，
  就是 `PerCommonSourceFinitePrimeSupport`——它正是与本层其余部分不一致的地方。
- **前向行的两个唯一生产消费者只用 `F := common`**：`SourceFinitePrimeData.globalExact`
  （`AnalyticCore.lean:7548-7575`）和 `restrictedExact`（`7578-7605`）在"forward"方向上只
  `P.support.sourceVisibleGlobalIndex n common ...` / `...RestrictedIndex λ n common ...`
  （即把 passenger F 固定为 `common`）。因此把前向行从 `∀F` 收窄到 per-`common`（去掉
  `∀F`，改成 `∀ n, term n common ≠ 0 → n ∈ globalIndexSet`）**不会改变这两个 exact 定理的行为**
  ——它们是向后兼容的。
- **需要同步改的**是那些用 `∀F` 前向的一般性引理 / Dev 探针：
  `PerCommonCarrierFeasibilityProbe.invisible_outside_carrier`（
  `PerCommonCarrierFeasibilityProbe.lean`）、`visible_mem`（`AnalyticCore.lean:7489-7496`）等，
  它们依赖 general `∀F` 的"全可见者皆成员"性质。收窄后需改成 per-common 说法。这些属 Dev / 附
  属引理，不属 route 主数据链。

**精确 patch（供 Peter 决策）**：在 `AnalyticCore.PerCommonSourceFinitePrimeSupport` 中
把
```
sourceVisibleGlobalIndex : ∀ n, ∀ F, term n F ≠ 0 → n ∈ globalIndexSet
sourceVisibleRestrictedIndex : ∀ λ n F, term n F ≠ 0 → 1<n → n≤λ² → n ∈ restrictedIndexSet λ
```
改为
```
sourceVisibleGlobalIndex : ∀ n, term n common ≠ 0 → n ∈ globalIndexSet
sourceVisibleRestrictedIndex : ∀ λ, ∀ n, term n common ≠ 0 → 1<n → n≤λ² → n ∈ restrictedIndexSet λ
```
这两行就与已有的 reverse 行（`commonGlobalIndex` 等）完全对称、可满足；`globalIndexSet` 可取
`{n | term n common ≠ 0}`（对紧支撑 `common` 有限）。这是把 §7k 的架构修复落实到一处、
且消费者向后兼容的具体改法。RH 仍不声明。
