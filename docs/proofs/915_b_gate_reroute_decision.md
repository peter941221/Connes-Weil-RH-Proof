# 915 (Door B, decision) — the route-level gate re-route: exact seam, roadblock, and plan

Status: STEP 1 of the re-route (archimedean gate slot) is BUILD-VERIFIED (916): `BGateSlotHilbertProbe916` closes it axiom-clean on the Hilbert carrier. The carrier re-wire (§4 steps 2-3) remains and needs a full cold build. No RH claimed. Zero `sorry`. No new `axiom`.


## 0. Bottom line up front

打穿 B 的唯一现实开口 **不是** 某个还没证的解析小 lemma，而是一条 **carrier 级的 gate 重路由**：

```
route 的 hilbertSchmidtGate (Test 级)  <-- 必须由非 axiom 的证据填充
         ^
         唯一已存在、非空、axiom-clean 的 gate 证据在 Hilbert 算子载体上
         (HilbertTraceModelClosure.closedTraceModel / Gate_nonempty)
         ^
         因此要把 route 的 archimedean.Test + SourceObject 耦合 重路由到 Hilbert 载体
```

要做到这一点是 **架构级改动**（涉及 `ArchimedeanTraceSymbols.Test` 的实际类型、
`SourceObjectPackage` 的 `cc20TraceTest_eq_commonTest` 桥、以及全体 route consumer 的
`archimedeanTest` 类型），需要一次可验证的长 WSL build。本 round 只把线路精确定位并给出
落地清单，不宣布闭合。

## 1. 现状：两条路分别停在哪个 gate

| 路 | gate | 状态 |
| -- | -- | -- |
| A-lane generic-λ `hfactor` | `Summable ‖sourceProlateHilbertSchmidtFactor λ (globalBasis i)‖²` @ generic λ | OPEN，有限网格测不出 (910/838) |
| B-lane `hilbertSchmidtGate` | `Objects.CC20TraceObjectPackage.sourceHilbertSchmidtGate : ∀ g, hilbertGate g` | OPEN，当前由 `…Root` axiom 填 |

B 不撞 A 的 λ 墙（913）：B 的 gate 是有限合取 `traceClass g ∧ cyclicLegal g`
（`AnalyticCore.lean:8177-8186`），不量化任何无穷谱和，是"有限"级的判断。

## 2. 精确缺位：route 实际消费的 gate field

`Objects.lean`：

```lean
structure CC20TraceObjectPackage where
  archimedeanSymbols : ArchimedeanTraceSymbols
  sourceTraceTest : archimedeanSymbols.Test
  sourceHilbertSchmidtGate : ∀ g : archimedeanSymbols.Test,
      archimedeanSymbols.hilbertSchmidtGate g          -- ← B 的洞口
  sourceTraceClassCyclicityTemplate : ArchimedeanTraceSymbols.TraceClassTemplateStatement ...
```

而 `hilbertSchmidtGate : Test → Prop` 在 route 载体 `SourceTestAlgebra A` + `SourceTraceScaleData T`
上定义成（`AnalyticCore.lean:8177-8181`）：

```lean
hilbertSchmidtGate g = T.traceClass g ∧ T.cyclicLegal g
```

`sourceHilbertSchmidtGate : ∀ g, …` 强制对载体上 **所有** 测试成立。要 axiom-free 地证明它，
必须选一个"每个测试都具备可证 HS 结构"的载体去定义 `Test` / `traceClass` / `cyclicLegal`，
否则 `∀ g` 是假命题，只能靠 `axiom`（现在的状况正是如此）。

所以 B 的修复不是"再证一个 lemma"，而是为 route 选定一个 `traceClass ∧ cyclicLegal`
**恒可证**的载体，再把 route 重路由到它上面。

## 3. 供选载体：Hilbert 算子载体（已有、非空、axiom-clean）

仓库里**唯一**已具备"每个载体元素都满足 HS gate"结构的，在 Hilbert 算子载体上：

| 组件 | 内容 | 位置 |
| -- | -- | -- |
| 载体 | `cc20GlobalLogCrossingL2` | `Source/CC20Concrete/GlobalLogCrossing.lean` |
| gate 谓词 | `Gate g = ∃ w, Nonempty (HilbertBasis w ℂ …)`；`Gate_nonempty : ∀ g, Gate g` | `Dev/HilbertCarrierReTypedSymbols.lean` |
| trace/square | `‖g‖²` 非负；trace-square 闭合 | `HilbertCarrierReTyped.reTypedArchimedean` |
| trace-class 内容 | smoothed crossing `IsTraceClassAlong`（rank-one base） | `Source/CC20Concrete/GlobalLogCrossingTraceClass.lean` |
| 整链 `CC20TraceModel` | `closedTraceModel`（gate/模板/普通/混合半密度/号归一化 closed） | `Dev/HilbertTraceModelClosure.lean` |

即：`hilbertGate` 需要的 `gate` 已在 Hilbert 载体上**非空、可证、axiom-clean**
（`Gate_nonempty`）。缺的只是把 route 的 `Test` 载体接到这里，并让
`sourceHilbertSchmidtGate` 改读 `Gate_nonempty` 为真，替换 `…Root` axiom。

## 4. 落地执行：三步

1. **载体接通**：route 正式 `archimedean.Test` 采用 `cc20GlobalLogCrossingL2`，符号取
   `HilbertCarrierReTyped.reTypedArchimedean`（`Test = H`，gate 恒为 Hilbert-basis 存在）。
2. **gate 卸载**：`sourceHilbertSchmidtGate g := Gate_nonempty g`（恒真、axiom-clean），
   `sourceTraceClassCyclicityTemplate := closedTraceModel.traceClassTemplate`，
   positive-trace 非负 / ordinary-trace-square 由 `‖g‖²` 给出。
3. **耦合重定位**：把 `Objects.CC20TraceObjectPackage` 之后（`SourceObjectPackage` 的
   `cc20TraceTest_eq_commonTest` 等）中的 compatibility Prop，从现在的 axiom 改为在新载体上
   证一版 real 断言。

### 4a. 三个可选路径（推荐 A）

| option | 内容 | 优点 | 缺点 / blast radius |
| -- | -- | -- | -- |
| **A（推荐）** | 把 route 正式 `archimedean.Test` 重定义到 `cc20GlobalLogCrossingL2` 算子载体（`reTypedArchimedean`） | 与已有闭环完全对齐；`gate` 已非空 axiom-clean；Hilbert 载体本就是 RH 正确起点(852-888) | 重写 `SourceObjectCoupling` + 全体 consumer；冷 build 数小时级 |
| B | 保留 `Test = TestFunction`，把 gate 直接引到算子级 HS | 少动 `SourceObjectCoupling` | gate 语意仍混 `Test`/算子两层，`∀ g` 更难证真；不推荐 |
| C | 建 `TestFunction ↔ GlobalLogCrossing2` 同构再嵌入 route | 概念优雅 | 需大量同构 + 迁移 lemma，blast radius 最广；暂缓 |

=> 推荐 **Option A**：不是"再找一个载体"，而是把 route 正式 re-type 到已有闭环定理的
Hilbert 算子载体上。

## 5. 验证现实

仓库只有唯一的持久 WSL 镜像（`.lake` 7.9G），且与本轮 Windows HEAD 属不同 git lineage 且 dirty。
按 rule 不 overwrite dirty / stale，cold build 需 isolated ext4 dir + 重新 seed（§8b 冷 tail 7h 量级）。
本轮的 gate-slot leaf（916）已单独 build 验证；唯一未做的是 SourceObject 载体重路由所依赖的全量冷 build（见 §7），无那一步 build 就不声称 B 全闭合。
## 6. Next steps


1. 新建 isolated ext4 verify dir（seed `.lake` 包缓存，排除 `.git/.lake`），对 Windows HEAD 做
   warm build 确认基线（914c seam 已 build-verified，此步复用）。
2. 按 Option A 落地：载体接通 + `sourceHilbertSchmidtGate := Gate_nonempty` + SourceObject 耦合重定位。
3. 全 build（final milestone）+ `#print axioms` 审计，确认 `sourceHilbertSchmidtGate` 只依赖
   `[propext, Classical.choice, Quot.sound]`，无 sorry / 新 axiom。
4. 三个 sign 行依赖 `closedTraceModel` 的 data-bearing 证据（888-wiring）；旧 M3 `D_S` / sign /
   rank-pole 仍是打开的解析 obligation，随 Proof717 链条一起评审，不打补丁。

RH 不声明。




## 7. Step 1 closed, build-verified (916)

`Dev/BGateSlotHilbertProbe916.lean` builds axiom-clean: `gate_slot_all : ∀ g,
  HilbertCarrierReTyped.hilbertSchmidtGate (reTypedArchimedean) g` depends only on
`[propext, Classical.choice, Quot.sound]` (zero sorry, zero new axiom).  This fills the
route `sourceHilbertSchmidtGate` slot (`Objects.CC20TraceObjectPackage`) once the route
adopts the Hilbert carrier — the finite first half of the re-route.

The full Hilbert model `HilbertTraceModelClosure.closedTraceModel` also builds (once the
stale mirror `.olean` for `HilbertCarrierReTypedSymbols` is refreshed).  `HilbertTrace
ModelClosure.lean` itself is unchanged (no source bug; the earlier build failure was a
stale build artifact).

Remaining B work = the `SourceObjectPackage` carrier wiring (§4 steps 2-3), which needs
a full cold build.

RH not claimed.


## 8. Step 2 partial: Hilbert CC20Interface layer build-verified (917)

`Dev/BCC20InterfaceHilbertProbe917.lean` builds in the WSL verifier with
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (zero sorry, zero new
axiom) on the Hilbert carrier:

- `gateSlotInInterface` : `forall g, hilbertSchmidtGate (reTypedArchimedean) g`
  (916's slot, re-exposed inside the assembled interface).
- `cc20InterfaceOfHilbertCarrier` : assembles `Source.CC20Interface` from
  `HilbertTraceModelClosure.closedTraceModel` rows (trace square, trace-class
  template, ordinary trace support-square, half-density Mellin, sign
  normalizations) + `RHDefinitionBridge.standard`, taking only the terminal
  finite-vanishing RH exit package as a carried argument (that exit source
  criterion is the RH step, not B's door).

So the CC20-interface layer of the re-route is now concrete + axiom-clean on
Hilbert.  This is the finite first half.  The true B door is DOWNSTREAM:
`Route.FullWeilPositivity` -> `toWeilPositivityInput` -> `fullWeilPositivity` ->
`c1InputData` currently needs a COHERENT Hilbert-backed RouteInputs, because the
route fixed-test frame is single-carrier (you cannot embed Hilbert archimedean
into a TestFunction-based SourceFixedSTest without re-typing the whole frame).
That is the remaining architecture-level re-wire (four steps in 915 section 4
step 2-3) and needs a full cold build.

RH not claimed.


## 9. Routes 1-3 verdict (2026-08-09)

- **Route 1 (trusted baseline) — DONE, verified.** Isolated ext4 dir
  `/home/peter/verify/cwr-b917`, Windows HEAD synced, vendor package cache seeded.
  `lake build ConnesWeilRH.Dev.BCC20InterfaceHilbertProbe917` = 3187 jobs clean;
  `cc20InterfaceOfHilbertCarrier` and `gateSlotInInterface` depend only on
  `[propext, Classical.choice, Quot.sound]`, zero sorry. This confirms the Hilbert
  CC20-interface layer on the CURRENT Windows lineage (not the stale mirror).
- **Route 2 (alternative positivity witness) — scan NEGATIVE.** No non-full-frame
  inhabitant of `WeilPositivityInput.fullWeilPositivity` exists in the codebase.
  The only producer is `Route.FullWeilPositivity`, which routes through the source
  model.
- **Route 3 (re-type fixed-frame to Hilbert) — BLOCKED at documented source bottom.**
  The route frame is `TestFunction = SchwartzMap R C`; re-typing to Hilbert does
  not remove the real blocker: `UnconditionalSkeleton` `normalizedCoreSourceWeil
  FormDataRoot` (axiom, L137) is contradicted by `not_nonempty_...` (L152), the
  concrete convolution is pointwise addition (non-Mellin), and L657/L1551 source
  bottoms persist (docs/831/833/834). Closing B soundly requires the shared-type
  source-model refactor (~31 files / ~200 edits), not a build hack. RH not claimed.


## 10. S1 L137 residue resolved (2026-08-09, build-verified)

The source-model false-axiom `normalizedCoreSourceWeilFormDataRoot` (L137 in
`UnconditionalSkeleton`) is GONE.  New leaf `Dev/ConcreteP1SupportProbe.lean`
constructs a real `PerCommonSourceFinitePrimeSupport` on `concreteTestAlgebra`
(common bump, value `1` at `t=2`, exact index set `{2}`, prime-`2` term strictly
positive) and lifts it to `SourceWeilFormData concreteTestAlgebra`
axiom-clean.  `UnconditionalSkeleton` now defines
`normalizedCoreSourceWeilFormDataFromTheorems := ConcreteP1SupportProbe
.concreteWeilForm` (no axiom).  Isolated build `cwr-b917`: `UnconditionalSkeleton`
3500 jobs green; `#print axioms normalizedCoreSourceAnalyticCoreFromTheorems` =
`[propext, Classical.choice, Quot.sound]`.  Remaining separate source bottom:
`normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot` (L657) still feeds
`ModelConstructorCoreFromTheorems`; that is the next S-obligation, not this one.
RH not claimed.


## 11. L657 (CCM25 finite-prime arithmetic source data) — honest assessment

Root `normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot` =
`CommonFinitePrimeArithmeticSourceData W` (W real after S1).  Unlike L137
(plain existence), L657 requires:

1. `finitePrimeData : FinitePrimeArithmeticSourceData W (concreteCommonSourceTest W common)` —
   the full `∀ f g lambda hlambda` certificate family.  Buildable from the per-common
   prime-`2` arithmetic read-offs via `FinitePrimeSourceDataBridge.ofSourceEvaluation
   VisibleCanonicalData`, given the evaluation-visible rows for the common test.
2. `scopedArchimedeanContributionBalance : restricted formula = global formula` —
   a real scalar identity (`SourceScopedArchimedeanContributionBalance`).

No real `def : CommonFinitePrimeArithmeticSourceData` exists yet in-repo; only
statement probes (`Parallel09A_CommonTestRows`, `Parallel09B_CertificateFamilyRows`).
Replacing L657 is the next real S-construction: a meaningful finite-prime arithmetic
+ balance obligation, not a seam.  Integrity guard: do not axiom-hack it. RH unclaimed.


## 12. L657 Step-A: rooted at the non-Mellin concrete convolution (2026-08-09)

Step A (`finitePrimeData` of `CommonFinitePrimeArithmeticSourceData`) requires the
`∀ f g lambda hlambda` finite-prime arithmetic certificate family, built on
`W.convolutionStar`.  The concrete skeleton carrier has pointwise ADDITION as its
convolution, and `not_normalizedCC20MellinConvolutionLaw`
(CC20YoshidaConstruction:2727) proves the Mellin-convolution law fails there
(a Mellin-one test IS doubled by the concrete operation instead of squared).  So a
sound all-pair family cannot be built on the current concrete carrier; L657/A
collapses back to the source-convolution redefinition (the documented
"composite carrier需重定义" root).  Forcing the family onto the additive carrier
would be unsound; this is out of honest per-leaf reach. RH unclaimed.
