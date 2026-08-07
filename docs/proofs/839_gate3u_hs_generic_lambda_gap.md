# Proof-717 / Gate-3U: 839 — the real open 3U point is the LAMBDA-GENERIC HS summability (unit-scale HS is closed); the `hilbertSchmidtGate" field is already proven

Date: 2026-08-07 · Status: audit verdict (build-verified). This pins WHERE the
3U gate truly rests after 838: not on the HS gate proposition, and not on the
unit-scale prolate HS (both axiom-clean), but on the **generic-λ** HS
summability that the full fixed-source route must supply, which is still an
**open premise** (external `hfactor : Summable …`).

PROBE: repo-native audit — `Dev/CC20ProlateTraceReductionAudit.lean`,
`Dev/AHilbertSchmidtGateReuseProbe.lean`, `Dev/A0WireFeasibilityProbe.lean`.
BUILD: WSL `lake build` (3198 jobs, successful).

## 0. Result (先讲结论)

```
Gate-3U 输入层              axiom 状态                         结论
──────────────────────     ───────────────────────────────     ──────────────────
hilbertSchmidtGate (field) hinge on traceClass ∧ cyclicLegal → 已证 bridge（AHilbertSchmidtGateReuseProbe）
sourceProlateHilbertSchmidtFactor_unit_summable (unit λ)     → axiom-clean（任务2 证实）✓
sourceProlateRemainder_unit_isTraceClassAlong (unit λ)       → axiom-clean ✓
generic-λ SUM ‖sourceProlateHilbertSchmidtFactor λ‖²          NOT a named closed thm → 真开放点
========================================================================================
Gate-3U 的承重输入 `hfactor : Summable λ·‖F λ‖²`（`sourceProlateRemainder_isTraceClassAlong`
的堆前提）在完整固定路线（generic λ）下**仍然作为 open 前提出现**，没有关合的 λ-general
HS 定理可供接入。
```

所以任务 1 的答案不是「某个 `…Root` axiom 是 3U 的占位」，而是：**Gate 自己关键
的 `λ` 依赖是「generic-λ prolate HS 可和」这一未经定理化的分析事实**——它被写进每条
`sourceSecondSupportProlate…` / `ThreeBranch…` / `Gate3U` 定理的签名，作为一个
`hfactor` 前提，而不是一个证出来的可复用引理。

## 1. Gate-3U 的经验层（都是 axiom-clean，不是占位）

`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCanonicalSupportGate3U.lean:180`
```
theorem canonicalRealGate3UAt_of_supportMajorant
    … (hfactor : Summable fun i =>
          ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    canonicalRealGate3UAt … (canonicalRealGate3USupportMajorant …)
```
唯一非结构输入就是 `hfactor`。再上一步 `sourceBandGramTrace_norm_le_invLowerFactorSq_supportEnergy`
也吃同一个 `hfactor`。而 `canonicalRealGate3USupportMajorant`（:167-176）把
`Σ ‖sourceProlateHilbertSchmidtFactor λ (basis i)‖²` 放进了 majorant 本身——

因此 **如果** `hfactor` 有 λ-一般可和，那 `canonicalRealGate3UAt` 就是干净成立的；
**现在** λ 一般可和还只是前提。这就是「3U 表层 HS」在 838 已关（unit），而「完整
路线 Gate」仍接不上（λ）+ 的表白。

## 副本可核查的 axiom-clean 客户（任务 2 的结果）

```
sourceProlateHilbertSchmidtFactor_unit_summable          → [propext, Classical.choice, Quot.sound]
sourceProlateRemainder_unit_isTraceClassAlong            → 同上
norm_unitProlateFactor_lt_one                            → 同上
unitRawSupportCrossing_summable_of_additiveKernel…       → 同上
```
WSL `lake build ConnesWeilRH.Dev.CC20ProlateTraceReductionAudit` (3198 jobs) 直接对
`#print axioms` 证实。**没有任何 `sorryAx`、没有任何取名 `…Root` 的 axiom** 进到
这些 unit-scale HS 结论。

## 细链（the unit λ → generic λ 的唯一缺口）

```
unit λ HS 已 axiom-clean:
   unitRawSupportCrossing_summable_of_additiveKernelIdentification (axiom-clean)
   norm_unitProlateFactor_lt_one                                  (axiom-clean)
   │ └─ sourceProlateHilbertSchmidtFactor_unit_summable           (axiom-clean) ✓
   │
Route 需要 (generic λ):
   hfactor : Summable ‖sourceProlateHilbertSchmidtFactor λ‖²      ← 无泛型定理
   └─ canonicalRealGate3UAt                                        ← 正 Gate，接受 hfactor 前提
```

没有看到任何 `sourceProlateHilbertSchmidtFactor λ` 的**泛型** Summable 定理、也没有
λ-scaling/transport 把 unit-scale 结果搬到 general λ。所有泛型出现（`SActualBand…`、
`ThreeBranch…`、20 余文件）都是把它当参数消费，非生产。

## Gate-不是 只是 A0 的拆解

A0 之前担心的「是否需要非平凡 test 使 hilbertSchmidtGate 成立」也已在
`AHilbertSchmidtGateReuseProbe`（self-adjoint + signed-boundary trace-class）和
`A0WireFeasibilityProbe`（statements 对 HS-carrier 可编译）处拆掉——
`hilbertSchmidtGate = traceClass ∧ cyclicLegal` 本身是@{simp} 定理
（AnalyticCore.lean:8150）。所以「Gate」这一层不拉 axiom；真正没被管线关死的唯一
分析事实是 **generic-λ 的 HS 可和**。

## Verdict（诚实）

1. **任务2 达成**：unit-scale 的 HS 输入整串 axiom-clean（build 证实），838 的判断
   不变——因子在连续载体上 HS。
2. **任务1 的点位**：Gate 的表层（hilbertSchmidtGate、unit HS、unit trace-class）
   全部 axiom-clean；**真开放点是 generic-λ 的 `Summable ‖ProlateFactor λ‖²`**——作为
   前提出现在 Gate 与 20+ 下游，而非作为已证定理。
3. **所以「杀掉 3U」的正确下一步**就是对泛型 λ 证明 HS（或给 unit 的 transport/
   equivariance 到泛型 λ）。这不是 Lean plumbing，是一个真正的分析定理缺口。
4. 这既不证明也不否定 RH；它把「3U 还差哪」的答案从「一个占位 axiom」细化到
   「一个未关合的泛型 HSL 事实」——比 314/四六更可下手。

## Repro

```bash
# WSL
cd ~/projects/Connes-Weil-RH-Proof
lake build ConnesWeilRH.Dev.CC20ProlateTraceReductionAudit
lake build ConnesWeilRH.Dev.AHilbertSchmidtGateReuseProbe
lake build ConnesWeilRH.Dev.A0WireFeasibilityProbe
```