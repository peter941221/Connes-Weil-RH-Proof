# 834 — "接线 L137" 的不可能性证据链：全链追到一个被证明为空的 axiom，无法非重构替代

Date: 2026-08-07 · Status: verdict (full-repo audit + build-verified probe, no code change to shared types).
Related: `docs/proofs/830_…`、`831_…`、`832_…`、`833_…`（探针根基）。
Probe: `CarrierReplacementFeasibilityProbe.lean`（axiom-clean，build 绿）。
File: `ConnesWeilRH/Dev/UnconditionalSkeleton.lean`（8060 行）。

## 0. 一句话结论

想在不改共享承载类型的前提下，"把 L137 这条假 axiom 接成真实 per-common 证书数据"——**不可能**。证据链显示：骨架所有 CCM25 有限素主线都追到**唯一一个赋值点** `SourceAnalyticCore.weilForm = normalizedCoreSourceWeilFormDataFromTheorems`（L322），它**唯一**的数据源是 L137 axiom，而 L137 断言的对象被 L152 证明不存在。要"接线"就必须先给 `SourceWeilFormData` 一个非假实例——但那需要改变它的概念（重定义类型），即 831 已判定的共享层重构。

## 1. 唯一赋值点：一处 axiom 撑起全链

全仓检索（`weilForm :=`、`: SourceWeilFormData`、`SourceAnalyticCore.mk`）唯一真实构造 `SourceAnalyticCore.weilForm` 的是骨架 L322：

```
L318 noncomputable def normalizedCoreSourceAnalyticCoreFromTheorems : SourceAnalyticCore where
L320   testAlgebra := …
L322   weilForm := normalizedCoreSourceWeilFormDataFromTheorems    ← 唯一赋值
```

而 `normalizedCoreSourceWeilFormDataFromTheorems : l := normalizedCoreSourceWeilFormDataRoot`，即 **L137 axiom**（L137-144）。

其余 `SourceWeilFormData` 引用（`AnalyticCore.lean` 的 psi/qw/…、`Route/RouteTheorem.lean:2736` 等、`CC20RouteRealization.lean:551/7318`、`CCM25TheoremBase.lean:130`）都是**消费者/签名/∃断言**，无一给出可执行的构造。且 `CC20RouteRealization.lean:13079` 的"真实路线"文件本身就是 `∃ A, ∃ sourceWeilForm : SourceWeilFormData A, …`——它把自己建立在 `SourceWeilFormData` 存在性上，**并不能作为非假构造源**。

## 2. 死循环：per-common 证书 ≠ 可替代 L137 的源头

骨架里 finite-prime 主线走 `…toWeilFormSymbols` → `WeilFormSymbols`：

```
L659  CommonFinitePrimeArithmeticSourceData normalizedCoreSourceAnalyticCore…toWeilFormSymbols
L667  FixedLambdaArithmeticSourceTestCertificatesForAllTests …toWeilFormSymbols
L2068 normalizedCommonFinitePrimeArithmeticSourceData …BaseFromTheorems.ccm25Model.toWeilFormSymbols
```

概念循环：

```
[证书] FixedLambdaCommonFinitePrimeSupportData (per-common) 需要 : W : WeilFormSymbols
[WeilFormSymbols] 来自 toWeilFormSymbols
[toWeilFormSymbols] 定义 = core.weilForm.toWeilFormSymbols (AnalyticCore.lean:8232)
[core.weilForm] 唯一的非假源 = L137 axiom → 已证空
```

per-common 证书（`CommonFinitePrimeArithmeticSourceData`、`FixedLambdaCommon…`）**是消费 `WeilFormSymbols` 的下游**，它不反向供给 `weilForm`。引入它不消除对 L137 的依赖，只是再加一层消费。

## 3. L137 为什么不可"换根"用真证书替代（结构性）

- `SourceWeilFormData` 需要：
  ```
  evaluation    : SourceEvaluationData A    == 空结构 → 可 .mk（trivial，可用于任何载体）
  archimedean   : A.Test → ℝ               == fun _ => 0（trivial）
  finitePrime   : SourceFinitePrimeData A E == 唯一卡点：exactSupport 的 ∀F 后端 witness
  ```
- 探针 `exactSupport_has_no_visible_prime`（axiom-clean）证明：这个 `∀F` 后端 witness（`n∈carrier → term n F ≠ 0`）让任何带零元素 + 可见素原子的载体都无法容纳非零素项 → `SourceWeilFormData` 在 concrete 及其同形载体上无对象。
- 因此 L152（正确拒斥该形状）是真的。要"填真" L137，唯一不是换载体所能，而是**重定义 `SourceWeilFormData` 的 `finitePrime.exactSupport`**（per-common / 证书形态），即共享层重构。

## 4. 可回滚、诚实、不动的端点

> `SourceWeilFormData` 是该项目历史性决定留下的"抽象偏执着"：把 per- лок的真实有限素数据（健康、可造、already 存在：`FixedLambdaCommon…`）起成"∀F 后端全局 exactSupport"。这个过度约束正是骨架 L137/L152 的数学死结。

所以"处理干净"的真相是：
- **不破坏**：L152 为正确判定，L137 是 false 前提——两者应一起移除/重写，而非保留互相杀。
- **真正接线所需**：把 `SourceWeilFormData` 的 `finitePrime` 改造成 per-common 形态（对齐 `FixedLambdaCommon…`），让真实可造数据能进入——这**必然**改共享类型（831 已量出 31 文件/约 200 处求和族爆）。
- **"接线消除 L137 但不碰共享层" = 数学上无路**（本 document 证明链）。

## 5. 建议（供 Peter 决策）

| 选项 | 内容 | 建议 |
|------|------|------|
| A1 | 保持现状，L137/L152 登记为"结构待换根"（RH 仍无条件），不改码 | ✅ 诚实、不破坏、最小 |
| A2 | 启动共享层重构 `SourceWeilFormData` per-common 重构（31 文件多轮 build） | 大手术，事后另做 |
| A3 | 把"不可接线"当作对"连接 40 根"的上限证据——所有 Coverage 根级联到 L137，故接线上限 = 无共享重构下不可达 | 证据固化（本 doc） |

我建议 **A1 + 保留 A3 这份证据**：在不对共享层动大手术的前提下，这是"能处理的处理干净、同时诚实记录不可处理的根因"的终点。若你要在 A2 投入，本证据链是起点（先重造 `SourceWeilFormData`）。

## Handoff

- Files read: `AnalyticCore.lean:7754-7993`（psi/toWeilFormSymbols）、`AnalyticCore.lean:8232`（toWeilFormSymbols）、`Basic.lean`（WeilFormSymbols）、`UnconditionalSkeleton.lean:137/141/322/657/2068`、`Route/RouteTheorem.lean:2736`、`Route/CC20RouteRealization.lean:13079-13110`、`FinitePrimeSourceData.lean:84`、`FinitePrimeInterface.lean`。
- Declarations changed: none（纯审计 + 探针已在此前）。
- Build: 探针 `CarrierReplacementFeasibilityProbe` 绿；骨架 `UnconditionalSkeleton` 基线（3495）未动。