# 832 — 载体替换不可行：L137/L152 矛盾是「结构性的」，不是「载体相关的」(Lean 已证)

Date: 2026-08-06 · Status: verdict (Lean build-verified).
Probe: `ConnesWeilRH/Dev/CarrierReplacementFeasibilityProbe.lean`
Build: `lake build ConnesWeilRH.Dev.CarrierReplacementFeasibilityProbe`（WSL，通过 2936 jobs）。
依赖: `ConnesWeilRH.Source.AnalyticCore.lean:7375`（`SourceFinitePrimeExactSupportData`）。

## 0. 一句话结论

**把 L137 的载体 `testAlgebra` 从 `concreteTestAlgebra` 换成 `cc20 GlobalLogCrossingL2`（CC20/Lp trace 载体）并不能消除 L137/L152 矛盾。** 因为矛盾不在"载体是 concrete"，而在 `SourceWeilFormData` 的 `finitePrime.exactSupport` 这个**结构性形状**：它要求一个「对所有测试 `∀ F : A.Test` 都成立的全局支撑下标」，任何带零元素、且含有非零素项原子的实载体都会撞上同一个矛盾。

这个结论**不是推理而是 Lean 定理**：`exactSupport_has_no_visible_prime` 的 `#print axioms = [propext, Classical.choice, Quot.sound]`（无 `sorryAx`、无根）。

## 1. 为什么「换载体」看起来可行（用户最初方向）

831 发现 L137（`axiom ...SourceWeilFormData ...`）与 L152（`theorem not_nonempty_... : ¬ Nonempty (...)`）在同一文件矛盾。自然的第一个修复方向是：

```
SourceWeilFormData concreteTestAlgebra      ← axiom 断言存在
```

它被证明不存在。那"换一个不矛盾的真实载体"（= `换真实载体`）似乎可避开：

```
SourceWeilFormData cc20GlobalLogCrossingL2   ← 尝试对着真载体构造
```

假设这样就能绕开 L152（L152 只驳 `concreteTestAlgebra`）。**这个方向被本 probe 否决。**

## 2. 结构性矛盾的本质（载体的 `∀ F` 两个消毒证人）

`SourceFinitePrimeExactSupportData`（AnalyticCore.lean:7375）合并了两条**对全体测试 `F : A.Test` 量化**的消毒证人：

```
sourceVisibleGlobalIndex  : ∀ F, ∀ n, term n F ≠ 0  ->  n ∈ globalPrimeIndexCarrier.1
globalPrimeIndexCarrier.2 : ∀ F, ∀ n, n ∈ carrier     ->  term n F ≠ 0
```

`term n (0)`（zero 测试）必须同时满足：

```
1. 若 n 在某可见项中被携带 → term n 0 ≠ 0   （来自 second witness）
2. 若 0 编码成逐点零函数 → term n 0 = 0      （来自 encoding identity, 结构性抵消）
```

这两条只依赖**独立于具体载体的零元素**（zero 的编码是点点零函数），**从不提及 `concreteTestAlgebra` 名字**。所以这条矛盾对 concrete、对 CC20-Lp、对任何未来"函数的向量空间"都成立。

## 2.2 为何探针构造非要一个显式 `z` 而不是 `(0 : A.Test)`

构建时第一个版直接写 `(0 : A.Test)`，Lean 报错 `difficulty synthesizing OfNat A.Test 0`：`SourceTestAlgebra` **并没有为 `Test` 提供 `Zero` 实例**，所以要证明"每个实载体的零元素"就必须把该元素当作显式参数 `z : A.Test` + 其"逐点零编码"为条件 `EncodesZeroPointwise A z`。这正是关键点：**每个实载体确实拥有这样一个 `z`**（concrete 用 `0`，Lp 空间用零向量），所以条件非空洞、且对所有实载体恒成立。

## 3. 判决（Lean 定理，axiom-clean）

探针证明了两条载-具体化无关的定理：

| 定理 | 内容 | `#print axioms` |
|------|------|-----------------|
| `zero_sourceFinitePrimeTerm` | 零元素 `z` 的 term 在任意下标 `n` 恒为 0 | `[propext, `Classical choice, Quot.sound]` |
| `no_nonzero_..._of_exactSupport` | 只要有零元素 `z`，excatSupport datum与任何非零 term 共存 | `[propext, Classical choice, Quot.sound]`（构建成功） |
| `exactSupport_has_no_visible_prime` | `¬ ∃ F, term n F ≠ 0`（结构性否决） | `[propext, Classical choice, Quot.sound]`（无 sorryAx） |

`exactSupport_has_no_visible_prime` 的证毕：给定任意精确支持 `S` 与任意可见 term `hnf : term n F ≠ 0`，`S.sourceVisibleGlobalIndex` 保证 `n ∈ carrier`，`S.globalPrimeIndexCarrier.2` 保证 `term n z ≠ 0`，与 `zero_sourceFinitePrimeTerm` 冲突。这是 `concrete_all_sourceFinitePrimeTerms_zero`（7399）的载体无关对账，the concrete name。

## 4. 结论：真修复必须重构 `SourceWeilFormData`，而非换载体

```
换载体（concrete → Lp）   ==>  失败，probe 已证   ✗
```

要真正处理 L矛盾，落点是**形状**：

- 让全局支撑载体的 witness **按测试对象分 index**：`carrier F`（去「一个下标对全体 F 都成立」的强性）；
  或
- **去掉 `exactSupport` 这个全局字段**，把支撑行的数据挪进「正文可读」的读表对（visible read-off row），不要在结构里强制"每个测试都带同样全局 index 且要 term n 0 ≠ 0"。

这是真正的数学/结构重排（影响 `SourceWeilFormData` 消费者：`SourceAnalyticCore`、30+ Root、整条归一化路线），不是一两行的载体 re-point。

## 5. 对「能接的全部处理干净」的更新

```
40 根
 ├─ C≈28  纯位移/输入包装  —— 仍等 A/B 存在后才有定义可填
 ├─ B≈4   定理形            → 1706 可白捡；1551/1665/5883 需单点
 └─ A≈8   源数据/地基       → 137 已确认「无法换载体解决」；
                                  真修复=重构 SourceWeilFormData 的形状
```

- L137/L152 不再是「换个 carrier 就好的装配坑」，而是真正的**建模行为选择：支持载波必须 per-test index。**
- 迭代工具账户结论不变：**「换 carrier」这条路关闭，「重构 `SourceWeilFormData.support`」是通往无绳基线地基/让其余 B/C 根落座的先决条件。**

## Handoff

- Files read: `AnalyticCore.lean:7360-7450`（ExactSupport 结构）、`CCM25SourceDataGuards.lean`、`CC20ConcreteTestSpace.lean`（发现 `normalizedCC20ConcreteTestAlgebra` 是 `concreteTestAlgebra` 的 abbrev，并非真差异载体）。
- Declarations changed: **新增** `ConnesWeilRH/Dev/CarrierReplacementFeasibilityProbe.lean`（3 定理，无关 Axiom，build 验证）。Source/Route 未改。
- Build: `lake build ConnesWeilRH.Dev.CarrierReplacementFeasibilityProbe`（WSL，through）。
- 下一步（需 Peter 裁量）：选**重构 SourceFormData**: ① 卡 per-test，② 去全局 exactSupport；或先只做"修改形状的最小版"探针。