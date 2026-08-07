# Proof-717 / Gate-3U: 838 — reconciliation: 837's finite-grid "non-HS" is a discretization collapse, NOT a fact about the continuum operator (the repo already proves the continuum factor IS Hilbert-Schmidt, axiom-clean)

Date: 2026-08-07 · Status: audit/reconciliation verdict (build-verified).
The conclusion flips 837's *reading*: the finite-grid result is real but it
does NOT transfer to the genuine operator. We reconcile 837 with an existing
axiom-clean repo theorem.

PROBE/REFERENCES:
- `docs/proofs/837_real_sonin_gate_factor_probe.py` (the finite-grid probe)
- `docs/proofs/837_gate3u_exact_r0_verdict.md` (its original reading)
- `ConnesWeilRH/Source/CCM25Concrete/CCM24SourceProlateTrace.lean`
- `ConnesWeilRH/Source/CCM25Concrete/CCM24UnitScaleProlateAlignment.lean`
- `ConnesWeilRH/Source/CCM25Concrete/CCM24UnitScaleStrictAngle.lean`
- `ConnesWeilRH/Dev/CC20ProlateTraceReductionAudit.lean` (the axiom ledger)

## 0. Result (先讲结论)

**837 的「空交集 / 非HS」是有限网格的数值坍缩，不是对仓库真实连续算子的陈述。**
仓库已经在 `CCM24UnitScaleStrictAngle.lean:1501` 用一条 **axiom-clean** 定理
（`sourceProlateHilbertSchmidtFactor_unit_summable`，依赖只有
`[propext, Classical.choice, Quot.sound]`，无 axiom、无 sorry）证明了**同一个
量**在连续载体上是可和的（=Hilbert-Schmidt）。两者不矛盾，因为载体不同：

```
载体                 R0 = range(R)∩range(Q)   factor = Q(R−R₀) 的 HS
─────────────────    ─────────────────────    ─────────────────────────
finite grid (837)   空 (dim=0)               非HS（近线性增长，op→1.0）
continuum H
  (repo 定理)        非空（闭 Sonin 子空间）   Σ‖Q(R−R₀)bᵢ‖² 可和（HS）✓
```

这里的决定性解剖是：**377 测的是与仓库一致的算子（`F=Q(R−R₀)`，同一定义），
但收敛域不同。** 在 837 的有限格上，`range(R_n)` 的格点径向支撑与离散傅里叶
支撑 `range(Q_n)` 几乎不交（`dim(R∩Q)=0`），于是 `R₀` 退化为一个全秩投影差分，
`op` 饱和到 1.0、HS 近线性增长。而仓库算子作用在连续载体
`H = cc20GlobalLogCrossingL2` 上，其中 `ccm24ArchimedeanSoninClosedSubspace =
径向 ⊓ Fourier`（`CCM24HardyTitchmarsh.lean:376-380`）是**非空闭子空间**，且
`‖unitProlateFactor‖<1`（严格压缩，不饱和），因子在其上**真 HS**。这正是「有限格
近似无法保留交互子空间维数」的经典现象。

## 1. The repo theorem (the authoritative statement)

`ConnesWeilRH/Source/CCM25Concrete/CCM24UnitScaleStrictAngle.lean`

```
1492  theorem sourceProlateRemainder_unit_isTraceClassAlong
1493      {ι} (basis : HilbertBasis ι ℂ H) :
1494      IsTraceClassAlong basis (sourceProlateRemainder unitSoninScale)
1501  theorem sourceProlateHilbertSchmidtFactor_unit_summable
1502      {ι} (basis : HilbertBasis ι ℂ H) :
1503      Summable fun i => ‖sourceProlateHilbertSchmidtFactor
                              unitSoninScale (basis i)‖ ^ 2
```

其中 `H = cc20GlobalLogCrossingL2 = finiteSCarrier`（射线上的 L2），
`sourceProlateHilbertSchmidtFactor = sourceFourierSupportProjection ∘
(radialSupportProjection - sourceSoninProjection)` = `Q (E − R₀)` ——这就是 837
探头测的那个算子。单位截断 S（`unitSoninScale`，`ẞ=1`）只是把 `logλ=0` 定为
规范，不失一般性。

关键归一：`CCM24UnitScaleProlateAlignment.lean`
- `sourceProlateRemainder_unit : sourceProlateRemainder unitSoninScale =
  cc20TransportedProlateRemainder Hinf`（把 repo 的因子 恒等地对到 CC20 的
  已证 transport 量）；
- `sourceSoninProjection_unit : sourceSoninProjection unitSoninScale =
  cc20TransportedSoninProjection Hinf`（R₀ 的投影也一样）。

## 3. The axiom ledger (build-verified)

已在 WSL 镜像上 `lake build ConnesWeilRh.Dev.CC20ProlateTraceReductionAudit`
（3196 jobs, successful），其中对目标定理直接跑 `#print axioms`：

```
sourceProlateRemainder_unit_isTraceClassAlong            depends on: [propext, Classical.choice, Quot.sound]
sourceProlateHilbertSchmidtFactor_unit_summable          depends on: [propext, Classical.choice, Quot.sound]
norm_unitProlateFactor_lt_one                            depends on: [propext, Classical.choice, Quot.sound]
```

无 `sorryAx`、无起名为 `*Root` 的 open axiom。这是**真正的 Lean 定理**，不是
另一个占位。

## 4. Why 837's finite-grid conclusion does not transfer

| 量 | 837 有限格（n=80..320） | 仓库连续载体 H |
|---|---|---|
| `range(R) ∩ range(Q)` | `dim=0`（数值） | 非空闭子空间（定义 + HS 定理推导）|
| `Q(E−R₀)` 的 HS | 近线性增长→非HS | Σ‖·‖² 可和 → **真 HS** |
| 结论 | 因子非HS | 因子 **HS**（axiom-clean）|

网格坍缩的机制：离散傅里叶支撑 `range(Q_n)` 与格点径向支撑 `range(R_n)` 几乎不
交；于是 `R₀[finite] = proj(range(R)∩range(Q))` 退化，`Q(E−R₀)` 变成全秩投影差分，
HS 随 n 线性增长。这正是「有限格近似无法保留交互子空间维数」的经典现象。在真
实连续空间里，闭 Sonin 子空间是真正的中间项，因子是 HS。

**推论**：837 的「空交集证明真实 R₀ 为空、因子非HS」**只在数值探针的语义域成立**
；对仓库 `finiteSCarrier` 上的抽象算子**不成立**。837 不能作为「Gate-3U factor 非HS」的证据。
那个「墙」不存在于仓库真算子——反而仓库已有它为 HS 的 axiom-clean 证明。

## 5. What this means for "killing 3U"

- **不**能借 837 的数值「非HS」去否掉 3U 因子层。相反，HS 那一维已由 repo
- `sourceProlateHilbertSchmidtFactor_unit_summable` 干净地成立。
- 因此 3U 的真正承重门仍然在**非 HS 量**之外的跨分支取消（memory 路线语：
  `forward + outer + secondSupport + prolate = 0`，需精确 Sonin R₀）。HS 的
  可和性只是**设定好了 majorant**，不是消去的器具。
- 「拿到精确连续 R₀ 才算数」这句在 837 里是对有限探测的诚实表述；对 repo
  R₀ 本身而言，它已经是闭子空间，其投影的 HS 已经被（有条件地）可和
  （`sourceProlateHilbertSchmidtFactor_summable_of_isTraceClassAlong`，输入端一句
  `IsTraceClassAlong` 是一个仍待真证的行）。

## 6. Honest boundary & next step

- HS 可和 ≠ 跨分支消去。`sourceProlateHilbertSchmidtFactor_unit_summable` 只保证
  量贩可次，不保证 `endpoint=0`。所以「因子是 HS」不关闭 Gate，但它把 3U 的
  剩余门件推回真正的解析承诺。
- 下一步：定位 `IsTraceClassAlong (sourceProlateRemainder ...)` 的**开输入**
  （`sourceProlateRemainder_isTraceClassAlong_of_rawCrossing` 接受
  `‖unitProlateFactor‖<1` + `unitRawSupportCrossing_summable`，两者均已 axiom-clean
  证明）。数是：`unitRawSupportCrossing_summable_of_additiveKernelIdentification`
  在多最多已证。它本身已做 clean——所以**单位端点 prolate 余量 trace-class 已是
  循环clean**，Gate 真真不在这里。

## Repro

```bash
# WSL
cd ~/projects/Connes-Weil-RH-Proof
lake build ConnesWeilRH.Dev.CC20ProlateTraceReductionAudit
# 注：837 数值探针
cd docs/proofs && source ../../.venv-probe/bin/activate
python3 837_real_sonin_gate_factor_probe.py
```