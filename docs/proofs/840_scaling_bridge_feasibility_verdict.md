# Proof-717 / Gate-3U: 840 — the unit→generic-λ bridge is BLOCKED by scattering-phase non-translational invariance; no offline λ-scaling closure exists

Date: 2026-08-07 · Status: audit/feasibility verdict (build-verified under 839).
This answers 839's two probes at once: (a) can the unit→generic-λ conjugate
bridge close the Gate HS, and (b) is there an existing offline λ-scaling closure
being missed.

PROBE SOURCE: `837` (finite grid), `838` (continuum HS axiom-clean),
`839` (generic-λ HS is the open 3U point). BUILD: WSL `lake build`, all the
`…RadialBoundaryPair/GlobalLogCrossing/SelectedCrossingOperatorBridge` Audits
(3198 jobs). This is a structured audit; no new Lean object was produced.

## 0. Result (先讲结论)

**unit→generic-λ 的共轭桥 cannot directly close the Gate HS.** 平移共轭表达的
是「径向投影」；但投影的 Fourier 产(含散射相位 `m(2πξ)`)与平移不交换。因此
`Factor(λ)=Q(λ)(R(λ)−R₀(λ))` **不会**共轭到 `Factor(1)`；generic-λ 的 HS 可和
仍是**真正的分析开放事实**,不是被漏掉的某个定理或一处 filling。

```
对象                       状态与组件
────────────────────────   ──────────────────────────────────────────────
R(λ)  径向支持投影          可平移共轭,U_c⁻¹ P₊ U_c   (axiom-clean)
Q(λ) = H⁻¹ R(λ) H           H 用固定 scattering 相位 m(2πξ), 与 λ 无关
R₀(λ) = R(λ) ∩ Q(λ)         二者纠缠,不与 unit 共轭
Factor(λ) = Q(λ)(R(λ)−R₀(λ))   Generic-λ 的 Summable 无定理可依
─────────────────────────   ──────────────────────────────────────────────
结论: 不存在「把 unit-λ 的 HS 搬到泛型 λ」的函数.
```

## 1. First probe — the conjugate bridge (径向 ok, Fourier 阻塞)

839 已证 `Factor(unit)` 的 HS 是**连续载体上 axiom-clean**。若要搬它到泛型 λ,
自然想到 log-平移共轭:

- 单位半径是 `unitSoninScale=⟨1,0⟩`（`CCM24UnitScaleProlateAlignment.lean:30`）。
- `R^{λ}=U_c⁻¹ P₊ U_c`, `U_c = cc20GlobalLogTranslation c`（`CCM24RadialHalfLine`
  `.lean:187`, axiom-clean）。
- `Q(λ)=H⁻¹ R(λ) H`, `H = ccm24ArchimedeanHardyTitchmarsh` 相位用 `m(2πξ)=
  Γ_R(1/2−2πiξ)/conj(...)`（`CCM24HardyTitchmarsh.lean:331-336`),**不含 λ**。

阻得点: `m(2πξ)` 不随平移 ξ→ξ+const 不变。所以当一个 λ≠1 的径向支持被挪到
`log λ` 时,相位算子仍作用在原点附近的频率处——交 `R(λ)∩Q(λ)` 的几何与 λ=1 时
不同,无法用 `U_c` 从 unit 直接共轭。Probe 1 的唯一两个逃逸假设都不成立:
- (H1) 散射相位平移不变      → 假（m 非常数）。
- (H2) 存在 `H_λ` 且 `H_λ U_c = U_c H_` 的对角化   → 仓库无该引理。

**Probe 1 = blocked**: 不是「很长但可做」,而是「结构上没有这样的桥」。这不与
838 的「连续载体 HS」矛盾——838 的定理作用域是 `λ=1`。

## 2. Probe 2 — 其余离线 λ-scaling 闭式也不存在

仓库范围内用关键字（scaling / equivariant / invariant / λ 泛型 `Summable
‖ProlateFactor λ‖`）查询,**没有任何**「产出 λ-general HS」的 Lean lemma; 所有
`Summable ‖…Factor λ‖` 出现均为消费者(约 30 处签名里的前提),无生产者。
与 839 一致: generic-λ HS 是分析事实缺口,不是漏接。

## 3. Verdict / honest ceiling

1. **839 的「generic-λ HS」是真开放分析事实,不是某个 plug-in 或遗漏的等频桥。**
   它被 Gate 和 ~30 个下游签名当作前提消费,但仓库里既无该定理,也无从 unit 赴泛型
   的桥。
2. 之所以是「能精确定位的障碍」而非「一团迷雾」: 卡点处是 **散射相位相对 log-平移
   的不变**——这是可证明、可归属、可书面说明的分析原因;不是「缺一段形式化」。这比
   836 的「数值非 HS(已死)」、837 的离散化坍缩(已死)前进了一大步。
3. 这不证明也不否定 RH。它把残余 3U 承重点收敛到唯一一个未证分析事实:
   `Summable ‖sourceProlateHilbertSchmidtFactor λ‖²`（generic λ）。
4. 之后的合法出路有二:(a) 引入真正 λ-dependent 的散射/尺度分析（新分析输入）;
   或 (b) 让 3U 载体的 λ-尺度从更上游就被 transport 对角化（Route-C 的 trace lane,
   `TraceScale` 等）。两者都是真数学,不是填洞。

## Repro

```bash
WSL:
  lake build ConnesWeilRH.Dev.CCM24RadialBoundaryPairAudit
  lake build ConnesWeilRH.Dev.GlobalLogCrossingAudit
  lake build ConnesWeilRH.Dev.SelectedCrossingOperatorBridgeAudit
# 三个审计都打印 conjugation/translation/norm 引理 axioms =
# [propext, Classical.choice, Quot.sound]; 无 sorryAx, 无 *Root.
```