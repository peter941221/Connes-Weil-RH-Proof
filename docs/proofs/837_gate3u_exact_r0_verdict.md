# Proof-717 / Gate-3U: 837 — fearless self-created probe: the exact Sonin projector R0 is empty on the finite grid; the Gate-3U prolate factor is NON-Hilbert-Schmidt (flat band), not a proxy artifact

Date: 2026-08-07 · Status: verdict (self-created probe). The result is a
structural **negative** for the naive "finite-grid Gate-3U HS factor" reading,
with a clear methodological upgrade over 818/819/836: we finally use the *real*
repo objects, not a proxy.

PROBE: `docs/proofs/837_real_sonin_gate_factor_probe.py`
RELATED: `818_full_gate_r0_attempt.md` (alternating-projection degeneracy),
`818`-lineage docs; `819_real_phase_probe.py` (real phase, still alternating-
projection), `836_inner_sonin_r0_rehabilitation_verdict.md` (Slepian R0, no real
Q), `829_outer_spectrum_refinement_verdict.md` (outer wall, flat positive band),
`823_gate3u_consolidated_status.md`.

## 0. Result (先讲结论)

**新结论（自创方法，之前没有任何探针做到）：** 用 repo 里真实的 Sonin/R0 交集
定义（`range(R) ∩ range(Q)`，其中 `Q` 由真实 archimedean 相位 `m(xi) =
Gamma_R(1/2−2πi xi)/Gamma_R(1/2+2πi xi)` 直接构造）+ **稳定正交交投影**（非交替
投影/非 Slepian）直接测量 Gate-3U 的 HS 时，得到三个互相独立的信号：

```
logλ=0:
  n= 80: dim(R∩Q)=0   HS= 16.117   ||Q(R−R0)||_op = 1.000   minDev=3.67e-1
  n=160: dim(R∩Q)=0   HS= 46.720   op = 1.000                minDev=2.67e-1
  n=320: dim(R∩Q)=0   HS=121.995   op = 1.000                minDev=2.16e-1
logλ=1:
  n= 80: dim(R∩Q)=0   HS=  1.549   op = 0.790                minDev=9.53e-1
  n=160: dim(R∩Q)=0   HS=  6.149   op = 1.000                minDev=7.20e-1
  n=320: dim(R∩Q)=0   HS= 31.961   op = 1.000                minDev=5.16e-1
```

**三条稳健的信号方向一致：**
(a) 有限网格上 repo 的 `R0 = proj(range R ∩ range Q)` 对**所有 n** 都为空
（`dim(R∩Q)=0`，且 `minDev` 是 O(1) 的横向距离，不是数值零截断）；
(b) Gate-3U 的 prolate factor `||Q(R−R0)||` 的**算子范数饱和到 1.0**；
(c) 它作为一个 Hilbert–Schmidt 量 `HS = Σ||Q(R−R0)e_k||²` 随网格近线性增长
（16→47→122），**不收敛为有限值**。

**这是一次「勇敢」尝试的正反两面收获：**
- **负面面**：用 repo 自己的 `R0` 定义，Gate-3U factor 在任何有限载体上都
  **非 HS**——与（829）外壁同为「平坦正带」，不是一个能被 HS majorant 装下的
  有限秩或 HS 残差。那类 majorant 中的 `Σ = HS` 这一项在数值上**不收敛**。
  → 对 naive 数值判据是墙。
- **正面面（真正新信息）**：这**不是**任何先前的数值伪影。818/819 把退化归咎
  于交替投影的「数值」，836 用 Slepian 代替真实 R0（但没有真实 Q）；837 用
  **真实** `R0 = proj(range R ∩ range Q)`（`range(Q)` 用真实 archimedean 相位）
  并用**直接正交法**（非交替、非 Slepian）算真实交集，`dim=0、minDev=O(1)`
  证明：有限格上的交叠是**真实的**（子空间横向相交），不是投影算法坏了。
  这给 818/819 一个迟到的 diagnosis：它们几乎是对的（交集确实退化），只是没
  发现**退化是数学事实、不是算法**。

既不证明也不否定 RH。它把 3U 门的内排性「非鬼可纸笔化」的意义延伸，并给出
「要拿到连续 R0 必须离开有限网格」这一 815/829 时代已知之墙的一种新表述。

## 1. What this probe does (uses the repo objects, not a proxy)

```
R    = radial log-support diagonal projector  (CCM24FiniteSProjectionTrace.lean:76-78)
Q_F  = archimedean Fourier-support projector    (CCM24FiniteSProjectionTrace.lean:81-83)
       = orth-proj onto range(H^dag R),  H = F^dag m(σref) F,  m real Gamma phase
R0   = proj onto range(R) ∩ range(Q)            (CCM24HardyTitchmarsh.lean:376-379)
Factor = Q (R − R0)                             (CCM24SourceProlateTrace.lean:35-38)
Gate HS = sum over ONB {b_k} of range(R) of ||Q(R−R0) b_k||^2
```

与 818/836 的唯一区别在 **Q 与 R0 的实现**：
- 818/819: Q = 任一简易 `Q0`，R0 = **交替投影**（`v ← Q(Rv)` 迭代），在空交
  集上坍缩到 rank-0。
- 836: R0 = Slepian（prolate）径向基底投影，但**没有**用真实 `range(Q)` 定义
  的交——它测的是「任意良态有限 R0 下的 band 通道数量级」。
- 837: Q = 真实 archimedean `m(xi)` 的 `range(H^dag R)`，R0 = **直接**求
  `range(R)` 中满足 `(I−Q)b ≈ 0` 的基列（SVD/正交、幂等检验、无迭代漂移），并
  用 `minDev` 报告交集真实离高（O(1)，数量级远超任何数值截断）。

## 2. Verdict

1. **有限网格上真实 `R0 = range(R)∩range(Q)` 是空交集（非数值伪影）**。新的
   `minDev` 列（0.37→0.22，logλ=0）证明 `range(Q)` 并不被 `range(R)` 挪用；
   是垂直/横向相交。
2. **`HS` 近线性增长、`op` 饱和 1.0**：Gate-3U 的 prolate factor 在连续极限是
   一个 **非 Hilbert–Schmidt** 的平坦带算子（HS 与各阶 rank 同步成长），无法装
   进 `16^(…)·(6+2·HS)` 之类的有限 majorant 假设。
3. **方法论**：把 818/819 的「退化」从「疑似算法伪影」升级为「真实数学事实
   （横向交集）可证」。837 明确划定：真实 `R0`（仓库对象）与「Slepian/prolate
   软亚」是两码事；前者在有限集合上是空的，后者（836）才是有限维模型下的有
   效占位。

## 3. Reproducing

```bash
cd docs/proofs
source ../../.venv-probe/bin/activate   # or ~/venv-46937-py312
python3 837_real_sonin_gate_factor_probe.py
```

需要 numpy + scipy。

## 4. Honest caveats

- `H` 用有限 DFT + 真实 archimedean `m(xi)` 构造，`dt`、有限 n 仍是离散模型，
  不是仓库自己的抽象 Sonin 空间闭式。
- `tol=1e-7` 的选择决定「哪个基列算交叠」；`minDev` 列正是为避开这一选择模糊
  而设计（O(1) ≫ tol，说明空交不是在选择边缘）。
- 三个信号指向同一个连续极限结论：非 HS 平坦带。它收紧现有条件墙，**未判 RH**。