# Connes-Weil RH Proof

一个用 Lean 4 研究黎曼猜想的形式化数学项目。

工具链：Lean 4.30.0，Mathlib 4.30.0。

## 1. 这个项目研究什么

黎曼猜想断言，黎曼 zeta 函数的非平凡零点都落在临界线
`Re(s) = 1/2` 上：

$$
\zeta(s)=0,\qquad 0<\operatorname{Re}(s)<1
\quad\Longrightarrow\quad
\operatorname{Re}(s)=\frac12.
$$

本项目探索 Connes-Weil 路线，并把论证逐层写进 Lean 4。最终目标采用
Mathlib 中的命题 [`_root_.RiemannHypothesis`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/LSeries/RiemannZeta.lean)。

Connes-Weil 路线从显式公式出发。取一个紧支撑测试函数 $g$，构造卷积平方

$$
F_g=g^* * g.
$$

零点、素数幂和无穷位在 Weil 分布中同时出现。合适的测试函数族若满足

$$
\sum_v W_v(F_g)\le 0,
$$

便能导向 RH。这里最难的工作是把右侧变成某个正算子的迹，同时保持测试函数、
卷积平方、素数项和谱对象属于同一个数学对象。Lean 会迫使每次换序、取伴随、
换迹和极限都带上相应的可和性、定义域与支撑证明。

项目的主线可以压缩为下面的图：

<pre>
compact test g
     |
     v
convolution square F = g* * g
     |
     +-------------------+
     |                   |
     v                   v
prime-power values     archimedean operator
     |                   |
     v                   v
finite-S crossing sum  semilocal positive owner
     |                   |
     +---------+---------+
               |
               v
          Weil inequality
               |
               v
        Riemann Hypothesis
</pre>

### 1.1 研究过的代表性思路

1. Connes-Weil 半局部迹公式

   这条路线把有限素数集 $S$、Sonin 空间、半局部 Fourier 结构和 Weil 显式公式放到
   同一 Hilbert 空间中。当前主线已经形式化单次 crossing 的精确素数幂系数，并把
   有限个 crossing 组装成紧自伴算子。

2. Yoshida 零点探测函数

   Yoshida 的方法为指定的离临界线零点构造 Mellin 探测函数。项目形式化了紧支撑
   预算、卷积幂缩尾、有限节点插值以及临界带上的一致二次衰减。该路线把最终问题
   归结为探测函数族是否能进入同一个半局部正迹对象。

3. Xi 函数与零点计数

   项目使用 Mathlib 的 theta 核控制 completed Xi，并把零点求和所需的计数条件削弱
   到右半平面的几何球界。二次 Mellin 衰减只需壳层增长率低于 $4^n$，不必预先导入
   完整的 Riemann-von Mangoldt 渐近式。

4. Nyman-Beurling 与 Möbius 块

   项目研究过投影后的 Möbius dyadic blocks、有限 Gram 矩阵、Vasyunin 对偶系和固定
   卷积方向。精确数值和结构推导表明，关键下界重新引入逆 Gram 非消去问题；该问题
   与 RH 本身处于同一难度层。相关实验保留为路线排除证据。

5. Prolate、Sonin 与算子正性

   这部分研究时间频率截断、prolate 波算子、Wiener-Hopf crossing 和 CC20 的
   $-2I+K$ 分解。紧性控制了算子理想，却不决定谱的符号。当前工作因此聚焦于
   同一半局部对象上的精确分解和余项符号。

6. 算子层的反例筛选

   项目检验过 Xi 零空间紧修正、log-Poisson 正算子、Fredholm/Fock Euler-log
   展开、高阶 $Q$ 滤波、adelic 标量补偿和 Clifford 素数通道。每条路线都留下了
   可复核的失效机制，避免把形式漂亮但系数错误的算子接入 RH 主线。

## 2. Lean 4 中已经完成的核心形式化

### 2.1 Hilbert-Schmidt 换迹与核展开

设 $A,B:H\to G$ 在 Hilbert 基 $(e_i)$ 上满足

$$
\sum_i\lVert A e_i\rVert^2<\infty,
\qquad
\sum_i\lVert B e_i\rVert^2<\infty.
$$

项目先证明双基系数绝对可和：

$$
\sum_{i,j}
\left|
\langle A e_i,f_j\rangle
\langle f_j,B e_i\rangle
\right|<\infty.
$$

因此可以在 Lean 中合法交换两重级数，并得到真正的跨 Hilbert 空间换迹公式

$$
\operatorname{Tr}_H(A^*B)=\operatorname{Tr}_G(BA^*).
$$

对应声明：

- [`summable_cyclicCoefficients`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L307)
- [`ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L520)
- [`ordinaryTraceAlong_three_comp_eq_cycle`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L566)

同一模块还证明了 Hilbert-Schmidt 乘积的核展开

$$
A^*B
=
\sum_j
\operatorname{rankOne}(A^*f_j,B^*f_j),
$$

并证明右侧在连续线性映射的算子范数中绝对收敛。有限秩算子的紧性与紧算子集合的
闭性随后给出 $A^*B$ 的 Mathlib `IsCompactOperator` 证明。

- [`summable_norm_traceProductNuclearTerm`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L427)
- [`traceProduct_eq_tsum_nuclearTerm`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L445)
- [`traceProduct_isCompactOperator`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L474)

### 2.2 连续核的精确 crossing trace

对有限区间上的连续核 $L$ 与 $R$，项目构造相应的 $L^2$ 算子，证明它们具有
Hilbert-Schmidt 平方可和性，并把 $L^*R$ 的对角迹化为核截面的内积积分：

$$
\operatorname{Tr}(L^*R)
=
\int \langle L_s,R_s\rangle\,ds.
$$

- [`pairData_trace_eq_kernel_inner`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/ContinuousKernelHilbertSchmidt.lean#L316)

将该定理应用到选定卷积平方 $F$ 的 crossing 核，Lean 得到两个方向的精确系数：

$$
\operatorname{Tr}(L^*R)=bF(b),
\qquad
\operatorname{Tr}(R^*L)=bF(-b).
$$

- [`pairData_trace_eq_mul_convolutionSquare`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingKernel.lean#L289)
- [`reversePairData_trace_eq_mul_convolutionSquare_neg`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingKernel.lean#L320)
- [`eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingKernel.lean#L390)

取 $b=m\log p$ 后，Euler 权重把这两个 trace 变成显式公式中的素数幂项：

$$
\frac{1}{m\sqrt{p^m}}
\left(bF(b)+bF(-b)\right)
=
\frac{\log p}{\sqrt{p^m}}
\left(F(\log p^m)+F(-\log p^m)\right).
$$

### 2.3 从紧区间 crossing 到整条实线

紧区间核和全局卷积算子生活在不同 Hilbert 空间。项目构造限制算子 $S$、零延拓
$E=S^*$、平移 $U_b$ 与半线投影 $P$，并在 Lean 中证明

$$
J_b=(I-P)U_bP
$$

与源窗口上的边界平移是同一个算子。关键声明包括：

- [`restrictedSetZeroExtension_eq_adjoint_restrict`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L210)
- [`globalBoundaryTranslationProjection_eq_singleCrossingOperator`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L1085)
- [`globalLogConvolution_involution_eq_adjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L1765)

换迹过程中出现的投影 $EE^*$ 不能凭形式计算删除。Lean 先证明相关因子的值域落在
$E$ 的值域中，再在这个值域上消去投影。随后，三因子换迹把紧区间 trace 送到
整条实线：

$$
\operatorname{Tr}(L^*R)
=
\operatorname{Tr}(C_h C_{h^*}J_b),
$$

$$
\operatorname{Tr}(R^*L)
=
\operatorname{Tr}(J_b^*C_h C_{h^*}).
$$

- [`leftKernelAdjoint_range_factorization`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L1842)
- [`pairData_trace_eq_namedSourceCrossingProduct`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L2008)
- [`reflectedWholeLineLeftFactor_summable`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L2545)
- [`pairData_trace_eq_globalConvolutionCrossing`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L2711)
- [`reversePairData_trace_eq_globalConvolutionCrossing_adjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L2767)

### 2.4 有限素数集上的紧自伴算子

对素数幂 $(p,m)$，令 $T_{p,m}$ 表示位移长度 $m\log p$ 的全局 crossing。项目定义

$$
K_{p,m}
=
\frac{1}{m\sqrt{p^m}}
\left(T_{p,m}+T_{p,m}^*\right),
$$

并在取迹前组装有限和

$$
K_{\mathcal T}=\sum_{(p,m)\in\mathcal T}K_{p,m}.
$$

所有项作用在同一个全局 $L^2(\mathbb R)$ 空间，并使用同一个
`SelectedWeilSquareOwner`。Lean 已证明：

1. $K_{\mathcal T}$ 自伴；
2. $K_{\mathcal T}$ 是 Mathlib 意义下的紧算子；
3. 指定 Hilbert 基上的对角绝对可和；
4. 它的 ordinary trace 等于同一卷积平方的有限素数幂和。

$$
\operatorname{Tr}(K_{\mathcal T})
=
\sum_{(p,m)\in\mathcal T}
\operatorname{finitePrimeTerm}(p^m).
$$

- [`eulerLogWeightedGlobalPairTraceOperator`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L2906)
- [`eulerLogWeightedGlobalPairTraceOperatorSum_isSelfAdjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L3064)
- [`eulerLogWeightedGlobalPairTraceOperatorSum_isCompactOperator`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L3088)
- [`ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperatorSum_eq_finitePrimeTerm_pow_sum`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L3123)

### 2.5 CC20 有限窗口算子的全局实现

CC20 的正则核最初作用在有限 Haar 窗口。设 $H_\lambda$ 为有限窗口算子，$E_\lambda$
为从窗口到 $L^2(\mathbb R)$ 的零延拓。项目证明全局算子满足精确共轭关系

$$
H_\lambda^{\mathrm{global}}
=
E_\lambda H_\lambda E_\lambda^*.
$$

有限窗口核的连续性与对称性给出紧性和自伴性；共轭关系把两项性质搬到与
$K_{\mathcal T}$ 相同的全局 Hilbert 空间。

- [`cc20GlobalLogWindowL2Operator_eq_zeroExtension_conjugation`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/GlobalLogKernel.lean#L1629)
- [`isCompactOperator_cc20GlobalLogWindowL2Operator`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/GlobalLogKernel.lean#L1639)
- [`cc20GlobalLogWindowL2Operator_isSelfAdjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/GlobalLogKernel.lean#L1649)

### 2.6 素数项的平移二次型实现

设 $h\in L^2(\mathbb R)$ 为选定测试函数的卷积根，$U_b$ 为全局平移。Lean 证明

$$
\langle h,U_bh\rangle=F_h(b).
$$

由此定义自伴平移组合

$$
D_{p,m}
=
\frac{\log p}{\sqrt{p^m}}
\left(U_{m\log p}+U_{-m\log p}\right),
$$

并得到同一向量上的有限素数读出

$$
\langle h,D_{p,m}h\rangle
=
\operatorname{finitePrimeTerm}(p^m).
$$

- [`inner_sourceRootLp_translation_eq_convolutionSquare`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedPrimeTranslationQuadratic.lean#L32)
- [`primePowerTranslationOperator_isSelfAdjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedPrimeTranslationQuadratic.lean#L87)
- [`inner_primePowerTranslationOperator_eq_finitePrimeTerm_pow`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedPrimeTranslationQuadratic.lean#L109)

平移算子保留连续谱；这个模块承担二次型读出。第 2.4 节的 crossing 分解承担紧性与
ordinary trace 读出。两种实现从不同方向校验有限素数系数。

### 2.7 Yoshida 支撑预算与 Xi 尾部

Yoshida 构造需要同时完成两件事：在有限个 Mellin 节点精确插值，并让其他零点上的
值足够小。项目在 log 坐标中使用缩放

$$
f_r(x)=r^{-1}f(x/r),
\qquad
\Phi_{f_r}(s)=\Phi_f(rs),
$$

再取 $r=1/N$ 的 $N$ 重卷积。卷积幂缩小 Mellin 尾部，而总支撑仍留在预定预算内。
残余窗口中的修正函数承担有限节点插值，并保持临界带上的一致二次衰减。

- [`exists_residualWindow_correction_with_quadratic_decay`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20YoshidaConvolution.lean#L278)
- [`exists_uniform_mellin_vertical_quadratic_decay`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20YoshidaTail.lean#L257)
- [`exists_residualWindow_nearbyZero_assembled_distance_bound_lt`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20YoshidaConvolution.lean#L780)

对 completed Xi，项目从 theta 核矩估计出发，证明右半平面球计数足以推出源非平凡
零点上的可和性。活跃 consumer 只要求几何壳层界

$$
\#\{\rho:q^n\le \lVert\rho\rVert<q^{n+1}\}
\le Kc^n,
\qquad c<4,
$$

因为二次 Mellin 衰减在壳层和中产生 $(c/4)^n$。

- [`norm_completedRiemannXi_le_kernelMoment`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20ZetaCounting.lean#L239)
- [`sourceNontrivialZero_summable_of_xi_right_halfplane_ball_bounds`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20ZetaCounting.lean#L531)

## 3. 当前进展

截至 2026-07-13，有限素数 crossing 的分析链已经从连续核走到一个全局紧自伴算子。
每一步都保留同一个卷积平方：

<pre>
continuous kernels on finite intervals
               |
               v
       traces b F(b), b F(-b)
               |
               v
legal rectangular trace cycle
               |
               v
whole-line C_h C_h* J_b and its adjoint
               |
               v
Euler-log prime-power atom
               |
               v
finite-S compact self-adjoint K_S
               |
               v
trace(K_S) = selected finite-prime sum
</pre>

这条链解决了四个长期纠缠的问题。

1. crossing 的几何区间

   $J_b$ 的函数级表达把 crossing 限制到精确区间 $[-b,0]$。紧核使用的源区间由此与
   全局半线投影一致。

2. 换迹的合法性

   项目没有使用形式恒等式 $\operatorname{Tr}(ABC)=\operatorname{Tr}(BCA)$。Lean
   通过 Hilbert-Schmidt 平方和、双级数绝对可和性和三因子矩形换迹逐次完成循环。

3. 紧性

   指定基上的绝对对角可和不足以推出 Mathlib 的紧算子。项目为 $A^*B$ 构造算子范数
   绝对收敛的 rank-one 展开，再把紧性传给每个 prime-power crossing 和有限和。

4. 公共载体

   有限素数 crossing 和 CC20 正则窗口算子已经作用在同一个全局 log-Hilbert 空间。
   后续恒等式无需在两个不兼容载体之间搬运谱符号。

### 3.1 当前数学边界

下一层需要在有限 $S$ 的半局部空间上构造正算子 $\mathcal P_S(h)$，并证明同对象分解

$$
\mathcal P_S(h)=K_S(h)+R_S(h).
$$

这里的 $K_S(h)$ 必须逐项等于第 2.4 节已经形式化的 crossing 和；$R_S(h)$ 必须与
$\mathcal P_S(h)$ 共享定义域、测试函数和 $Q$ 作用。随后需要一个足以推出 Weil 符号的
余项估计。理想的推导形状是

$$
\mathcal P_S(h)\ge 0,
\qquad
\mathcal P_S(h)=K_S(h)+R_S(h),
\qquad
R_S(h)\ \text{满足所需符号或极限估计}.
$$

完成该层之后，最后的量词问题是证明路线产生的测试函数族足以探测每个离临界线零点：

$$
\text{semilocal positivity}
\Longrightarrow
QW(h,h)\ge 0
\Longrightarrow
\sum_v W_v(F_h)\le 0
\Longrightarrow
\mathrm{RH}.
$$

### 3.2 已排除的代表性捷径

研究记录保留了每条路线的具体失效点。

| 路线 | 失效机制 | 记录 |
|---|---|---|
| Xi 零空间紧支撑修正 | 指数型零密度与紧支撑 entire transform 的零密度冲突 | [proof 110](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/110_xi_null_compact_support_zero_density_death.md) |
| log-Poisson 正迹 | 正系数无法读出显式公式所需的素数标量 | [proof 111](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/111_log_poisson_positive_trace_readoff_death.md) |
| 紧 Wiener-Hopf 边界修复 | 紧扰动无法消去主符号中的非紧部分 | [proof 118](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/118_wiener_hopf_compact_boundary_cannot_cancel_symbol.md) |
| Fredholm/Fock Euler-log | 所需 Euler-log 导数项没有进入目标 trace ideal | [proof 119](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/119_fredholm_euler_log_traceclass_death.md) |
| 高阶 $Q$ 滤波 | 微分权重加强 cusp 主部，未产生所需符号 | [proof 120](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/120_higher_q_filter_unbounded_cusp_rejection.md) |
| adelic 标量补偿 | product-formula 系数与单素数 read-off 不匹配 | [proof 121](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/121_adelic_product_formula_scalar_mismatch.md) |
| Clifford 素数通道 | Gram 化保留了原符号问题，并引入额外通道成本 | [proof 122](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/122_clifford_prime_channel_gram_cost.md) |

这些排除结果约束了下一步：新构造必须给出有限 $S$ 的精确 trace read-off，且必须在
同一 form domain 上处理 post-$Q$ 余项。

## 4. 文献坐标

项目围绕以下工作建立形式化接口：

1. Alain Connes and Caterina Consani, *Weil positivity and Trace formula:
   the archimedean place*, [arXiv:2006.13771](https://arxiv.org/abs/2006.13771).

   该文给出 archimedean trace、Sonin/prolate 结构和 CC20 的 Weil 判据。

2. Alain Connes, Caterina Consani and Henri Moscovici, *Zeta Zeros and Prolate
   Wave Operators: Semilocal Adelic Operators*,
   [arXiv:2310.18423](https://arxiv.org/abs/2310.18423).

   该文建立半局部空间、模映射、Fourier 相容性与 Sonin 传输。当前项目使用这些结构
   定位有限 $S$ 正算子的正确载体。

3. Alain Connes, Caterina Consani and Henri Moscovici, *Zeta Spectral Triples*,
   [arXiv:2511.22755](https://arxiv.org/abs/2511.22755).

   该文研究自伴逼近与谱三元组。其收敛问题说明 prolate 近似仍需要新的谱估计。

4. q-series/Jacobi 模型，[arXiv:2403.01247](https://arxiv.org/abs/2403.01247)，
   以及有限 Guinand-Weil 字典，[arXiv:2607.02828](https://arxiv.org/abs/2607.02828)。

   两项工作提供 Jacobi 矩阵、有限维字典和尾部阶数。当前缺少的部分仍是统一的
   半局部正迹恒等式与余项符号。

Burnol 紧支撑显式公式与项目 `SelectedWeilFormulaOwner` 的逐项对齐见
[proof 109](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/109_burnol_selected_weil_formula_alignment.md)。

## 5. Lean 工程结构

<pre>
ConnesWeilRH/
  Basic.lean                         Mathlib RH 目标与基础接口
  Source/
    CC20Concrete/                    连续核、trace、全局窗口算子
    CCM25Concrete/                   选定卷积平方、crossing、素数项
    CC20Yoshida*.lean                Mellin 探测函数与支撑预算
    CC20ZetaCounting.lean            Xi 核估计与零点求和
  Route/                             条件路线的组合层
  Dev/                               无前提 RH 根、审计入口与研究边界

docs/proofs/                         数学推导、路线排除与里程碑证明
docs/audits/                         源文献核对、量词和公理审计
formalization/                       接口设计与形式化准备材料
</pre>

根入口是 [`ConnesWeilRH.lean`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH.lean)。
条件路线在 [`RouteTheorem.lean`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Route/RouteTheorem.lean#L3539)
中结束于 Mathlib RH。无前提 RH 的依赖审计位于
[`UnconditionalSkeleton.lean`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/UnconditionalSkeleton.lean#L8048)。

本地构建使用 `lake build ConnesWeilRH`。各审计文件通过 `#check`、`#print` 和
`#print axioms` 同时检查完整定理类型与公理依赖；最终定理还需检查显式参数、隐式参数
和 typeclass 参数，避免把普通前提藏在公理审计之外。

## 6. License

Apache License 2.0。参见 [LICENSE](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/LICENSE)。
