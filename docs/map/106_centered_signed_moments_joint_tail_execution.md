# 106 — 完整中心化有符号矩与同次数尾项：执行合同

日期：2026-09-24。

状态：PROJECT CANDIDATE / 执行计划；核心解析估计 OPEN。
隶属 [003](003_b1_b5_minimal_exit_route_selection.md) 和
[103](103_four_point_same_span_three_cut_campaign.md)，承接
[1957 审计](../proofs/1957_plan_b_same_owner_joint_margin_reaudit.md)。
本文件取代 [105](105_coarse_macro_atom_variance_domination.md) 的执行安排，
不改变 healthy CompactLog B5 的绑定路线，不声称 RH 已证明。
执行状态：R0 已新增显式有限节点 correction、支撑保持及 selectedOwner
变换公式/上界（[1958](../proofs/1958_explicit_finite_node_correction.md)）。
聚焦构建及标准公理审计通过；主线/root 回归状态见该记录。
实际 signed determinant 和联合尾项预算仍 OPEN，不记作核心符号闭合。

## 1. 任务入口与唯一消费者

```text
owner:    g_n = (selectedOwner base correction n).sourceTest
          u_n = fullFunctionalEquationOrbitAnnihilator g_n rho
          h_n = annihilatorDetectorSpanVector u_n g_n lambda_n
consumer: 同一 h_n 的 gate -> qw(h_n) >= 0
          同一 h_n 的有限前缀 + 谱尾项 -> qw(h_n) < 0
          矛盾 -> SourceRH -> Mathlib RiemannHypothesis
known:    轨道插值、前缀消零、支撑与衰减构造及条件性消费者已有源码
remove:   实际 owner 的 determinant 符号及同次数严格尾项预算
failure:  命名参数类上可复核的障碍，或完整误差超过可用余量
```

`rho : sourceNontrivialZeroSet` 且 `1/2 < rho.re` 是反证入口。
不能把 span 的 healthy detector 数据直接从 g_n 继承。
所有可见素数幂、支撑上界、Fourier/Laplace 坐标均须与实际测试对应。
若共用较大支撑界形成有限素数集合，须证明新增节点的实际贡献为零。

失败必须注明是 owner、参数类、估计方法还是精度预算失败；
估计未闭合不能写成 determinant 非负，也不能扩大为整条路线的 no-go。

## 2. 最小联合终点

定义实际 gate 数值，不先用试验数据或有理数替换它们：

```text
C_n = ICgate(g_n.convolutionSquare)
b_n = (ICgate(u_n.involution.convolution g_n)
       + ICgate(g_n.involution.convolution u_n))/2
D_n = ICgate(u_n.convolutionSquare)
lambda_n = b_n/C_n
H = 3 + norm(rho)
```

保留交叉项之和；不预设两个交叉项相等。对每个假设 rho，仅需一个
满足构造全部前提的 n，并在这个 n 上证明：

```text
C_n > 0
b_n > 0
det_n = C_n*D_n-b_n^2 < 0
beta_s * L_n < multiplicity_rho * lambda_n^2

beta_s = 4 * spectralMultiplicityConstant * (3/4)^s
L_n = H^4 * (H^4+abs(lambda_n))^2 * (2*pi)^12
      * ((1/2)^n * (C4*C2))^2
multiplicity_rho = (xiMultiplicity rho : Real)
```

`C4,C2` 是实际 base/correction 的衰减常数；`s` 是固定的谱壳前缀。
还须证明消费者需要的支撑、三重消失、轨道值、前缀消零、高度及
构造 admissibility 条件，不能将上述四行视为全部输入。

验收时使用具体 `lambda_n = b_n/C_n`：已有 vertex 恒等式给出
`gate(h_n.square) = det_n/C_n < 0`。不要先消去具体见证，只留下
`exists lambda`，再对另一个 lambda 做尾项认证。

## 3. 量词与构造顺序

| 次序 | 固定对象 | 必须交付的依据 |
|---|---|---|
| 1 | rho、窗口、base | base 的目标节点值为 1；真实 CompactLog 支撑 |
| 2 | base 收缩阈值 T、四阶常数 C4 | 同一 base 的条带收缩与四阶衰减 |
| 3 | 壳前缀 s、插值半径 R、routeNodes | T 和 rho 高度被前缀覆盖；R 覆盖所需全部前缀零点 |
| 4 | 构造容差 epsilon_sel > 0、correction | 对该固定前缀的插值；固定 correction 后保留 all-index 形式 |
| 5 | C2、构造常数 Csel | 同一 correction 的二阶衰减；明确 admissibility 阈值 |
| 6 | n、它的实际有限素数集合、矩认证、lambda_n | 联合完成 determinant 与尾项预算 |
| 7 | epsilon_span、最终 M | 接回同一个 h_n 的谱前缀和谱尾项 |

`epsilon_sel` 与 `epsilon_span` 必须分名：前者属于构造消费者，
后者为联合预算成立后选择的 span 尾项参数。
all-index API 中仍有
`(6*pi)^2 * ((1/2)^(n+1)*Csel) < epsilon_sel`，必须在选定 n 上消去。
`HealthyMinimalLaplaceRealizes` 不能被写成完整 `HealthyYoshidaDetectorData`。
若选用需要后者的消费者，必须另外证明其全部字段；也可使用实际
parabola 和三重消失的直接 gate 消费者，避免不必要的加强假设。

改变前缀须重新处理 correction；改变 base/correction 后旧矩、旧常数
和旧尾项证书失效。仅增加 n 时也必须重新使用该 n 的支撑及有限素数集合。
不得假设 gate 符号或 lambda 的界随 n 自动保持。

最终量词是 `forall rho, exists construction, exists n`。
不要求所有 rho 共用窗口、常数、精度或 n。
有限参数采样不能代替这个全称结论；若分高度区间，须明确低段和无界高段的完整覆盖。
本合同不依赖 1955 的 `gamma^2-delta^2 >= 190`；若后续采用该引理，
该高度前提及未覆盖区间须另行证明/处理。

## 4. 中心化矩及精确认证公式

选择实数中心 a_n，可来自 owner-specific 初步估计；它不是新的 span 系数。

```text
U_n = b_n-a_n*C_n
V_n = D_n-2*a_n*b_n+a_n^2*C_n
det_n = C_n*V_n-U_n^2
lambda_n = a_n+U_n/C_n
```

以上是精确代数，保持 owner、vertex 和全部有符号抵消。
连续积分表示需要另有同一 owner 的证明：

```text
omega = 2*pi*xi
P(omega) = (delta^2+gamma^2-omega^2)^2+4*delta^2*omega^2
W_n(xi) = abs(ghat_n(xi))^2
C_n = integral K_n*W_n
U_n = integral K_n*W_n*(P-a_n)
V_n = integral K_n*W_n*(P-a_n)^2
```

这里积分为全实线。须核对 half-density shift、Fourier 约定、实部、
两个交叉 gate 的对应、积分可积性和有限素数截断。
不能从普通 bump 的 Fourier 变换替换出 g_n，也不能未经证明令 W_n 为偶函数。
Record 1919 是纸面/数值来源；有限和 ANOVA 定理并非连续表示的 Lean 证明。

设实际矩的认证中心为 `(C0,U0,V0)`，非负绝对误差为 `(eC,eU,eV)`。
认证必须证明实际矩位于这些区间，不能只存储通过不等式的数值。

```text
Clo = C0-eC
Chi = C0+eC
blo = a_n*C0+U0-abs(a_n)*eC-eU

E = abs(V0)*eC+abs(C0)*eV+eC*eV+2*abs(U0)*eU+eU^2
detUpper = C0*V0-U0^2+E
```

验收 `Clo > 0`、`blo > 0`、`detUpper < 0`。
从实际区间包含关系推出 `lambda_n >= blo/Chi > 0`。
这个下界也可直接用于该 n 的尾项上界。
中心 a_n 若由近似值给定，应选取确切实数/有理数定义；其计算误差不能遗漏。

复核依据：展开 `CV-C0*V0`，误差依次为
`V0*dC+C0*dV+dC*dV`；展开 `U^2-U0^2`，误差为
`2*U0*dU+dU^2`。上述 E 来自三角不等式，不要求 U 或 V 为正。

## 5. 区间与补集的执行规则

1. 从实际 K_n、W_n 的可认证表达式选择有限区间划分；原 I0、I1 只可作
   候选初始划分，不预设其全核符号或质量比例。
2. 每格分别认证三个有符号矩。若格内符号不定，保留有效区间包络；
   不能用 n=2 的符号代替全核符号。
3. 记录每格积分误差及全线补集误差，汇总为 eC、eU、eV。
   补集须控制到 `(P-a_n)^2` 的八次增长，单独 L2 尾界不足。
4. 保留负区内部方差与 Archimedean/prime 抵消，不要求各通道分别为负。
5. 先计算 detUpper 的误差构成，再决定细化哪一格或哪一项。
   不先承诺低精度必够；不能用加密网格的经验稳定性充当认证误差。
6. Fourier 积分补集与谱零点高壳尾项是不同对象，各自出具证明，不能互换。

允许使用完整物理积分估计得到同样的三个实际 gate 矩界；若比连续 Fourier
表示更短，可沿现有 same-owner 物理 readback 实施，不必为统一形式另建框架。

## 6. 相对尾项：单次数优先，下界子序列为备选

当 lambda_n > 0，联合尾项条件等价于现有充分预算的归一化形式：

```text
A_rho * (1/4)^n * (1+H^4/lambda_n)^2 < multiplicity_rho
A_rho = beta_s * H^4 * (2*pi)^12 * (C4*C2)^2
```

首选：以该 n 的 `ell_n = blo/Chi` 证明
`A_rho*(1/4)^n*(1+H^4/ell_n)^2 < multiplicity_rho`。
这是充分条件；失败只能否定该上界的闭合能力。

备选：固定 rho、base、correction、前缀后，证明某个 ell_rho > 0，
并对每个 N 找到 n >= N 满足 admissibility、det_n < 0 和
lambda_n >= ell_rho。几何衰减随后保证某个此类 n 闭合尾项。
这里“任意大的成功次数”与“正下界”均为 OPEN；单个成功 n 不能推出它们。
无需 lambda 的上界，也不要求所有足够大的次数均成功。

最后设 `M = multiplicity_rho*lambda_n^2`。在 beta_s > 0 下，
可选择 `epsilon_span^2 = (L_n+M/beta_s)/2`，并取正平方根。
从 `beta_s*L_n < M` 推出两个严格条件：
`L_n < epsilon_span^2` 和 `beta_s*epsilon_span^2 < M`。
证明这些条件后才调用 FourthOrderSpectralTail 和最终组装函数。

## 7. 分轮执行与交付

R0 当前实现：`C1ExplicitFiniteNodeCorrection.lean` 用指数加权 seed 与
其他节点上的微分消零，构造节点差乘积作分母的显式 cardinal correction。
具体 seed 的非零质量与可压缩支撑已证明；base 可由同一公式取目标值 1，
correction 取所需数据，目标值保持对所有 n 成立。它是已有插值类中的
具体候选，不宣称等于旧 classical-choice 代表，也不自动继承任何 gate 符号。
下一入口是完整 target/prefix 节点实例化、衰减成本和 signed-margin 筛查，
不能直接跳到 R3。新 norm 上界仅用于成本/误差控制，signed 矩仍使用精确和式。

| 轮次 | 输入与工作 | 可审查交付 | 验收/停止点 |
|---|---|---|---|
| R0：owner 定量化 | 读取实际 base/correction 构造；明确选择方式与插值数据 | 源码定位、支撑/节点/常数依赖表；可估计表达式或具体缺失字段 | 任意 bump 或仅存在性选择器不得充当定量 producer |
| R1：可行性筛查 | 在 R0 同一类上针对 detUpper、blo、相对尾项做最小参数化 probe | 参数、源哈希、owner/素数集来源、误差分类、明确的待证余量 | 无完整 owner/readback 时停止实际-owner 认证宣称；浮点失败/通过均注明范围 |
| R2：关键解析界 | 证明实际矩包络、补集及必要的连续或物理 readback | 一个真正作用于选定 detector 的定量界，或可复核 scoped no-go | 仅代数恒等式/接口包装不计核心进展 |
| R3：联合选择 | 消去 det、blo、admissibility、相对尾项前提 | 同一 n、明确 lambda_n、完整前缀数据的见证 | 不允许从不同次数/不同 owner 拼接证书 |
| R4：覆盖与终验 | 对每个假设 rho 完成构造并调用既有出口 | 无 producer 留空的 RH 定理及配对 axiom audit | 覆盖未完成则保持 OPEN；不能以四个锚点替代全称 |

不预先批量新建 Lean 叶子。确需新增的定量引理放入现有 owning module
或一个有直接消费者的 focused leaf；每个新增 Dev leaf 配套 Audit。
候选代数误差引理必须与实际矩的认证一起接入；单独完成不升级 producer 状态。

R1 只能在明确数学决策下运行。计算型样本可以选择形式参数，但不得声称
其为实际离线零点；还须明确它满足构造合同中的哪些可检查部分。
四个旧有理数锚点可作算术回归数据，不能作真实积分证据。

## 8. 已核对的源码接口与未完成部分

| 文件/声明 | 已有作用 | 仍须交付 |
|---|---|---|
| `C1HealthyYoshidaUnscaledOrbit.lean` / `exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner_with_raw_targets_all_indices_of_base_data` | 固定 correction 后保留 all-index 结论，带显式 hsmall | 实际定量选择、admissibility、所用消费者全部字段 |
| `C1FourPointSpanGateCertificate.lean` / `annihilator_span_gate_eq_parabola`, `gate_quadratic_at_vertex` | 实际 span 二次式及具体 vertex 恒等式 | 支撑输入、C_n > 0、b_n > 0、det_n < 0 |
| 同文件 / `exists_pos_lambda_gate_and_prefix_of_annihilator_det_neg` | gate 与有限集合前缀的条件组合 | healthy/轨道/消零字段；具体 vertex 的保留与谱壳前缀转换 |
| `C1FourPointHighShellTail.lean` / `selectedOwner_fullOrbit_span_fourthOrderSpectralTail` | 从 L_n < epsilon_span^2 产生实际 span 尾界 | 固定常数、同 n/lambda、严格 scalar 预算 |
| `C1FourPointMainlineRH.lean` / `witness_of_gate_and_tail` | 同一 span 的 gate、壳前缀和尾界组装 | T <= 2^(s+1)、2*abs(rho.im) <= 2^(s+1)、壳前缀 <= -M、beta_s*epsilon_span^2 < M |
| 同文件 / `riemannHypothesis_of_mainline_witness_producer` | 对每个右离线零点的矛盾见证推出 RH | 实际全称 producer；不是另一个 conditional exit |

有限集合前缀到 `sum k in range(s+1), tsum z : spectralHeightShell k` 的转换
必须显式复核：包括 rho、全部相关壳、重数、轨道碰撞及边界约定。
不能只证明某个任意有限 S 的不等式就交给 shell 消费者。

具体复用 `C1HealthyYoshidaSpectralNegativity.lean` 的
`spectralHeightShellPrefix (s+1)` 作为 S，并调用
`sum_spectralHeightShellPrefix_eq_shell_prefix`，取 F 为 h_n 的卷积平方。
成员条件由 `mem_spectralHeightShellPrefix_iff` 给出；
`spectralHeightShellPrefix_subset_finiteHeightZeros` 提供高度覆盖。
从高度覆盖到构造所用闭球半径 R 的包含关系仍须证明。
谱壳使用 `dyadicShellIndex` 的严格上界约定，不能自行换成端点重复的闭区间分割。

## 9. 复核及验收纪律

本计划已按当前源码签名复核；中心化与误差/相对尾项公式属于纸面代数，
不是新落地 Lean 定理。原 105 的 30x、全区均值差 5700、固定 5% 质量比
自动闭合和 determinant 符号表述均不作为本计划依据。

后续数学验收必须检查：

- gate 用 `b=B'/2`，vertex 用 `b/C`；ANOVA 的正支配表达式为 `-det`。
- 实际矩与数值包络有证明连接；误差非负；除数正；两处尾项不等式严格。
- 没有省略负区方差、补集或实际可见素数；没有未证偶性/通道符号。
- 同 rho、base、correction、n、lambda、前缀及支撑贯穿全部消费者。
- hproducer/hdom/hdet/hsmall 已由实际估计证明，未存入结构作为输入。
- 无 sorry/admit、新公理或替代 owner；审计叶子只有标准三公理。

Lean 修改前执行冻结检查。构建只在 WSL ext4 验证副本，仅同步
改动文件并核对哈希，使用资源 runner 和绝对 Lake 路径。
验收次序：owning module、import-facing probe、paired audit、route/Dev batch、
full root；以成功 footer 且零 `error:` 行为准，不以退出码替代日志。
每个数学判断变化更新对应 map/proof record 和一条 dated MEMORY。
计划最初的落地检查为源码引用、公式推导、相对链接及 diff。
后续 Lean 实施及构建证据单独记录在对应 proof record，目前为 1958。

## 10. Implemented budget wrapper (1960)

The new theorem norm_laplaceAt_le_exp_mul_l1Mass in C1CompactSupportLaplaceBounds.lean controls any finite-support correction Laplace value by exp(abs(Re(s))*B) * l1Mass. Its paired audit passes with only the standard three axioms. This is an interface reduction for the correction quadratic budget, not a signed determinant proof. The next quantitative obligation is to bound the explicit correction's l1Mass and node-product denominators for the actual finite zero owner, then feed those bounds into hcorrectionQuadratic and the same-owner determinant budget.


## 11. Correction mass envelope (1961)

l1Mass_correction_le now reduces the correction L1 budget to explicit coefficient norms and the individual cardinalRaw L1 masses. The next proof must estimate those individual masses for the actual node set; the finite-sum triangle inequality itself is no longer an open obligation.


## 12. Core no-go for current quantitative selector (1962)

The actual cardinalRaw contains an arbitrary finite product of derivativeShift. The committed Mathlib ContDiffBump seed exposes no quantitative derivative or higher-derivative L1 constants, and baseBump is noncomputable. Therefore the 1961 correction L1 envelope cannot be turned into an explicit owner-level budget under the current API. This is now a scoped no-go: continue only with a concrete analytic seed, a selector carrying certified derivative seminorms, or a different quantitative interpolation basis. Do not claim determinant progress until one of these changes supplies an explicit margin.


## 13. Option A concrete seed (1963)

C1ExplicitSmoothSeed.lean now replaces the noncomputable ContDiffBump at the seed boundary with a concrete Real.smoothTransition product. Its support, plateau, smoothness, and nonzero Laplace value are audited. The next core obligation is explicit derivative/L1 constants for this seed and iteration through cardinalRaw; the failed derivative-budget draft was removed and is not counted as progress.



## 11. CardinalRaw derivative/L1 budget status (1964)

The actual selector now has a checked L1 recurrence in C1ExplicitSmoothSeedDerivativeBudget.lean. The one-step derivativeShift inequality is proved by the norm triangle inequality and compact-support integrability; induction preserves the exact owner list and gives l1Mass_cardinalRaw_le. Owning and paired-audit builds passed with only the standard three axioms. This closes the interface gap identified in 1962/1963, but does not close the quantitative budget: explicit derivativeL1 constants for the concrete smooth seed, exponential weighting, and the actual node-product separation are still OPEN.


## 12. Node-product denominator interface (1964 follow-up)

The derivative-budget module now also proves norm_nodeProduct_self_ge_pow. The actual denominator is bounded below by a power of any certified uniform node separation delta. This is a checked reduction, not the missing separation estimate: the selected finite zero owner must still provide an explicit delta and the correction coefficient budget must consume the resulting power.


## 13. Batch mass-budget closure (1965)

The explicit seed mass is now bounded by 4, using its actual support interval [-2,2] and amplitude bound. The exponential-weight initial mass is bounded by 4 * exp(2 * |Re(a)|). Both statements have paired standard-axiom audits.

The cardinalRaw module now exposes l1Mass_cardinalRaw_le_of_budget: an exact induction consumer that closes the actual (nodes.erase z).toList recurrence from any supplied suffix derivative budget. This is the correct batch interface; a stronger unproved length/product formula was explicitly discarded.

Status: seed mass and exponential-weight mass CLOSED; exact cardinalRaw budget consumer CLOSED; concrete derivativeL1 constants, actual node separation, correction quadratic margin, signed determinant, and same-index tail remain OPEN.


## 14. Derivative constant reduction (1966)

A generic checked theorem now converts a pointwise derivative bound into an L1 bound: support in [-B,B] plus norm(deriv f) <= M implies derivativeL1 f <= (2*B)*M. This is the correct next interface for the explicit smoothTransition seed. The concrete M remains OPEN; no numerical derivative constant is claimed.


## 15. expNegInvGlue derivative constant (1967)

The exact Mathlib formula for expNegInvGlue now yields a verified pointwise derivative bound norm(deriv expNegInvGlue x) <= 4. The proof uses only t >= 0 and t^2 exp(-t) <= 4, avoiding the false global version for negative t. Owning and paired audits pass. The derivative bound for the product smoothSeedRaw remains OPEN because the CompactLogTest wrapper and explicit chain-rule bridge still need to be proved.


## 16. Committed owner density probe (1959)

The Cut-2 gate entries of the committed `selectedOwner` shape are now measured
(`docs/proofs/1959_fourpoint_owner_density_probe.md`, rig
`scripts/fourpoint_owner_density_1959.py`, four result JSONs). Findings that
change the execution picture:

```text
C>0 is not implied by the producer hypotheses.  On the committed owner shape
the archimedean and prime channels cancel to 3..5 digits (|arch|/|residual| up
to 7.2e+03 on C and 8e+04 on D), and C changes sign with the free window knob.
Of 27 grid rows only 5 have C > 0; of 9 points of a local scale scan, 6.

The section 2 endpoint pattern (C>0, b>0, det<0) IS realized on the committed
owner shape, at two knob points: (delta=0.05, gamma_1, n=0) with (k=30,
scale=0.90) giving C=+5.0545, b=+2.9649e+04, det=-1.2857e+09, lambda_n=5866.0,
gate(h_n)=det/C=-2.5436e+08; and (k=40, scale=1.0) giving C=+9.8445e-01,
b=+2.3050e+03, det=-1.2317e+07, lambda_n=2341.4, gate(h_n)=-1.2511e+07.
In this regime D < 0, so det = C*D - b^2 < 0 is AUTOMATIC once C > 0: the
binding obligations of section 2 are C > 0 and b > 0 only.

The signs are a knife edge, not a mechanism: b changes sign between adjacent
scan knots (scale 0.86: -4.5e+03; 0.88: -2.0e+04; 0.90: +2.96e+04; 0.92:
-7.2e+03).  A Cut-2 witness (some nonzero lambda with Q(lambda) <= 0) exists
on 36/36 measured rows, in three different sign regimes, but no monotone or
Lipschitz mechanism for C > 0 or b > 0 is visible.  Any Lean proof of the
endpoint must therefore come from the actual construction's analytic
structure, not from sign bookkeeping.
```

Rigid byproducts usable in the mainline: `W(0) = 0` exactly for every
admissible owner (raw node `1/2` has target value `0`
`[C1HealthyYoshidaUnscaledOrbit.lean:33,43,567]` with `L_base(1/2) = 1`
`[ibid.:544-547]` through the Hermitian pairing
`[UnscaledYoshidaSelectedOwner.lean:153]`) — the density never carries mass at
the origin; the density is confined to `|xi| <~ 4` (worst mass beyond 4 is
6.6e-05), which bounds the visible prime book; the committed 1958 cardinal
bump base is numerically unusable for a gate reading (99.9% of its mass
beyond `|xi| > 4`, strip contraction fails on `t <= 150`), so the missing
analytic object of this lane is a computable admissible base with a certified
contraction constant.

Status: the sign side of section 2 is demonstrably reachable, the quantitative
side (section 2 tail budget, `beta_s * L_n < multiplicity_rho * lambda_n^2`
with `lambda_n ~ 2.3e+03..5.9e+03`) is untouched, and no gate sign, determinant
sign or RH claim is made.

## 17. Explicit seed derivative constant (1968)

The last named blocker of the explicit-seed chain is now closed: the transition
function has the exact derivative `uv (a^2 + b^2) / (u + v)^2` with a pointwise
constant that is sharp (`norm (deriv smoothTransition x) <= 2`, attained at
`x = 1/2`), the committed seed inherits `norm (deriv smoothSeedRaw x) <= 4`
through the product rule (the true supremum is `2`: the two derivative factors
have disjoint active windows, so the region split is the named sharpening), the
complex and `CompactLogTest` wrappers carry the same constant, the derivative
support stays in `[-2,2]`, and the committed
`derivativeL1_le_of_support_of_norm_le` returns `derivativeL1 smoothSeed <= 16`.
Record: `docs/proofs/1968_smooth_seed_derivative_value.md`; build log
`build-logs/1968_smoothseed_derivative_value.log` (3645 jobs, zero errors, no
warnings in the two new modules, all 14 declarations on the standard three
axioms).

Status: the base of the explicit-seed budget chain is CLOSED. The next
obligations are the shifted-product recurrence constants and the node-product
constants that multiply this base, the strip contraction, and then the numeric
`cardinalRaw` budget at a concrete node set.

## 18. Sharp seed derivative constant (1969)

Section 17 named a sharpening and left it open: the seed bound `4` came from
the product rule, and the true supremum is `2` because the two derivative
factors of `smoothSeedRaw x = smoothTransition (x + 2) * smoothTransition (2 - x)`
are active on the disjoint windows `(-2,-1)` and `(1,2)`, where the passive
factor equals `1` and has zero derivative. That sharpening is now executed. The
transition derivative vanishes on `[1, inf)` (`deriv_smoothTransition_eq_zero_of_one_le`),
so for `x <= 1` the seed derivative is `T' (x + 2) * T (2 - x)` and for `1 <= x`
it is `- T (x + 2) * T' (2 - x)`; with `0 <= T <= 1` and `|T'| <= 2` both
regions give `norm (deriv smoothSeedRaw x) <= 2`. The bound is attained:
`deriv smoothTransition (1/2) = 2`, `deriv smoothSeedRaw (-3/2) = 2` and
`deriv smoothSeedRaw (3/2) = -2`, so `2` is the exact supremum and not merely an
upper bound. The complex and `CompactLogTest` packaging carries `2`, and the
budget consumer returns `derivativeL1 smoothSeed <= (2 * 2) * 2 = 8`, halving
the `16` of section 17. The coarser statements of section 17 stay in place and
remain true. Record: `docs/proofs/1969_sharp_smooth_seed_derivative_constant.md`;
build log `build-logs/1969_sharp_seed_derivative.log` (3646 jobs, zero errors,
no warnings in the two new modules, all 9 declarations on the standard three
axioms).

Status: the seed derivative constant is now optimal for the committed budget
shape, so this sub-chain is closed pending only the shifted-product recurrence
constants and the node-product constants that multiply the base, the strip
contraction, and the numeric `cardinalRaw` budget at a concrete node set.

## 19. The derivative ladder for shifted products (1970)

Section 18's status line named the shifted-product recurrence constants as the
next obligation. Writing them down exposes why they cannot be a single number:
the committed `shiftedProductL1Bound` feeds `derivativeL1 (shiftedProduct as f)`
back into its own recursion, so the step for a suffix asks for the derivative
budget of that suffix and never closes on the seed. The honest recursion needs
one number per derivative order, and those numbers are the masses of the
iterated derivatives of the seed:

    derivOrderL1 m f = ∫ x, norm (iteratedDeriv m (f.test) x),

which starts at `l1Mass` (`m = 0`) and meets the committed `derivativeL1` at
`m = 1`. One shift raises the order — `iteratedDeriv m ((derivativeShift f a).test) x
= iteratedDeriv (m + 1) (f.test) x + a * iteratedDeriv m (f.test) x`
(`iteratedDeriv_derivativeShift_apply`) — hence
`derivOrderL1 m (derivativeShift f a) <= derivOrderL1 (m + 1) f + norm a * derivOrderL1 m f`
(`derivOrderL1_derivativeShift_le`), the committed shift step one order up. The
ladder budget `L m` for `[]` and `L (m + 1) + norm a * L m` for `a :: as` is
nonnegative for nonnegative `L` and majorizes every shifted product at every
order (`derivOrderL1_shiftedProduct_le`), and its `m = 0` case is delivered both
directly and through the committed consumer `l1Mass_shifted_product_le_of_budget`
(`l1Mass_shiftedProduct_le_of_ladder`), whose step condition is the recursion
itself. For a one-node list the budget is exactly the committed
`l1Mass_derivativeShift_le`, so the ladder extends the committed interface
rather than replacing it. The order-`m` form of the support-times-sup budget
(`derivOrderL1_le_of_support_of_norm_le`) converts each ladder value into a
`(2 * B) * M` pair, with the committed order-one form's `0 <= M` hypothesis
dropped as redundant. Record: `docs/proofs/1970_derivative_ladder.md`; build log
`build-logs/1970_derivative_ladder.log` (3641 jobs, zero errors, no warnings in
the two new modules, all 13 declarations on the standard three axioms).

Status: the shifted-product recurrence constants are now a named ladder — the
masses `derivOrderL1 j smoothSeed` for `j <= m + |nodes|` at order `m`, each
convertible to a `(2 * B) * M` pair — and no number is chosen yet. The open
obligations are the numerical ladder values at a concrete node set, the
node-product constants, the strip contraction, and then the numeric
`cardinalRaw` budget, the correction quadratic margin, the signed determinant
and the joint tail margin.

## 20. One support radius for the whole ladder (1971)

Section 19's status line left the ladder as a bound with, apparently, two inputs
per order: a support radius and a sup norm of the `m`-th derivative. The radius
was never a second unknown. The support of a derivative stays inside the closure
of the support of the function, because a point outside that closure has an open
neighbourhood on which the function vanishes identically; there the function is
eventually `0`, so by `Filter.EventuallyEq.deriv_eq` and `deriv_const` its
derivative vanishes at the point as well
(`support_deriv_subset_closure_support`, for every `f : ℝ → ℂ`, no
differentiability hypothesis needed). Iterating with `iteratedDeriv_succ`,
`closure_mono` and `closure_closure` gives the same for every iterated
derivative, and `closure_minimal` with `isClosed_Icc` puts every order inside
one closed interval as soon as the hypothesis holds at the function itself:
`support_iteratedDeriv_subset_Icc`. The committed seed satisfies it at the
function level (`support_smoothSeed_test_subset`, support inside `[-2, 2]`), so
the radius of the ladder is the single number `2` at every order, and
`derivOrderL1_le_of_supportRadius` is the order-`m` support-times-sup budget
with that slot discharged once and for all.

The seed oracle is then `derivOrderL1 m smoothSeed <= 4 * M` for any real `M`
bounding the `m`-th derivative (`derivOrderL1_smoothSeed_le`, the factor `4`
being `2 * B` at `B = 2`), and its `m = 1` case with the committed sup bound `2`
returns `derivativeL1 smoothSeed <= 8` — section 18's constant, recovered
through the new route as a consistency check rather than as a new number. The
ladder is monotone in its input family (`ladderBound_mono`, by induction on the
node list with the order generalized), so the seed-level statement needs exactly
one unknown per order: whenever `M j` bounds the `j`-th derivative of the
committed seed, the shifted product obeys
`l1Mass (shiftedProduct nodes smoothSeed) <= ladderBound (4 * M ·) nodes 0`
(`l1Mass_shiftedProduct_smoothSeed_le`). The ladder also reaches the committed
owner functional: the step condition of `l1Mass_cardinalRaw_le_of_budget` is
the ladder recursion itself, so the committed consumer accepts the ladder of the
exponentially weighted seed as its budget function
(`l1Mass_cardinalRaw_le_ladder`), for every node set, seed and base point.
Record: `docs/proofs/1971_support_stability_one_radius.md`; build log
`build-logs/1971_support_stability.log` (3648 jobs, zero errors, no warnings in
the two new modules, all 10 declarations on the standard three axioms).

Status: the shifted-product budget for the committed seed is now a bound with
one unknown family per order, the sup norms of the seed's iterated derivatives;
no number is chosen for that family, so the ladder is still a reduction and not
a numeric budget. The open obligations are the numerical ladder values at a
concrete node set, the node-product constants, the strip contraction, and then
the numeric `cardinalRaw` budget, the correction quadratic margin, the signed
determinant and the joint tail margin.

## 21. The seed ladder over the transition function (1972)

Section 20's status line left the seed ladder as a bound with one unknown family
per order, the sup norms of the seed's iterated derivatives. That family is the
transition function's. The committed seed is the product of two translates of
`Real.smoothTransition` (`T`), and each translate is constant on the side of the
window where the other one acts: `T (x + 2) = 1` for `x >= -1` and
`T (2 - x) = 1` for `x <= 1`. For every positive order only one term of the
Leibniz sum is therefore alive at a time,
`iteratedDeriv j smoothSeedRaw x = iteratedDeriv j T (x + 2) + (-1)^j *
iteratedDeriv j T (2 - x)` (`iteratedDeriv_smoothSeedRaw_eq`), the two cases
being `Filter.EventuallyEq.iteratedDeriv_eq` at the points where the seed is
eventually one translate. The transition derivatives vanish at both ends
(`iteratedDeriv_smoothTransition_eq_zero_of_lt_zero`, and `..._of_one_lt` for
positive orders, where the positive-order hypothesis is genuine), so
`support (iteratedDeriv j T) <= [0, 1]`, at every point at most one term of the
split is nonzero, and the norms add (`norm_iteratedDeriv_smoothSeedRaw_eq`, and
at the committed complex packaging `norm_iteratedDeriv_smoothSeed_test_eq`
through `iteratedDeriv_smoothSeedComplex_eq`).

Integrating the norm identity against Lebesgue measure — invariant under the
shift by `2` and under the reflection — gives the ladder identity
`derivOrderL1 j smoothSeed = 2 * Integral x, norm (iteratedDeriv j T x)` for
`j >= 1` (`derivOrderL1_smoothSeed_eq`): the seed's ladder is the transition
function's derivative mass doubled, one integral per order. Order one is then a
number: the transition rises from `0` to `1`, so its derivative is nonnegative
(`deriv_smoothTransition_nonneg`), supported in `[0, 1]`
(`support_deriv_smoothTransition_subset`), and
`Integral x, norm (deriv T x) = 1`
(`integral_norm_deriv_smoothTransition_eq_one`), whence
`derivativeL1 smoothSeed = 2` (`derivativeL1_smoothSeed_eq_two`) — section 18's
committed bound `<= 8` is not sharp. The seed oracle carries the transition's
sup norms with the factor `2` instead of section 20's `4`
(`derivOrderL1_smoothSeed_le_two_mul`), and the first numerically bounded rung
of the ladder is `l1Mass (shiftedProduct [a] smoothSeed) <= 2 + 4 * norm a`
(`l1Mass_shiftedProduct_singleton_smoothSeed_le`). Record:
`docs/proofs/1972_seed_transition_reduction.md`; build log
`build-logs/1972_seed_transition_reduction.log` (3650 jobs, zero errors, no
warnings in the two new modules, all 20 declarations on the standard three
axioms).

Status: the seed ladder is now one function and one integral per order, and its
first rung is the exact number `2`; the order-`j >= 2` values stay the explicit
integral `2 * Integral x, norm (iteratedDeriv j T x)`, and no number is chosen
for the sup norms there. The open obligations are the numerical ladder values
at a concrete node set, the node-product constants, the strip contraction, and
then the numeric `cardinalRaw` budget, the correction quadratic margin, the
signed determinant and the joint tail margin.

## 22. The second rung of the seed ladder is eight (1973)

Section 21 left the order-two value as the integral of `norm (T'')`. That
integral is now evaluated. The committed derivative formula of the transition
factors through the logistic pair and a gain,
`deriv T x = T x * (1 - T x) * windowGain x` with
`windowGain x = (x^-1)^2 + ((1 - x)^-1)^2`
(`deriv_smoothTransition_eq_mul_windowGain`; the identity is universal in `x`
because both sides die at the window's edges through the `inv_zero`
conventions). The gain is even under `x -> 1 - x` (`windowGain_one_sub`), its
named derivative `windowGainSlope x = -2 * (x^-1)^3 + 2 * ((1 - x)^-1)^3` is
odd under the reflection (`windowGainSlope_one_sub`) and is produced from
`hasDerivAt_inv` by the chain rule (`hasDerivAt_windowGain`). On the open
window `1 - 2 T` is the logistic ratio in the exponential variable
`w = (1 - 2 x) / (x * (1 - x))`,
`1 - 2 T x = (exp w - 1) / (exp w + 1)`
(`one_sub_two_mul_smoothTransition_eq`, through the addition formula for `exp`
applied to `expNegInvGlue (1 - x) = exp w * expNegInvGlue x`), it is odd in `w`
(`exp_neg_sub_one_div_exp_neg_add_one`), and it dominates the elementary ratio
`v / (v + 2) <= (exp v - 1) / (exp v + 1)` for `v >= 0`
(`self_div_add_two_le_exp_ratio`, whose content is exactly the convexity
inequality `1 + v <= exp v`).

Differentiating the factorization gives, on `(0, 1)`,
`T'' x = T x * (1 - T x) * ((1 - 2 T x) * windowGain x ^ 2 + windowGainSlope x)`
(`iteratedDeriv_two_smoothTransition_eq`), and the sign of that expression is
decided by comparing the gain's relative slope against the logistic ratio at
the standard point `x = (1 + s)/2`, `s = |2 x - 1|`: there
`windowGain ((1 + s)/2) = 8 (1 + s^2) / (1 - s^2)^2` and
`windowGainSlope ((1 + s)/2) = 32 s (s^2 + 3) / (1 - s^2)^3`
(`windowGain_half_eq`, `windowGainSlope_half_eq`), so the relative slope is
`s (s^2 + 3) (1 - s^2) / (2 (1 + s^2)^2)` times the squared gain
(`windowGainSlope_div_sq_half_eq`), which sits strictly below the logistic
ratio at `v = 4 s / (1 - s^2)` (`windowGain_ratio_lt_exp_ratio`). The
polynomial core of that comparison is
`4 (1 + s^2)^2 - (s^2 + 3) (1 - s^2) (1 + 2 s - s^2)
= (13 s^2 - 6 s + 1) + s^3 (4 + 3 s + 2 s^2 - s^3) > 0` on `[0, 1]`, the two
summands being `((13 s - 3)^2 + 4)/13` and a nonnegative factor; the logistic
variable is `-v` at the standard point (`halfPoint_one_sub_two_div`) and `+v`
at the reflected point (`reflectPoint_one_sub_two_div`). The conclusion is the
sign of the second derivative, `0 <= T'' x` on `(0, 1/2]` and `T'' x <= 0` on
`[1/2, 1)` (`iteratedDeriv_two_smoothTransition_nonneg`, `..._nonpos`, with the
half point decided by the Fermat value), alongside the three vanishing values
`T'' 0 = T'' 1 = T'' (1/2) = 0`
(`iteratedDeriv_two_smoothTransition_zero`, `..._one`, `..._half`) read off
`IsLocalMin.deriv_eq_zero` and `IsLocalMax.deriv_eq_zero` from the committed
`0 <= deriv T`, `deriv T (1/2) = 2` and `norm (deriv T x) <= 2`.

The fundamental theorem of calculus on the two halves then gives
`Integral x in 0..1/2, T'' x = 2` and
`Integral x in 1/2..1, T'' x = -2`
(`integral_iteratedDeriv_two_smoothTransition_left`, `..._right`), the sign
turns the absolute value into `T''` on the left half and `-T''` on the right
half (`integral_abs_iteratedDeriv_two_smoothTransition_left`, `..._right`), and
the absolute-value mass of the transition's second derivative is the exact
number `Integral x, norm (T'' x) = 4`
(`integral_abs_iteratedDeriv_two_smoothTransition`). With section 21's ladder
identity the second rung is therefore

    derivOrderL1 2 smoothSeed = 8

(`derivOrderL1_smoothSeed_two`). Record:
`docs/proofs/1973_seed_second_order_mass.md`; build log
`build-logs/1973_seed_second_order_mass.log` (3651 jobs, zero errors, no
warnings in the two new modules, all 27 declarations on the standard three
axioms).

## 23. The third rung of the seed ladder is not a number (1974)

The second slope of the gain, `windowGainSecondSlope x = 6 * (x^-1)^4 +
6 * ((1 - x)^-1)^4`, is produced from `hasDerivAt_windowGainSlope` by the chain
rule on `hasDerivAt_inv` alone (`hasDerivAt_windowGainSlope`); it is even under
the reflection (`windowGainSecondSlope_one_sub`), positive on the open window
(`windowGainSecondSlope_pos`) and equal to `192` at the midpoint
(`windowGainSecondSlope_half_eq`). The transition itself satisfies the exact
reflection identity `smoothTransition (1 - x) = 1 - smoothTransition x`
(`smoothTransition_one_sub`), so the logistic pair flips sign,
`1 - 2 * T (1 - x) = -(1 - 2 * T x)`
(`one_sub_two_mul_smoothTransition_one_sub`), with the midpoint values
`T (1/2) = 1/2`, `windowGain (1/2) = 8`, `windowGainSlope (1/2) = 0`
(`smoothTransition_half_eq`, `windowGain_half_point_eq`,
`windowGainSlope_half_point_eq`). Differentiating the committed second-order
closed form by the product rule (bridge
`iteratedDeriv 3 T = deriv (iteratedDeriv 2 T)`,
`iteratedDeriv_three_smoothTransition_eq_deriv_deriv`) gives, on `(0, 1)`,

    T''' x = T x * (1 - T x) * ( ((1 - 2 T x)^2 - 2 T x (1 - T x)) * G x^3
                                  + 3 * (1 - 2 T x) * G x * G' x + G'' x )

(`hasDerivAt_iteratedDeriv_two_smoothTransition`,
`iteratedDeriv_three_smoothTransition_eq`), with the bracket coefficient `3`
and the normal form `(1 - 2 T)^2 - 2 T (1 - T) = (3 u^2 - 1)/2` in
`u = 1 - 2 T`; the first hand pass had `2` in place of `3` and the probe's
Richardson difference of `T''` at `x = 0.218` rejects it (`135.868` against
`0.367`).

Reflection transports the two closed forms to `T'' (1 - x) = -T'' x` and
`T''' (1 - x) = T''' x` (`iteratedDeriv_two_smoothTransition_one_sub`,
`iteratedDeriv_three_smoothTransition_one_sub`), the midpoint value is
`T''' (1/2) = -16` (`iteratedDeriv_three_smoothTransition_half`), the committed
sign lemmas of section 22 upgrade to genuine local extrema at the endpoints
through `Ioo_mem_nhds` (`isLocalMin_iteratedDeriv_two_smoothTransition`,
`isLocalMax_iteratedDeriv_two_smoothTransition`), Fermat's theorem gives
`T''' 0 = T''' 1 = 0` (`iteratedDeriv_three_smoothTransition_zero`, `..._one`),
and the fundamental theorem of calculus on the left half gives
`Integral x in 0..1/2, T''' x = T'' (1/2) - T'' 0 = 0`
(`integral_iteratedDeriv_three_smoothTransition_left`). That is the end of the
order-two mechanism: the sign flip of `T'''` is interior.

The bracket is a cancellation among three terms of different homogeneity, with
the leading term's zero at `x = 0.350163715843` and the bracket's zero at
`x* = 0.218255829186` (probe bisection; there the three cleared terms read
`+1.841656e4`, `-2.373702e4`, `+5.320452e3`, summing to `2.8e-10`). Since
`T''` rises from `0` to its peak `T'' x* = 9.841042301831` and returns to `0`
at `1/2`, the total-variation identity
`Integral x in 0..1/2, norm (T''' x) = 2 * T'' x*` holds (probe residual
`5e-9`), reflection doubles it, and the third rung is the transcendental
constant `derivOrderL1 3 smoothSeed = 8 * T'' x* = 78.728338...` (quadrature
`78.72833839` against `8 * T'' x* = 78.72833841`). Without single-peakedness
the certified half is the comparison chain
`norm (T''' (1 - u)) = norm (T''' u)` on `[0, 1/2]`,
`T'' x <= Integral y in 0..x, norm (T''' y)`, the same bound with the integral
over the whole left half, and hence

    4 * T'' x <= derivOrderL1 3 smoothSeed     for 0 < x < 1/2

(`norm_iteratedDeriv_three_one_sub`,
`iteratedDeriv_two_le_integral_norm_iteratedDeriv_three`, `..._left`,
`derivOrderL1_smoothSeed_three_ge`), one point value certifying a lower bound.
Record: `docs/proofs/1974_seed_third_order_structure.md`; build log
`build-logs/1974_seed_third_order_structure.log` (3652 jobs, zero errors, no
warnings in the two new modules, all 24 declarations on the standard three
axioms); probe `scripts/seed_third_order_probe_1974.py`.

## 24. The third-order sign comparison: one explicit one-variable inequality (1975)

Record 1974 left the third rung at `8 * T'' x*` with single-peakedness of `T''`
on `(0, 1/2)` open. In the half-width coordinate `s = 1 - 2 x` (so the left half
is `0 < s < 1`) the committed third-order closed form clears to a quadratic in
the logistic variable `u = 1 - 2 T x`:

    (1 - s^2)^6 * T''' ((1 - s) / 2)
      = 64 * (T x * (1 - T x)) * thirdOrderBracket s (1 - 2 T x)

(`iteratedDeriv_three_smoothTransition_eq_bracket`), with

    thirdOrderBracket s u = thirdOrderLeading s * u^2
                            - thirdOrderMiddle s * u + thirdOrderConstant s,
    thirdOrderLeading  s = 12 (1 + s^2)^3                     > 0,
    thirdOrderMiddle   s = 12 s (1 + s^2) (3 + s^2) (1 - s^2) >= 0 on [0, 1],
    thirdOrderConstant s = -1 + s^4 (3 s^4 + 8 s^2 - 42)      <= -1 < 0 on [0, 1]

(`thirdOrderBracket_eq_quadratic`, `thirdOrderLeading_pos`,
`thirdOrderMiddle_nonneg`, `thirdOrderConstant_neg`; the negativity of the
constant coefficient is the whole arithmetic input, and the middle coefficient
needs no sign). The clearing identity `bracket_clearing` multiplies the three
bracket terms of the closed form by `(1 - s^2)^6` into `64 * thirdOrderBracket`,
the degree-two first factor is normalized by the committed
`logistic_degree_two_normal_form`

    (1 - 2 t)^2 - 2 t (1 - t) = (3 (1 - 2 t)^2 - 1) / 2

(prose only in record 1974), and the reflected gain evaluations come from the
committed values at `(1 + s) / 2` through `windowGain_one_sub`,
`windowGainSlope_one_sub`, `windowGainSecondSlope_one_sub`
(`windowGain_reflect_eq`, `windowGainSlope_reflect_eq`,
`windowGainSecondSlope_reflect_eq`), with the one missing standard-point
evaluation
`windowGainSecondSlope ((1 + s)/2) = 192 (1 + 6 s^2 + s^4)/(1 - s^2)^4`
supplied by `windowGainSecondSlope_standard_eq` (record 1974 pinned `G''` only
at `1/2`).

The logistic input is the committed reflection route:
`one_sub_two_mul_smoothTransition_reflect_eq` reads `u` as the logistic pair
`(e^v - 1)/(e^v + 1)` at `v = 4 s/(1 - s^2)` and
`one_sub_two_mul_smoothTransition_reflect_pos` gives `u > 0`. The quadratic sign
rules `quadratic_pos_iff` and `quadratic_neg_iff` (for `a > 0 > c` and `u > 0`)
rest on the division-free discriminant identity
`4 a P u = (2 a u - b)^2 - (b^2 - 4 a c)` (`quadratic_discriminant_identity`)
and on the local sign transfer `mul_neg_of_pos_left_iff` (the pinned Mathlib has
`mul_pos_iff_of_pos_left` but no negative counterpart); they are stated as full
iff's, so the sign of `T'''` is read off in both directions. The threshold

    thirdOrderThreshold s
      = (thirdOrderMiddle s + sqrt (beta s^2 - 4 * alpha s * gamma s))
        / (2 * thirdOrderLeading s)

is the positive root (`thirdOrderThreshold_pos`), and the two sign theorems read

    0 < T''' ((1 - s)/2) <-> thirdOrderThreshold s < 1 - 2 T x,
    T''' ((1 - s)/2) < 0 <-> 1 - 2 T x < thirdOrderThreshold s

(`iteratedDeriv_three_smoothTransition_sign_iff`,
`iteratedDeriv_three_smoothTransition_neg_iff`). Single-peakedness of `T''` on
`(0, 1/2)` is therefore EXACTLY the single crossing of the logistic curve
`tanh (v/2)` with the quadratic irrationality `thirdOrderThreshold s` on
`(0, 1)`. The probe `scripts/seed_single_peakedness_probe_1975.py` locates the
crossing at `s* = 0.563488341628`, i.e. `x* = 0.218255829186`, the same
interior zero record 1974 found (factored `T'''` residual `-2.5e-13` there),
with crossing value `0.929034992747`, exact rational discriminants
`Delta (1/2) = 169275/256` and `Delta (1) = 12288`, and margins of the
comparison `-0.2887` on the left against `+1.07e-03` just past the crossing.
Record: `docs/proofs/1975_seed_third_order_comparison.md`; build log
`build-logs/1975_seed_third_order_comparison.log` (3653 jobs, zero errors, no
warnings in the two new modules, all 25 declarations on the standard three
axioms); probe log `build-logs/1975_single_peakedness_probe.log`.

## 25. The third rung is a certified rational bracket (1976)

The interval certificate of §24's obligation landed. The brick is
`ConnesWeilRH/Dev/C1ExplicitSeedThirdOrderIntervalCertificate.lean` (2175
lines, 131 declarations, paired audit with 131 `#print axioms`), in four
layers.

The exp machinery: `expTaylor` is the order-20 truncation of `exp` at `0` and
`expTail` the Lagrange tail `y^20/20! * 20/19`, giving the rational power
enclosure `exp_bounds_pow`

    (expTaylor (w/m) - expTail (w/m))^m <= Real.exp w
      <= (expTaylor (w/m) + expTail (w/m))^m        for 0 <= w, 1 <= m, w <= m.

Through the increasing ratio `x -> (x-1)/(x+1)` this transfers to the
logistic variable `seedU s = tanh (seedV s / 2)`, `seedV s = 4 s/(1 - s^2)`:
`seedU_mem_Icc` gives `seedULo s m <= seedU s <= seedUHi s m` for
`0 <= s < 1`, `seedV s <= m`. The bracket enclosure `seedBracket_mem_Icc`
then bounds the committed profile
`seedBracket s = thirdOrderBracket s (seedU s)` by the explicit rationals
`seedBracketLower a b uL uH` and `seedBracketUpper a b uL uH` on any window
`[a, b]` inside `[0, 1]` with a rational sandwich `uL <= seedU <= uH`, using
the monotone expansions of the three bracket coefficients.

The partition: 37 rational pieces, `[0, 11/20]` in 22 negative pieces
(`seedBracket_neg_L01` .. `L22`), the straddle `[11/20, 23/40]`, and
`[23/40, 1)` in 15 positive pieces (`seedBracket_pos_R01` .. `R15`); each
piece is a `norm_num` comparison on the explicit rational enclosure. On the
straddle the derivative of the profile along the curve is bounded below by the
explicit constant `seedHprimeLower`, whose two terms are `+1.869140038` and
`+18.264149737`, so `seedBracket_strictMonoOn` holds there
(`seedHprime_ge_lower` with `seedHprimeLower_pos`), and the interior zero is
unique: `existsUnique_seedBracket_eq_zero`, straddled by
`seedBracket (5634883/10^7) < 0 < seedBracket (1408721/2500000)`. The sign
split extends to the whole half-line on each side
(`seedBracket_neg_of_Icc_zero_s_d`, `seedBracket_pos_of_Ico_s_c_one`).

The rung: the sign transfer
`(1 - s^2)^6 * T'''((1-s)/2) = 64 * T x (1 - T x) * seedBracket s`
(`iteratedDeriv_three_smoothTransition_eq_seedBracket`) gives
`T''' > 0` on `x ∈ (0, x_c]` and `T''' < 0` on `x ∈ [x_d, 1/2)` with
`x_c = 1091279/5000000`, `x_d = 4365117/20000000`. With `T''((1-s)/2)`
bracketed by a Lipschitz evaluation (`iteratedDeriv_two_smoothTransition_mem_Icc`,
via `ttwoMp`, `ttwoLower`, `ttwoUpper`) and the gap bounded by
`iteratedDeriv_three_abs_le_gapBound` with
`gapBound = 16 |gapHi| / (1 - s_c^2)^6`, the two proper integrals evaluate by
FTC, and

    derivOrderL1 3 smoothSeed
      ∈ Set.Icc (787283384 / 10^7) (787283385 / 10^7)

(`derivOrderL1_smoothSeed_three_mem_Icc`). The rig
`scripts/seed_third_order_interval_certificate_1976.py` (exact rationals) puts
the rung at `78.7283384146455 .. 78.7283384149908`, width `3.45e-10`, so the
`1e-7` bracket is the certificate's chosen coarseness, not a limit of the
method. A rational bracket on the crossing follows: `x* ∈ (x_d, x_c)`, i.e.
`0.21825580 < x* < 0.21825585`. Record:
`docs/proofs/1976_seed_third_order_interval_certificate.md`; build log
`build-logs/1976_interval_certificate_build4.log` (3654 jobs, zero errors, no
warnings in the two new modules, all 131 declarations on exactly
`[propext, Classical.choice, Quot.sound]`).

Status: three rungs of the seed ladder are under control: `derivOrderL1 1
smoothSeed = 2`, `derivOrderL1 2 smoothSeed = 8` exactly, and the third rung
is now a certified rational bracket
`derivOrderL1 3 smoothSeed ∈ [787283384/10^7, 787283385/10^7]` around the
transcendental `8 * T'' x*` (which still has no closed form, and whose exact
value remains the model value only up to the certified bracket). The certified
sign split of `T'''` around the crossing also yields the rational bracket
`0.21825580 < x* < 0.21825585`, so the "single crossing" statement of §24 is
certified, not merely probed. What remains on this lane is the higher rungs
`j >= 4` (the same partition method applies at any order, at the cost of
enclosing the corresponding higher-order profile) and the final assembly of
the certified rungs into the committed consumer's budget. The remaining open obligations are otherwise
unchanged: the node-product constants, the strip contraction, and then the
numeric `cardinalRaw` budget, the correction quadratic margin, the signed
determinant and the joint tail margin, with `C > 0` still to come from a
designed admissible base on the construction side.
