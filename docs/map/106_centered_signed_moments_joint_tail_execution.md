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
