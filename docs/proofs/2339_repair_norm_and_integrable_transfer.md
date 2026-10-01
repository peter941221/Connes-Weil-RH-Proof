2339: 精确修复的加法范数转移与可积误差界

日期: 2026-10-01

结果: 部分推进。101 个节点中 100 个通过旧上限。节点 j=-50 的充分估计
超出约 0.315443。这不能证明实际范数超过上限，不能构成不可能结论。
n=0 的修复已有全频率可积误差界；完整核加权以及选定检测器的符号预算
仍然未完成。本记录保留旧范数全部膨胀余量，没有放宽旧 pin。

1. 对象与证据边界

范数 (norm) 把函数的大小积分成一个预算数。M0 计函数本身的大小，M2
计二阶导数的大小；后者控制频率增大时的衰减。

f0 使用原始存储系数和精确宽度平方，f1 使用记录 2338 的唯一解析插值解。
B0/C0、B1/C1 是对应变换。这里仅处理 n=0，源变换 H=B*C，临界线上的
卷积平方变换为 |H|^2。源零点、节点列表完整性和完整健康检测器仍未建立。

记录 2303 使用浮点半径 width*width。本记录先精确提升存储宽度再平方，
30 个半径中 29 个存在差别，单列几何误差。网格 sigma=j/100 与旧浮点
sigma 的指数权重误差也计费。三角不等式就像对账: 旧数额、换尺寸差额
和改系数差额各计一次。

本记录依赖 2303 的既有范数证书和 2338 的解析矩阵证书；没有重新积分
2303，没有把数值证书导入 Lean，没有替换当前生产者。

2. 101 节点检查

最小乘积 (min-product) 在两个合法乘积上界中取小者，用于控制源的二阶
衰减。它仍是上界，不能充当实际函数大小的下界。

```text
+------------------------------------------+----------------------+
| Quantity                                 | Reading              |
+------------------------------------------+----------------------+
| Existing pin                             | 2644542.8515         |
| Additive maximum, j=-50                  | 2644543.166942142... |
| Excess of sufficient bound               | 0.315442142224572... |
| Nodes fitting unchanged pin              | 100 / 101            |
| Nonzero radius-rounding bridges          | 29 / 30              |
| Unweighted full-line square-change upper | < 3.602              |
| Two-sided tail charge, |t| > 65536       | < 1.425e-19          |
+------------------------------------------+----------------------+
```

保留 published norms 的全部膨胀，没有扣除 point+panel 与 norms 的差额。
后续使用这些余量前，必须重建基础积分的分项证据以及求和舍入上界，说明
哪些旧系数变化费用可以替换。本次失败只冻结这一充分估计，不冻结修复路线。

3. 逐项预算推导

令 u=x/R，q=1-u^2，K=30。psi(u)=exp(-K/q) 在 |u|<1 定义，区间外取零。
函数及所有导数在两端趋于零，延拓光滑。S_k 是其第 k 阶导数的大小上界。
对 0<q<=1、K>=m，有 exp(-K/q)*q^(-m)<=exp(-K)，由此得到:

S0=exp(-30), S1=60 exp(-30), S2=3900 exp(-30), S3=272160 exp(-30).

写 g=-K/q，则 g'=-2Ku/q^2，g''=-2K/q^2-8Ku^2/q^3，
g'''=-24Ku/q^3-48Ku^3/q^4。使用 psi''=psi(g''+g'^2) 和
psi'''=psi(g'''+3g'g''+g'^3) 得到上述常数。自测另用整数多项式递推
验证常数，不重抄实现公式。

每项含调制因子 exp(i theta x)，theta 是真实存储调制数，没有额外添加
2*pi。导数必须计入 theta。设 d 为理想系数与存储系数差的复数模，
sigma 为指数权重参数，则该项系数修复费用是:

M0: d*2R*exp(|sigma|R)*S0
M1: d*2R*exp(|sigma|R)*(S1/R+|theta|S0)
M2: d*2R*exp(|sigma|R)*(S2/R^2+2|theta|S1/R+theta^2 S0)

几何转移令 r=min(R,Rold)，rmax=max(R,Rold)，dR=|R-Rold|，
其中 Rold 是浮点半径。对半径求导的三个大小上界是:

G0=S1/r, G1=(S1+S2)/r^2, G2=(2S2+S3)/r^3.

分别乘以 |stored coefficient|*dR*2rmax*exp(|sigma|rmax)，并加入调制项
G1+|theta|G0、G2+2|theta|G1+theta^2 G0，即得到几何费用。
旧权重与精确权重之间再乘 exp(|sigma-sigma_float|*Rmax)。

4. 从点态界到可积界

可积 (integrable) 意味着覆盖整个实数频率轴以后，总误差预算仍有限。
记录 2338 的常数点态界没有这一性质；这里增加二阶导数控制。

定义 Mk=integral exp(sigma*x)*|f^(k)(x)| dx。取步长 h=1/10，
从 f(x+h)-f(x)=h f'(x)+integral_0^h (h-u)f''(x+u)du 推出:

M1 <= (1+exp(|sigma|h))*M0/h + (h/2)*exp(|sigma|h)*M2.

原因是指数权重下平移范数的乘子为 exp(-sigma*u)，至多 exp(|sigma|h)。
在原始变换临界线 sigma=1/2，weighted_f=exp(x/2)f(x)，其二阶导数
大小积分至多 M2+M1+M0/4。两次分部积分无边界项，故因子或修复差的
变换上界为 min(E0,E2/t^2)，E0=M0，E2=M2+M1+M0/4，t 为原始虚部频率。

令 MB/MC 为旧精确半径源因子的上述上界，eB/eC 为纯系数修复上界。
H0=MB*MC 是旧产品大小上界，D=eB*MC+MB*eC+eB*eC 是产品变化上界。
平方变换的误差至多 D*(2H0+D)。

高频四个因子都按 t^-2 衰减，平方变化界为 A/t^8。A 由 tail_numerator
使用各 E2 上界计算。低频使用递减包络在分段左端的上界，绝非采样积分。
最后从 T=65536 到无穷大用解析积分，不用下溢或截断替代无穷尾。

t=-2*pi*xi，两侧都计费，所以 full_tail <= A/(7*pi*T^7)。
1/pi 包含正负两侧以及变量替换的 1/(2*pi)。

12 个自测覆盖调制项、半径舍入、正负两侧、极小非零尾项、哈希篡改和
已知解析积分对照。WSL 全量重放核查结果逐字段相同。

5. Next steps 与完成条件

1) 重建向上舍入的 point+panel 基础上界，证明旧膨胀费用中可替换部分，
   再计精确修复；保留旧 pin。完成条件是 101 节点通过，或者明确剩余义务。

2) 计完整核的权重。核 (kernel) 把各频率贡献加权汇总，无权误差 3.602
   不能直接代替其费用。保留 2336 组合支撑范围，覆盖完整素数账本与无穷尾。
   完成条件是完整核修复费用，不是窄范围重复定价。

3) 比较同一对象的有符号预算，判断修复是否可支付。P-only 余量与标记节点
   的两单位负值都不能替代。源零点和节点完整性仍是独立义务。

证据:
- scripts/routea_repair_norm_transfer_2339.py
- scripts/routea_repair_norm_transfer_selftest_2339.py
- results/2339_repair_norm_transfer.json
- build-logs/2339_repair_norm_transfer.log
- build-logs/2339_repair_norm_selftest.log
- results/2339_repair_norm_validation.json

No producer GO, no RH claim, no owner replacement.
