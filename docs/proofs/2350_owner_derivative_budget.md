# 2350 - Actual owner derivative ladder in Lean

日期：2026-10-01。

结果：本轮取得实质证明进展。2349在外部推导的零到四阶导数常数，
现在已通过Lean接到项目实际的widthBump、带振荡项的家族，以及30项
correctedPhysical定义。两个面板积分定理不再把导数界作为外部假设。
这不是新的数值降价，也不是RH证明。

## 本轮关闭的缺口

导数（derivative）表示函数怎样变化：一阶描述坡度，二阶描述坡度怎样变化。
反复求导得到三阶、四阶。导数上界（derivative majorant）是对整个区间有效的
天花板，而不是少数采样点的读数；就像证明整条路的最大坡度，而不是每隔一段
拍照后推断路面没有陡坡。

2349已经证明指数包络（exponential envelope）：指数衰减足以抵消支撑边缘
分母变小带来的幂次增长。但候选多项式还没有被证明是实际函数的导数。
2350补上这个连接，并把实际导数界直接交给2348面板定理。

```text
actual widthBump
      |
      +--> interior derivative recurrence + coefficient-sum ceilings
      |
      +--> exterior zero + continuity at BOTH edges
      |
      v
orders 0..4 globally bounded
      |
      v
complex oscillatory families --> actual 30-term correctedPhysical
      |
      v
2348 panel consumers: derivative hypotheses removed
      |
      v
STILL OPEN: actual numeric coefficients + finite node import + signed budget
```

## 从实际bump开始的证明

设R > 0为支撑半径，x为位置，u = x/R为归一化位置，q = 1-u^2。
当|x| < R时q > 0。n表示求导次数，P_n表示导数分子多项式。
项目的实际定义是区间内exp(-30/q)、区间外和两端为零。

内部公式：

widthBump^(n)(R,x) = exp(-30/q) q^(-2n) P_n(u) / R^n。

分子递推：

P_(n+1) = q^2 P_n' + (-60u + 4nuq) P_n。

这里P_n'是分子多项式的一阶导数。第一项来自分子求导，-60u项来自指数求导，
4nuq项来自分母幂次求导。Lean直接证明每一项，再证明n = 0..3的递推，
因此覆盖实际函数的n = 0..4导数；不是把该公式作为输入假设。

边界（support boundary）是|x| = R的位置。这里不能代入内部公式，因为q = 0。
证明先利用支撑外邻域中的函数恒为零，得到所有阶导数为零；然后利用项目已有
光滑性（smoothness，任意阶导数都存在且连续），把零值延伸到左右两个边界。
全线公式保留分支保护，不在边界计算奇异表达式。

C_n是P_n所有系数绝对值的和。对|u| <= 1，|P_n(u)| <= C_n。
利用2349的指数包络，Lean得到以下全线统一界：

|widthBump^(n)(R,x)| <= C_n exp(-30) / R^n，n <= 4。

```text
+-------+------------+
| order | C_n        |
+-------+------------+
| 0     |          1 |
| 1     |         60 |
| 2     |       3720 |
| 3     |     236160 |
| 4     |   15130080 |
+-------+------------+
```

小例子：R = 1、x = 0时，实际二阶导数是-60 exp(-30)，其绝对值小于
3720 exp(-30)。统一界允许宽松，但必须处处有效。n <= 4的条件始终显式保留；
辅助定义在更高阶的默认分支不是更高阶定理。

证据：ConnesWeilRH/Dev/C1RouteABumpDerivativeLadder.lean中的
widthBump_iteratedDeriv_global2350和widthBump_iteratedDeriv_abs_le2350。

## 接到带振荡项的实际30项函数

每一项是c exp(i theta x) widthBump(R,x)。c是复系数，theta是实振荡频率，
i是虚数单位。复数模（complex modulus）表示复数的大小，例如3+4i的模是5。
纯振荡exp(i theta x)的模是1；其第j阶导数的模是|theta|^j。

乘积求导法则（Leibniz rule）会列出“对振荡项求导j次、对bump求导n-j次”
的所有分配。choose(n,j)是该分配出现的次数。由实际导数公式，得到单项界：

B_n(c,theta,R) = |c| sum_(j=0..n) choose(n,j) |theta|^j
                C_(n-j) exp(-30) / R^(n-j)。

对30项分别求和，定义M_n = sum_family B_n。Lean证明：

|correctedPhysical^(n)(x)| <= M_n，n <= 4。

这覆盖全部位置，包括每个家族自己的左右边界；各家族半径始终是对应的精确
storedWidth(index)^2。定理对任意系数和频率成立，没有更换函数定义，没有冻结
某个频率，也没有把实际系数解的正确性偷偷作为已证明结论。

这一步采用标准乘积求导、复数模三角不等式和连续性，不作原创性主张。
Mathlib的iteratedDeriv_fun_mul与iteratedDeriv_fun_sum负责有限乘积和求和链；
使用的是项目固定的Lean/Mathlib v4.30环境。

证据：ConnesWeilRH/Dev/C1RouteAOwnerDerivativeBudget.lean中的
externalFamilyValue2344_iteratedDeriv_budget2350和
correctedPhysical_iteratedDeriv_budget2350。

## 对积分消费者的实际改变

面板（panel）是相邻两个积分节点之间的小区间。2348已经证明：若节点上界
有效，再支付由二阶导数界确定的区间费用，就能控制整个连续积分。
2350的两个专用定理直接提供所需导数界：

- stripNorm使用M_0、M_1、M_2。
- stripSecondNorm使用M_2、M_3、M_4。

因此两个消费者各自的三项导数界假设被定理消除。它们仍要求节点上界有效、
步长严格为正，以及cells*step = 2*storedWidth(4)^2的精确网格关系。
没有把整段积分结论重新存成一个输入字段。

范数（norm）只回答函数大小；有符号预算（signed budget）回答保留正负贡献
后的表达式是否非负。前者好比重量，后者好比方向，不能互相替代。

```text
+-------------------------------------+-------------------------------+
| obligation                          | status                        |
+-------------------------------------+-------------------------------+
| bump derivative identities 0..4     | proved in Lean                |
| both support edges and exterior     | proved in Lean                |
| concrete C_n coefficient ceilings   | proved in Lean                |
| symbolic 30-family owner bounds     | proved in Lean                |
| derivative premises of panel rules  | discharged in Lean            |
| numeric repaired coefficients       | NOT instantiated              |
| finite directed node certificate    | NOT imported                  |
| selected healthy detector           | NOT instantiated              |
| full signed-kernel producer budget  | OPEN                          |
| RH claim                            | NO                            |
+-------------------------------------+-------------------------------+
```

## 验证

最终Linux聚焦构建完成3716个构建计划任务。两个审计模块共21条定理，
逐条公理回读均为[propext, Classical.choice, Quot.sound]，没有sorryAx。
这三项是项目允许的逻辑基础，不是额外假设RH或正性。四个新Lean文件没有
新源码警告，Windows与Linux镜像逐字节相同。

12项2349回归测试和15项2342回归测试通过；它们检查原外部数值链没有漂移，
不是新Lean证明的替代品。本轮没有重新评估120001节点，也没有修改2349的
历史数值或历史范围标志。1808469.1730280858仍是2349的外部数值上界，
不能因为本轮导数证明通过就称其已导入Lean。

开发期构建先发现两类接口匹配问题：自然数阶数与无限光滑度的比较，以及隐式
位置参数的归纳假设。另一次构建发现实数嵌入复数的光滑性不能靠自动搜索找到。
均通过显式类型转换、明确位置参数和现有连续线性嵌入定理解决，没有增加证明
心跳预算、放松数学前提或禁用检查。最后一条行宽警告也已修复并重建。

证据：results/2350_owner_derivative_budget_validation.json。
日志：build-logs/2350_owner_derivative_budget_build_clean.log、
build-logs/2350_derivative_ladder_regression.log、
build-logs/2350_direct_ideal_regression.log。

## Next steps

1. 把2338精确修复系数解接到当前任意系数的定理。系数实现
   （coefficient realization）是证明这些具体系数确实满足实际矩阵方程。
   它让外部计算和Lean讨论同一个具体函数；完成标准是精确方程与可逆性都被
   消费，而不是只有相近的小数或一致的哈希。

2. 证明外部计算公式的含义并导入有限节点上界。计算语义（evaluator semantics）
   是证明程序算的表达式就是Lean中的实际函数。完成标准是八个端点通道的
   节点求和、向外舍入和精确网格关系被核查，从而真正实例化连续积分上界。
   现有余量足够支持这项工作，暂不需要继续细化网格。

3. 把实例化后的范数界交回选定检测函数的全支撑有符号核预算。检测函数
   （detector）是被选来检查潜在RH反例的具体测试函数；核（kernel）给各处
   贡献附上权重。完成标准是同一健康检测函数的正负贡献账目闭合，且其来源
   零点与尾部条件全部保留；不能以无符号范数改善代替这一步。
