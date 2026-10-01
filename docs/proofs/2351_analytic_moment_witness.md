# 2351 - Actual analytic moment system and exact rational coefficient witness

日期：2026-10-01。

结果：本轮取得两项实际进展。第一，2338原解析矩阵的900个复区间和候选逆
已完整导出，独立纯有理数检查证明原60个复系数区间不需要扩大。第二，Lean
证明项目实际CompactLog函数的Laplace值正是该解析矩阵乘系数，在矩阵可逆的
显式前提下，精确系数存在且唯一。数值矩阵包围和可逆性尚未导入Lean；因此
本轮不是完整的具体系数实例化，也不声称producer GO或RH。

## 为什么这一步必要

系数（coefficient）是30个基本函数各自的权重。积分变换（Laplace transform）
把函数乘以exp(z*x)再积分，在指定z处读出一个复数。插值（interpolation）要求
这些读数等于指定值。矩阵（matrix）把30个节点与30个基本函数的900个积分
放在一张表里；矩阵乘系数就是组合函数在30个节点的读数。

小例子：一个基本函数在节点的积分是2，希望组合后的读数是3，权重就应是
3/2。真实问题有30个互相影响的权重，需要解A*c=y，而不能逐项相除。
这里A是解析积分矩阵，c是系数向量，y是指定节点值。

2338已用Arb的向外区间运算包围精确解，但结果只保存矩阵摘要，缺少逐项
可检查矩阵和候选逆。2351导出原始证据，避免后续把“残差很小”误当作
“系数一定正确”。残差（residual）是目标与当前矩阵读数之差；奇异矩阵也能
在某些目标上有零残差，所以残差不能单独证明解存在唯一。

```text
actual analytic family integrals
             |
             v
900 original complex rectangles + exact rational candidate inverse
             |
             v
Fraction-only checker: invertibility + original boxes invariant
             |
             +------------------ external certificate
             |
             v
Lean: actual CompactLog Laplace values = A * coefficients
             |
             v
Lean: unique exact coefficients, CONDITIONAL on actual det being a unit
             |
             v
OPEN: analytic enclosure/import -> discharge numeric invertibility premise
```

## 不改变2338计算的证据导出

新生成器调用未修改的2338计算路径，只拦截其900次矩阵积分以记录输出。
逐次检查行=节点、列=家族的调用顺序、宽度、频率、节点与16个积分面板。
父记录所有字段除elapsed_seconds外必须精确复现，任何差异都会拒绝导出。
候选逆X由同次矩阵计算得到，每项是没有半径的精确有理数点。

原矩阵、原系数区间、原捕获文件、节点目标、宽度平方、频率分别绑定：

- 导出的矩阵组件序列必须重建2338原matrix_entry_bounds_sha256。
- 系数区间必须逐项等于2338，禁止通过扩大区间获得通过。
- 节点、目标、宽度和频率从捕获的十六进制二进制数转成精确有理数。
- 纯有理数检查器不导入flint，不执行浮点运算，也不调用矩阵求逆求解器。

源码哈希和逐项相同只绑定数据来源，并不证明积分计算语义。这一边界仍保留。

证据：scripts/routea_moment_matrix_witness_2351.py、
results/2351_moment_matrix_witness.json、
scripts/routea_moment_matrix_exact_check_2351.py。

## 精确有理数的可逆性与系数区间检查

用有理数端点对复数的实部和虚部分别包围，所有加减乘运算精确执行。
对一个复数a+ib，检查器使用|a|+|b|作为大小上界，例如3+4i的实际模是5，
该上界是7。它更保守，但不需要开平方，且保留两个分量。

定义D = I-X*A，其中I是单位矩阵，X是候选逆，D是偏离单位矩阵的误差。
检查每行所有组件大小上界之和，eta是最大的行和。

eta < 1意味着X*A可由收敛几何级数求逆；在有限方阵上，它也保证A与X可逆。
本轮完全由有理数重算得到eta约为5.8731583073e-38。
该数字比2338使用复模的读数略大，因为检查器改用保守的实虚绝对值和。
它依然远低于1，但不把两个不同范数的读数冒称逐字节相同。

接下来验证原系数盒（coefficient box，给每个实部、虚部各一个闭区间）。
设m是盒中心，B是整盒，目标为y；对盒内c定义迭代

T(c) = m + X*(y-A*m) + D*(c-m)。

这等于c+X*(y-A*c)，其变化率受eta控制。检查器用区间算术证明T(B)包含于B。
盒是闭的，迭代是收缩（contraction，每次误差按小于1的比例缩小），所以
迭代留在盒内并收敛到唯一不动点。X可逆，因此不动点满足A*c=y。
这验证的是原完整盒，而不是只检查一个近似中心的残差。

```text
+-----------------------------+--------------------------+
| check                       | result                   |
+-----------------------------+--------------------------+
| actual matrix entries       | 900 complex rectangles   |
| candidate inverse entries   | 900 rational points      |
| channels                    | base + correction        |
| original components gated   | 120 / 120 contained      |
| eta                         | 5.8731583073e-38         |
| base max displacement/radius| 0.9999999438559326       |
| corr max displacement/radius| 0.9999999414312410       |
| coefficient boxes widened   | NO                       |
+-----------------------------+--------------------------+
```

最后两个比例接近1，不能描述成“大余量”：最紧组件只有约5.6e-8和5.9e-8
的相对半径余量。判定由精确有理数的不等式完成，不由表格小数或相对容差完成。
每个组件的精确上下余量都保存在结果里。

该检查是独立于Arb的代数引擎，不是独立的解析积分引擎。它仍依赖2337导出的
矩阵区间确实包围实际积分；这项解析语义和Lean导入尚未关闭。

## Lean中的实际函数绑定

momentFamily2351读取原externalFamilyValue2344，系数为1，半径为精确
storedWidth(index)^2；momentEntry2351定义实际全线加权积分，绝不定义成
外部小数。ownerMomentMatrix2351按节点与家族组装实际解析矩阵。

首先证明每个家族紧支撑（compact support，在一个有限闭区间外恒为零），
以及乘上exp(z*x)后的函数可积。再把有限求和与积分交换，证明

laplaceAt(correctedPhysicalCompactLogTest(coefficients,modulations), nodes[row])
= (ownerMomentMatrix2351(modulations,nodes) * coefficients)[row]。

因此不是给一个新矩阵模型编造成功结论；该矩阵确实读出原实际函数。
随后把精确解定义为实际解析矩阵的逆乘目标，并在hdet前提下证明插值与唯一性。
hdet表示实际矩阵行列式是可逆元素，在复数上等价于行列式非零。
它是数值导入必须消除的明确前提，尚未因外部有理数检查通过而自动消失。

证据：ConnesWeilRH/Dev/C1RouteAAnalyticMomentSystem.lean中的
correctedPhysical_laplaceAt_mulVec2351和
existsUnique_actualOwnerMomentCoefficients2351。

这使用标准有限维线性代数、积分线性性和收缩论证，不作原创性主张。
官方python-flint acb_mat文档用于确认原求解算法接口；固定Mathlib源码中的
Matrix.mulVec与nonsingular inverse定理用于Lean绑定。数值方程目标只规定节点
插值，不储存Weil正性、检测健康或RH结论。

## 验证与剩余范围

17项新测试通过，覆盖纯有理数复乘、负区间端点、十六进制精确解码、正常与
不确定矩阵、小型奇异矩阵、错误候选逆、错误系数盒、退化盒、维度缺失，以及
实际矩阵、系数、节点、目标、半径和频率的污染。独立命令重放逐字节相同。

最终Lean聚焦构建3716个任务，逐条公理检查见validation JSON和final日志。所有7条审计
定理均只依赖[propext, Classical.choice, Quot.sound]，没有新增数学公理。
不把开发期失败日志当作通过：初次构建修正实际Laplace命名空间及矩阵乘向量
重写方向，最后清理行宽警告及弃用的积分求和API，最终无新源码警告。
一次资源调度镜像锁等待超时发生在计算启动前；
原构建已确认终止后再重试，不重复启动仍在运行的任务。

本轮未改2338/2342/2349冻结输入及结果，没有重算120001条积分节点，也没有
新范数价格。数值矩阵积分包围、实际矩阵可逆性的Lean实例化、精确解属于原
系数盒的Lean导入、节点范数上界、选定检测函数健康和完整有符号预算仍未完成。

## Next steps

1. 把实际矩阵积分与导出的矩阵区间绑定并导入。解析包围（analytic enclosure）
   是证明积分真值位于区间内；它让纯有理数证据作用于Lean中的实际A。
   完成标准是900项积分的区间结论被可信检查，不只是矩阵摘要相同。

2. 形式化并实例化本轮收缩证据，消除hdet并证明实际精确解位于原系数盒。
   这样已有2350导数界和2342节点计算才共同作用于同一具体函数。
   完成标准是实际方程、存在唯一性、系数区间均接通，不用近似系数替代精确解。

3. 继续导入有限积分节点上界，再回到选定检测函数的完整有符号核预算。
   数值桥接闭合后应检查它究竟消除了哪项生产前提；完成标准是同一健康函数
   的符号账目闭合，并保留源零点、尾部与完整支撑，而不是继续收集外围证书。

证据：results/2351_moment_matrix_witness.json、
results/2351_moment_matrix_exact_check.json、
results/2351_analytic_moment_validation.json。
最终构建日志：build-logs/2351_analytic_moment_build_final.log。
