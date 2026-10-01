2354 - Same-source conditional scalar tail acceptance lanes

日期：2026-10-01。

结果：同一2353外部解析供应界能够容纳更强的有理数q=2^-52。
在实际源H=B^(n+1)C不变、壳层N=6不变的前提下，得到两条条件接受路线：
n=2且lambda>=256，或n=3且lambda>=1e-13。
这只是完整尾部接受公式的标量预算通过，不是实际闸门通过。
没有换函数、重解系数、枚举素数、扫描闸门或重开map103。

What is being priced

积分变换（Laplace transform）把物理函数乘上exp(z*x)后积分。
基函数的读数记为B，校正函数的读数记为C；卷积（convolution）是在不同
位置组合两个函数，在这里对应变换读数相乘。n是卷积迭代索引，所以
H=B^(n+1)C；它不是壳层索引N，后者表示高度按2的幂分组的范围。

q是全部高频上的B读数大小上界。2353证明的外部解析上界约为
1.718203766281698e-16，小于2^-52，且大于2^-53。
因此2^-52是能包住这一供应界的最小二进制幂上界。
这里是重新读取同一个严格上界，没有重新取样，更没有修改函数。

lambda是四点线性组合（span）的系数：v=u-lambda*g，其中g是实际
选中函数，u是其四点消去函数（annihilator），用于把指定点读数清零。
它必须来自同一对象的实际闸门；256只是接受区间的端点，不能当成闸门
已经选出的系数。两条路线覆盖端点以上的全部正lambda，不是固定系数分支。

How the full formula is retained

rho是捕获的复坐标，尚未证明是源的非平凡零点。
R是rho的模长上界，不是函数支撑半径；本轮以
abs(Re rho)+abs(Im rho)<=41给出R=41。
D4、D2分别控制abs(t)^4*abs(B)和abs(t)^2*abs(C)。
两个向外整数上界是746785658244和71280628476。
K控制高度壳层中的带重数零点数量；重数（multiplicity）是一个零点
重复出现的次数。K<=128.65已由C1RouteAMultiplicityBound证明，
这里不沿用更大的旧数值代理，也不改变xi归一化。

令L=(3+R)^4，A=L*(L+lambda)^2*(q^n*D4*D2)^2。
现有四阶谱尾部（fourth-order spectral tail）接口要求A<epsilon^2。
epsilon是允许尾部大小的参数。取epsilon^2=(3/2)*A保留严格余量，
再把现有消费者的4*epsilon^2*K*(3/4)^N与前缀负值m*lambda^2比较。
m是标记零点重数，预算先按m>=1读取。

因此需要的无量纲比值是：

ratio=(3/2)*4*K*(3/4)^N*L*(1+L/lambda)^2*(q^n*D4*D2)^2/m

ratio<1只是足够条件。大于1表示这个预算不够，不证明实际尾部失败。
lambda保留在尾部和前缀两侧；没有冻结它或删除其影响。
对lambda>0，lambda增加使L/lambda减小，所以ratio不会增加。
Lean证明这个单调性（monotonicity），即端点通过后端点以上也通过。

角频率（angular frequency）t不是旧脚本的xi；C4=D4/(2*pi)^4、
C2=D2/(2*pi)^2。Lean验证全部pi因子严格抵消：
(2*pi)^12*(q^n*C4*C2)^2=(q^n*D4*D2)^2。
这里没有使用浮点pi，也没有附加P-only乘子。

```text
+------------+-----+--------------------+--------------------+------------------+
| q          | n   | lambda condition   | scalar ratio       | scope            |
+------------+-----+--------------------+--------------------+------------------+
| 2^-14      | 8   | lambda = 1 control | 0.7602858719594    | conditional only |
| 2^-52      | 2   | lambda >= 256      | <= 0.7603893268553 | conditional only |
| 2^-52      | 3   | lambda >= 1e-13    | <= 0.2456614834776 | conditional only |
+------------+-----+--------------------+--------------------+------------------+
```

第一行只是旧q的同次计算控制，不是新的固定lambda闸门路线。
例如q=2^-52、n=2但lambda=1时，ratio约为4.9826e4，不能省略系数条件。

Composed support and the next bottleneck

支撑（support）是函数可能不为零的区域。设实际家族最大支撑半径为r，
实际源半径上界为(n+2)*r，卷积平方半径上界为2*(n+2)*r。
这里r约为6.5536，n=2、3、8的平方半径上界分别约为52.4288、65.536、
131.072。减小n确实缩小后续核积分和可见素数的覆盖范围；它不证明
覆盖内每一项非零，也没有枚举该覆盖范围内的素数。

```text
same analytic supplier, unchanged coefficients
                    |
               q <= 2^-52
                    |
     +--------------+---------------+
     |                              |
 n=2, lambda>=256            n=3, lambda>=1e-13
     |                              |
     +--------------+---------------+
                    |
         scalar acceptance envelope only
                    |
         actual same-owner gate coefficient [OPEN]
         complete actual zero prefix        [OPEN]
         source-zero identity               [OPEN]
         numeric Lean import                [OPEN]
                    |
             healthy detector NOT supplied
```

前缀（prefix）是高频尾部之前必须控制的实际零点集合。
消费者需要sourceNontrivialZerosInClosedBallFinset rho
(2^(N+1)+2+dist(2,rho))与routeNodes的并集；30个捕获节点不是其完整证明。
如果为了补齐前缀而修改系数或函数，必须重新证明供应界与闸门，不能
把本轮常数移到新对象上。

Verification and limits

五个Lean审计叶子验证pi归一化、与系数缩放预算的等式、lambda单调性、
两条接受区间。它们不导入外部积分、系数盒或rho的源零点身份。
18项新测试检查参数边界、系数不能丢弃、迭代平方因子、壳层因子、
保留严格余量、同一来源哈希、支撑组合与条件结果的范围。
精确矩阵见证在本次运行重新检查，所有价格用Fraction有理数算术读取。
最终聚焦构建3569个计划任务通过，五个审计叶子仅依赖
propext、Classical.choice、Quot.sound，没有新源码警告。
独立命令重放逐字节一致；Linux镜像与Windows两份Lean源码一致，
全部源文件和输入哈希匹配最终字节。
完整重放、构建与哈希证据见results/2354_same_owner_tail_acceptance_validation.json。

首次导入完整尾部消费者的构建未通过：
C1HealthyYoshidaSpectralNegativity.lean第371行的Finset.sum_sdiff重写，
以及第385行的spectralHeightShellSum_split重写均找不到目标形式。
该文件在Windows和Linux镜像字节一致，并未被本轮修改。
纯算术模块不需要这个依赖，所以移除了冗余导入；失败日志仍保留在
build-logs/2354_acceptance_build.log。聚焦算术构建通过不能覆盖这个
消费者集成失败，也不等于端到端证明通过。

Evidence

scripts/routea_same_owner_tail_acceptance_2354.py及其selftest。
ConnesWeilRH/Dev/C1RouteATailAcceptance.lean及其Audit模块。
results/2354_same_owner_tail_acceptance.json及其validation记录。
原接受接口：C1FourPointHighShellTail.selectedOwner_fullOrbit_span_fourthOrderSpectralTail_of_q，
以及C1FourPointContradictionAssembly.qw_neg_of_spectralHeightShellPrefix_and_fourthOrderTail_scaled。

Next steps

1. 修复并单独验证原消费者的两处重写兼容问题。保持原定理陈述与数学
   假设不变；完成标准是消费者实际构建和公理审计通过，而非算术模块通过。

2. 明确当前对象能否控制全部所需实际零点前缀。补齐身份与完整性证明，
   或提供同一对象上的参数化构造；完成标准是消费者的前缀前提真正可用。
   若必须换对象，本轮供应界重新计算，不能继承。

3. 先在同一n与完整支撑上证明有符号物理核闸门，再读取它实际给出的
   lambda是否落在接受区间。完成标准是闸门、尾部与前缀来自同一对象；
   无关对象的小lambda、负对角或已通过行都不能移借。
