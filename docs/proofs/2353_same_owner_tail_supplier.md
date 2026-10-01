# 2353 - Same-owner uniform tail supplier by rectangle deformation

日期：2026-10-01。

结果：同一2338/2351修复基函数得到外部解析供应界：所有sigma属于[0,1]、
所有abs(t)>=128及两个频率方向，abs(B(sigma+i*t)) <= 2^(-14)。
实际向外上界约为1.7182037663e-16，远小于注册值1/16384。
没有更换系数、家族、节点或门槛。这个结论仍依赖实际精确系数属于原系数盒，
完整数值界尚未导入Lean；不是健康检测函数、完整谱尾部预算或RH结论。
Lean是逐条检查数学推理的形式验证系统；通过符号定理不等于数值前提已证明。
系数盒是每个系数的实部、虚部各自允许取值的闭区间。

## What this supplies

基函数（base）是随后重复卷积的第一个函数。系数（coefficient）是30个
基本函数各自的权重。积分变换（Laplace transform）把函数乘以exp(z*x)
后积分，得到复数读数B(z)。exp(x)=e^x，e约为2.718。

这里z=sigma+i*t，sigma是实部，t是虚部的角频率（angular frequency），
它控制积分中振荡的速度，i*i=-1。
这不是旧数值脚本的xi；旧约定t=-2*pi*xi不能漏掉换算系数。
模长（complex modulus）表示读数大小。尾部收缩（tail contraction）是
在全部高频范围把这个大小控制到q<1，让重复卷积的读数按q的幂缩小。

2352只证明T必须大于强制单位读数节点的最高高度79.337375...。
本轮在同一函数上给出足够条件T=128、q=2^(-14)。它不迁移另一函数的
T=28结论，也不证明任意rho或任意系数都满足同一数值界。

## Point controls are not the supplier

同次计算用256位Arb（实数区间引擎）/Acb（复数区间引擎）积分，读取
sigma=0、1/2、1及t=+128、-128。256位是运算精度，不是采样点数。
六个基函数模长上界均很小，最大读数约4.9733e-20。捕获rho处的基函数
和校正函数读数区间都包含规定值1。

区间算术（interval arithmetic）同时保留每次运算的上下界，让真值被包住。
这些有限点可以反驳一个错误的全带上界，却不能认证未读取的sigma、t。
本轮的全带结论来自下面的解析界，而不是采样点通过。

```text
directed point integrals ------------> controls only

actual analytic family + Cauchy rectangle identity
                         |
                         v
top path + both connectors + BOTH omitted real edges
                         |
                         v
interval sup on every connector cell
                         |
                         v
all sigma in [0,1], both signs, all abs(t)>=128
```

## Initial integration-by-parts price

分部积分（integration by parts）把指数积分中的频率移到分母，用函数导数
控制高频读数。2350已证明实际平滑凸起函数的0到4阶导数界，常数为
[1,60,3720,236160,15130080]。支撑外和两端导数为零，因此没有边界项。

对半径R、调制theta、系数a，角频率是t+theta。R是精确存储宽度平方，
theta是该家族的原角频率，a的模长使用原系数盒的向外区间。
调制（modulation）是乘以exp(i*theta*x)：改变实轴上的转动速度，
但不改变大小，所以能把它合并进积分的频率。
第k阶积分上界为E_k=2R*exp(R)*abs(a)*exp(-30)*A_k/R^k。
A_k是上述导数常数；这里使用k=0、2、4。

若Delta=T-abs(theta)>0，则这一家族的尾部界不超过
min(E_0,E_2/Delta^2,E_4/Delta^4)。不分离载频时退回E_0，不除以零。
所有家族相加后，注册q=1/2的第一档认证起点是512，不是128。

```text
+-----------------------+--------------------+---------------------+
| supplier method       | T                  | base upper          |
+-----------------------+--------------------+---------------------+
| IBP orders 0/2/4      | 128                | 38.39189065...      |
| IBP orders 0/2/4      | 256                | 0.76475735...       |
| IBP orders 0/2/4      | 512                | 0.03265695...       |
| rectangle, delta=1/64 | 128                | 0.0012976443...     |
| rectangle, delta=1/8  | 128                | 1.7182037663e-16    |
+-----------------------+--------------------+---------------------+
```

前三行是充分上界，不是实际值。第一行超过1不证明函数不能收缩。
IBP是integration by parts，即前面解释的分部积分。
两个矩形方法和前三行都在同次运行计算；不是跨记录拼接的收益。

## Rectangle proof and exact geometry

积分路径变形（contour deformation）把实轴积分移到复平面中的平行线。
柯西定理（Cauchy's theorem）说：函数在矩形内没有奇点时，四条边的
积分和为零，所以原积分可以由顶边和两条连接边恢复；连接边不能丢掉。

令u=x/R为归一化坐标，w=u+i*v为复路径坐标；源节点z仍为sigma+i*t。
内区间是[-c,c]，c=1-delta。
对omega=t+theta选择与omega同号的路径高度d=1/2，产生指数衰减。
实际复积分函数为exp(-30/(1-w^2)+R*(sigma+i*omega)*w)。
矩形满足abs(Re(w))<=c<1，故不包含仅有的分母零点+1、-1。

```text
          -c + i*d ----------------------- c + i*d
              |          top                 |
              |                              |
           connector                     connector
              |                              |
             -c ----------------------------- c
                        real integral

negative omega: use the reflected rectangle below the real axis
real slices [-1,-c] and [c,1] are bounded separately, NOT dropped
```

顶边使用abs(exp(-30/(1-w^2)))<=1。它的界为
2cR*exp(Rc-R*Delta*d)。

连接边取w=+c+i*v或-c+i*v，0<=v<=d。设A=1-c^2+v^2，
D=A^2+4c^2*v^2，则Re(1/(1-w^2))=A/D。连接边共同的衰减因子是
E(v)=exp(-30*A/D-R*Delta*v)。两侧实指数权重的共同上界为exp(Rc)+1。
把[0,d]切成64个精确有理数单元，用区间输入包围每个单元的全部E(v)，
再累加单元长度乘上界。这是整个单元的包围，不是中点积分规则。

两片被省略的实边缘，使用原实际凸起函数在支撑端点为零的定义，界为
2*delta*R*exp(-30/(delta*(2-delta))+R)。它在Arb中保持正值，
不通过浮点下溢置零，也不在w=+1、-1处代入复有理扩展公式。

每项先乘系数模长上界，再相加。两个有效矩形界逐家族取最小值，
不扩大系数盒。delta改变的是积分分割，不是实际函数支撑或素数账本。
直接点积分仍沿用2337的delta=1/64；尾部供应者使用delta=1/8。

新矩形的基函数预算分项约为：顶边2.03034e-18、连接边1.69790e-16、
实边缘4.06539e-40。三项都是界，没有测量项充当无穷尾部证书。

## Lean binding and consumer scope

新模块C1RouteAContourTail证明四项实际连接：
复积分函数在abs(Re(z))<1内复可微；实际指数模长等于算法使用的实公式；
原家族的实轴加权值等于这个复积分函数；矩形四边积分恒等式对正负高度
均成立。审计不引入新公理。聚合数值界与实际系数盒的导入仍未完成。

另保留全线角频率常数D4、D2，满足abs(t)^4*abs(B)<=D4和
abs(t)^2*abs(C)<=D2，C是校正函数的积分变换。低频用E_0，高频用
abs(t+theta)>=abs(t)/2，每项取max((2*abs(theta))^k*E_0,2^k*E_k)。
转换为既有消费者时C4=D4/(2*pi)^4，C2=D2/(2*pi)^2；
(2*pi)^12*(C4*C2)^2恰等于(D4*D2)^2，不引入近似pi常数。

实际源H=B^(n+1)*C可以组合这些供应界；n是卷积迭代索引，不是高度壳层N。
但q通过不等于消费者的最终尾部预算通过。只有接到同一n、门槛系数、
完整零点前缀及实际接受不等式，才可能成为健康检测函数。
q也不能单独作为常数上界在全频率积分；仍需使用衰减常数。

T=128仍要求至少高度壳层N=6，不是分部积分方法T=512所需的N=8。
这里仅说明供应参数的必要壳层，不声称完整谱尾部已经闭合。
所需零点列表完整性、捕获rho的源零点身份、完整组合支撑的有符号核预算
均未证明；map103不因此重新开启。producer GO和RH均不声称。

## Evidence and next steps

源码：scripts/routea_same_owner_tail_supplier_2353.py及其selftest；
ConnesWeilRH/Dev/C1RouteAContourTail.lean及其Audit模块。
数据：results/2353_same_owner_tail_supplier.json、
results/2353_same_owner_tail_precision384.json及
results/2353_same_owner_tail_validation.json。

最终验证：聚焦构建3716个计划任务通过，四个审计叶子仅依赖
propext、Classical.choice、Quot.sound，没有新源码警告。
六组测试合计86项通过。384位精度控制保留注册q，七点、两通道、
实部和虚部共28个区间分量全部相交；所有源文件与输入哈希已复核。
精度重放仍是同一个引擎，不称为独立解析证明。
另一次Linux镜像命令重放与主工件逐字节一致；旧/tmp回放文件已不存在，
因此这个结论来自新命令的实际重放，不依赖旧临时文件仍然存在。
Mathlib来源为固定v4.30的Analysis/Complex/CauchyIntegral.lean，
integral_boundary_rect_eq_zero_of_differentiableOn，不作原创性主张。

1. 把本轮q、D4、D2接到当前同一源的接受不等式，保持门槛系数随owner变化。
   完成标准是具体尾部预算与实际门槛行同时通过，不是q很小。

2. 核对该壳层要求的全部零点消去条件。完成标准是参数化构造或真实前缀
   证明；30个浮点捕获节点不能冒充完整源零点集合。

3. 对可行对象继续导入实际积分矩阵、系数盒和数值供应界。完成标准是
   Lean消除相关数值前提，不增加公理，也不把本轮外部界改名为形式化数字。
