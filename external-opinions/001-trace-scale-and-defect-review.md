# 第一份外部意见：Trace-scale、Defect、S(g) 问题

日期：2026-06-28

状态：本地外部意见记录。该目录已加入 `.gitignore`，不作为公开仓库材料。

## 结论

这份外部意见命中当前路线的核心风险。

当前 README 已经承认路线不是 RH 证明：

```text
accepted-source certification: open
external referee certification: open
Lean proof status: open
public proof status: source-conditional
```

但这份意见进一步指出：即使只按 source-conditional 路线看，Step 2 到
Step 5 之间仍可能存在迹量纲不匹配。这个问题比泛泛批评
“没有证明 RH”更具体，应该作为下一轮攻关的第一 blocker。

## 四个待解决问题

| 编号 | 问题 | 当前判断 | 优先级 |
|---|---|---|---|
| B1 | 正迹 `Tr(A^*A)` 的极限尺度是否和 `QW_lambda + ledgers + Cdef` 匹配 | 未解决；必须新增 trace-scale compatibility 审计 | P0 |
| B2 | 若改用 Sonin 投影，极限是否平凡化 | 不是当前路线定义，但堵住一个自然修补方向 | P2 |
| B3 | 半局部 `Y_S` 是否存在 rank/pole/Cdef 之外的第四正缺陷 | 当前只有 route-evidence；需要外部或更强本地审计 | P0 |
| B4 | 动态选择 `S(g)` 是否破坏 CC20 全称量词或全局对象一致性 | 需要精确定式；不一定要求 uniform in `g`，但必须证明每个 `g` 投回同一个 global `QW` | P1 |

## B1：Trace-scale Compatibility

当前 README 使用：

```text
A_(S,lambda,g)
  =
P_hat_(S,G)(lambda) P_(S,G)(lambda) theta_S(g)
```

并声明：

```text
PositiveTrace^G_(S,lambda)(g)
  =
Tr(A_(S,lambda,g)^* A_(S,lambda,g))
  >= 0
```

随后路线需要：

```text
PositiveTrace
  =
QW_lambda(g,g)
+ Rank
+ PoleJetExtra
+ R
```

三重点消去后：

```text
PositiveTrace
  =
QW_lambda(g,g) + R
```

再用：

```text
QW_lambda(g,g) = QW(g,g)
R -> 0
```

如果 `PositiveTrace` 是普通未重整化迹，则外部意见指出它可能随
`lambda -> infinity` 发散，而右侧趋向有限数 `QW(g,g)`。这会造成：

```text
LHS -> infinity
RHS -> finite value
```

因此必须补出一个明确审计：

```text
TraceScaleCompatibility(S,I,lambda,g):
  ordinary positive trace,
  finite-part trace,
  source support-square trace,
  QW_lambda read-off,
  and Cdef remainder
  all refer to the same normalized scalar quantity.
```

审计必须回答：

1. `PositiveTrace` 是普通迹、有限部迹、还是已经减去 bulk 的迹？

2. 如果是普通迹，为什么不发散？

3. 如果是有限部迹，非负性 `Tr(A^*A) >= 0` 是否仍然适用？

4. read-off 等式是否缺一个 divergent bulk ledger？

5. `Cdef -> 0` 控制的是全余项，还是只控制 endpoint-strip 余项？

## B2：Sonin 投影修补方向

外部意见指出，若把正迹改成 Sonin 投影：

```text
S_lambda theta_S(g)
```

则 `S_lambda -> 0` 可能导致正迹极限变成 0，进而错误推出
`QW(g,g)=0`。

当前路线没有采用这个定义，所以 B2 不是当前 README 的直接漏洞。

但它说明不能用一句“改成 Sonin 空间压缩”来逃避 B1。任何替代正迹都必须先证明：

```text
positive scalar has the same asymptotic scale as QW_lambda.
```

## B3：第四正缺陷

README 自己把问题写成外部 review target：

```text
Does the Rows 1-7 chain classify every CC20 post-Q remainder term as killed
rank/pole ledger or endpoint-strip Cdef?
```

外部意见把风险说得更尖锐：

```text
semilocal place coupling may create cross-terms
outside local endpoint-strip Cdef.
```

当前状态：

```text
Rows 1-7 route-evidence proof package exists.
accepted-source/external certification remains open.
```

下一步不能再写“无第四缺陷”结论。要改成逐项审计：

```text
NoFourthPositiveDefectAudit:
  list every term produced by semilocal transport,
  tag it as rank, pole, endpoint-strip Cdef, or unresolved cross-term.
```

如果出现 unresolved cross-term，路线停在这里。

## B4：动态 S(g) 与全称量词

当前 route condition 是：

```text
S contains every finite prime visible to F_g.
```

外部意见说 `S=S(g)` 可能破坏全称量词。

更精确的判断：

```text
CC20 需要对每个 g 证明 global Weil inequality。
这不必要求一个统一的 S 对所有 g 有效。
但每个 g 的 S(g)-local construction 必须回到同一个 global QW(g,g)
和同一个 CC20 local Weil sum。
```

因此 B4 的待证目标不是简单的 uniform bound in `g`，而是：

```text
SLocalToGlobalQuantifierAudit:
  for every admissible g,
  choosing S(g) does not change the target scalar QW(g,g),
  does not omit finite-prime atoms,
  does not double-count finite-prime atoms,
  and gives the exact CC20 sum_v W_v(F_g).
```

## 接下来怎么打

### 第一阶段：先打 B1，不打别的

原因：

```text
如果 PositiveTrace 的尺度不对，
后面的 defect、S(g)、final sign 都没有意义。
```

行动：

1. 新增公开审计文件：

```text
docs/audits/trace-scale-compatibility-audit.md
```

2. 在 README Review Checklist 加第一行：

```text
Trace-scale compatibility:
Does the ordinary positive trace have the same scalar normalization and
lambda-asymptotic scale as QW_lambda + ledgers + Cdef?
```

3. 搜索现有 proof package 中所有 `PositiveTrace`、`Tr(A^*A)`、
   `support-square trace`、`no-defect trace`、`finite part`、`Cdef` 的定义。

4. 做一个表：

```text
object | source | finite lambda meaning | lambda limit | positivity available?
```

5. 若找不到有限部/重整化说明，则公开承认：

```text
Trace-scale compatibility is unresolved.
```

### 第二阶段：再打 B3

原因：

```text
B3 是 sign/defect 桥的核心。
B1 没过之前，B3 即使过了也不能推出 QW >= 0。
```

行动：

1. 建立 semilocal term ledger。

2. 把 Rows 1-7 每个 term 和 source line 对齐。

3. 对每个 term 强制分类：

```text
rank
pole
endpoint-strip Cdef
unresolved cross-term
```

4. 任何 unresolved cross-term 都变成 blocker。

### 第三阶段：打 B4

原因：

```text
B4 关系到是否能从 fixed-test 结论喂给 CC20 的 forall g。
```

行动：

1. 明确 CC20 Proposition C.1 的量词。

2. 明确路线对每个 `g` 选择 `S_A(g)` 的规则。

3. 证明或否定：

```text
S_A(g)-local QW read-off = global QW(g,g)
```

4. 不追求不必要的 uniform in `g`，除非 CC20 条件或某一步极限真的要求。

### 第四阶段：只在 B1/B3/B4 过后再碰 final sign

final sign bridge 只有在前面给出真正的 `QW(g,g)>=0` 后才有意义。

当前顺序：

```text
B1 trace scale
  -> B3 no fourth defect
  -> B4 S(g) quantifier
  -> final sign
  -> external accepted-source review
  -> Lean
```

## 当前战术判断

最可能出问题的是 B1。

如果 B1 失败，路线应停止在：

```text
positive trace read-off not scale-compatible with QW_lambda.
```

如果 B1 通过，再审 B3。

如果 B3 失败，路线应停止在：

```text
hidden semilocal defect not classified by rank/pole/Cdef.
```

如果 B1 和 B3 都通过，再审 B4。

只有 B1、B3、B4 都通过，才值得把 final sign bridge 和 CC20 exit
送外部 reviewer 做 accepted-source 判定。
