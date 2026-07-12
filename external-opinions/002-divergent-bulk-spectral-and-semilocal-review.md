# 第二份外部意见：Divergent Bulk、谱污染、偶扇区、S(g) 非一致性

日期：2026-06-28

状态：本地外部意见记录。该目录已加入 `.gitignore`，不作为公开仓库材料。

## 总判断

第二份意见比第一份更尖锐。它没有停在“尚未证明 RH”这种总评，而是把攻击集中在四个可审查点：

```text
S2-B1: divergent bulk / trace-scale incompatibility
S2-B2: finite-operator spectral pollution and domain mismatch
S2-B3: even-sector spectral assumption in the CCM25 spectral route
S2-B4: semilocal fourth defect and non-uniform S(g)
```

当前项目的正确回应不是宣称这些问题已经被数学界接受解决，而是把它们分成两类：

```text
direct route attacks:
  S2-B1 divergent bulk
  S2-B4 semilocal fourth defect / S(g)

attacks on a route not imported here:
  S2-B2 finite-operator spectral convergence
  S2-B3 even-sector spectral assumption
```

S2-B1 是最危险的点。若 reviewer 能在 CC20/CCM25 源公式中找到一个

```text
BulkScaleTerm_(S,I,lambda,g)
  ~ C log(lambda) ||g||^2
```

且它不属于 `QW_lambda`、rank、pole、endpoint-strip `Cdef` 中的任何一类，路线必须停止在 positive-trace read-off。

## S2-B1：Divergent Bulk

外部意见的攻击模型是：

```text
Tr(A^*A)
  =
Bulk_(S,lambda)(g,g)
+ QW_lambda(g,g)
+ Rank
+ Pole
+ R_lambda

Bulk_(S,lambda)(g,g)
  ~ C log(lambda) ||g||^2
```

若该模型对应源公式中的真实项，则普通迹非负性只给出：

```text
QW_lambda(g,g) >= -Bulk_(S,lambda)(g,g) + lower order terms.
```

这不能推出 `QW(g,g) >= 0`。

项目目前已有回应：

```text
docs/proofs/trace-scale-compatibility-proof-package.md
```

该文件只在 route-evidence / project proof-package 层声明：

```text
PositiveTrace
  =
QW_lambda + Rank + Pole + CdefRemainder
```

并声明没有未命名的 bulk-scale 项。

当前判断：

```text
S2-B1 is answered only at project proof-package level.
accepted-source certification remains open.
Lean status remains open.
```

第三轮攻击最可能继续打这里。

## S2-B2：Spectral Pollution

第二份意见说有限维截断算子的正性不能推出无限维 Weil 形式正性。这是泛函分析中的真实危险。

但当前路线公开说不导入：

```text
CCM25 finite-operator spectral convergence
determinant convergence toward Xi
finite-dimensional eigenvalue convergence to zeta zeros
```

当前路线声称使用的是 fixed-test scalar restriction bridge：

```text
QW_lambda(g,g) = QW(g,g)
```

该桥不是谱极限。它依赖 CCM25 中 `QW_lambda` 是 `QW` 在限制区间上的 restriction，以及同一固定测试函数的支撑已经落入该区间。

当前判断：

```text
S2-B2 is fatal only if the route uses finite-operator spectral positivity.
The public route says it does not use that step.
```

第三轮 reviewer 应检查是否有任何 hidden import 偷用了谱收敛。

## S2-B3：Even-Sector Spectral Assumption

第二份意见指出 CCM25 谱路线可能依赖偶扇区最小特征向量假设。

这可以打击 CCM25 spectral program，但当前 route 不应导入该 program。项目应继续把以下内容列为 non-importable shortcut：

```text
even-sector minimum eigenvector assumption
finite-operator spectral convergence
determinant convergence
numerical eigenvalue convergence
```

当前判断：

```text
S2-B3 does not directly hit the fixed-test scalar route.
It becomes fatal if any accepted-source row secretly depends on the even-sector conjecture.
```

## S2-B4：Semilocal Fourth Defect and Dynamic S(g)

第二份意见把第一份意见中的 B3/B4 合并成一个更强说法：

```text
S(g) grows with g;
cross-term constants may blow up;
endpoint-strip Cdef may not control all semilocal defects uniformly.
```

当前项目回应分两层：

```text
semilocal defect classification:
  Rows 1-7 classify source terms as rank, pole, or endpoint-strip Cdef.

S(g) quantifier:
  for each fixed g, choose S(g), prove global QW(g,g) >= 0,
  then discharge CC20 by universal introduction.
```

`S(g)` 依赖 `g` 本身不是逻辑错误。错误只在以下情形出现：

```text
1. CC20 Proposition C.1 requires constants uniform in g.
2. The fixed-S construction returns an S-local scalar instead of global QW(g,g).
3. A source cross-term survives outside rank, pole, and endpoint-strip Cdef.
4. The Cdef exhaustion takes a supremum over varying g.
5. The final sign bridge applies to a different F_g.
```

当前判断：

```text
S2-B4 is answered at route-evidence / project proof-package level only.
accepted-source certification remains open.
```

## 第三轮攻击准备

第三轮 reviewer 最可能打三个问题：

| 优先级 | 攻击点 | 该怎么接 |
|---|---|---|
| P0 | 源公式中存在未命名 divergent bulk | 要求给出源公式行号和该项在 route ledger 中的位置；若不在 `QW_lambda/rank/pole/Cdef`，路线停止 |
| P0 | route 偷用了 finite-operator spectral convergence | 检查每个 `QW_lambda -> QW` 引用；只允许 restriction-definition + fixed support |
| P1 | `S(g)` 需要 uniform-in-g 常数 | 要求指出哪一步量词需要 uniformity；若是 CC20 或 final sign 需要，路线停止 |

当前公开文件应补：

```text
docs/audits/second-external-opinion-audit.md
```

该文件应把第二份意见映射到公开审查行，避免外部 reviewer 误以为项目已经把这些问题升级为 accepted-source theorem。
