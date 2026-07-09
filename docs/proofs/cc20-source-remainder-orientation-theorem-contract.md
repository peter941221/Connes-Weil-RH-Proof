# CC20 Source Remainder Orientation Theorem Contract

Status: theorem contract for Row 1 of the Sonin/prolate defect discharge
ledger.

This contract fixes the source orientation of the CC20 archimedean
trace-remainder terms. It does not prove the fixed-S transport theorem, and it
does not prove that the remainders are endpoint-strip `Cdef`. Its purpose is to
make the sign of the source obstruction explicit before the route uses any
positive trace.

The discharge ledger that consumes this contract is:

```text
docs/audits/sonin-prolate-defect-discharge-ledger.md
```

## Evidence Lock

| item | source evidence |
|---|---|
| CC20 abstract warning | `weil-compo.tex:85-88` says the Weil distribution and Sonin trace differ by a prolate-spheroidal term that must be controlled |
| trace-remainder `delta` | `weil-compo.tex:488-509` defines `delta` and proves the trace formula for `Tr(vrep(f) P P_hat P)` |
| positive functional `L` | `weil-compo.tex:584-604` defines positive `L(f)=int f(rho^-1)(delta-tau)` |
| need to control `D circ Q` | `weil-compo.tex:875-878` states `D=L-W_infty` and says Weil positivity requires sign control after `Q` |
| positive Sonin functional `S` and `epsilon` | `weil-compo.tex:1132-1140` states `Tr(rep(f) S)=W_infty(f)+int f(rho^-1)epsilon(rho)` |
| need to analyze `E circ Q` | `weil-compo.tex:1196-1199` defines `E` and says one must analyze `E circ Q` |
| formula for `Q epsilon` | `weil-compo.tex:1338-1346` gives `Q epsilon` as a sum with bulk and boundary terms |

Primary source:

```text
Alain Connes and Caterina Consani,
"Weil positivity and Trace formula, the archimedean place",
arXiv:2006.13771, https://arxiv.org/abs/2006.13771
```

## Contract Theorem 1. Delta Trace Remainder Orientation

Target:

```text
CC20DeltaTraceRemainderOrientation(f):
  D(f) = integral f(rho^-1) delta(rho) d^*rho
  L(f) = integral f(rho^-1)(delta(rho)-tau(rho)) d^*rho
  W_infty(f) = - integral f(rho^-1) tau(rho) d^*rho
  L(f) = W_infty(f) + D(f)
  W_infty(f) = L(f) - D(f).
```

Meaning:

The positive trace functional `L` is not the Weil functional. The source
remainder `D` is subtracted when recovering `W_infty`.

Blocked shortcut:

```text
L(f) >= 0
  ->
W_infty(f) >= 0.
```

This shortcut is invalid unless `D` is separately controlled.

## Contract Theorem 2. Q Makes The Remainder The Object To Control

Target:

```text
CC20DeltaAfterQControlTarget(f):
  after imposing the finite vanishing conditions through
    Q = -(rho d/drho)^2 + 1/4,
  the obstruction to Weil positivity is the sign of D(Qf),
  not the positivity of L alone.
```

Required source content:

```text
D(f) = L(f) - W_infty(f)
Q implements the vanishing conditions
D circ Q must be controlled
```

Meaning:

The `Q` step is not a cosmetic operation. It is the place where the source
paper moves from a positive trace to a controlled remainder problem.

## Contract Theorem 3. Epsilon Sonin Remainder Orientation

Target:

```text
CC20EpsilonSoninRemainderOrientation(f):
  E(f) = integral f(rho^-1) epsilon(rho) d^*rho
  S(f) = Tr(rep(f) boldS)
  S(f) = W_infty(f) + E(f)
  W_infty(f) = S(f) - E(f)
  S(f) is positive.
```

Meaning:

The Sonin projection trace `S(f)` is positive, but it still differs from
`W_infty(f)` by `E(f)`. A route using Sonin positivity must account for `E`.

Blocked shortcut:

```text
Sonin trace is positive
  ->
W_infty is positive.
```

## Contract Theorem 4. Epsilon After Q Has Bulk And Boundary Terms

Target:

```text
CC20EpsilonAfterQFormula(f):
  Q epsilon(rho)
    =
  sum_n coefficient_n T_n(rho),
```

where each `T_n` has:

```text
bulk integral term
boundary term at rho^-1
boundary term at rho.
```

Meaning:

The source remainder after `Q` is not a scalar sign. It has bulk and boundary
pieces. A fixed-S route must prove that the transported pieces become exactly
rank, pole, or endpoint-strip `Cdef`.

## Combined Contract

The Row 1/2 orientation target is:

```text
CC20SourceRemainderOrientationContract(f):
  CC20DeltaTraceRemainderOrientation(f)
  CC20DeltaAfterQControlTarget(f)
  CC20EpsilonSoninRemainderOrientation(f)
  CC20EpsilonAfterQFormula(f)
```

Projection target:

```text
CC20SourceRemainderOrientationContract(f)
  ->
CC20SourceProlateRemainderObject(f)
```

for Row 1 of:

```text
docs/audits/sonin-prolate-defect-discharge-ledger.md
```

and:

```text
CC20SourceRemainderOrientationContract(f)
  ->
CC20SourceRemainderAfterQ(f)
```

for Row 2.

## Import Acceptance Checklist

| requirement | required evidence |
|---|---|
| exact source formulas | `L`, `D`, `S`, and `E` are defined by the source integrals or traces |
| sign orientation | both `W_infty=L-D` and `W_infty=S-E` are explicit |
| positivity boundary | positivity applies to `L` or `S`, not directly to `W_infty` |
| `Q` role | `Q` is the vanishing-condition operator and moves the problem to `D circ Q` or `E circ Q` |
| post-`Q` structure | `Q epsilon` has bulk and boundary terms that still require classification |
| no endpoint-strip conclusion | this contract does not claim the terms are `Cdef`; that is a later fixed-S transport theorem |

## Current Judgment

| question | answer |
|---|---|
| Does this contract discharge sign/defect? | no |
| Does it fix the source sign orientation of the obstruction? | yes |
| Does it block positive-trace-to-Weil shortcutting? | yes |
| Does it prove the fixed-S endpoint-strip `Cdef` bridge? | no |

After this contract, the live sign/defect question becomes sharper:

```text
Can the source `D circ Q` / `E circ Q` bulk and boundary pieces, after fixed-S
transport, be exhausted by rank, pole, and endpoint-strip Cdef?
```
