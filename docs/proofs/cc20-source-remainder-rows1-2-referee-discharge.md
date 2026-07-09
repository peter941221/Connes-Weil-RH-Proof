# CC20 Source Remainder Rows 1-2 Referee Discharge

Status: mathematics-only referee discharge package for Rows 1 and 2 of the
sign/defect bridge.

This file closes the source-entry part of the sign/defect bridge at project
proof-package level. It does not claim Lean verification, journal acceptance,
Clay acceptance, or external source-import certification.

The target is:

```text
Rows 1-2 identify the exact CC20 source obstruction and its post-Q image
before Rows 3-7 transport and classify it.
```

## Verdict

Good result:

```text
Rows 1-2 now have a referee-readable project proof package.
```

Boundary:

```text
This package cites CC20 source formulas and fixes their route use.
External acceptance of those source formulas remains a separate certification
step.
```

Combined with:

```text
docs/proofs/sonin-prolate-defect-referee-discharge.md
```

the sign/defect bridge is now covered by project proof packages from source
entry through Row 7.

## Source Anchors

Primary source:

```text
Alain Connes and Caterina Consani,
"Weil positivity and Trace formula, the archimedean place",
arXiv:2006.13771.
```

The package uses these CC20 source-line anchors already recorded in the
repository:

| source lines | role |
|---|---|
| `weil-compo.tex:488-509` | `delta` and the trace-remainder formula for the archimedean positive trace |
| `weil-compo.tex:584-604` | positivity of `L` and the relation between `L`, `W_infty`, and `delta` |
| `weil-compo.tex:710-719` | the finite-vanishing ideal as the range of `Q=-(rho d/drho)^2+1/4` |
| `weil-compo.tex:747-761` | positivity after vanishing reduces to controlling `D circ Q` |
| `weil-compo.tex:875-878` | `D=L-W_infty` and the refinement from `W_infty=L-D` to `W_infty=S-E` |
| `weil-compo.tex:1132-1140` | positive Sonin trace and the `epsilon` remainder |
| `weil-compo.tex:1196-1199` | the need to analyze `E circ Q` |
| `weil-compo.tex:1260-1270` | domain warning for `D_u` and the repaired endpoint terms |
| `weil-compo.tex:1308-1333` | integration-by-parts derivation of lower and upper boundary terms |
| `weil-compo.tex:1338-1346` | displayed `Q epsilon` formula |
| `weil-compo.tex:2168-2185`, `2243-2250` | source-side convergence and tail estimates for the `Q epsilon` series |

These anchors come from:

```text
docs/proofs/cc20-source-remainder-orientation-theorem-contract.md
docs/audits/cc20-post-q-remainder-term-map.md
docs/audits/sonin-prolate-defect-source-readiness-audit.md
```

## Row 1. Source Remainder Object And Orientation

### Statement

For the CC20 test `f`, define:

```text
D(f) = L(f) - W_infty(f),
E(f) = S(f) - W_infty(f).
```

Equivalently:

```text
W_infty(f) = L(f) - D(f),
W_infty(f) = S(f) - E(f).
```

Here `L` and `S` are the positive trace functionals supplied by CC20. The
remainders `D` and `E` are the source obstruction terms. Positivity applies to
`L` or `S`, not to `W_infty` until the obstruction has been controlled.

### Proof

CC20 first introduces the `delta` trace-remainder formula and the positive
functional `L`. The repository records the source anchors at:

```text
weil-compo.tex:488-509
weil-compo.tex:584-604
```

The source then names:

```text
D = L - W_infty.
```

The route therefore reads the equality in the direction:

```text
W_infty = L - D.
```

This direction blocks the shortcut:

```text
L(f) >= 0
  therefore
W_infty(f) >= 0.
```

CC20 later introduces the Sonin trace functional `S` and the `epsilon`
remainder:

```text
Tr(rep(f) S)
  =
W_infty(f)
  +
integral f(rho^-1) epsilon(rho) d^*rho.
```

The repository records this at:

```text
weil-compo.tex:1132-1140
```

Define:

```text
E(f) = integral f(rho^-1) epsilon(rho) d^*rho.
```

Then:

```text
S(f) = W_infty(f) + E(f),
W_infty(f) = S(f) - E(f).
```

This gives the Row 1 source object:

```text
CC20SourceProlateRemainderObject(f)
  =
the pair of oriented obstruction identities
  W_infty = L - D
  W_infty = S - E.
```

The source object is not a route-local placeholder. It is the CC20 obstruction
between a positive trace functional and the Weil distribution.

### Output

Row 1 supplies:

```text
source_positive_functional_L
source_positive_sonin_functional_S
source_delta_obstruction_D
source_epsilon_obstruction_E
orientation_W_infty_equals_L_minus_D
orientation_W_infty_equals_S_minus_E
no_positive_trace_shortcut
```

## Row 2. Q Image Of The Source Remainder

### Statement

CC20 uses:

```text
Q = -(rho d/drho)^2 + 1/4
```

to impose the finite vanishing conditions. After applying `Q`, the obstruction
that Rows 3-7 must handle is the post-`Q` source remainder:

```text
D circ Q
```

on the `L-D` side, refined through the Sonin formula to:

```text
E circ Q
```

with the displayed `Q epsilon` itemization.

The `Q epsilon` formula has four source-owned classes:

```text
bulk integral term,
moving lower-boundary term,
fixed upper-boundary term,
series tail.
```

### Proof

CC20 identifies the finite-vanishing ideal as the range of `Q` and explains
that positivity after vanishing reduces to controlling the source remainder
after `Q`. The repository records this at:

```text
weil-compo.tex:710-719
weil-compo.tex:747-761
```

For the `D` side, CC20 states that the route must control:

```text
D circ Q.
```

The repository records this at:

```text
weil-compo.tex:875-878
```

CC20 then passes to the Sonin remainder and states that one must analyze:

```text
E circ Q.
```

The repository records this at:

```text
weil-compo.tex:1196-1199
```

The displayed source formula for `Q epsilon` is:

```text
Q epsilon(rho)
  =
sum_n lambda(n)/sqrt(1-lambda(n)^2) * T_n(rho),
```

with:

```text
T_n(rho)
  =
rho^(1/2) int_(rho^-1)^1
  (D_u xi_n)(x) (D_u zeta_n)(rho x) dx

  + rho^(-1/2) (D_u xi_n)(rho^-1) zeta_n(1)

  - rho^(1/2) xi_n(1) (D_u zeta_n)(rho).
```

The repository records this formula at:

```text
weil-compo.tex:1267-1270
weil-compo.tex:1338-1346
```

The first line gives the bulk integral term. The second line gives the moving
lower-boundary term. The third line gives the fixed upper-boundary term. The
summation over `n` gives the series-tail problem.

CC20 also records the domain warning that the formal `D_u` identity cannot be
applied to `xi_n,zeta_n` without repair:

```text
weil-compo.tex:1260-1264
```

This warning matters for Row 2 because it explains why the boundary terms
belong to the source post-`Q` image. A proof may not drop them before fixed-S
transport.

CC20 supplies source-side convergence and tail estimates for the series:

```text
weil-compo.tex:2168-2185
weil-compo.tex:2243-2250
```

These estimates give the source tail object that Row 3 later transports
through the fixed-S comparison.

### Output

Row 2 supplies:

```text
Q_operator_for_finite_vanishing
D_after_Q_control_target
E_after_Q_control_target
E_postQ_bulk_n
E_postQ_leftBoundary_n
E_postQ_rightBoundary_n
E_postQ_seriesTail_N
source_domain_warning_for_Du
source_tail_estimate
```

## Link To Row 3

Rows 1-2 hand this object to Row 3:

```text
CC20PostQSourceRemainder(f)
  =
E_postQ_bulk
  +
E_postQ_leftBoundary
  +
E_postQ_rightBoundary
  +
E_postQ_seriesTail.
```

For the route tuple:

```text
(S,I,lambda,g,F_g),
```

the source test is the common square:

```text
F_g = g^* * g.
```

Row 3 may transport only this source-owned object:

```text
CC20PostQSourceRemainder(F_g).
```

It may not replace it with:

```text
a route-local compact remainder,
a generic small prolate error,
a positivity defect with unspecified sign,
or a source tail without boundary terms.
```

The Row 3 object is therefore fixed before any CCM24 fixed-S transport begins.

## Combined Rows 1-2 Theorem

Statement:

```text
CC20SourceRemainderRows12Discharge(f):
  CC20SourceProlateRemainderObject(f)
  and
  CC20SourceRemainderAfterQ(f)
```

where:

```text
CC20SourceProlateRemainderObject(f)
  =
{ W_infty = L - D, W_infty = S - E }
```

and:

```text
CC20SourceRemainderAfterQ(f)
  =
{ D circ Q control target,
  E circ Q bulk term,
  E circ Q lower-boundary term,
  E circ Q upper-boundary term,
  E circ Q series tail }.
```

Proof.

Row 1 follows from the CC20 definitions of `D` and `E` and their orientation
against `W_infty`. Row 2 follows from the CC20 finite-vanishing `Q` reduction,
the source instruction to analyze `D circ Q` and `E circ Q`, the displayed
`Q epsilon` formula, the domain warning for `D_u`, and the source tail
estimates.

The theorem gives Row 3 a source-owned post-`Q` object with no missing bulk,
boundary, or tail class.

## Referee Acceptance Tests

| test | required answer |
|---|---|
| Does Row 1 identify the source obstruction by CC20 formula, not by route name? | yes |
| Does Row 1 expose both `W_infty=L-D` and `W_infty=S-E`? | yes |
| Does Row 1 block `positive trace -> Weil positivity` shortcutting? | yes |
| Does Row 2 identify `Q` as the finite-vanishing operator? | yes |
| Does Row 2 keep `D circ Q` and `E circ Q` as obstruction targets? | yes |
| Does Row 2 include the bulk term? | yes |
| Does Row 2 include both boundary terms? | yes |
| Does Row 2 include the series tail and source estimate? | yes |
| Does Row 2 pass the source-owned post-`Q` object to Row 3? | yes |

## Integration With Rows 3-7

Combining this package with:

```text
docs/proofs/sonin-prolate-defect-referee-discharge.md
```

gives the full project proof-package chain:

```text
Rows 1-2:
  CC20 source obstruction and post-Q image
        |
        v
Rows 3-7:
  fixed-S transport, projection split, rank/pole identification,
  endpoint-strip Cdef domination, and no-hidden-defect equality
        |
        v
finite-lambda lower bound:
  QW_lambda(g,g) >= -C Cdef.
```

## Remaining Certification Work

This package closes Rows 1-2 as a project proof package. External proof status
still requires a referee or formal source-import layer to accept the cited
CC20 formulas and the route's source-test identification.

The next mathematical gates after the sign/defect chain are:

```text
restricted-to-full QW_lambda(g,g) = QW(g,g),
final sign bridge QW(g,g) = -sum_v W_v(F_g),
CC20 Proposition C.1 finite-vanishing exit,
source RH to standard RH definition.
```

## Current Status

```text
Rows 1-2 source orientation:            closed at project proof-package level
Rows 3-7 sign/defect classification:    closed at project proof-package level
Full sign/defect chain Rows 1-7:        closed at project proof-package level
Accepted-source certification:          open
Lean proof status:                      not part of this pass
RH proof status:                        source-conditional
```
