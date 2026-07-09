# CC20 Post-Q Remainder Term Map

Status: item-level map for Row 3 of the sign/defect discharge ledger.

This audit refines:

```text
docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md
docs/audits/ccm24-fixed-s-post-q-transport-obstruction-audit.md
```

It asks whether the CC20 post-`Q` source remainder terms are at least named
well enough to enter the fixed-S CCM24/Sonin transport problem.

It does not prove the transport theorem. It also does not classify any term as
rank, pole, or endpoint-strip `Cdef`.

## Result

Good result:

```text
The CC20 post-Q epsilon remainder has an explicit item-level source formula.
```

Bad result for final certification:

```text
No source theorem was found that transports these items through the fixed-S
CCM24 model and then identifies them with the route Cdef ledger.
```

The Row 3 status is therefore:

```text
term map built;
transport theorem still open.
```

## Source Formula

CC20 first fixes the role of `Q`:

| source lines | content |
|---|---|
| `weil-compo.tex:710-719` | the finite vanishing ideal is the range of `Q=-(rho d/drho)^2+1/4`, with support preserved |
| `weil-compo.tex:747-750` | positivity after vanishing is equivalent to positivity of `phi circ Q` on the same support interval |
| `weil-compo.tex:759-761` | controlling `D circ Q` gives Weil positivity on the vanished test class |

The source then replaces the `D` obstruction by the Sonin `E` obstruction:

| source lines | content |
|---|---|
| `weil-compo.tex:875-878` | `D=L-W_infty`, and the section refines `W_infty=L-D` to `W_infty=S-E` |
| `weil-compo.tex:1132-1140` | positive Sonin trace: `Tr(rep(f) S)=W_infty(f)+int f(rho^-1) epsilon(rho)` |
| `weil-compo.tex:1196-1199` | to control `W_infty` after vanishing, one must analyze `E circ Q` |

The post-`Q` formula is:

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

Source anchors:

```text
weil-compo.tex:1267-1270
weil-compo.tex:1338-1346
```

The analytic-continuation rewrite gives the same three term classes using
`xi_n^an`:

```text
weil-compo.tex:1352-1360
```

The convergence appendix controls the infinite series:

```text
weil-compo.tex:2168-2185
weil-compo.tex:2243-2250
```

## Item-Level Map

| item | CC20 source shape | Row 3 transport target | later row |
|---|---|---|---|
| `E_postQ_bulk_n` | `rho^(1/2) int_(rho^-1)^1 (D_u xi_n)(x)(D_u zeta_n)(rho x) dx` | transport as a source-owned scaling coefficient in the same fixed-S Sonin window | Row 4 decides whether its fixed-S drift is a projection-defect normal form |
| `E_postQ_leftBoundary_n` | `rho^(-1/2)(D_u xi_n)(rho^-1) zeta_n(1)` | transport as a source-owned boundary-evaluation term at the lower moving endpoint | Row 5/6 decide rank/pole or endpoint-strip ownership |
| `E_postQ_rightBoundary_n` | `-rho^(1/2) xi_n(1)(D_u zeta_n)(rho)` | transport as a source-owned boundary-evaluation term at the upper fixed endpoint after scaling | Row 5/6 decide rank/pole or endpoint-strip ownership |
| `E_postQ_seriesTail_N` | source-controlled infinite-series tail | transport only after a theorem preserves the convergence bound under the fixed-S comparison | Row 6 decides domination by route `Cdef` if the tail is endpoint-strip |

This map is deliberately one-sided: it maps the `E circ Q` side. The `D circ
Q` side remains controlled through the earlier `D=L-W_infty` orientation and
the source compact-operator statement, but the explicit termwise post-`Q`
formula currently available for the rapid Row 3 route is the `E`/`epsilon`
formula.

## Row 3 Transport Requirements

For each item above, Row 3 needs only these facts:

| requirement | reason |
|---|---|
| same source test `F_g` | prevents classifying a remainder built from a different test |
| same route tuple `(S,I,lambda,g,F_g)` | prevents moving the defect through a different cutoff |
| same fixed-S canonical coordinate `V_S=M_S U_S` | makes later commutators with `M_S` meaningful |
| same CCM24 support window | aligns the positive trace, `QW_lambda`, and future `Cdef` exhaustion |
| same fixed-window Sonin comparison | ensures the source Sonin remainder is being transported through the Sonin model used by the positive trace |
| convergence preservation | allows the termwise map to pass from finite partial sums to the full source remainder |

Row 3 does not need to prove:

```text
endpoint-strip normal form,
rank/pole ledger equality,
Cdef trace-norm domination,
or fixed-test exhaustion.
```

Those are Rows 4-6.

## Fast Pass Judgment

| question | answer |
|---|---|
| Is the post-`Q` epsilon remainder itemized in CC20? | yes |
| Are the item classes source-owned? | yes, for `E circ Q` via `T_n` |
| Is there an immediate escaped fourth item in the displayed `Q epsilon` formula? | no; the displayed structure is bulk, two boundary terms, and series tail |
| Does CC20 itself transport these terms through fixed finite `S`? | no |
| Does CCM24 itself identify these transported terms with route `Cdef`? | no |
| Does this discharge Row 3? | no |

The useful consequence is narrower:

```text
Row 3 can now be attacked item by item.
```

The next theorem target is:

```text
CC20PostQTermwiseFixedSTransport(S,I,lambda,g,F_g,n):
  E_postQ_bulk_n,
  E_postQ_leftBoundary_n,
  E_postQ_rightBoundary_n
  transport through the common fixed-S CCM24/Sonin window.
```

Together with:

```text
CC20PostQSeriesTailTransport(S,I,lambda,g,F_g,N):
  the source convergence bound for the tail survives the fixed-S bounded
  comparison in the graph class used later by Cdef.
```

If either target fails, the failed item must be named as a new defect class and
the route cannot claim the sign/defect bridge is repaired.

The CCM24 fast pass further splits these targets into:

```text
PostQDerivativeDomainCompatibility
PostQBoundaryEvaluationTransport
PostQSeriesTailBoundedComparison
```

This split is forced by `mainc2m24fine.tex:846-852`, where CCM24 warns that
`N_S eta_S != eta_S N_infty` and
`|.|_S^2 eta_S(f) != eta_S(|.|^2 f)` outside the purely archimedean case.

The first subcontract is now stated in:

```text
docs/proofs/cc20-post-q-derivative-domain-compatibility-theorem-contract.md
```

It is also forced by `weil-compo.tex:1260-1264`, where CC20 says the formal
`D_u` identity cannot be directly applied to `xi_n,zeta_n` because they do
not belong to the domain of `D_u`.

The second subcontract is now stated in:

```text
docs/proofs/cc20-post-q-boundary-evaluation-transport-theorem-contract.md
```

It is forced by `weil-compo.tex:1267-1270` and `1308-1333`, where the failed
formal `D_u` argument is repaired by the lower moving endpoint and upper fixed
endpoint terms.

The third subcontract is now stated in:

```text
docs/proofs/cc20-post-q-series-tail-bounded-comparison-theorem-contract.md
```

It is forced by `weil-compo.tex:2243-2250`, where CC20 proves a source-side
uniform scalar tail estimate but does not transport it through the fixed-S
graph or trace class used later by `Cdef`.
