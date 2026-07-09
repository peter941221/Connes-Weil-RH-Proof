# Fixed-S Post-Q Bulk Graph Transfer Proof Package

Status: route-evidence proof package for the first Row 3 subcontract.

This package proves the project-level bridge targeted by:

```text
docs/proofs/fixed-s-post-q-bulk-graph-transfer-theorem-contract.md
```

It is not a CC20 or CCM24 source import. It is not a Lean theorem. It records
the route proof that must later be formalized or replaced by an accepted
external theorem.

## Result

Good result:

```text
FixedSPostQBulkGraphTransfer is closed at route-evidence level for the
single CC20 post-Q bulk term.
```

Boundary:

```text
This does not close Row 3 as a whole.
Boundary evaluation transport is closed separately at route-evidence level.
Series-tail bounded comparison remains open.
Rows 4-7 remain separate.
```

## Target

For the CC20 source bulk term:

```text
B_bulk_n(rho)
  =
rho^(1/2) int_(rho^-1)^1
  (D_u xi_n)(x) (D_u zeta_n)(rho x) dx,
```

prove the route-evidence bridge:

```text
FixedSPostQBulkGraphTransfer(S,I,lambda,g,F_g,n):
  PostQDerivativeDomainCompatibility(S,I,lambda,g,F_g,n)
  and
  PostQBulkFixedSEquality(S,I,lambda,g,F_g,n).
```

## Evidence Boundary

| claim | evidence |
|---|---|
| CC20 source bulk term | `weil-compo.tex:1267-1270`, `1338-1346` |
| CC20 domain failure | `weil-compo.tex:1260-1264` |
| CC20 source derivative bounds | `weil-compo.tex:2171-2211` |
| CCM24 fixed-S coordinate | `mainc2m24fine.tex:237-253`, `786-804` |
| CCM24 bounded comparison | `mainc2m24fine.tex:805-823` |
| CCM24 non-commutation warning | `mainc2m24fine.tex:846-852` |
| route fixed graph model | `docs/proofs/fixed-test-graph-cdef-exhaustion.md:47-85` |
| fixed finite-S graph boundedness | `docs/proofs/fixed-test-graph-cdef-exhaustion.md:112-141` |
| derivative-shift commutation | `docs/proofs/rank-repair-finite-normal-form.md:226-236` |
| `Q` graph-order stability | `docs/proofs/semilocal-q-compact-form.md:279-289` |

## Proof Skeleton

```text
CC20 source bulk term
        |
        v
logarithmic graph translation
        |
        v
fixed finite-S graph boundedness
        |
        v
V_S=M_S U_S common coordinate
        |
        v
fixed-S source-owned bulk object
        |
        v
input for Row 4 only
```

The proof stops before projection-defect classification. It does not prove
that the bulk term is endpoint-strip `Cdef`.

## Lemma 1. Source Bulk Object Is Already Boundary-Repaired

Statement:

```text
CC20PostQBulkDerivativeObject(n):
  B_bulk_n(rho) is the source-owned bulk term produced by Lemma devil3 after
  the failed formal `D_u` domain argument has been repaired by explicit
  boundary terms.
```

Proof.

CC20 first records the formal identity involving `D_u`:

```text
<eta | rep(Qf) xi>
  =
<D_u eta | rep(f) D_u xi>.
```

Then CC20 states that the identity cannot be applied directly to
`xi_n,zeta_n` because they are not in `Dom(D_u)`. Source:

```text
weil-compo.tex:1260-1264
```

Lemma `devil3` replaces the failed formal-domain move by:

```text
Qk(rho)
  =
bulk derivative integral
  +
lower boundary term
  -
upper boundary term.
```

Source:

```text
weil-compo.tex:1267-1270
```

Therefore the bulk term used here is not a formal derivative shortcut. It is
the source-owned bulk summand after boundary repair. Boundary terms remain
separate and are not consumed by this package.

## Lemma 2. Source-To-Log Graph Translation

Statement:

```text
SourcePostQBulkLogGraphTranslation(n):
  the two source factors `D_u xi_n` and `D_u zeta_n` are represented by the
  route logarithmic graph derivative on the open strip where the CC20 bulk
  integral is taken.
```

Proof.

Use the logarithmic coordinate:

```text
t = log x.
```

For a source function `f(x)`, define the log-coordinate representative:

```text
F(t) = f(e^t).
```

Then:

```text
dF/dt = e^t f'(e^t) = D_u f(e^t).
```

Thus the CC20 operator:

```text
D_u(f)(x)=x f'(x)
```

is the first logarithmic graph derivative on the open interval where the bulk
integral lives.

The moving interval:

```text
x in [rho^-1,1]
```

becomes:

```text
t in [-log rho,0].
```

For the route tuple, `rho` is read inside the same lambda/window gate used by
the fixed-S positive trace and restricted `QW_lambda`. Thus the bulk strip is
a substrip of the route logarithmic support window.

The domain failure at `x=+-1` is not erased by this translation. It is already
accounted for by Lemma 1 and remains outside this bulk statement.

Output:

```text
source_Du_equals_log_scaling_derivative
source_bulk_interval_maps_to_log_strip
rho_window_maps_to_route_window
domain_failure_boundary_terms_remain_separate
```

## Lemma 3. Source L2 Estimates Feed Fixed Graph Seminorms

Statement:

```text
SourceBulkEstimatesFeedGraphSeminorms(n,J_Q):
  the CC20 bounds for `D_u xi_n` and `D_u zeta_n` provide the fixed graph
  seminorm inputs needed for the transported bulk representative at graph
  order J_Q.
```

Proof.

CC20 bounds the `D_u zeta_n` contribution by estimating:

```text
int_(rho^-1)^1 (D_u zeta_n)(rho x)^2 rho dx.
```

Source:

```text
weil-compo.tex:2171-2188
```

CC20 bounds the `D_u xi_n` contribution using the prolate differential
equation and Wang's estimate:

```text
||D_u xi_n||
  <=
8 n^2 +(6 pi + 2)2n + 16 pi^2 + 12 pi + 1.
```

Source:

```text
weil-compo.tex:2190-2211
```

Under Lemma 2, these are exactly first-log-derivative estimates on the source
bulk strip. The route graph package uses fixed finite graph orders. For the
bulk term created by one application of `Q`, choose a fixed graph order:

```text
J_Q = J + 2
```

or any fixed order large enough to contain the two scaling derivatives
generated by `Q`. The exact integer is not material here; what matters is
that it is fixed before the lambda limit and before Row 4.

Output:

```text
source_L2_estimates_become_graph_seminorm_inputs
graph_order_JQ_named
```

## Lemma 4. Fixed Finite-S Euler Graph Boundedness

Statement:

```text
FixedSEulerGraphBoundedness(S,I,J_Q):
  for fixed finite S and fixed graph order J_Q, `M_S`, `M_S^*`, their finite
  Euler shift pieces, and the route finite-prime shifts preserve the graph
  domain with constants depending only on S,I,J_Q.
```

Proof.

CCM24 gives the fixed-S comparison map with bounded inverse. Source:

```text
mainc2m24fine.tex:805-823
```

That is an `L2` fact, not by itself a graph-domain theorem. The route graph
package supplies the graph upgrade in the fixed finite-S regime:

```text
Since S_A is fixed, multiplying by M_S, M_S^*, or finitely many fixed Euler
graph factors preserves Schwartz-tail decay up to a fixed polynomial weight.
```

Evidence:

```text
docs/proofs/fixed-test-graph-cdef-exhaustion.md:112-141
```

The finite-prime shifts commute with the logarithmic scaling derivative:

```text
[D_u,T_a]=0.
```

Evidence:

```text
docs/proofs/rank-repair-finite-normal-form.md:226-236
```

Therefore, at fixed finite `S` and fixed graph order, Euler factors and finite
shifts preserve the graph domain with constants fixed before the lambda limit.

This is exactly where CCM24's warning matters:

```text
N_S eta_S != eta_S N_infty
```

is not used. The proof works in the common logarithmic graph coordinate after
moving to `V_S=M_S U_S`, with named graph order and fixed finite-S constants.

Output:

```text
MS_preserves_graph_domain
MS_star_preserves_graph_domain
finite_shift_Ta_preserves_graph_domain
Du_commutes_with_finite_shift_Ta_in_log_coordinate
constants_fixed_before_lambda_limit
```

## Lemma 5. Fixed-S Bulk Representative

Statement:

```text
FixedSPostQBulkRepresentative(S,I,lambda,g,F_g,n):
  the CC20 source bulk term has a fixed-S representative in the common
  coordinate V_S=M_S U_S at fixed graph order J_Q.
```

Proof.

Combine:

```text
1. source-owned boundary-repaired bulk object,
2. log graph translation,
3. CC20 source derivative estimates as graph seminorm inputs,
4. fixed finite-S Euler graph boundedness,
5. CCM24 canonical coordinate V_S=M_S U_S.
```

CCM24 supplies the canonical coordinate:

```text
V_S=M_S U_S.
```

Source:

```text
mainc2m24fine.tex:237-253
mainc2m24fine.tex:786-804
```

The transported bulk object is defined by applying this common coordinate and
the fixed-S graph-bounded Euler transport to the source bulk object from
Lemma 1. The tuple is unchanged:

```text
(S,I,lambda,g,F_g,n)
```

No new test, window, finite set, or lambda parameter is introduced.

Output:

```text
fixedS_bulk_uses_same_S
fixedS_bulk_uses_same_I
fixedS_bulk_uses_same_lambda
fixedS_bulk_uses_same_g_and_Fg
fixedS_bulk_lives_in_VS_coordinate
fixedS_bulk_graph_order_JQ_named
```

## Lemma 6. Source-Bulk Equality Before Row 4

Statement:

```text
PostQBulkFixedSEquality(S,I,lambda,g,F_g,n):
  the fixed-S bulk representative is the transported image of the CC20 source
  bulk object, not a route-local lookalike.
```

Proof.

The fixed-S object in Lemma 5 is not introduced independently. It is defined
as the image of the CC20 source bulk object under the chain:

```text
CC20 source bulk object
        |
        v
log-coordinate graph translation
        |
        v
fixed finite-S graph-bounded Euler transport
        |
        v
V_S=M_S U_S coordinate
```

Each arrow is indexed by the same tuple:

```text
(S,I,lambda,g,F_g,n).
```

Thus the equality required before Row 4 is definitional at the route-evidence
level, once the transport chain is fixed and no fresh local object is allowed.

This is not an endpoint-strip or `Cdef` conclusion. It only says that Row 4
will classify the source-owned transported bulk term.

## Theorem. Fixed-S Post-Q Bulk Graph Transfer

Statement:

```text
FixedSPostQBulkGraphTransfer(S,I,lambda,g,F_g,n):
  PostQDerivativeDomainCompatibility(S,I,lambda,g,F_g,n)
  and
  PostQBulkFixedSEquality(S,I,lambda,g,F_g,n).
```

Proof.

`PostQDerivativeDomainCompatibility` follows from Lemmas 2 through 5:

```text
source D_u factor
  =
log graph derivative
  ->
fixed-S graph representative in V_S coordinate.
```

`PostQBulkFixedSEquality` follows from Lemma 6.

The proof uses:

```text
source ownership from CC20,
fixed-S coordinate from CCM24,
project graph boundedness at fixed S,
same tuple and same window throughout.
```

It does not use:

```text
N_S eta_S = eta_S N_infty,
automatic Sonin-isomorphism transport of D_u,
triple vanishing,
rank/pole classification,
endpoint-strip Cdef domination,
or a lambda -> infinity limit.
```

## Output To The Row Ledger

This package supplies, at route-evidence level:

```text
PostQDerivativeDomainCompatibility
PostQBulkFixedSEquality
```

It does not supply:

```text
PostQBoundaryEvaluationTransport
PostQSeriesTailBoundedComparison
CC20PostQRemainderFixedSSoninTransport
SoninProlateDefectEqualsEndpointStripCdef
```

## Current Status

```text
Source-to-log graph translation:        proved at route-evidence level
Fixed-S Euler graph boundedness:        proved at route-evidence level
Fixed-S bulk representative:            proved at route-evidence level
Source-bulk equality before Row 4:      proved at route-evidence level

Boundary evaluation transport:          closed separately at route-evidence level
Series-tail bounded comparison:         closed separately at route-evidence level
Full Row 3 transport:                   closed separately at route-evidence level
Sign/defect bridge:                     open
```
