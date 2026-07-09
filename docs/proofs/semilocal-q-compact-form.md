# Semilocal Q Compact Form Proof Package

Status: proof-reduction package for the remaining rank-repair compact-form
leg.

This file does not close Battle 1. It proves the projection-defect part of

```text
SemilocalQCompactFormIdentity(S,I)
```

at the current route-evidence level, and it upgrades

```text
BoundaryJetRankCdefDichotomy(S,I)
```

for all boundary jets that contain a canonical projection-order defect. The
remaining no-defect compact-form read-off is still a source-sensitive theorem.

## Target

The rank-repair proof package needs:

```text
SemilocalQCompactFormIdentity(S,I):
  E_S(Q(h*h^*)) =
    <phi_h, N_(S,I) phi_h>
    + BoundaryJet_(S,I)(h)
    + PureRank_(S,I)(h),
```

with:

```text
PureRank_(S,I)(h)=C_(S,I)|hat h(0)|^2,
BoundaryJet_(S,I)(h) in rank + killed pole + endpoint-strip Cdef,
N_(S,I)-N_I factored through endpoint-strip projection defects.
```

The proof splits into two parts:

```text
semilocal Q compact form
        |
        +-- no-defect fixed-S compact read-off
        |
        +-- canonical projection-defect stability
```

This file proves the second part and records the exact first-part dependency.

## Evidence Boundary

| claim | evidence |
|---|---|
| The route remains source-conditional, not a completed RH proof | `docs/ConnesWeilPositivity.md:20`, manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:1642-1643` |
| Raw semilocal periodization creates `S`-smooth boundary jets | `docs/ConnesWeilPositivity.md:138498-138650` |
| Canonicalization cancels raw Euler products before projection through `M_S F(E_S g)=F(g)` | `docs/ConnesWeilPositivity.md:138700-138768`, `138928-138974` |
| Projection-order leftovers are commutators with `M_S` or `M_S^*` | `docs/ConnesWeilPositivity.md:138994-139046`, manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:489-538` |
| Endpoint-strip trace ideal controls projection defects and their `Q` remainders | `docs/ConnesWeilPositivity.md:139389-139835`, `146192-146320`, manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:489-538` |
| No-strip quotient ledgers are only `hat g(0)`, `hat g(+i/2)`, and `hat g(-i/2)` | manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:832-878`, `1132-1151`, `1161-1172` |

## Lemma 1. Canonical Boundary-Jet Quarantine

Statement:

```text
CanonicalModelBoundaryJetQuarantine(S,I):
  after passing from raw semilocal periodization to the canonical fixed-S model
  V_S=M_S U_S, cross-prime S-smooth boundary jets do not survive as no-strip
  phase ledgers.
```

Proof.

Raw semilocal periodization has the schematic form:

```text
E_S(g)(u)=sum_(a in A_S) a^(-1/2) g(a u),
```

so the raw coordinate representative has breakpoints at:

```text
u=a^(-1),  a in A_S.
```

Those breakpoints include cross-prime `S`-smooth points such as `(pq)^(-1)`.
They cannot appear in the final Weil ledger, which is additive over prime
powers.

The canonical fixed-S spectral model inserts:

```text
V_S = M_S U_S,
```

and the Mellin-side identity:

```text
M_S F(E_S g)=F(g).
```

Thus cross-prime boundary jets created by the raw representative disappear
before support and Fourier-support projections are applied. They are
pre-canonical artifacts, not phase-face Weil coefficients.

After projection, the only possible leftover is an order defect:

```text
P_I M_S F(E_S g) - M_S P_I F(E_S g)
  =
[P_I,M_S]F(E_S g),

P_hat_I M_S F(E_S g) - M_S P_hat_I F(E_S g)
  =
[P_hat_I,M_S]F(E_S g).
```

The same formulas hold with `M_S^*`. Therefore every projected leftover
contains one of:

```text
[P_I,M_S],
[P_hat_I,M_S],
[P_I,M_S^*],
[P_hat_I,M_S^*].
```

The endpoint-strip trace ideal lemma in the manuscript charges each such
commutator to endpoint-strip `Cdef`.

Output:

```text
raw cross-prime boundary jet
  ->
pre-canonical artifact
  or
projection-order endpoint-strip Cdef.
```

## Lemma 2. Projection-Defect Normal Form

Statement:

```text
CanonicalProjectionDefectNormalForm(S,I):
  every canonical projection-order defect in the fixed-S support-square
  operator is a finite graph-bounded sum of endpoint-strip shifted kernels.
```

Proof.

For `R=P_I` or `R=P_hat_I`, the metric projection defect has the schematic
form:

```text
Delta_R = R_(S,G) - R.
```

The off-diagonal metric block contains:

```text
R G (1-R) = -R [G,R](1-R),
```

where:

```text
G=M_S^*M_S.
```

Expanding the commutator gives:

```text
[G,R]=M_S^*[M_S,R]+[M_S^*,R]M_S.
```

For fixed finite `S`, the Euler multiplier has an absolutely summable finite-S
shift expansion:

```text
M_S=sum_alpha c_alpha T_alpha.
```

Hence:

```text
[R,M_S]
  =
sum_alpha c_alpha [R,T_alpha]
  =
sum_alpha c_alpha M_(b_(R,alpha)) T_alpha,
```

where `b_(R,alpha)` is supported on a shifted endpoint strip determined by the
window boundary and the shift `alpha`.

Thus every projection-order defect that enters the support-square expansion
has normal form:

```text
Delta =
sum_alpha X_(0,alpha) M_(b_alpha) T_alpha X_(1,alpha),
```

with fixed graph-bounded factors `X_(0,alpha), X_(1,alpha)` and endpoint-strip
support for `b_alpha`.

Output:

```text
canonical projection defect
  ->
endpoint-strip shifted kernel normal form.
```

## Lemma 3. Endpoint-Strip Cdef Trace Ideal

Statement:

```text
EndpointStripCdefTraceIdealTheorem(S,I,J):
  if Delta is any projection-order defect generated by
  [P,M_S], [P_hat,M_S], [P,M_S^*], or [P_hat,M_S^*], then

    theta(h) Delta theta(h)^*

  is trace-class in the Connes-Consani support-square trace ideal, and its
  trace norm is bounded by a fixed graph-order Cdef norm. The same remains
  true after the Connes-Consani Q trace-remainder extraction.
```

Proof.

By Lemma 2, each summand has the form:

```text
theta(D^r h) X_0 M_b T_a X_1 theta(D^s h)^*,
```

with `b` supported on a finite endpoint strip `E_(lambda,a)`. Factor the
operator through the strip:

```text
L2(R)
  --B_s-->
L2(E_(lambda,a))
  --A_r-->
L2(R).
```

The Hilbert-Schmidt estimates are:

```text
||A_r||_2^2
  <=
|E_(lambda,a)| ||K_(D^r h,X_0)||_2^2,

||B_s||_2^2
  <=
||b||_2^2 ||K_(D^s h,X_1)||_2^2.
```

Therefore:

```text
||A_r B_s||_1
  <=
||A_r||_2 ||B_s||_2
  <=
C_(S,I,J)(h) Cdef_(S,I,lambda,J)(h),
```

after summing the fixed-S Euler coefficient budget.

Applying `Q` adds a bounded number of scaling derivatives. The graph order
increases from `J` to `J+J_Q`, but the middle endpoint-strip factor remains.
Bulk terms are controlled by the same Hilbert-Schmidt factorization.

Boundary terms also keep a strip factor before the evaluation functional:

```text
evaluation o theta(D^r h) X_0 M_b T_a.
```

The Sobolev trace theorem on a finite strip gives:

```text
|evaluation(A_r v)|
  <=
C_(S,I,J)(h) ||v||_(L2(E_(lambda,a))).
```

The adjoint side satisfies the same estimate, so every boundary rank term
created from a projection defect has the same `Cdef` bound.

A pure no-strip boundary jet would require a path from `theta(h)` to the
boundary evaluation with no commutator-generated strip factor. That cannot
occur for `Delta`, because `Delta` contains such a commutator by definition.

Output:

```text
projection defect
  ->
trace ideal Cdef
  ->
Q trace-remainder Cdef.
```

## Lemma 4. Trace-Remainder Functor Stability

Statement:

```text
TraceRemainderFunctorStability(S,I):
  the operation

    support-square projection defect
      ->
    Connes-Consani trace remainder after Q
      ->
    compact form on L2(I)

  sends canonical projection-order Cdef defects to endpoint-strip Cdef
  defects, modulo the existing rank and pole ledgers.
```

Proof.

Combine:

```text
CanonicalProjectionDefectNormalForm
  +
EndpointStripCdefTraceIdealTheorem.
```

Every projection-order defect has an endpoint-strip factor before `Q`.
The `Q` extraction differentiates a bounded number of times and introduces
bulk terms plus endpoint boundary terms. Lemma 3 controls both families with
the graph-order-enlarged `Cdef` norm.

The only no-strip boundary jets occur in the no-defect source calculation.
The manuscript assigns those to:

```text
hat h(0),
hat h(+i/2),
hat h(-i/2).
```

Thus the trace-remainder functor does not create a new positive compact
direction from fixed-S projection defects.

## Lemma 5. Projection-Defect Boundary Jet Dichotomy

Statement:

```text
ProjectionDefectBoundaryJetDichotomy(S,I):
  every fixed-S Q-boundary term that contains a canonical projection-order
  defect is an endpoint-strip Cdef term.
```

Proof.

By Lemma 3, a boundary term with a projection defect has one endpoint-strip
factor before the evaluation functional. The finite-strip trace theorem bounds
that evaluation by the same Cdef norm. Therefore such a term cannot be a
new no-strip rank or pole channel.

Output:

```text
boundary jet with projection defect
  ->
endpoint-strip Cdef.
```

## Conditional Semilocal Compact Form

The remaining source-sensitive input is:

```text
FixedSNoDefectCompactFormReadOff(S,I):
  after canonical fixed-S transport and before projection-order defects,
  the Connes-Consani E o Q compact-form calculation has only:

    1. the archimedean compact form;
    2. pure zero-mode rank;
    3. pole/zero jets at 0,+i/2,-i/2;
    4. the CCM25 finite-prime Weil ledger.
```

Assume this input. Then:

```text
SemilocalQCompactFormIdentity(S,I)
```

holds modulo endpoint-strip `Cdef`.

Proof.

`FixedSNoDefectCompactFormReadOff` supplies the no-defect compact-form
calculation and identifies the no-strip boundary channels.

`CanonicalModelBoundaryJetQuarantine` removes raw cross-prime boundary jets
from the canonical phase ledger. Any projected leftover contains a commutator
with `M_S` or `M_S^*`.

`TraceRemainderFunctorStability` charges those projection-order leftovers to
endpoint-strip `Cdef` after `Q`.

Therefore the fixed-S compact form has only:

```text
archimedean compact form
  +
pure zero-mode rank
  +
killed pole jets
  +
finite-prime Weil ledger
  +
endpoint-strip Cdef.
```

This is the required compact-form identity for the rank-repair route, subject
to the displayed no-defect read-off.

## Consequence For Rank Repair

This file upgrades the remaining rank-repair gap from:

```text
SemilocalQCompactFormIdentity(S,I)
  +
BoundaryJetRankCdefDichotomy(S,I)
```

to the sharper dependency:

```text
FixedSNoDefectCompactFormReadOff(S,I).
```

All projection-defect boundary jets are now charged to endpoint-strip `Cdef`.
The no-defect boundary jets remain exactly the source-sensitive rank and pole
ledger channels.

## Current Status

```text
Canonical boundary-jet quarantine:       proved at route-evidence level
Projection-defect normal form:           proved at route-evidence level
Endpoint-strip Q trace ideal stability:  proved at route-evidence level
Projection-defect boundary dichotomy:    proved at route-evidence level
SemilocalQCompactFormIdentity:           closed after no-defect read-off package
RankRepairFiniteNormalForm:              closed at route-evidence level
Battle 1:                                closed at route-evidence level,
                                         source- and Cdef-conditional
```
