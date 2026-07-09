# Rank Repair Finite Normal Form

Status: proof package for the Battle 1 rank-repair leg.

This file proves the pure zero-mode rank part from the current route evidence
and records how the remaining rank-repair gap is discharged by the follow-up
proof packages. The first reduction was:

```text
SemilocalQCompactFormIdentity(S,I)
  +
BoundaryJetRankCdefDichotomy(S,I).
```

The follow-up proof package
`docs/proofs/semilocal-q-compact-form.md` proves the projection-defect side of
that reduction at route-evidence level. The source-sensitive input:

```text
FixedSNoDefectCompactFormReadOff(S,I).
```

is discharged at source-interface level by
`docs/proofs/fixed-s-no-defect-compact-form-read-off.md`.

After these packages, the theorem

```text
RankRepairFiniteNormalForm(S,I)
```

is closed at route-evidence level, conditional on the cited source interfaces
and on endpoint-strip `Cdef` being defined and exhausted as in Battle 3.

## Target

The theorem needed by Battle 1 is:

```text
RankRepairFiniteNormalForm(S,I):
  every no-strip fixed-S rank repair is a scalar multiple of |hat h(0)|^2,
  and every non-pure fixed-S repair term belongs to the endpoint-strip Cdef
  ledger.
```

It should imply:

```text
Rank_(S,I)(g)=C_(S,I)|hat g(0)|^2
```

modulo endpoint-strip `Cdef` terms.

## Evidence Boundary

| claim | evidence |
|---|---|
| Pure Euler multipliers preserve the zero functional | `docs/ConnesWeilPositivity.md:137968-138030`, `140048-140091` |
| Projection/Euler commutators are the non-pure fixed-S terms | `docs/ConnesWeilPositivity.md:138032-138092`, `139481-139556` |
| Q applied to endpoint-strip defects keeps a strip factor | `docs/ConnesWeilPositivity.md:139384-139477`, `139720-139810`, `146192-146320` |
| Current route-note closure depends on compact-form and boundary-jet lemmas | `docs/ConnesWeilPositivity.md:138333-138435`, `138478-138496` |
| Projection-defect boundary jets reduce to endpoint-strip Cdef | `docs/proofs/semilocal-q-compact-form.md`, `docs/ConnesWeilPositivity.md:139389-139835`, `146192-146320`, manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:489-538` |
| No-defect fixed-S compact-form read-off is CCM25 `QW_lambda` | `docs/proofs/fixed-s-no-defect-compact-form-read-off.md`, `docs/audits/source-reread-v0.2.md:47-54`, manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:991-1033`, `1338-1361` |
| Manuscript records the desired rank ledger | `docs/manuscripts/connes-weil-rh-proof-draft.md:832-878`, `1132-1151`, `1161-1172` |

## Decomposition

```text
RankRepairFiniteNormalForm(S,I)
        |
        +-- PureEulerRankIdentification(S,I)
        |
        +-- EndpointStripDefectNormalForm(S,I)
        |
        +-- QTraceRemainderDefectContinuity(S,I,J)
        |
        +-- SemilocalQCompactFormIdentity(S,I)
        |
        +-- BoundaryJetRankCdefDichotomy(S,I)
        |
        +-- FixedSNoDefectCompactFormReadOff(S,I)
```

The first three legs are supported by the current route evidence.
`docs/proofs/semilocal-q-compact-form.md` proves the projection-defect part of
the last two legs. `docs/proofs/fixed-s-no-defect-compact-form-read-off.md`
discharges the no-defect compact-form read-off at source-interface level.

## Lemma 1. Pure Euler Rank Identification

Statement:

```text
PureEulerRankIdentification(S,I):
  every fixed-S rank-one term obtained from the archimedean rank term by
  Mellin-side Euler multiplication, without inserting a support-projection
  commutator, factors through hat h(0).
```

Proof.

The fixed finite-S Euler multiplier has the schematic Mellin form:

```text
A_S(z)=prod_(p in S_fin) L_p(1/2-iz)^(epsilon_p),
```

where the exponent depends on whether the term uses `M_S`, `M_S^(-1)`,
`M_S^*`, or `(M_S^*)^(-1)`. For fixed finite `S`, `A_S` is holomorphic and
nonzero at `z=0`.

A no-commutator rank term applies this multiplier before evaluating at
`z=0`:

```text
h -> hat h(z) -> A_S(z) hat h(z) -> evaluation at z=0.
```

Therefore:

```text
(A_S hat h)(0)=A_S(0) hat h(0).
```

For a rank-one quadratic term:

```text
|(A_S hat h)(0)|^2
  =
|A_S(0)|^2 |hat h(0)|^2.
```

This proves the pure rank contribution has the same zero-mode support as the
archimedean rank repair. The exploration note records this calculation at
`docs/ConnesWeilPositivity.md:137968-138030` and uses it again at
`docs/ConnesWeilPositivity.md:140048-140091`.

Output:

```text
PureRank_(S,I)(h)=C_(S,I)|hat h(0)|^2.
```

## Lemma 2. Endpoint-Strip Defect Normal Form

Statement:

```text
EndpointStripDefectNormalForm(S,I):
  every non-pure projection/Euler defect contains a commutator with M_S or
  M_S^*, and expands into endpoint-strip shifted kernels.
```

Proof sketch.

For `R=P_I` or `R=P_hat_I`, write the fixed-S metric projection defect as:

```text
Delta_R = R_(S,G)-R
        = (R G R |_(Ran R))^(-1) R G (1-R),

G = M_S^* M_S.
```

The off-diagonal block satisfies:

```text
R G (1-R) = -R [G,R] (1-R),
```

and:

```text
[G,R] = M_S^*[M_S,R] + [M_S^*,R]M_S.
```

The finite-prime Euler multiplier has a fixed-S shift expansion:

```text
M_S = sum_alpha c_alpha T_alpha.
```

Thus:

```text
[R,M_S]
  =
sum_alpha c_alpha [R,T_alpha]
  =
sum_alpha c_alpha M_(b_(R,alpha)) T_alpha,
```

where each multiplier `b_(R,alpha)` is supported on a shifted endpoint strip.

Therefore each canonical projection-order defect has normal form:

```text
Delta =
sum_alpha X_(0,alpha) M_(b_alpha) T_alpha X_(1,alpha),
```

where the `X` factors are fixed graph-bounded operators. The exploration note
states this normal form at `docs/ConnesWeilPositivity.md:139481-139556`.

Output:

```text
non-pure fixed-S term -> endpoint-strip shifted kernel.
```

## Lemma 3. Q Trace-Remainder Defect Continuity

Statement:

```text
QTraceRemainderDefectContinuity(S,I,J):
  applying the Connes-Consani Q trace-remainder extraction to an endpoint-strip
  projection defect produces only Cdef-controlled bulk and boundary terms.
```

Proof sketch.

The source calculation uses:

```text
D = D_u^2 + D_u.
```

The finite-prime shifts commute with the logarithmic scaling derivative in the
log model:

```text
[D_u,T_a]=0.
```

Thus `Q` adds a bounded number of graph derivatives, but it does not remove the
middle endpoint-strip factor:

```text
M_b T_a.
```

Bulk terms keep the normal form:

```text
theta(D^r h) X_0 M_b T_a X_1 theta(D^s h)^*.
```

Boundary terms contain one strip factor before the evaluation functional:

```text
evaluation o theta(D^r h) X_0 M_b T_a.
```

The finite-strip Sobolev trace estimate bounds these boundary rank terms by
the same graph-Cdef norm with two additional derivatives. The exploration note
records the proof skeleton at:

```text
docs/ConnesWeilPositivity.md:139384-139477
docs/ConnesWeilPositivity.md:139720-139810
docs/ConnesWeilPositivity.md:146192-146320
```

Output:

```text
endpoint-strip projection defect -> Cdef.
```

## Reduced Lemma 4. Semilocal Q Compact Form Identity

Status: closed at route-evidence level after the no-defect read-off package.

The needed theorem is:

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
N_(S,I)-N_I factored through endpoint-strip commutators,
BoundaryJet_(S,I) sorted by BoundaryJetRankCdefDichotomy.
```

Why this has narrowed:

The semilocal compact-form package proves that raw cross-prime boundary jets
are pre-canonical artifacts and that every projected leftover contains a
commutator with `M_S` or `M_S^*`. Those projection-defect terms are
endpoint-strip `Cdef` after the `Q` trace-remainder extraction.

What the no-defect read-off package supplies:

The no-defect compact-form calculation shows that canonical fixed-S transport
creates no no-strip compact-form channel beyond:

```text
hat h(0),
hat h(+i/2),
hat h(-i/2),
the CCM25 finite-prime Weil ledger.
```

The exploration note first states the raw boundary-jet danger at
`docs/ConnesWeilPositivity.md:138498-138650`, then quarantines the
projection-defect branch at `docs/ConnesWeilPositivity.md:138700-139046` and
proves `Q` trace-remainder stability at
`docs/ConnesWeilPositivity.md:139389-139835`.

Required output:

```text
fixed-S Q compact form
  =
archimedean compact form
  +
pure zero-mode rank
  +
killed pole jets
  +
endpoint-strip Cdef.
```

## Reduced Lemma 5. Boundary Jet Rank-Cdef Dichotomy

Status: proved for projection-defect boundary jets and closed at
source-interface level for no-defect boundary jets.

The needed theorem is:

```text
BoundaryJetRankCdefDichotomy(S,I):
  every boundary-jet term in the fixed-S Q-remainder is one of:
    1. a scalar multiple of |hat h(0)|^2;
    2. a killed finite pole/zero jet at z=0,+i/2,-i/2;
    3. an endpoint-strip Cdef term.
```

Endpoint support alone does not prove Cdef control. The semilocal compact-form
package uses the stronger condition: a boundary term containing a
projection-order defect also contains a commutator-generated strip factor
before evaluation. That is enough for endpoint-strip `Cdef`.

The no-defect boundary terms are not charged to `Cdef` by support alone. They
must be identified directly as the zero-mode rank and the two killed Tate
channels.

## Conditional Rank Repair Theorem

Use the sharpened no-defect input:

```text
FixedSNoDefectCompactFormReadOff(S,I)
```

Then:

```text
RankRepairFiniteNormalForm(S,I)
```

holds.

Proof.

`PureEulerRankIdentification` gives:

```text
PureRank_(S,I)(h)=C_(S,I)|hat h(0)|^2.
```

`EndpointStripDefectNormalForm` classifies every non-pure fixed-S transport
term as a projection/Euler commutator with endpoint-strip normal form.

`QTraceRemainderDefectContinuity` routes those commutator terms through the
endpoint-strip `Cdef` ledger after `Q` and trace-remainder extraction.

`docs/proofs/semilocal-q-compact-form.md` ensures that projection-order
boundary jets do not create extra no-strip rank functionals.

`FixedSNoDefectCompactFormReadOff` supplies the remaining no-defect
compact-form channels and sorts them into zero-mode rank, killed pole/zero
jets, or the CCM25 finite-prime Weil ledger.

Thus no no-strip nonzero-mode rank functional remains. The only rank repair
not charged to `Cdef` is:

```text
C_(S,I)|hat h(0)|^2.
```

## Consequence For Battle 1

With the sharpened no-defect read-off package, Battle 1 closes at
route-evidence level:

```text
TestHalfDensityCompatibility
  +
TateDirectionsToPoleLedger
  +
RankRepairFiniteNormalForm
  ->
TestAndQuotientCompatibility.
```

Without that read-off package, Battle 1 would remain open for a precise
reason:

```text
the no-defect fixed-S compact-form calculation may create a no-strip positive
direction that is not hat h(0), not a killed pole jet, and not part of the
CCM25 finite-prime Weil ledger.
```

## Current Status

```text
Pure zero-mode rank:                 proved at route-evidence level
Endpoint-strip defect normal form:   proved at route-evidence level
Q defect continuity:                 proved at route-evidence level
Projection-defect boundary jets:     proved at route-evidence level
Semilocal Q compact form identity:   closed at route-evidence level
Boundary jet rank-Cdef dichotomy:    closed at route-evidence level
RankRepairFiniteNormalForm:          closed at route-evidence level
Battle 1:                            closed at route-evidence level,
                                     source- and Cdef-conditional
```
