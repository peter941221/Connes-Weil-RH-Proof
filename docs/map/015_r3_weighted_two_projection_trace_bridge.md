# 015 — R3 weighted two-projection trace bridge

**Date:** 2026-09-14
**Status:** new-math candidate; T1 closed-subspace transport and the actual
angle-free strong power limit are formal, while the weighted trace bridge is
unproved.  This record is supporting, not a route authority, and makes no RH
claim.
**Consumer:** the healthy-`CompactLog`, B5-shaped statement
`0 <= C1SameOwnerWeil.qw g` for the same tower-selected detector.

This record is the next refinement of
[014](014_r3_doubled_shift_sonin_transport.md).  It is written after the
formal T1 results in [1430](../proofs/1430_r3_doubled_shift_sonin_transport_t1.md)
and [1431](../proofs/1431_r3_doubled_shift_projection_transport.md).
The aim is to attack the actual moving-scale R3 obstruction with a theorem
that can still be connected to the existing G8 readback owner.

## 1. Review verdict

The doubled-shift idea survived its first hard test:

```text
map U_b ( U_(-2*b) Ran(E_1) intersect Ran(Q_1) )
  = Ran(E_lambda) intersect Ran(Q_lambda).
```

This is now a formal closed-subspace identity, and the corresponding
orthogonal projection transport is formal in [1431](../proofs/1431_r3_doubled_shift_projection_transport.md).
Neither result proves trace-classness of the projection commutator with the
detector.

The next tempting move is a uniform Friedrichs-angle bound for the two
subspaces.  That move is not accepted as a premise.  The unit-scale
time/frequency model already has prolate near-extremal directions, so a
uniform gap may be false or may be exactly the old prolate difficulty in new
notation.  The new proposal is therefore **angle-free but detector-weighted**:
use the spectral approach to the intersection projection only after inserting
the smoothing factors supplied by the positive convolution-square detector.

```text
T1 subspace transport       FORMAL GREEN
T1 projection transport     FORMAL GREEN
T1 angle-free power limit   FORMAL GREEN
T2 weighted trace bridge    OPEN, genuine new mathematics
T3 basis witness             OPEN
T4 G8 reconnect              OPEN
R3                           OPEN
RH                           not claimed
```

## 2. Exact objects

Let `b = log lambda`.  On the finite-S source carrier write, as subspaces,

```text
A_b = U_(-2*b) Ran(E_1)
B   = Ran(Q_1)
R_b = A_b intersect B.
```

Let `p_b` and `q` be the orthogonal projections onto `A_b` and `B`, and let
`r_b` be the orthogonal projection onto `R_b`.  The formal T1 theorem says
that the actual Sonin projection is the conjugate of `r_b`, once the separate
projection-uniqueness step is supplied.

Let `D` be the exact selected detector operator.  The committed source
factorization is the positive convolution square

```text
D = C† C.
```

The R3 target remains the signed trace object

```text
[r_b, D] = r_b D - D r_b,
```

or, equivalently, the full source remainder with its two outer branches kept
in the same owner.  No sign of `qw` is allowed in this stage.

## 3. New mathematical move: spectral intersection without an angle gap

The two-projection product on `A_b` is

```text
T_b = p_b q p_b.
```

The intersection is the fixed-point space at spectral value `1`:

```text
Ran(r_b) = { v in Ran(p_b) : T_b v = v }.
```

There are two equivalent search coordinates.

### 3.1 Alternating-projection coordinate

The powers of the positive contraction `T_b` approach the intersection
projection strongly without a uniform angle gap.  This is now formal for the
actual `finiteSCarrier` in `C1G8R3PowerProjectionBridge.lean`, theorem
`doubledShiftAlternatingProduct_tendsto_intersectionProjection_no_gap`:

```text
T_b^n  ->  r_b.
```

The remaining theorem is not operator-norm convergence.  It is the weighted
limit

```text
lim_n || (T_b^n - r_b) D ||_1 = 0
and
lim_n || D (T_b^n - r_b) ||_1 = 0,
```

or the corresponding two-sided estimates after the `C† C` factorization.
If this holds, then the finite-stage commutator identity

```text
[T_b^n, D]
  = sum_{j=0}^{n-1} T_b^j [T_b, D] T_b^(n-1-j)
```

can be passed to the trace ideal.  The sum must be controlled as a complete
signed object; estimating each summand by a norm bound that grows with `n` is
not sufficient.

### 3.2 Resolvent coordinate

For `eps > 0`, define the regularized spectral filter on `Ran(p_b)`:

```text
S_(b,eps) = eps * (eps*I + I - T_b)^(-1).
```

Strongly as `eps -> 0`, this filter selects the fixed-point space and tends to
`r_b`.  The resolvent identity turns the commutator into a weighted defect
problem:

```text
[S_(b,eps), D]
  = eps * (eps*I + I - T_b)^(-1)
      [T_b, D]
    (eps*I + I - T_b)^(-1),
```

with the domain/compression projections made explicit in the formal version.
The target is a uniform trace-norm bound and a trace-norm limit, not an
unbounded inverse at the spectral endpoint.

The alternating and resolvent forms are not two independent claims.  They are
two ways to expose the same endpoint singularity.  The project should choose
the one for which the committed prolate Hilbert--Schmidt factor gives a second
factor rather than merely a compactness statement.

## 4. Where the detector smoothing enters

The positive-square factorization gives the algebraic expansion

```text
[T_b, C† C] = [T_b, C†] C + C† [T_b, C].
```

This is only a search identity.  It becomes an admissible proof route only if
the actual terms can be grouped into two Hilbert--Schmidt factors, a direct
nuclear kernel, or a signed cancellation with a summable trace norm.

The specific new target is a **weighted defect estimate** of one of the forms

```text
sum_n || (T_b^n - r_b) C† ||_2 * || C ||_2 < infinity,
```

or, more realistically for the non-global detector,

```text
sum_n || A_(b,n) ||_2 * || B_(b,n) ||_2 < infinity,
```

where `A_(b,n)` and `B_(b,n)` are the two source-owned factors obtained by
expanding the complete coupled remainder, not arbitrary replacements for its
branches.

The prolate data already present in the source are the candidate supplier for
one factor.  The doubled-shift Hardy involution

```text
K_b = U_(2*b) H,       K_b^2 = identity
```

is the candidate supplier for pairing the opposite boundary terms.  The
unknown theorem must show that the pairing produces a summable defect, rather
than merely restating that `K_b` is an involution.

The finite-stage source ledger now also has the lower-data spectral facts
needed before an endpoint argument: `p_b q p_b` is formally positive,
self-adjoint, and contractive for every `b`, because `p_b` and `q` are
orthogonal projections.
These facts are recorded in [1432](../proofs/1432_r3_weighted_finite_stage_commutator.md).
They do not imply a spectral gap, a trace estimate, or convergence to the
intersection projection.

The next finite-stage block is now formal in [1433](../proofs/1433_r3_endpoint_fixed_vectors_and_stage_bound.md):
every vector in the doubled-shift Sonin intersection is fixed by `p_b q p_b`,
and hence by every finite power.  Independently, for any contraction `T`, the
weighted commutator stage satisfies the explicit lower-data estimate
`||weightedCommutatorStage T D n|| <= n * ||[T,D]||`.
This is the correct endpoint ledger: it identifies the spectral value `1`
without assuming a gap and prevents finite-stage commutators from being
treated as uncontrolled algebraic remainders.  It is still insufficient for
R3, because the required detector-weighted trace-norm tail must be summable;
the linear bound alone does not provide that decay.

The first analytic transfer lemma is now formal in
`C1G8R3WeightedStrongToHS.lean`: strong convergence of the endpoint operators
on each detector-root column, a uniform operator-norm bound, and one
Hilbert--Schmidt square-sum imply convergence of the weighted square energy.
This does not assume operator-norm convergence or a Friedrichs-angle gap.  The
strong-convergence premise is now supplied by the no-gap bridge above; the
remaining obligations are the exact detector-root square-sum and the
same-owner trace/readback estimate.

## 5. Projection step before the trace step

The formal T1 theorem is about closed subspaces.  Before using `r_b`, prove a
small abstract lemma in the committed Hilbert-space API:

```text
mapEquiv (f) (starProjection S)
  = starProjection (mapEquiv f S),
```

for the relevant unitary/linear-isometry equivalence, or prove the equality by
the uniqueness of the orthogonal projection with the transported range and
self-adjoint/idempotent laws.  Instantiate it with the T1 subspace identity to
obtain

```text
sourceSoninProjection lambda
  = U_b r_b U_(-b).
```

This is a separate formal obligation.  It may not be silently inferred from
equality of ranges in the R3 trace proof.

## 6. Generation card

```text
candidate/id
  R3-SC2b / weighted two-projection endpoint calculus

target
  A basis-compatible trace-class theorem for [r_b, D],
  where r_b projects onto U_(-2*b) Ran(E_1) intersect Ran(Q_1),
  followed by the exact T1 projection transport and G8 readback.

novel move
  Do not assume a Friedrichs-angle gap.  Treat the intersection as the
  spectral endpoint 1 of p_b q p_b and use the detector's C†C smoothing
  to make the endpoint filter trace-summable.

sign source
  the signed full remainder and paired Hardy/Sonin boundary cancellation;
  no universal Weil positivity and no RH input.

consumer
  0 <= C1SameOwnerWeil.qw g for the same tower-selected detector.

cheap falsifier
  In the unit-scale prolate model, test on the exact near-extremal
  directions whether the proposed weighted series has a summable majorant.
  If the detector-weighted defect still has a non-summable tail, record a
  typed no-go and do not build the resolvent in Lean.

second falsifier
  If the finite-stage commutator expansion requires an unproved uniform
  spectral gap, kill that version and retain only the angle-free resolvent
  candidate.

anti-circularity
  No qw sign, SourceRH, healthy-detector proposition, all-test gate, or
  external Weil-formula dictionary may enter the weighted estimate.
```

## 7. Staged obligations and stop rules

```text
015-A  prove the abstract projection-map uniqueness lemma
015-B  derive the exact r_b conjugacy from T1
015-C  derive a source-owned finite-stage commutator identity and lower-data
             positivity facts                         FORMAL PASS (batch 1432)
015-D  prove the detector-weighted alternating/resolvent trace estimate
015-E  construct the same global-basis IsTraceClassAlong witness
015-F  reconnect the signed limit to the G8 source/cutoff ledger
```

Kill or revise the candidate if:

1. the projection step needs more than the committed subspace and isometry
   laws, or changes the source owner;
2. the only route to convergence is a uniform angle gap contradicted by the
   prolate near-extremal tail;
3. the weighted series has no summable majorant supplied by the exact detector
   factors and source support;
4. trace-classness is obtained only for a changed basis or an abstract unitary
   basis rather than the named global basis;
5. the signed limit cannot be identified with the exact G8 same-owner response.

## 8. RH reachability

This candidate is RH-reaching only conditionally.  If 015-A through 015-F
close, then 014 and 013 provide the moving-scale Sonin commutator leg, and 012
provides the existing conditional composition:

```text
weighted Sonin trace bridge
  -> R3 signed source remainder
  -> G8SameOwnerReadbackData
  -> 0 <= qw g for the selected detector
  -> contradiction with the formal detector qw g < 0
  -> SourceRH
  -> project RH output.
```

The conditional chain is logically valid, but the weighted trace estimate is
not yet proved.  Thus this record is a sharpened attack plan, not a claim that
R3 or RH has been completed.

The finite-stage algebraic entry point is now explicit in the candidate
module `C1G8R3WeightedFiniteStage.lean`: the recursively accumulated
`weightedCommutatorStage T D n` is proved equal to
`T^n D - D T^n`, and it is instantiated with the doubled-shift alternating
product `p_b q p_b`.  The paired audit passed in batch 1432; see [1432](../proofs/1432_r3_weighted_finite_stage_commutator.md).  This is only the exact finite-stage ledger; it does not provide the weighted trace-norm summability or the limit at the intersection endpoint.

## 9. New endpoint bridge (batch 1435)

The next obstruction has now been given an exact operator socket in
`C1G8R3PowerProjectionBridge.lean`. Define `r_b` to be the orthogonal
projection onto the doubled-shift Sonin intersection. The formal source facts
include `T_b r_b = r_b` for `T_b = p_b q_1 p_b`, because every vector in the
intersection is fixed by the alternating product.

The new abstract lemma proves the geometric endpoint statement:

```text
T P = P,  P T = P,  P^2 = P,  ||T - P|| < rho < 1
  ==>  T^(n+1) -> P  in operator norm.
```

The proof is the exact identity `T^(n+1) - P = (T - P)^(n+1)` followed by
the norm-power limit. This is not the R3 conclusion: the remaining target is
the explicit defect-gap estimate `||T_b - r_b|| < 1`. Record 1436 formally
discharged the opposite product identity `r_b T_b = r_b` by taking the
adjoint of the already-formal identity `T_b r_b = r_b`; it adds no spectral
gap or trace estimate. The gap remains a named analytic obligation rather
than a hidden assumption inside “alternating projections converge”.

If a strict gap is false at moving scale, its failure is a typed obstruction
to the geometric route and forces an angle-free spectral/weighted estimate.
No trace classness, G8 readback, R3 sign, or RH conclusion is claimed.

Record 1437 now formalizes the non-gap prerequisite on the actual carrier:
the fixed vectors of `T_b = p_b q p_b` are exactly the doubled-shift Sonin
intersection.  Its forward implication uses only projection absorption and
the norm characterization of an orthogonal projection's range.  It does not
give the von Neumann strong limit of the powers, a rate, or a trace estimate;
the remaining endpoint theorem is therefore sharply separated from the
already-closed fixed-space algebra.

Record 1438 adds the first scalar energy ledger for the same operator. It
proves contraction of every power, antitonicity of
`n |-> ||(p_b q p_b)^n v||`, and convergence of that scalar sequence to its
explicit infimum. This is a formal lower-data result, not the von Neumann
strong limit: the vector endpoint and its equality with `r_b v` remain open.
It also proves the exact Pythagorean drop on `Ran(p_b)`: one step loses the
sum of the `q`-orthogonal defect of `v` and the `p`-orthogonal defect of
`q v`. The remaining analytic task is to show that this cumulative defect
loss exhausts the non-intersection component.

Record 1439 proves the finite cumulative version exactly: the defect sum
through stage `n` is `||v||^2 - ||T_b^n v||^2` for every radial input. This
is the budget identity that an eventual infinite-stage strong-limit or
spectral-measure argument must consume. The same audited leaf proves that
each nonnegative defect term tends to zero by summability. The vector limit,
identification with `r_b`, and any detector-weighted trace estimate remain
open; the two component defect energies now also vanish separately by
squeezing, which is only asymptotic regularity. Record 1440 adds the exact
triangle bound from those two orthogonal residuals and proves the adjacent
power iterates have norm difference tending to zero. This still supplies no
Cauchy estimate or trace-class tail. Record 1441 now proves that any strong
limit, if it exists, is exactly `r_b v`; only existence of the no-gap limit
and the detector-weighted trace tail remain. Record 1442 supplies the
Fejér-distance formulation of that existence problem: the orbit distance to
each intersection vector is monotone with a named infimum endpoint. Its
consumer theorem shows that a zero infimum for the intersection projection is
already sufficient for strong convergence; the unresolved input is exactly
the zero-infimum/exhaustion estimate.
Record 1443 sharpens that estimate to the exact scalar identity relating the
distance to `r_b v` and the norm-energy drop, so only the scalar endpoint
equality and the detector-weighted trace tail remain.
Record 1444 proves the automatic lower half of that equality:
`||r_b v|| <= ciInf_n ||T_b^n v||`, by projection contractivity at every
finite stage. The remaining scalar endpoint bone is therefore only the reverse
inequality, equivalently exhaustion of the finite defect budget or zero Fejer
distance to `r_b v`.
Record 1445 closes the consumer side of that reverse inequality: convergence of
the squared orbit norms to `||r_b v||^2` implies
`ciInf_n ||T_b^n v|| <= ||r_b v||`. Thus the remaining analytic input is one
named squared-norm exhaustion statement, with both scalar inequalities and the
strong-limit consumer formal.
Record 1446 lowers that input to the finite-defect ledger itself: the single
`tsum` equality `sum'_k defect(T_b^k v) = ||v||^2 - ||r_b v||^2` implies the
squared-norm exhaustion. The live R3 analytic bone is now exactly this
defect-series equality (plus the separate detector-weighted trace tail).
Record 1447 proves the converse as well: the defect-series equality is
equivalent to the scalar endpoint equality `ciInf_n ||T_b^n v|| = ||r_b v||`.
Thus the no-gap strong-limit obstruction has one exact scalar formulation; no
second hidden endpoint estimate remains.
Record 1448 closes the endpoint consumer itself conditionally: the same
defect-series equality is equivalent to strong convergence `T_b^n v -> r_b v`.
Record 1450 then proves the missing no-gap existence theorem directly from
self-adjointness, contraction, and asymptotic regularity: the range of `T-I`
is dense in the fixed-space complement, and telescoping kills that dense
range. The explicit defect-series exhaustion is therefore no longer a live
existence premise for the actual operator. The remaining R3 analysis is the
detector-root square-sum and the separate same-owner detector-weighted trace
tail.
Record 1449 wires this endpoint into the existing strong-to-Hilbert–Schmidt
transfer: columnwise defect exhaustion plus a square-summable detector factor
implies the weighted square energy tends to zero. The remaining trace issue is
now only the actual columnwise exhaustion and the same-basis trace/readback.
Record 1451 makes the first exact factor split concrete. The raw selected
convolution root is not an HS factor on the whole-line multiplier carrier; the
unit-scale `sourceRootCompletedRangeLeftLeg` is the legal source-owned factor.
Its column square-sum and its no-gap weighted energy limit are formal. This is
only one of the independent root legs: the band-minus-prolate leakage leg and
the common-right finite-Euler leg remain open, as does the same-basis signed
trace witness. Record 1452 gives the leakage leg an exact same-carrier normal
form: the source root leakage is the selected root conjugated against the
doubled-shift projection defect `p_b - T_b`, where `T_b = p_b * q_1 * p_b`.
This is a structural identity only; the defect estimate and the common-right
leg remain open.
