# 015 — R3 weighted two-projection trace bridge

**Date:** 2026-09-14
**Status:** new-math candidate; T1 closed-subspace transport is formal, the
weighted trace bridge is unproved.  This record is supporting, not a route
authority, and makes no RH claim.
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
projection strongly:

```text
T_b^n  ->  r_b.
```

The required theorem is not operator-norm convergence.  It is the weighted
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
needed before an endpoint argument: `p_b q p_b` is formally positive and
self-adjoint for every `b`, because `p_b` and `q` are orthogonal projections.
These facts are recorded in [1432](../proofs/1432_r3_weighted_finite_stage_commutator.md).
They do not imply a spectral gap, a trace estimate, or convergence to the
intersection projection.

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
