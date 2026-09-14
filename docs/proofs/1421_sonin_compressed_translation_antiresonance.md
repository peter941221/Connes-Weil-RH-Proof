# 1421 - Sonin-compressed translation antiresonance

Date: 2026-09-14.

Status: `PAPER / NEW MATHEMATICAL LEMMA`, not a Lean theorem and not an RH
claim.  This record is the next R3-F0 candidate for the healthy-
`CompactLog` B5 consumer

```text
0 <= C1SameOwnerWeil.qw g
```

for the same detector selected against a hypothetical off-line zero.

## 1. The exact new idea

The global source leg is not Hilbert--Schmidt merely because every finite
window is Hilbert--Schmidt.  Record 1420 exposed the obstruction: a nonzero
compactly supported convolution can escape by translating a compact input.

The source carrier in the G8 construction is not the whole logarithmic
`L2` space.  It is the intersection of two upper-half-line conditions:

```text
R_lambda = {u : u vanishes below log(lambda)}
F_lambda = {u : H u vanishes below log(lambda)}
S_lambda = R_lambda intersect F_lambda
```

Here `H` is the committed archimedean Hardy--Titchmarsh transform.  Let
`T_b u(t) = u(t + b)` be the committed global logarithmic translation.  The
source code proves the two identities needed for the new mechanism:

```text
T_b(R_lambda) subset R_lambda                 for b <= 0
H T_b = T_(-b) H
```

The first is `cc20GlobalLogTranslation_mem_ccm24LogRadialSupport` in
`CCM24LogRadialSupport.lean:124-137`.  The second is
`archimedeanHardyTitchmarsh_globalLogTranslation` in
`C1SemilocalHardyTitchmarshUnitarityReduction.lean:319-322`.

The sign is now fixed.  A negative source translation `T_(-na)` is harmless
for the radial condition, but its Hardy image is the positive translation
`T_(na) H u`.  The latter can remain in the upper half-line only through the
far tail of `H u`.

## 2. The antiresonance lemma

Let `a > 0`, let `u` belong to `S_lambda`, and let `P_S` and `P_F` denote the
orthogonal projections onto `S_lambda` and `F_lambda`.  The proposed paper
lemma is

```text
|| P_S T_(-n*a) u ||
    <= || P_F T_(-n*a) u ||
    =  || P_R T_(n*a) H u ||
    -> 0                 as n -> infinity.
```

The proof has three independent steps.

### Step A: projection nesting

`S_lambda` is a closed subspace of `F_lambda`.  Therefore the component of a
vector in `S_lambda` is no larger than its component in `F_lambda`:

```text
||P_S v|| <= ||P_F v||.
```

This is a pure Hilbert-space fact.  It uses no detector, prime sum, sign, or
RH premise.

### Step B: Hardy covariance

For `u in S_lambda`, `H u` belongs to `R_lambda`.  Since `H` is an isometry
and `H T_(-n*a) = T_(n*a) H`, the Fourier-support projection satisfies

```text
||P_F T_(-n*a) u||
  = ||P_R H T_(-n*a) u||
  = ||P_R T_(n*a) H u||.
```

This is the point at which the two support conditions interact.  A proof
using only the radial support would miss the sign reversal and would not
produce antiresonance.

### Step C: the L2 tail identity

Put `A = log(lambda)`.  If `h in R_lambda`, then, up to the fixed `Lp`
normalization,

```text
||P_R T_(n*a) h||^2
  = integral over [A, infinity) of |h(t + n*a)|^2 dt
  = integral over [A + n*a, infinity) of |h(s)|^2 ds.
```

The last quantity tends to zero because `h` is in `L2`.  Applying this to
`h = H u` proves the displayed antiresonance estimate.

No numerical input is involved.  The result uses only the actual committed
translation definition, the actual Hardy--Titchmarsh covariance, and the
vanishing-tail property of an `L2` function.

## 3. Why this is genuinely new for R3

Record 1420's global noncompactness argument uses translated compact inputs
in the ambient carrier.  The new lemma shows why that exact counterexample
does not pass through the source Sonin compression:

```text
ambient escape:       T_(-n*a) u stays norm 1;
Sonin readback:       P_S T_(-n*a) u tends strongly to 0.
```

Thus the source carrier supplies a real antiresonant mechanism.  It is not a
claim that the finite cutoff converges, and it is not the invalid statement
that the source carrier is finite-dimensional.

The mechanism also explains the old radial antiresonance files.  Their
identities
`radialComplement_comp_negativeTranslation_comp_radialSupport_eq_zero` and
`radialSupport_comp_positiveTranslation_comp_radialComplement_eq_zero` are
the one-sided triangular pieces.  The new lemma adds the missing second
side: the Hardy image turns the apparently harmless negative translation
into a positive translation whose surviving source component is only an
`L2` tail.

## 4. The exact remaining gap: pointwise versus collective antiresonance

The lemma above is not yet F0.  Strong convergence on each fixed source
vector does not imply compactness, Hilbert--Schmidt convergence, or trace
convergence on an infinite-dimensional carrier.  The required upgrade is a
collective source-energy estimate.

For an orthonormal source basis `(e_k)` and the global source column
coefficients `c_j`, the useful target has the shape

```text
sum over k sum over j
  |c_j|^2 * ||P_S T_(-s_j) e_k||^2 < infinity,
```

with the actual prime-power shifts `s_j` and the actual G8 source column.
Equivalently, one must prove that the compressed source leg is
Hilbert--Schmidt, or provide a different trace-class factorization whose
bound is implied by the same double sum.

The pointwise lemma supplies the `j -> infinity` mechanism for every fixed
`e_k`; it does not supply the sum over `k`.  Any future claim that “the
Sonin projection kills translations, hence F0 is solved” is therefore
incorrect and is explicitly rejected here.

## 5. New mathematical target R3-F1

```text
R3-F1 / collective Sonin antiresonance

Input:
  the committed source Sonin carrier S_lambda,
  the committed G8 source column and its prime-power shifts,
  no healthy/sign/RH premise.

Target:
  a source-basis-independent Hilbert--Schmidt or trace-class estimate for
  the compressed global source leg, derived from the two-sided support
  geometry and the actual coefficients.

Minimum acceptable form:
  an explicit finite bound for the double source-energy sum above, or a
  factorization into two Hilbert--Schmidt legs with a summable tail.

Consumer:
  G8SameOwnerReadbackData -> 0 <= qw owner.sourceTest -> SourceRH.

Cheap falsifier:
  find a bounded orthonormal source sequence whose compressed translation
  columns have a nonvanishing lower energy along a prime-power subsequence.
  Such a sequence would refute F0 for the current source owner.
```

## 6. Verdict

```text
R3-F1 pointwise core:        PAPER-GREEN candidate
R3-F1 collective upgrade:    OPEN
F0 Hilbert--Schmidt limit:   OPEN
G8SameOwnerReadbackData:     NOT CONSTRUCTED
RH:                          NOT CLAIMED
```

The R3 route is therefore not dead, and it now has a real new mathematical
mechanism rather than another convergence assumption.  But it is not yet a
proof of RH.  The next honest move is to derive the collective source-energy
bound from the same Sonin geometry, not to declare the pointwise tail lemma a
trace theorem.

## 7. Interface correction

The preceding conclusion must be read with one important operator-level
qualification.  The pointwise lemma controls

```text
P_S T_(-n*a) J,
```

or a source-compressed translation, while the first F0 factor in the actual
G8 trace is of the form

```text
G_S^(1/2) * B_infinity * J.
```

The output of `B_infinity` is in the ambient global carrier; it is not known
to be followed by `P_S`.  Therefore the pointwise lemma alone does **not**
prove that the actual G8 source leg is Hilbert--Schmidt.  In particular, the
sentence in the earlier version that this already “blocks the ambient
translated-input escape after Sonin compression” was too strong when applied
to the full G8 source leg.

The valid use is the following conditional decomposition.  If the actual
limiting source leg admits a translation expansion compatible with the source
projection, split it as

```text
B_infinity J
  = P_S B_infinity J + (I - P_S) B_infinity J.
```

The first term is a legitimate consumer of the new antiresonance lemma.  The
second term is an ambient Sonin-leakage term and needs an independent
commutator, boundary, or trace-ideal estimate.  No such factorization for the
current `B_infinity` has yet been proved.  Thus the lemma remains a valid
geometric result, but its direct F0 status is downgraded to `INTERFACE
PREMISE`, not `F0 GREEN`.
