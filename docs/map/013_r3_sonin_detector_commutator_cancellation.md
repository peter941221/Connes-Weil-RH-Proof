# 013 — R3 Sonin–detector commutator cancellation

**Date:** 2026-09-14
**Status:** supporting route candidate; SC1 passed on paper, unit-scale SC2 is
formal, moving-scale SC2 remains open.
**Consumer:** the selected healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g`, for the same detector selected against a
hypothetical off-line zero.

This record refines the open R3 target in
[012](012_g8_same_owner_readback_rh_reachability.md). It does not alter the
binding route choice in [003](003_b1_b5_minimal_exit_route_selection.md), does
not reopen universal B1, and does not claim RH. Its purpose is to test whether
the remaining positive-looking prolate remainder should be attacked as a
signed commutator instead of as a standalone positive square.

## 1. Review verdict

The candidate is mathematically legitimate as a new attack surface, for three
reasons already visible in committed source:

1. The coupled source remainder has an exact signed decomposition.
2. The two outer terms in that decomposition already have trace-class
   theorems, with the same owner, scale, support interval, and global basis.
3. The detector is already presented as a positive convolution square, so the
   commutator has a natural algebraic structure rather than being an arbitrary
   subtraction.

The candidate is **not** yet a proof strategy. The missing Sonin commutator
estimate is a genuine Schatten-1 problem. No implication
`Hilbert-Schmidt -> trace-class` is admitted, and no cancellation is declared
until a norm or kernel estimate proves it.

The honest review is therefore:

```text
route quality       : structurally sound candidate
current evidence    : formal identities + formal outer trace legs
new theorem needed  : direct signed trace-class/cancellation estimate
R3 status           : OPEN
RH status           : not claimed
```

## 2. The exact source identity

The committed theorem
[`sourceSecondSupportProlateRemainder_eq_sonin_sub_outerPair`](../../ConnesWeilRH/Source/CCM25Concrete/CCM24ReflectedCompactRoot.lean)
states, for every selected owner and Sonin scale,

```text
sourceSecondSupportProlateRemainder owner lambda
  = cc20Commutator (sourceSoninProjection lambda) (detectorOperator owner)
      - (outerBranch lambda owner + reflectedOuterBranch lambda owner)
```

Here `cc20Commutator A W` is the signed operator `A.comp W - W.comp A`.
The two outer terms are exactly
`cc20OuterCommutatorBranch` and
`cc20ReflectedOuterCommutatorBranch`.

This is important because it prevents a false choice between “second-support”
and “prolate” terms. The source already records their coupled cancellation;
splitting them and estimating each positive piece separately can destroy the
only available sign mechanism.

The companion theorems
[`sourceOuterCommutatorBranch_isTraceClassAlong`](../../ConnesWeilRH/Source/CCM25Concrete/CCM24RadialBoundaryPairTransport.lean)
and
[`sourceReflectedOuterCommutatorBranch_isTraceClassAlong`](../../ConnesWeilRH/Source/CCM25Concrete/CCM24RadialBoundaryPairTransport.lean)
prove trace-classness along the global source basis under the existing compact
radial support and boundary-basis data. Their sum is packaged by
`sourceOuterCommutatorPair_isTraceClassAlong`.

Therefore the new analytic target can be stated without changing the owner:

```text
prove IsTraceClassAlong globalBasis
  (cc20Commutator (sourceSoninProjection lambda)
    (detectorOperator owner))
```

or, more strongly and more usefully for the readback,

```text
prove the signed trace limit of the full
sourceSecondSupportProlateRemainder owner lambda,
with the outer pair retained in the same trace owner.
```

The first target would make trace legality follow by subtraction. The second
target is the actual R3 target because legality alone does not identify the
limit with `qw`.

## 3. Why the detector factorization gives a new lever

The existing theorem
`detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution`
identifies the detector as a positive convolution square. Write this only as
an algebraic mnemonic:

```text
D = C† C
[P, D] = [P, C†] C + C† [P, C]
```

with `P = sourceSoninProjection lambda` and
`D = detectorOperator owner`.

This exposes two possible sources of summability:

- a direct Schatten-1 estimate for the signed commutator `[P,D]`; or
- a factorization of the two summands into explicit Hilbert-Schmidt factors,
  with the product estimate proved in the correct order.

The second bullet is a candidate only if both factors are genuinely supplied.
The following shortcut is forbidden:

```text
"[P,C] is Hilbert-Schmidt, therefore [P,C†C] is trace-class."
```

That implication is not automatic. The commutator expansion is a search
coordinate, not a theorem. A successful proof must either exhibit two
Hilbert-Schmidt factors for every trace term, prove a direct nuclear-kernel
bound, or prove a signed cancellation estimate for the complete remainder.

## 4. Relation to the R3 ledger

The candidate attacks the exact bottleneck left by F2/F3/F6:

```text
R3-F0  global uncut source leg                    OPEN
R3-F1  Sonin antiresonance mechanism              PAPER candidate
R3-F2  exact leakage split                        FORMAL reduction
R3-F3  trace-legality normal form                 FORMAL
R3-F4  scale-defect normal form                   FORMAL
R3-F5  Hardy defects vanish                      FORMAL
R3-F6  doubled-shift Hardy involution             FORMAL
R3-SC1 Sonin–detector commutator cancellation     THIS RECORD, OPEN
```

F6 is useful here but not sufficient. The involution
`K_b = T_(2*b) H`, with `K_b * K_b = id`, organizes the relative motion of
the radial and Fourier sides under scale transport. A future estimate may use
`K_b` to conjugate the Sonin projection or to pair two opposite boundary
contributions. Until such an estimate is written, `K_b` is only a normal-form
organizer and carries no positivity or trace conclusion.

The route must also preserve the source cutoff/source-ledger interface. A
commutator theorem proved for an abstract projection, a different owner, or a
finite-dimensional Sonin carrier does not discharge R3.

## 5. Generation card

```text
candidate/id
  R3-SC1 / Sonin–detector commutator cancellation

target equation
  Direct trace-class or trace-norm control for
    [sourceSoninProjection lambda, detectorOperator owner]
  strong form: a signed trace limit for
    sourceSecondSupportProlateRemainder owner lambda
  together with the existing cutoff/source transport data needed by
  G8SameOwnerReadbackData.

novel move
  Keep the second-support and prolate pieces coupled, expose the exact
  Sonin commutator, and use the detector's C†C structure to search for
  Schatten-1 cancellation.

sign source
  signed commutator cancellation plus Sonin antiresonance;
  not a new universal positivity assertion.

consumer
  0 <= C1SameOwnerWeil.qw g for the tower-selected healthy detector,
  then the existing same-detector contradiction and SourceRH wrapper.

cheap falsifier
  half-line model: take a radial half-line projection E and a nonzero
  compactly supported smooth convolution C. Derive the exact kernel of
  [E, C†C] and test whether the requested Schatten-1 decay is even
  compatible with the detector regularity. If the model fails, kill SC1
  before touching Lean.

second falsifier
  finite time-frequency/Sonin intersection model: compare the signed full
  remainder with the sum of its outer branches. If cancellation disappears
  when the two branches are coupled, the route reverts to the older prolate
  remainder problem.

anti-circularity
  The estimate may use support, convolution, Sonin projection, Fourier
  transport, and finite visible-prime data. It may not use qw >= 0,
  qw < 0, SourceRH, healthy detector data, or a universal Weil gate.
```

## 6. Staged obligations and kill rules

### SC0 — provenance and exact decomposition

Already green at the identity level. The source theorem and the two outer
trace-class theorems must be instantiated with one `owner`, one `lambda`, one
support interval, and one global basis. This is a formal/interface check, not
new mathematics.

### SC1 — half-line commutator model — PASSED on paper

The paper derivation is recorded in
[1429](../proofs/1429_r3_sonin_commutator_halfline_model.md). For a smooth
compact convolution kernel `h`, the half-line commutator has two off-diagonal
Hankel kernels `h(x+u)` and `h(-(x+u))` on the positive quadrant. Smooth
extension to `R^2`, followed by a harmonic-oscillator Sobolev factorization,
proves that each corner operator is trace class. The detector kernel
`g.convolutionSquare.test` satisfies the required compact-smooth and Hermitian
hypotheses by the committed source API.

This is a theorem-shaped S1 result, not a finite-grid observation. The model
distinguishes:

- raw half-line commutator;
- commutator of the positive square `C†C`;
- the signed outer-pair subtraction.

SC1 therefore passes. It also gives the correct negative information: a
half-line boundary alone cannot be the R3 obstruction. The remaining estimate
must control the Hardy-transport/interior Sonin correction. The paper lemma is
not yet a Lean theorem and does not imply the actual Sonin commutator is trace
class.

### SC2-unit — fixed unit scale — FORMAL

The source already contains a stronger fixed-scale result than the paper model:
`sourceThreeBranchCommutator_unit_isTraceClassAlong` in
[`CCM24UnitScaleStrictAngle.lean`](../../ConnesWeilRH/Source/CCM25Concrete/CCM24UnitScaleStrictAngle.lean)
proves trace-classness along every named global basis, after the exact
`sourceSoninCommutator_eq_threeBranch` identity is applied. Its input is the
formal unit-scale summability theorem for
`sourceProlateHilbertSchmidtFactor`; it is not an axiom and does not use a
Weil sign or RH.

Thus the unit-scale instance of the coupled commutator is no longer an open
trace-legality question. This does **not** prove the moving-scale theorem: the
unit result is explicitly a fixed-source endpoint, while R3 needs the scale and
cutoff/source transport used by the G8 ledger.

### SC2 — moving-scale Sonin lift

Transfer the model estimate and the formal unit-scale theorem to the actual
source Sonin carrier at moving scale. The lift must
use the committed Hardy/Sonin geometry and the source support hypotheses. F1's
tail estimate is only a starting antiresonance inequality; it is not yet a
collective trace-ideal estimate.

### SC3 — signed source remainder

Prove either direct trace-classness of the Sonin commutator or a complete
signed estimate for the full remainder. Then combine it with the formal outer
pair identity. This is the first stage that can legitimately replace the
current raw `sourceProlateHilbertSchmidtFactor` summability gate.

### SC4 — cutoff/source transport

Identify the resulting signed trace with the exact G8 cutoff ledger, including
the canonical finite-prime family and the same-owner endpoint. A trace theorem
for the wrong response or a different basis is not an R3 result.

### SC5 — readback and RH composition

Produce `G8SameOwnerReadbackData` for `ofCompactLogTest g`. The existing
formal chain then gives `qw >= 0` for the same detector, contradicts the
already formal `qw < 0` detector construction, and reaches `SourceRH`.
SC5 is composition after the analytic work; it is not evidence that SC1–SC4
are feasible.

Kill rules are binding:

1. A half-line model failure under the exact detector regularity kills the
   unqualified commutator candidate.
2. An HS estimate without a second HS factor, nuclear-kernel bound, or signed
   cancellation theorem does not count as progress toward trace-classness.
3. A proof that changes `sourceTest`, the selected owner, the canonical finite
   prime family, or the G8 basis is a route mismatch.
4. A use of any Weil sign, RH, healthy-detector proposition, or universal
   positivity premise is circular and stops the candidate.
5. If `K_b` only renames scale and supplies no summability or cancellation
   estimate, it is marked nonproductive rather than promoted.

## 7. Reachability judgment

Conditionally, this candidate can still feed the RH-reachable R3 contract:

```text
SC1-SC4
  -> exact signed G8 same-owner readback
  -> G8SameOwnerReadbackData
  -> qw >= 0 on the tower-selected detector
  -> existing same-detector contradiction
  -> SourceRH
```

That is a logical reachability statement, not a feasibility claim. The
candidate removes one structural obstacle — treating a coupled signed object
as a positive square — but it does not yet supply the decisive trace estimate.
The global source-leg issue, cutoff/source compatibility, and the final
trace-to-`qw` readback remain open until SC3–SC5 are actually proved.

**Current verdict:** `SC1-PASS / SC2(unit)-FORMAL /
SC2(scale)-OPEN`. The next allowed action is the doubled-shift transport
audit in [014](014_r3_doubled_shift_sonin_transport.md): express the actual
intersection-projection commutator as the passed half-line pieces plus the
Hardy-transport correction, then test the correction for an S1 estimate in the
project's basis-compatible trace witness. No R3 or RH result is claimed.
