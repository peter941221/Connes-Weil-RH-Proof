# 1040 - hqw sign attack: the single open analytic obligation

Date: 2026-08-24.

Status: **Stage 1: W1, W2, and the exact W3 complement split LANDED;
no RH claim.** After the 2026-08-24 refutations (bare-operator
FRONTIER-HS, P2 bulk-subtracted readback), both live producers of
`healthyCriterionState` reduce to one open statement — the
vanishing-test sign. This document fixes its exact shape, lays out the
term-by-term structure of both sides of the closed Gate-2 identity, and
defines the Lean lemma targets and bounded kill-tests. W4 (residual control)
and the genuine off-line conjugate pairing remain open.

## 1. The obligation (exact shape)

```lean
hqw : forall (g : CompactLogTest),
  CC20VanishesOn C1.healthyCC20TestSpace F g ->
    0 <= C1SameOwnerWeil.qw g
```

- Consumer: `frontierStatus_healthyCriterionState_of_rankOneCorrection`
  (`Dev/C1Stage3FrontierStatus.lean:165`) takes `hqw` as its only
  per-test input (plus one fixed carrier vector `d0`).
- `CC20VanishesOn C F g` is Mellin vanishing at each designated point:
  `forall p in F, C.mellinAt g (criticalVanishingPointValue p) = 0`
  (`Source/CC20TestSpace.lean:28`).
- `qw g = psi g.convolutionSquare` and
  `psi F = poleTerm F - archimedeanTerm F - finitePrimeSum F`
  (`Dev/C1SameOwnerWeil.lean:190-199`).

Both live routes land here: the rank-one route consumes `hqw` directly
(sign-transparent), and the projection-owner route derives it from
positivity plus kernel compatibility (see 1039 and section 6 below).

## 2. What is already a theorem (both sides of the sign)

Gate 2 is closed, so the obligation has two exact, axiom-clean faces:

```text
qw g = spectralWeilValue g.convolutionSquare
  (Dev/C1CenterTwoCriterionBridge.lean:28, qw_eq_spectralWeilValue_centerTwo,
   unconditional, no hypothesis)

healthyCriterionState F <-> (forall g vanishing on F, 0 <= qw g)
  (Dev/C1CenterTwoCriterionBridge.lean:39,
   healthyCriterionState_iff_all_vanishing_spectral_nonnegative)
```

Arithmetic face (three-term readback, also a theorem,
`Dev/C1CrossingEulerLogReadback.lean:228`):

```text
qw g = poleTerm g^2 - archimedeanTerm g^2
       - Re (canonical Euler-log carrier trace)
     = poleTerm g^2 - archimedeanTerm g^2 - finitePrimeSum g^2
  (carrier trace = finitePrimeSum:
   Dev/C1CrossingEulerLogReadback.lean:211)
```

Spectral face (`Dev/C1SpectralWeil.lean`):

```text
spectralWeilValue F = (tsum fun rho => spectralTerm F rho).re
spectralTerm F rho = m(rho) * laplaceAt F (rho - 1/2)
  m(rho) = xiMultiplicity rho >= 0        (nat multiplicity)
  (C1SpectralWeil.lean:112-118)
```

What is NOT built in: the summability machine only supplies the norm
majorant `spectralNormTerm >= 0` (`C1SpectralWeil.lean:123`). The real
part of the termwise sum carries no structural sign. The sign is the
content; there is no shortcut through the definitions.

## 3. Term-by-term sign audit (arithmetic face)

For `F = g.convolutionSquare` (written `g^2`), on the support window
`[a, c]` containing `support g.test`:

```text
A. poleTerm g^2 = Re[LaplaceAt g^2 (1/2) + LaplaceAt g^2 (-1/2)]
   (C1SameOwnerWeil.lean:31)
   - Structurally the pole pairing of the square:
     SourceEvaluationData.polePairing g =
       Re[mellinAt g^2 (I/2)] + Re[mellinAt g^2 (-I/2)]
     (Source/AnalyticCoreBase.lean:487, rfl-level identity).
   - Sign: no repo lemma pins it. It is a symmetric pair of evaluations
     of the square's transform, so the natural mechanism is a
     reflection/Plancherel factorization (section 5, lemma W1/W2).

B. archimedeanTerm g^2 = Re[(log 4pi + gamma) * (g^2).test 0
   + integral_{y>0} archimedeanIntegrand g^2 y]
   (C1SameOwnerWeil.lean:61)
   - The prefactor log(4pi)+gamma > 0; (g^2).test 0 and the integral
     against the Gamma-type denominator carry no fixed sign.
   - Realistic role: a BOUNDED perturbation, not a sign source.
     Target an estimate |B| <= C * (on-line spectral mass).

C. finitePrimeSum g^2 = sum_n Re[Lambda(n) n^{-1/2}
     ((g^2).test (log n) + (g^2).test (-log n))]
   over the finite selected support (C1SameOwnerWeil.lean:36-46, 161).
   - Lambda(n) >= 0 but the test samples are signed; no termwise sign.
   - Realistic role: bounded perturbation on a FINITE index set; a
     Cauchy-Schwarz bound against the carrier norm is plausible.
```

No arithmetic-face term has an individually proven sign. Any attack
that does not use the vanishing hypothesis is dead on arrival, because
qw on a general (non-vanishing) test is signed: the vanishing input is
what couples the three terms to the spectral face.

## 4. Term-by-term sign audit (spectral face) - where the mechanism lives

The square law ALREADY EXISTS in the repo, in Hermitian form and
stronger than the classical reflection guess:

```text
laplaceAt g.convolutionSquare s
  = conj (laplaceAt g (-(conj s))) * laplaceAt g s
  (Dev/C1HealthyYoshidaDetector.lean:48, laplaceAt_convolutionSquare;
   built from laplaceAt_convolution,
   Source/CC20YoshidaConvolution.lean:431 + laplaceAt_involution)
```

Consequence for an ON-LINE zero `rho = 1/2 + i*gamma`: the centered
coordinate `w = rho - 1/2 = i*gamma` is purely imaginary, so
`-(conj w) = w` and the law collapses to

```text
laplaceAt g^2 (i*gamma) = conj (L_g (i*gamma)) * L_g (i*gamma)
                        = |L_g (i*gamma)|^2 >= 0
```

- No reality symmetry of the test space is needed: the Hermitian
  structure of `convolutionSquare` (g convolved with its involution)
  supplies the conjugation.  This kills the feared W2 dependency.
- Therefore `Re[spectralTerm g^2 rho] = m(rho) * |L_g (i*gamma)|^2 >= 0`
  TERMWISE for on-line rho, unconditionally - one rewrite chain away
  from the existing square law plus `C1SpectralWeil.lean:112`.

For an OFF-LINE zero `rho` (w = rho - 1/2 has Re w != 0): the law
gives `L_{g^2}(w) = conj (L_g (-(conj w))) * L_g (w)` - a product of
two UNRELATED transform values; no termwise sign.  The reflection
partner needed by the Hermitian law has centered coordinate `-(conj w)`.
The existing `oneSubXiZero rho` transport (C1SpectralWeil.lean:54-104,
multiplicity symmetric) gives centered coordinate `-w`, not `-(conj w)`.
A separate conjugate-zero transport and the exact pairing structure must
therefore be derived, not assumed; the naive `2 Re[...]` collapse does NOT
follow automatically.

This is exactly Weil's criterion structure, in the repo's own
normalization (`centeredXiCoordinate`, `C1SpectralWeil.lean:107`):

- The on-line part of the spectral sum is a PROVEN-nonneg block
  (W1, now landed).
- The off-line terms are the genuine RH content.  The vanishing set F
  (finite: `cc20TripleFiniteVanishingSet`) kills the arithmetic pole pair,
  not source spectral zeros; the remaining off-line terms must be controlled
  by an inequality, not by an assumed pairing identity.

## 5. First Lean lemma targets (small, falsifiable, in dependency order)

```text
W1  ON-LINE TERMWISE NONNEG: LANDED 2026-08-24 (commit 20af271,
    Dev/C1SpectralOnlineNonneg.lean,
    spectralTerm_convolutionSquare_nonneg_of_onLine, axiom-clean).
    For rho on the critical line the term is m(rho) * |L_g(w)|^2 >= 0,
    unconditional in g, no vanishing input, no RH claim.

W2  VANISHING TRANSFER: LANDED 2026-08-24 (axiom-clean,
    `Dev/C1SpectralVanishingTransfer.lean`).  The theorem
    `laplaceAt_half_eq_zero_of_vanishesOn_of_mem_half` transports the
    `CC20TestSpace.mellinAt` vanishing at `1 / 2` to the same owner's
    `CompactLogTest.laplaceAt`; the route-facing Mellin readback is also
    explicit.  The Hermitian square law then gives zero at both `+1 / 2`
    and `-1 / 2`, and
    `qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_of_mem_half`
    removes the pole term.  This is an arithmetic-node result, not spectral
    zero cancellation.

W3  EXACT COMPLEMENT SPLIT: LANDED 2026-08-24 (axiom-clean,
    `Dev/C1SpectralOnlineSplit.lean`).  For a root `g` with
    `SpectralSummable g.convolutionSquare`,
    `spectralWeilValue g.convolutionSquare` equals the named critical-line
    mass plus the named off-line residual.  The critical-line mass is
    nonnegative by W1.  The module also records that `oneSubXiZero` reflects
    the centered coordinate and preserves multiplicity, but it does not
    identify this map with the conjugate-zero transport needed for a paired
    off-line formula.  That conjugate pairing remains open.

W4  RESIDUAL CONTROL (the deep step):
    off-line residual + (-poleTerm g^2) bounded by the on-line mass
    for g vanishing on F (arithmetic face: |B| + |C| from section 3
    enter here through the Gate-2 identity).  No prior evidence yet
    beyond the narrow root (section 7).
```

The exact complement split is sufficient to name the residual for W4 without
asserting a false `2 * Re` pairing.  W4 must still establish the required
bound for this residual on the vanishing-test subspace.

## 6. Relation to the projection-owner route (Prong C)

The projection route derives the sign from positivity of the trace
object once `||kernelInsertionDefect|| -> 0` along cutoffs
(`Dev/C1Stage3ProjectionDefectBounds.lean:352`, sufficiency already
proved).  Prong B and Prong C are complementary:

```text
Prong B (this doc): split the sign into proven-positive blocks
  + named residual; attack the residual analytically.
Prong C: derive the whole sign from operator positivity; attack
  kernel compatibility instead.
```

If W4 lands, the off-line residual object should be cross-checked
against the projection route's D1 defect - both are "the part of the
world that knows about off-line zeros".

## 7. Numerical priors and bounded kill-tests (discipline: bounded only)

Priors already on file:

- `qw narrowArchRoot ~= +5.82e48 +- 8.5e46 > 0` (kill-test 1016 era,
  `MEMORY.MD:197,225`), and this one is backed by a Lean THEOREM:
  `narrowArchRoot_qw_pos` (`Dev/C1LaneRStrictness.lean:260`), rigorous
  lower bound +1.26e48.  One explicit vanishing test is proven
  positive; the gap is ALL vanishing tests.

Proposed bounded kill-tests (each one script, bounded window, no new
machinery):

```text
KT-1040a  Second witness, different shape: evaluate qw on a second
          F-vanishing test from a different bump family (e.g. shifted
          center, or g1 + c*g2 combo - vanishing is linear, combos of
          F-vanishing tests still vanish).  GREEN = both positive.

KT-1040b  Adversarial probe for W4: minimize the on-line spectral mass
          over a bounded family of F-vanishing tests (shrink the
          on-line |L_g(i gamma)| coefficients) and watch qw.  If qw
          stays positive as on-line mass -> small, W4 has slack;
          if it tracks toward 0 or below, W4 is tight/false and the
          attack must find the compensating term first.
```

Both are evidence for steering only; neither replaces W1-W5.

## 8. Freeze-discipline note

Every lemma above must name its direct consumer on the
`normalizedSelectedFinalRouteDetectorCriterionCoverageRoot` chain
before landing: W1 + W2 feed W3; W3 feeds W4 (Prong B) or the
projection bridge cross-check (section 6).  Lemmas that feed nothing
on the chain do not get committed.
