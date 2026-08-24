# 1040 - hqw sign attack: the single open analytic obligation

Date: 2026-08-24.

Status: **Stage 2: W1, W2, W3, W4a (conjugate transport), the W4b-pairing
tsum split, the W5-lite reduction ledger, and the real-test phase interface
LANDED; KT-1040a/b/c RUN GREEN;
no RH claim.** After the 2026-08-24
refutations (bare-operator FRONTIER-HS, P2 bulk-subtracted readback), both live
producers of `healthyCriterionState` reduce to one open statement — the
vanishing-test sign. This document fixes its exact shape, lays out the
term-by-term structure of both sides of the closed Gate-2 identity, and
defines the Lean lemma targets and bounded kill-tests. What remains open is
the W4b analytic bound itself (the residual versus the on-line mass on the
F-vanishing subspace).  KT-1040c narrows WHERE that bound must live: the
modulus-form sufficient condition is already false on the bounded family;
the attack surface is the phase structure of the Hermitian pair product.

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

W4a CONJUGATE TRANSPORT: LANDED 2026-08-25 (axiom-clean,
    `Dev/C1XiConjugation.lean` + `Dev/C1SpectralHermitianPartner.lean`).
    The partner `rho |-> 1 - star rho` has centered coordinate `-star w`,
    is an involution, multiplicity survives the conjugation leg
    (`analyticOrderAt_completedRiemannXi_conj_symmetric` via iterated-derivative
    commutation), and a zero plus its partner contribute exactly
    `2 * Re` of either term (`spectralTerm_convolutionSquare_pair_re_sum_uncond`).

W4b-pairing  TSUM PAIR DECOMPOSITION: LANDED 2026-08-25 (axiom-clean,
    `Dev/C1SpectralOfflinePairing.lean`).  The off-line residual of the W3
    split equals twice the real part of the right-half (positive centered
    real part) spectral sum: `hermitianPartner` swaps the sign halves and is
    an involution, so the whole argument stays at indicator level on the
    index type — no orbit quotient, no termwise off-line sign asserted
    (`offLineSpectralMass_eq_two_mul_re_tsum_rightHalf`).

W5-lite REDUCTION LEDGER: LANDED 2026-08-25 (axiom-clean,
    `Dev/C1SpectralQwAssembly.lean`).  The ledger is assembled and the hqw
    obligation is REDUCED to one named inequality, in two interchangeable
    shapes:
      `hqw_of_forall_vanishing_rightHalf_bound`: hqw follows if, for every
        F-vanishing g,  Re (rightHalfSpectralSum g) >= -(1/2) * onLineSpectralMass g.
      `hqw_of_forall_vanishing_offLineNormMass_le`: the modulus form, if
        offLineNormMass g <= onLineSpectralMass g.
    Both reductions are pure bookkeeping — absolute summability
    (`summable_spectralNormTerm`, the shell argument read out for the
    scalar majorant) is unconditional, so NO vanishing input is consumed;
    the F-vanishing subspace enters only where the inequality premise is
    proved.  The module also binds the ledger to the W2 arithmetic face
    (`onLine_add_offLine_eq_neg_archimedeanTerm_sub_finitePrimeSum`), the
    identity a W4b-bound attack from the arithmetic side must close.
    KT-1040c below shows the modulus-form premise is FALSE on the bounded
    witness family — the live target is the right-half Re form.

W4b-PHASE INTERFACE: LANDED 2026-08-25 (axiom-clean,
    `Dev/C1SpectralRealPair.lean`, Build #20: 3614 jobs).  For a pointwise-real
    compact-log test, the leaf proves the conjugation transport
    `laplaceAt_star`, the Hermitian square collapse
    `laplaceAt_convolutionSquare_of_isReal`, and the explicit real-part
    readback
    `spectralTerm_convolutionSquare_re_of_isReal`:

      Re(spectralTerm(g^2,rho))
        = m(rho) * Re(L_g(-w_rho) * L_g(w_rho)).

    It also exposes the existing origin-mass theorem as
    `norm_convolutionSquare_test_zero_eq_integral_normSq`, and names the
    multiplicity-weighted phase kernel `rightHalfPhaseKernel`.  The new
    tsum-level readback is:

      Re(rightHalfSpectralSum g)
        = tsum rho, 1_rightHalf(rho) * rightHalfPhaseKernel(g,rho)

    via `rightHalfSpectralSum_re_eq_tsum_indicator_phase`.  The restricted
    analytic target is now named
    `rightHalfPhaseBound_onRealVanishing`, and
    `rightHalfPhaseBound_onRealVanishing_iff_spectral` proves that it is only
    a change of presentation from the original right-half bound on real
    vanishing tests.  This is a formal phase interface and an exact
    total-series identity.  It does NOT prove the missing off-origin
    autocorrelation bound or the W4b inequality; those remain analytic
    obligations.

W4  RESIDUAL CONTROL (the deep step, REMAINS OPEN):
    off-line residual + (-poleTerm g^2) bounded by the on-line mass
    for g vanishing on F (arithmetic face: |B| + |C| from section 3
    enter here through the Gate-2 identity).  On the pointwise-real
    subspace, the remaining target can be rewritten using the new readback
    as the lower bound

      tsum rho, 1_rightHalf(rho) * rightHalfPhaseKernel(g,rho)
        >= -(1/2) * onLineSpectralMass(g).

    This rewrite does not remove the analytic estimate, and the general
    `CompactLogTest` target remains the live W4b obligation.  Evidence beyond
    the narrow root: KT-1040a/b/c below, all GREEN; KT-1040c additionally
    narrows the attack surface to the phase structure (the modulus route is
    dead).
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
KT-1040a  RUN 2026-08-25 (docs/proofs/1041_kt1040_probe.py): GREEN.
          Five wide F-vanishing witnesses (plateau and non-plateau
          profiles, widths 0.6-0.9, centers -1.5..1.5, one combo), every
          qw > 0 under int g^2 = 1: min +1.096 (smooth wide), max +3.63.
          All built with the SAME triple operator as the narrow root,
          P(D)h with P(D) = D(D+1/2)(D+1), at widths where prime powers
          ARE visible (n <= 121).  Structural readback: qw is determined
          by the autocorrelation, hence shift-invariant (the two plateau
          witnesses at different centers agree exactly); the archimedean
          integral piece carries the positivity (I_main ~ -6.5 under
          F(0) = 1), and the finite prime sum is the only adversarial
          term (up to +0.47 against qw on the widest test).

KT-1040b  RUN 2026-08-25 (same script): qw STAYS POSITIVE.
          SVD combinations of a 20-member basis kill the Fourier
          coefficients at the first K zero ordinates (kills verified to
          ~1e-15) for K = 1, 2, 4, 6, 8: qw ranges +3.18..+3.66 while
          the visible first-16 on-line pair mass drops 0.274 -> 0.038.
          No track toward 0: W4 has slack inside this bounded family.
          Caveat: the first 16 zeros only - tail mass uncontrolled, so
          this is steering evidence, not a bound.

KT-1040c  RUN 2026-08-25 (docs/proofs/1042_kt1040c_probe.py): GREEN,
          and it NARROWS THE W4b ATTACK SURFACE.  The first K zeta zeros
          are relocated synthetically to beta = 1/2 + delta (delta =
          0.01..0.49), each zero arriving with its three mirrors; the
          margin moves by Delta_j = 4 Re[conj(v_j) u_j] - 2|L(i gamma_j)|^2
          with u = L_g(delta + i gamma), v = L_g(-delta + i gamma)
          (square law + W4b-pairing + W1).  Across all 6 members,
          7 deltas, K = 1..16: min qw_hyp = +1.025 (never negative;
          2^19 spot check +1.025291).  Structural readbacks:
          (i) real-phase injections are nearly neutral (Delta ~ 0 for
          every member; the widest witness erodes only 0.07 at
          delta = 0.49) — the true phase of conj(v) u sits in the
          nonnegative sector on this family;
          (ii) the pair contribution 4 Re[conj(v) u] is shift-invariant
          in g (the translation factors e^{(delta+i gamma)c} and
          e^{(-delta-i gamma)c} cancel), matching the qw
          shift-invariance of KT-1040a;
          (iii) WARNING: the modulus amplification |v u| / |L|^2 grows
          exponentially in delta (up to 428x on the widest witness,
          ~1e20 on the SVD-kill member), and the phase-worst floor
          dips to -2.33: the modulus-form sufficient condition
          (offLineNormMass <= onLine mass) is FALSE on this family.
          W4b-bound must exploit the Hermitian phase structure, not
          termwise modulus control.
```

All three are evidence for steering only; none replaces W1-W5.

## 8. Freeze-discipline note

Every lemma above must name its direct consumer on the
`normalizedSelectedFinalRouteDetectorCriterionCoverageRoot` chain
before landing: W1 + W2 feed W3; W3 feeds W4 (Prong B) or the
projection bridge cross-check (section 6).  Lemmas that feed nothing
on the chain do not get committed.
