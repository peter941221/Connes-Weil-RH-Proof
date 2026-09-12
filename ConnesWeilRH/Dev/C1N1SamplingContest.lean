/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1SpectralOfflinePairing
import ConnesWeilRH.Dev.C1WeilCriterionEquivalence

/-!
# C1N1SamplingContest - the (star) sampling-contest brick, B1 leg

Build preregistration: docs/proofs/1356_brick_build_prg.md (statements
LOCKED there before any build log, law-42 discipline). This leaf carries
the B1 quartet-algebra leg and the B4 total-contest iff wiring
(s5): pure bookkeeping of the committed
spectral-side dictionary terms (spectralTerm, centeredXiCoordinate,
conjugateXiZero, hermitianPartner, oneSubXiZero, the committed
`laplaceAt_convolutionSquare` product identity of
C1HealthyYoshidaDetector, and the W4a pair lemmas of
C1SpectralHermitianPartner / the W4b split of C1SpectralOfflinePairing).

Design note (1356 s0b, F5): for COMPLEX test functions the quartet
{rho, star rho, 1 - rho, 1 - star rho} splits as TWO W4a partner-pairs,
and the two pairs contribute 2 * Re[G_F(w)] and 2 * Re[G_F(star w)],
which need not agree. The pair-split form below is the general-correct
form; the 4-fold scalar shorthand of record 1345 is its real-g
specialization. No committed adjudication is contradicted.

Proves no inequality about zeta; certifies nothing toward the gate.
The (star) <-> gate iff (B4) is a separate locked addendum statement.
RH is not claimed anywhere.
-/

namespace ConnesWeilRH
namespace Source
namespace C1N1SamplingContest

open CC20YoshidaNearZeros
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1SpectralOnlineSplit
open C1SpectralHermitianPartner
open C1HealthyYoshidaDetector
open C1SpectralQwAssembly
open C1SpectralSummability

noncomputable section

/-! ### Partner/conjugate transport bookkeeping -/

/-- The Hermitian companion of the conjugated zero is the functional-equation
image of the zero: the quartet is two W4a pairs. -/
theorem hermitianPartner_conjugateXiZero
    (rho : sourceNontrivialZeroSet) :
    hermitianPartner (conjugateXiZero rho) = oneSubXiZero rho := by
  apply Subtype.ext
  simp [hermitianPartner_coe, conjugateXiZero_coe, oneSubXiZero_coe]

/-- The conjugation transport preserves the on-line set. -/
theorem conjugateXiZero_mem_onLineZeroSet
    (rho : sourceNontrivialZeroSet) (h : rho ∈ onLineZeroSet) :
    conjugateXiZero rho ∈ onLineZeroSet := by
  simpa [onLineZeroSet, conjugateXiZero_coe, Complex.ext_iff] using h

/-! ### B1a: the exact quartet real-part sum -/

/-- **B1a (quartet pair-split).**  The four members of the quartet of an
off-line zero contribute, in real part, exactly twice the real part of the
representative plus twice the real part of its conjugate. -/
theorem quadOrbit_re_sum (g : CompactLogTest)
    (rho : sourceNontrivialZeroSet) :
    (spectralTerm g.convolutionSquare rho +
        spectralTerm g.convolutionSquare (hermitianPartner rho) +
        spectralTerm g.convolutionSquare (conjugateXiZero rho) +
        spectralTerm g.convolutionSquare (oneSubXiZero rho)).re =
      2 * (spectralTerm g.convolutionSquare rho).re +
        2 * (spectralTerm g.convolutionSquare (conjugateXiZero rho)).re := by
  -- hpair2 mentions `part (conj rho)`; transport it to `onesub rho`.
  have heq :
      spectralTerm g.convolutionSquare
          (hermitianPartner (conjugateXiZero rho)) =
        spectralTerm g.convolutionSquare (oneSubXiZero rho) :=
    congrArg (spectralTerm g.convolutionSquare)
      (hermitianPartner_conjugateXiZero rho)
  -- The committed W4a pair lemmas list the partner first; re-orient.
  have hpair1 :
      (spectralTerm g.convolutionSquare rho +
          spectralTerm g.convolutionSquare (hermitianPartner rho)).re =
        2 * (spectralTerm g.convolutionSquare rho).re := by
    rw [add_comm, spectralTerm_convolutionSquare_pair_re_sum_uncond]
  have hpair2 :
      (spectralTerm g.convolutionSquare (conjugateXiZero rho) +
          spectralTerm g.convolutionSquare (oneSubXiZero rho)).re =
        2 * (spectralTerm g.convolutionSquare (conjugateXiZero rho)).re := by
    rw [add_comm, ← heq,
      spectralTerm_convolutionSquare_pair_re_sum_uncond]
  have hsplit :
      (spectralTerm g.convolutionSquare rho +
          spectralTerm g.convolutionSquare (hermitianPartner rho) +
          spectralTerm g.convolutionSquare (conjugateXiZero rho) +
          spectralTerm g.convolutionSquare (oneSubXiZero rho)).re =
        (spectralTerm g.convolutionSquare rho +
            spectralTerm g.convolutionSquare (hermitianPartner rho)).re +
          (spectralTerm g.convolutionSquare (conjugateXiZero rho) +
              spectralTerm g.convolutionSquare (oneSubXiZero rho)).re := by
    simp only [Complex.add_re]
    ring
  rw [hsplit, hpair1, hpair2]

/-! ### B1b: per-term unfoldings against the committed product identity -/

/-- The real part of one spectral term is multiplicity times the real part of
the square-laplace value at the centered coordinate. -/
theorem spectralTerm_re_unfold (g : CompactLogTest)
    (rho : sourceNontrivialZeroSet) :
    (spectralTerm g.convolutionSquare rho).re =
      (xiMultiplicity rho : ℝ) *
        (CompactLogTest.laplaceAt g.convolutionSquare
          (centeredXiCoordinate rho)).re := by
  simp [spectralTerm]

/-- Norm readout of the committed Hermitian square law. -/
theorem norm_laplaceAt_convolutionSquare (g : CompactLogTest) (s : ℂ) :
    ‖CompactLogTest.laplaceAt g.convolutionSquare s‖ =
      ‖CompactLogTest.laplaceAt g (-star s)‖ *
        ‖CompactLogTest.laplaceAt g s‖ := by
  rw [laplaceAt_convolutionSquare]
  simp

/-- The norm of one spectral term factors through the root transform. -/
theorem spectralTerm_norm_product (g : CompactLogTest)
    (rho : sourceNontrivialZeroSet) :
    ‖spectralTerm g.convolutionSquare rho‖ =
      (xiMultiplicity rho : ℝ) *
        ‖CompactLogTest.laplaceAt g (centeredXiCoordinate rho)‖ *
        ‖CompactLogTest.laplaceAt g
          (-star (centeredXiCoordinate rho))‖ := by
  have hprod :
      ‖CompactLogTest.laplaceAt g.convolutionSquare
          (centeredXiCoordinate rho)‖ =
        ‖CompactLogTest.laplaceAt g
          (-star (centeredXiCoordinate rho))‖ *
          ‖CompactLogTest.laplaceAt g (centeredXiCoordinate rho)‖ :=
    norm_laplaceAt_convolutionSquare g (centeredXiCoordinate rho)
  calc ‖spectralTerm g.convolutionSquare rho‖
      = (xiMultiplicity rho : ℝ) *
          ‖CompactLogTest.laplaceAt g.convolutionSquare
            (centeredXiCoordinate rho)‖ := by
        simp [spectralTerm]
    _ = (xiMultiplicity rho : ℝ) *
          (‖CompactLogTest.laplaceAt g
            (-star (centeredXiCoordinate rho))‖ *
            ‖CompactLogTest.laplaceAt g (centeredXiCoordinate rho)‖) := by
        rw [hprod]
    _ = _ := by ring

/-! ### B1c: the contest-reusable absolute-value bound -/

/-- The absolute real quartet mass is bounded by twice the norms of the two
independent pair representatives - the quantity the (star) contest must
dominate, in its general-correct pair-split form. -/
theorem quadOrbit_re_sum_abs_le (g : CompactLogTest)
    (rho : sourceNontrivialZeroSet) :
    |(spectralTerm g.convolutionSquare rho +
        spectralTerm g.convolutionSquare (hermitianPartner rho) +
        spectralTerm g.convolutionSquare (conjugateXiZero rho) +
        spectralTerm g.convolutionSquare (oneSubXiZero rho)).re| ≤
      2 * ‖spectralTerm g.convolutionSquare rho‖ +
        2 * ‖spectralTerm g.convolutionSquare (conjugateXiZero rho)‖ := by
  rw [quadOrbit_re_sum]
  calc |2 * (spectralTerm g.convolutionSquare rho).re +
        2 * (spectralTerm g.convolutionSquare (conjugateXiZero rho)).re| ≤
      |2 * (spectralTerm g.convolutionSquare rho).re| +
          |2 * (spectralTerm g.convolutionSquare
            (conjugateXiZero rho)).re| := abs_add_le _ _
    _ = 2 * |(spectralTerm g.convolutionSquare rho).re| +
          2 * |(spectralTerm g.convolutionSquare
            (conjugateXiZero rho)).re| := by
        simp only [abs_mul,
          abs_of_pos (show (0 : ℝ) < 2 from by norm_num)]
    _ ≤ 2 * ‖spectralTerm g.convolutionSquare rho‖ +
          2 * ‖spectralTerm g.convolutionSquare (conjugateXiZero rho)‖ := by
        refine add_le_add (mul_le_mul_of_nonneg_left ?_
            (show (0 : ℝ) ≤ 2 from by norm_num))
          (mul_le_mul_of_nonneg_left ?_
            (show (0 : ℝ) ≤ 2 from by norm_num))
        · exact Complex.abs_re_le_norm _
        · exact Complex.abs_re_le_norm _

/-! ### B1d: on-line degeneration (sanity bridge to W1) -/

/-- On the critical line the centered coordinate is purely imaginary, so the
Hermitian partner coincides with the functional-equation image and the
quartet degenerates to the conjugate pair {iy, -iy}. -/
theorem centeredXiCoordinate_mul_I_onLine (rho : sourceNontrivialZeroSet)
    (h : rho ∈ onLineZeroSet) :
    (centeredXiCoordinate rho).re = 0 := by
  -- carrier real part on the line (same reduction as the mem lemma above)
  have hline : rho.1.re = (1 : ℝ) / 2 := by
    simpa [onLineZeroSet] using h
  simp only [centeredXiCoordinate, Complex.sub_re]
  rw [hline]
  norm_num

/-- The conjugate of an on-line zero lies on the line. -/
theorem conj_pair_onLine (rho : sourceNontrivialZeroSet)
    (h : rho ∈ onLineZeroSet) :
    conjugateXiZero rho ∈ onLineZeroSet :=
  conjugateXiZero_mem_onLineZeroSet rho h

/-! ### B4: the gate IS the total on-line-vs-off-line contest (1356 s5)

Window-free by design: the per-window (star) of record 1345 is B2/B3
science and needs C6/NLLE-v2 (1353 two-limb grading). Nothing below
adds analysis - the balance equality and the on-line nonnegativity are
committed (C1SpectralQwAssembly.lean:65-66,
C1SpectralOnlineSplit.lean:88-90), and B4.3 is a transitivity over the
committed d767a1d equivalence. -/

/-- **B4.1 (per-test contest balance, unconditional).** The Weil value
of a test is nonnegative iff its on-line gain covers its off-line loss. -/
theorem contest_balance_iff_qw_nonneg (g : CompactLogTest) :
    0 ≤ C1SameOwnerWeil.qw g ↔
      onLineSpectralMass g ≥ max 0 (- offLineSpectralMass g) := by
  have hnonneg : 0 ≤ onLineSpectralMass g :=
    onLineSpectralMass_nonnegative_of_summable g
      (spectralSummableProp g.convolutionSquare)
  rw [qw_eq_onLineSpectralMass_add_offLineSpectralMass]
  rcases lt_trichotomy (offLineSpectralMass g) 0 with hlt | heq | hgt
  · rw [max_eq_right (show (0 : ℝ) ≤ -offLineSpectralMass g by linarith)]
    exact ⟨fun e => by linarith, fun e => by linarith⟩
  · rw [heq, show (-0 : ℝ) = 0 by norm_num, max_eq_left (le_refl 0)]
    exact ⟨fun _ => by linarith, fun _ => by linarith⟩
  · rw [max_eq_left (show (- offLineSpectralMass g) ≤ 0 by linarith)]
    exact ⟨fun _ => by linarith, fun _ => by linarith⟩

/-- **B4.2 (class iff).** The total-contest form IS the surviving gate
of record 1341, pointwise through B4.1. -/
theorem contestForm_iff_weilCriterion :
    (∀ g : CompactLogTest,
        CC20VanishesOn C1.healthyCC20TestSpace
          cc20TripleFiniteVanishingSet g →
          onLineSpectralMass g ≥ max 0 (- offLineSpectralMass g)) ↔
      (∀ g : CompactLogTest,
        CC20VanishesOn C1.healthyCC20TestSpace
          cc20TripleFiniteVanishingSet g →
          0 ≤ C1SameOwnerWeil.qw g) :=
  forall₂_congr (fun g _hg => (contest_balance_iff_qw_nonneg g).symm)

/-- **B4.3 (contest iff SourceRH).** Reassembly only: B4.2 composed
with the committed Weil-criterion equivalence (d767a1d). No new
direction, no inequality about zeta, RH not claimed. -/
theorem contestForm_iff_sourceRH :
    (∀ g : CompactLogTest,
        CC20VanishesOn C1.healthyCC20TestSpace
          cc20TripleFiniteVanishingSet g →
          onLineSpectralMass g ≥ max 0 (- offLineSpectralMass g)) ↔
      RHDefinitionBridge.standard.SourceRH :=
  contestForm_iff_weilCriterion.trans
    C1WeilCriterionEquivalence.weilCriterion_iff_sourceRH

end
end C1N1SamplingContest
end Source
end ConnesWeilRH
