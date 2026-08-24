import ConnesWeilRH.Dev.C1SpectralOnlineSplit
import ConnesWeilRH.Dev.C1SpectralHermitianPartner

/-!
# C1SpectralOfflinePairing - the off-line residual as a right-half pair sum

W4a (`C1SpectralHermitianPartner`) proved that a zero `rho` and its Hermitian
partner `1 - star rho` carry equal analytic multiplicity and contribute exactly
twice the real part of either spectral term.  This leaf lifts that termwise
pair identity to the total off-line residual of the W3 split
(`C1SpectralOnlineSplit`): the off-line spectral mass equals twice the real
part of the tsum over the right half of the centered coordinate.

The half split is by the sign of `Re (centeredXiCoordinate rho)`: the partner
negates this sign (`centeredXiCoordinate_hermitianPartner`), so it swaps the
two halves, and it is an involution on the whole index set
(`hermitianPartner_involutive`).  Everything therefore stays at the level of
indicator functions on the whole index type: no orbit-quotient type is built,
and no termwise sign of an individual off-line term is asserted.

Consumer on the coverage chain: this is the named residual shape for W4
(off-line residual control, `docs/proofs/1040_hqw_sign_attack.md` section 5);
its analytic bound on the F-vanishing subspace is what assembles `hqw`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SpectralOfflinePairing

open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1SpectralOnlineSplit
open C1SpectralHermitianPartner

noncomputable section

/-! ### The sign split of the off-line index set -/

/-- The off-line zeros with strictly positive centered real part. -/
def rightHalfOffLine : Set sourceNontrivialZeroSet :=
  offLineZeroSet ∩ {rho | 0 < (centeredXiCoordinate rho).re}

/-- The off-line zeros with strictly negative centered real part. -/
def leftHalfOffLine : Set sourceNontrivialZeroSet :=
  offLineZeroSet ∩ {rho | (centeredXiCoordinate rho).re < 0}

/-- Real-part readout of the centered coordinate `rho - 1/2`. -/
theorem re_centeredXiCoordinate (rho : sourceNontrivialZeroSet) :
    (centeredXiCoordinate rho).re = rho.1.re - 1 / 2 := by
  simp [centeredXiCoordinate]

/-- The partner negates the centered real part. -/
theorem re_centeredXiCoordinate_hermitianPartner (rho : sourceNontrivialZeroSet) :
    (centeredXiCoordinate (hermitianPartner rho)).re =
      -(centeredXiCoordinate rho).re := by
  rw [centeredXiCoordinate_hermitianPartner]
  simp

/-- On-line membership is vanishing of the centered real part. -/
theorem mem_onLineZeroSet_iff (rho : sourceNontrivialZeroSet) :
    rho ∈ onLineZeroSet ↔ (centeredXiCoordinate rho).re = 0 := by
  simp [onLineZeroSet, re_centeredXiCoordinate, sub_eq_zero]

/-- An off-line zero has nonzero centered real part. -/
theorem re_centeredXiCoordinate_ne_zero_of_offLine
    {rho : sourceNontrivialZeroSet} (h : rho ∈ offLineZeroSet) :
    (centeredXiCoordinate rho).re ≠ 0 := by
  intro hzero
  refine h ?_
  rw [re_centeredXiCoordinate, sub_eq_zero] at hzero
  simpa [onLineZeroSet] using hzero

/-- The partner preserves off-line membership. -/
theorem hermitianPartner_mem_offLine_iff (rho : sourceNontrivialZeroSet) :
    hermitianPartner rho ∈ offLineZeroSet ↔ rho ∈ offLineZeroSet := by
  simp only [offLineZeroSet, Set.mem_compl_iff, mem_onLineZeroSet_iff,
    re_centeredXiCoordinate_hermitianPartner, neg_eq_zero]

/-- The partner maps the right half into the left half. -/
theorem hermitianPartner_mem_leftHalf_of_mem_rightHalf
    {rho : sourceNontrivialZeroSet} (h : rho ∈ rightHalfOffLine) :
    hermitianPartner rho ∈ leftHalfOffLine := by
  refine ⟨(hermitianPartner_mem_offLine_iff rho).mpr h.1, ?_⟩
  show (centeredXiCoordinate (hermitianPartner rho)).re < 0
  rw [re_centeredXiCoordinate_hermitianPartner]
  have hre : 0 < (centeredXiCoordinate rho).re := h.2
  linarith

/-- The partner maps the left half into the right half. -/
theorem hermitianPartner_mem_rightHalf_of_mem_leftHalf
    {rho : sourceNontrivialZeroSet} (h : rho ∈ leftHalfOffLine) :
    hermitianPartner rho ∈ rightHalfOffLine := by
  refine ⟨(hermitianPartner_mem_offLine_iff rho).mpr h.1, ?_⟩
  show 0 < (centeredXiCoordinate (hermitianPartner rho)).re
  rw [re_centeredXiCoordinate_hermitianPartner]
  have hre : (centeredXiCoordinate rho).re < 0 := h.2
  linarith

/-- Partner membership in the left half reads back as right-half membership. -/
theorem hermitianPartner_mem_leftHalf_iff (rho : sourceNontrivialZeroSet) :
    hermitianPartner rho ∈ leftHalfOffLine ↔ rho ∈ rightHalfOffLine := by
  constructor
  · intro hl
    have h := hermitianPartner_mem_rightHalf_of_mem_leftHalf hl
    rwa [hermitianPartner_involutive] at h
  · exact hermitianPartner_mem_leftHalf_of_mem_rightHalf

/-- The off-line set is the union of the two halves. -/
theorem offLineZeroSet_eq_union :
    offLineZeroSet = rightHalfOffLine ∪ leftHalfOffLine := by
  apply Set.eq_of_subset_of_subset
  · intro rho h
    rcases lt_or_gt_of_ne (re_centeredXiCoordinate_ne_zero_of_offLine h) with hlt | hgt
    · exact Or.inr ⟨h, hlt⟩
    · exact Or.inl ⟨h, hgt⟩
  · intro rho h
    rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h

theorem disjoint_rightHalf_leftHalf :
    Disjoint rightHalfOffLine leftHalfOffLine :=
  Set.disjoint_left.mpr fun rho hr hl =>
    lt_asymm (show 0 < (centeredXiCoordinate rho).re from hr.2)
      (show (centeredXiCoordinate rho).re < 0 from hl.2)

/-! ### The partner as an involution of the index set -/

/-- The partner involution as an equivalence of the whole index set. -/
def hermitianPartnerEquiv : sourceNontrivialZeroSet ≃ sourceNontrivialZeroSet where
  toFun := hermitianPartner
  invFun := hermitianPartner
  left_inv := hermitianPartner_involutive
  right_inv := hermitianPartner_involutive

/-! ### The pair sum -/

/-- **W4b-pairing.**  The off-line residual of the W3 spectral split is exactly
twice the real part of the right-half spectral sum: every off-line zero pairs
with its Hermitian partner `1 - star rho`, the pair contributes `2 * Re` of
either term (W4a), and the partner involution swaps the two sign halves.  No
termwise sign and no orbit-quotient construction is asserted; the right-half
sum is the named residual shape that W4's analytic bound must control. -/
theorem offLineSpectralMass_eq_two_mul_re_tsum_rightHalf
    (g : CompactLogTest) (hF : SpectralSummable g.convolutionSquare) :
    offLineSpectralMass g =
      2 * (∑' rho : sourceNontrivialZeroSet,
            Set.indicator rightHalfOffLine
              (spectralTerm g.convolutionSquare) rho).re := by
  have hsumr : Summable (Set.indicator rightHalfOffLine
      (spectralTerm g.convolutionSquare)) := hF.indicator rightHalfOffLine
  have hsuml : Summable (Set.indicator leftHalfOffLine
      (spectralTerm g.convolutionSquare)) := hF.indicator leftHalfOffLine
  -- Step 1: split the off-line indicator sum into its two halves.
  have hsplit : (∑' rho : sourceNontrivialZeroSet, offLineSpectralTerm g rho) =
      ((∑' rho : sourceNontrivialZeroSet,
          Set.indicator rightHalfOffLine (spectralTerm g.convolutionSquare) rho) +
        (∑' rho : sourceNontrivialZeroSet,
          Set.indicator leftHalfOffLine (spectralTerm g.convolutionSquare) rho)) := by
    have hfun : (fun rho : sourceNontrivialZeroSet => offLineSpectralTerm g rho) =
        fun rho : sourceNontrivialZeroSet =>
          Set.indicator rightHalfOffLine (spectralTerm g.convolutionSquare) rho +
            Set.indicator leftHalfOffLine (spectralTerm g.convolutionSquare) rho := by
      funext rho
      unfold offLineSpectralTerm
      rw [offLineZeroSet_eq_union,
        Set.indicator_union_of_disjoint disjoint_rightHalf_leftHalf]
    rw [hfun, (hsumr.hasSum.add hsuml.hasSum).tsum_eq]
  -- Step 2: the left-half real part equals the right-half real part, by the
  -- partner reindex and the W4a conjugate pair identity.
  have hleft : (∑' rho : sourceNontrivialZeroSet,
      Set.indicator leftHalfOffLine (spectralTerm g.convolutionSquare) rho).re =
      (∑' rho : sourceNontrivialZeroSet,
        Set.indicator rightHalfOffLine (spectralTerm g.convolutionSquare) rho).re := by
    rw [Complex.re_tsum hsuml, Complex.re_tsum hsumr,
      ← Equiv.tsum_eq hermitianPartnerEquiv
        (f := fun rho : sourceNontrivialZeroSet =>
            (Set.indicator leftHalfOffLine (spectralTerm g.convolutionSquare) rho).re)]
    refine tsum_congr fun rho => ?_
    show (Set.indicator leftHalfOffLine (spectralTerm g.convolutionSquare)
        (hermitianPartner rho)).re =
      (Set.indicator rightHalfOffLine (spectralTerm g.convolutionSquare) rho).re
    by_cases h : rho ∈ rightHalfOffLine
    · rw [Set.indicator_of_mem (hermitianPartner_mem_leftHalf_of_mem_rightHalf h),
        Set.indicator_of_mem h]
      exact spectralTerm_convolutionSquare_hermitianPartner_re_eq g rho
        (xiMultiplicity_hermitianPartner_eq rho)
    · have hnp : hermitianPartner rho ∉ leftHalfOffLine := fun hpl =>
        h ((hermitianPartner_mem_leftHalf_iff rho).mp hpl)
      have e1 : Set.indicator leftHalfOffLine (spectralTerm g.convolutionSquare)
          (hermitianPartner rho) = 0 := by simp [hnp]
      have e2 : Set.indicator rightHalfOffLine (spectralTerm g.convolutionSquare)
          rho = 0 := by simp [h]
      rw [e1, e2]
  -- Step 3: assemble.
  unfold offLineSpectralMass
  rw [hsplit, Complex.add_re, hleft]
  ring

#print axioms re_centeredXiCoordinate
#print axioms re_centeredXiCoordinate_hermitianPartner
#print axioms mem_onLineZeroSet_iff
#print axioms re_centeredXiCoordinate_ne_zero_of_offLine
#print axioms hermitianPartner_mem_offLine_iff
#print axioms hermitianPartner_mem_leftHalf_of_mem_rightHalf
#print axioms hermitianPartner_mem_rightHalf_of_mem_leftHalf
#print axioms hermitianPartner_mem_leftHalf_iff
#print axioms offLineZeroSet_eq_union
#print axioms disjoint_rightHalf_leftHalf
#print axioms offLineSpectralMass_eq_two_mul_re_tsum_rightHalf

end
end C1SpectralOfflinePairing
end Source
end ConnesWeilRH
