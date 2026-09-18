/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.SoninWindowWitness

/-!
# The carrier obligation is a radial eigenvector problem

Record 1003 T4 targets a nonzero element of the archimedean Sonin carrier
`V_arch = Radial(λ) ⊓ H⁻¹(Radial(λ))` (docs/999 section 3.1,
`archimedeanSoninCarrier_nontrivial`).  This module proves that this obligation
is EXACTLY the existence of a nonzero radial `±1` eigenvector of the
Hardy--Titchmarsh involution `H = ccm24ArchimedeanHardyTitchmarsh`:

  `(∃ v : V_arch, v ≠ 0) ↔ ∃ u ≠ 0, u ∈ Radial(λ) ∧ (H u = u ∨ H u = -u)`.

Forward direction (symmetrization): for nonzero `v ∈ V_arch` with `H v ≠ -v`,
the vector `v + H v` is nonzero, radial, and `H`-fixed, hence again in
`V_arch`; if `H v = -v` then `v` itself is the eigenvector.  Backward
direction: the committed reduction lemma
`archimedeanSonin_membership_pred_of_radial_and_involutive`.

Consequence: T4 no longer has to produce an element of an intersection of two
support conditions; it has to produce a nonzero radial eigenvector of a single
involutive operator.  No witness is produced here: the existence stays the
open analytic obligation of records 1003/1590, and RH is not claimed.
-/

namespace ConnesWeilRH
namespace Dev
namespace SoninCarrierEigenvectorBridge

open ConnesWeilRH.Source.CC20Concrete
open ConnesWeilRH.Dev.SoninWindowWitness

/-- The carrier-nontriviality obligation is exactly the existence of a nonzero
radial `±1` eigenvector of the Hardy--Titchmarsh involution. -/
theorem archimedeanSoninCarrier_nontrivial_iff_radial_eigenvector
    (lambda : CCM24SoninScale) :
    archimedeanSoninCarrier_nontrivial lambda ↔
      ∃ u : cc20GlobalLogCrossingL2, u ≠ 0 ∧
        u ∈ ccm24LogRadialSupportClosedSubspace lambda ∧
          (ccm24ArchimedeanHardyTitchmarsh u = u ∨
            ccm24ArchimedeanHardyTitchmarsh u = -u) := by
  constructor
  · rintro ⟨v, hv⟩
    have hmem := v.property
    have hR : (v : cc20GlobalLogCrossingL2) ∈
        ccm24LogRadialSupportClosedSubspace lambda :=
      (Submodule.mem_inf.mp hmem).1
    have hF : ccm24ArchimedeanHardyTitchmarsh (v : cc20GlobalLogCrossingL2) ∈
        ccm24LogRadialSupportClosedSubspace lambda :=
      (Submodule.mem_inf.mp hmem).2
    by_cases hneg : ccm24ArchimedeanHardyTitchmarsh (v : cc20GlobalLogCrossingL2) =
        -(v : cc20GlobalLogCrossingL2)
    · refine ⟨(v : cc20GlobalLogCrossingL2), ?_, hR, Or.inr hneg⟩
      intro hzero
      exact hv (Subtype.ext (by simpa using hzero))
    · refine ⟨(v : cc20GlobalLogCrossingL2) +
          ccm24ArchimedeanHardyTitchmarsh (v : cc20GlobalLogCrossingL2),
        ?_, ?_, Or.inl ?_⟩
      · intro hzero
        rw [add_comm] at hzero
        exact hneg (eq_neg_of_add_eq_zero_left hzero)
      · exact (ccm24LogRadialSupportClosedSubspace lambda).add_mem hR hF
      · rw [map_add, ccm24ArchimedeanHardyTitchmarsh_involutive]
        abel
  · rintro ⟨u, hu, hR, heig⟩
    have hF : u ∈ ccm24ArchimedeanFourierSupportClosedSubspace lambda := by
      rw [mem_ccm24ArchimedeanFourierSupportClosedSubspace_iff]
      rcases heig with hfix | hanti
      · rw [hfix]
        exact hR
      · rw [hanti]
        exact Submodule.neg_mem
          (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule hR
    refine ⟨⟨u, Submodule.mem_inf.mpr ⟨hR, hF⟩⟩, ?_⟩
    intro hzero
    exact hu (by simpa using congrArg Subtype.val hzero)

/-- Extracted forward direction: every nonzero carrier element yields a
nonzero radial `±1` eigenvector of the Hardy--Titchmarsh involution.  This is
the exact shape in which the T4 obligation can be attacked as an eigenproblem
(record 1003 T4; record 1590 for the model-space reading). -/
theorem exists_radial_eigenvector_of_carrier_ne_zero
    (lambda : CCM24SoninScale) (h : archimedeanSoninCarrier_nontrivial lambda) :
    ∃ u : cc20GlobalLogCrossingL2, u ≠ 0 ∧
      u ∈ ccm24LogRadialSupportClosedSubspace lambda ∧
        (ccm24ArchimedeanHardyTitchmarsh u = u ∨
          ccm24ArchimedeanHardyTitchmarsh u = -u) :=
  (archimedeanSoninCarrier_nontrivial_iff_radial_eigenvector lambda).1 h

/-- A nonzero radial fixed vector witnesses carrier nontriviality. -/
theorem archimedeanSoninCarrier_nontrivial_of_fixed_radial
    (lambda : CCM24SoninScale) {u : cc20GlobalLogCrossingL2} (hu : u ≠ 0)
    (hR : u ∈ ccm24LogRadialSupportClosedSubspace lambda)
    (hfix : ccm24ArchimedeanHardyTitchmarsh u = u) :
    archimedeanSoninCarrier_nontrivial lambda :=
  (archimedeanSoninCarrier_nontrivial_iff_radial_eigenvector lambda).2
    ⟨u, hu, hR, Or.inl hfix⟩

/-- A nonzero radial antifixed vector witnesses carrier nontriviality. -/
theorem archimedeanSoninCarrier_nontrivial_of_antifixed_radial
    (lambda : CCM24SoninScale) {u : cc20GlobalLogCrossingL2} (hu : u ≠ 0)
    (hR : u ∈ ccm24LogRadialSupportClosedSubspace lambda)
    (hanti : ccm24ArchimedeanHardyTitchmarsh u = -u) :
    archimedeanSoninCarrier_nontrivial lambda :=
  (archimedeanSoninCarrier_nontrivial_iff_radial_eigenvector lambda).2
    ⟨u, hu, hR, Or.inr hanti⟩

/-- The eigenvector packaging: a radial `±1` eigenvector of `H` is an element
of the carrier by the committed membership reduction. -/
theorem radial_eigenvector_mem_carrier
    (lambda : CCM24SoninScale) {u : cc20GlobalLogCrossingL2}
    (hR : u ∈ ccm24LogRadialSupportClosedSubspace lambda)
    (heig : ccm24ArchimedeanHardyTitchmarsh u = u ∨
      ccm24ArchimedeanHardyTitchmarsh u = -u) :
    u ∈ ccm24ArchimedeanSoninClosedSubspace lambda := by
  have hpred :=
    archimedeanSonin_membership_pred_of_radial_and_involutive lambda hR heig
  exact Submodule.mem_inf.mpr hpred

end SoninCarrierEigenvectorBridge
end Dev
end ConnesWeilRH
