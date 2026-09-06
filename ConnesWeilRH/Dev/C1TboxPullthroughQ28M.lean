/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1TboxPullthrough
import ConnesWeilRH.Dev.C1HboxRationalDataQ28M

/-!
# Record 1218: T-box pull-through on the true (2,8) gate boxes

M-side fork of the committed `C1TboxPullthrough` q28 section: the whole
record-1119 (a)+(b) chain, re-pointed at the record-1217 TRUE gate
boxes (mixed entries exact zeros owned by D1).  The generic
`tbox_of_identities` is reused verbatim from the committed module; only
the data instances change (G side reused from the committed chain,
byte-equal underlying exact-Q data, 1218 regression gate F3).

RH NOT claimed; no gate Prop is discharged here beyond the named slots.
-/

namespace ConnesWeilRH
namespace Source
namespace C1TboxPullthroughQ28M

open Matrix
open C1EntrywiseBound
open C1TboxPullthrough (tbox_of_identities)
open C1HboxRationalData
open C1HboxRationalDataQ28M
open C1GateLevelTransferClasses
open C1GateLevelTransferClassesQ28M
open C1GateMatrixBoxData
open C1LocalConfigurationDomination
open C1WindowRationalIngest
open CCM25Concrete.CompactLogConvolution

theorem hUneg_q28M : Q28.U < 0 := by
  simp only [Q28.U]
  norm_num

theorem hUabs_q28M : |Q28.U| = mu_q28M := by
  simp only [mu_q28M]
  exact abs_of_neg hUneg_q28M

theorem hDtwo_q28M : Q28M.Dc + Q28M.Dc
    = (Q28.U • Q28.G - Q28M.M) + (Q28.U • Q28.G - Q28M.M).transpose := by
  rw [← Q28M.hD]
  exact Q28M.hDc

/-- **T-box (true boxes)**: the record-1118 §1a box theorem at radius
form - for EVERY `Gt/Mt` inside the true-box radius matrices the top
bound holds on `ker R`. -/
theorem tbox_q28M (Gt Mt : Matrix (Fin 8) (Fin 8) ℝ)
    (hG : ∀ i j, |Gt i j - Q28.G i j| ≤ radG_q28 i j)
    (hM : ∀ i j, |Mt i j - Q28M.M i j| ≤ radM_q28M i j)
    (c : Fin 8 → ℝ) (hc : Q28.R.mulVec c = 0) :
    c ⬝ᵥ (Mt *ᵥ c) ≤ Q28.U * c ⬝ᵥ (Gt *ᵥ c) :=
  tbox_of_identities Q28.U Q28.G Q28M.M Q28.R Q28.K Q28.V Q28.W
    Q28M.Dc Q28M.L Q28M.dd
    radG_q28 radM_q28M absK_q28 Lam_q28M absLam_q28M DredRad_q28M
    radp_q28M mu_q28M
    Q28.hclosure hDtwo_q28M Q28M.hPencil hUabs_q28M
    hsymRadG_q28 hsymRadM_q28M habsK_q28 habsLam_q28M
    hLLam_q28M hDredRad_q28M hRadp_q28M
    hradpos_q28M hslack_q28M Gt Mt hG hM c hc

/-- **T-box true (true boxes)**: `Hbox` (true data in the committed
boxes: G side of record 1112, M side of record 1217) suffices - the
bridge is the reverse containment. -/
theorem tbox_true_q28M (G_true M_true : Matrix (Fin 8) (Fin 8) ℝ)
    (hbox : Hbox GLo_q28 GHi_q28 MLo_q28M MHi_q28M G_true M_true)
    (c : Fin 8 → ℝ) (hc : Q28.R.mulVec c = 0) :
    c ⬝ᵥ (M_true *ᵥ c) ≤ Q28.U * c ⬝ᵥ (G_true *ᵥ c) := by
  refine tbox_q28M G_true M_true ?_ ?_ c hc
  · intro i j
    obtain ⟨h1, h2⟩ := hbox.1 i j
    obtain ⟨h3, h4⟩ := hrevG_q28 i j
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro i j
    obtain ⟨h1, h2⟩ := hbox.2 i j
    obtain ⟨h3, h4⟩ := hrevM_q28M i j
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **ABSOLUTE headline over true data (true boxes)**: with the
representation and L2-normalization slots, `Hbox` alone pins the gate
at the named margin. -/
theorem absolute_true_q28M {w : CompactLogTest}
    {G_true : Matrix (Fin 8) (Fin 8) ℝ}
    {M_true : Matrix (Fin 8) (Fin 8) ℝ} {c : Fin 8 → ℝ}
    (hrep : ICgate w.convolutionSquare = c ⬝ᵥ (M_true *ᵥ c))
    (hker : Q28.R.mulVec c = 0)
    (hnorm : c ⬝ᵥ (G_true *ᵥ c) = 1)
    (hbox : Hbox GLo_q28 GHi_q28 MLo_q28M MHi_q28M G_true M_true) :
    ICgate w.convolutionSquare ≤ -mu_q28M := by
  have h := tbox_true_q28M G_true M_true hbox c hker
  have hmu : Q28.U = -mu_q28M := by
    rw [show mu_q28M = -Q28.U from rfl, neg_neg]
  rw [hmu] at h
  exact absolute_headline hrep h hnorm

end C1TboxPullthroughQ28M
end Source
end ConnesWeilRH
