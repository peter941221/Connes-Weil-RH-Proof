/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1HkerSpan
import ConnesWeilRH.Dev.C1ArchimedeanIntegrabilityGeneric

/-!
# Record 1123: T2 assembly - Hnorm discharge, defect contract, one-window Stage-B

Closes the T2 normalization slot and fixes the remaining (iv) input as a
ONE-inequality contract (docs/proofs/
1123_t2_assembly_defect_contract_preregistration.md):

* Normalization layer: quadratic forms are homogeneous of degree 2 in the
  coefficient, so `hnorm` is WLOG - a positive-G-norm coefficient has a
  rescaled representative with unit G-norm.
* Span layer: the gate of a span square is likewise degree-2 homogeneous
  (via 1121 + 1122), and a span object inherits the common window.
* Hnorm discharge: for each certified class (q28/q38/q48), EVERY
  coefficient with positive G-norm yields an EXISTING Stage-B window `W`
  with `ICgate W.convolutionSquare <= -mu` and the inherited support -
  the 1120 absolute headline with `hnorm` absorbed into the choice of `W`.
* Defect contract: by the 1117 linearity layer plus 1122 legality, the
  one-window Stage-B defect gate is EXACTLY
  `ICgate gHead - ICgate W` - this fixes the 1116c consumption contract.
* Assembly: one literal `ICStageBContraction g` (iota = Unit) consuming
  a certified window, the defect bound, and the budget; the 1117 bridge
  then yields the 1089 orbit gate.

No sign theorem and no RH statement is asserted here.  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1T2Assembly

open MeasureTheory Set Filter
open CCM25Concrete.CompactLogConvolution
open C1HboxRationalData
open C1GateLevelTransferClasses
open C1HkerSpan
open C1LocalConfigurationDomination
open C1SameOwnerWeil
open C1GateMatrixRepresentation
open C1ArchimedeanIntegrabilityGeneric
open C1OrbitWindowSemiLocalGate
open Matrix
open scoped BigOperators ContDiff Filter Topology

noncomputable section

/-! ## Normalization layer -/

/-- Pointwise rescaling commutes with `mulVec`. -/
theorem mulVec_smul_pointwise {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (t : ℝ) :
    G *ᵥ (fun i => t * v i) = fun j => t * (G *ᵥ v) j := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Quadratic forms are homogeneous of degree 2 in the coefficient. -/
theorem qform_smul_homogeneous {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (c : Fin n → ℝ) (t : ℝ) :
    (fun i => t * c i) ⬝ᵥ (G *ᵥ (fun i => t * c i))
      = t ^ 2 * (c ⬝ᵥ (G *ᵥ c)) := by
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The sqrt-normalized representative of a positive-G-norm coefficient has
unit G-norm. -/
theorem qform_norm_representative_sqrt {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (hpos : 0 < c ⬝ᵥ (G *ᵥ c)) :
    (fun i => (Real.sqrt (c ⬝ᵥ (G *ᵥ c)))⁻¹ * c i) ⬝ᵥ
        (G *ᵥ (fun i => (Real.sqrt (c ⬝ᵥ (G *ᵥ c)))⁻¹ * c i)) = 1 := by
  rw [qform_smul_homogeneous]
  have hsqrt : Real.sqrt (c ⬝ᵥ (G *ᵥ c)) * Real.sqrt (c ⬝ᵥ (G *ᵥ c))
      = c ⬝ᵥ (G *ᵥ c) := Real.mul_self_sqrt hpos.le
  have hne : Real.sqrt (c ⬝ᵥ (G *ᵥ c)) ≠ 0 :=
    (Real.sqrt_pos.mpr hpos).ne'
  field_simp

/-- Normalization is WLOG: a positive-G-norm coefficient has a rescaled
representative with unit G-norm. -/
theorem qform_norm_representative {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (c : Fin n → ℝ) (hpos : 0 < c ⬝ᵥ (G *ᵥ c)) :
    ∃ t : ℝ, (fun i => t * c i) ⬝ᵥ (G *ᵥ (fun i => t * c i)) = 1 :=
  ⟨_, qform_norm_representative_sqrt G c hpos⟩

/-! ## Span layer -/

/-- A span object inherits the common window of its family. -/
theorem spanObj_support {k : ℕ} (w : Fin k → CompactLogTest)
    (y : Fin k → ℝ) {B : ℝ}
    (hw : ∀ i, Function.support (w i).test ⊆ Ioo (-B) B) :
    Function.support (spanObj w y).test ⊆ Ioo (-B) B := by
  intro x hx
  by_contra hout
  rw [Function.mem_support] at hx
  apply hx
  have hall : ∀ i : Fin k, y i * (w i).test x = 0 := by
    intro i
    have h0 : (w i).test x = 0 := by
      by_contra hne
      exact hout (hw i (Function.mem_support.mpr hne))
    simp [h0]
  rw [spanObj_apply]
  exact Finset.sum_eq_zero fun i _ => hall i

/-- The gate of a span square is homogeneous of degree 2 in the span
coefficient. -/
theorem gate_span_smul_homogeneous {k : ℕ} (w : Fin k → CompactLogTest)
    (y : Fin k → ℝ) (t : ℝ) {B : ℝ}
    (hw : ∀ i, Function.support (w i).test ⊆ Ioo (-B) B) :
    ICgate ((spanObj w (fun i => t * y i)).convolutionSquare)
      = t ^ 2 * ICgate ((spanObj w y).convolutionSquare) := by
  rw [gate_sum_span_free w (fun i => t * y i) hw,
    gate_sum_span_free w y hw]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- Window bound at any larger radius. -/
theorem support_subset_Ioo_of_radius_lt (F : CompactLogTest) {b : ℝ}
    (hlt : supportRadius F < b) :
    Function.support F.test ⊆ Ioo (-b) b := by
  intro x hx
  have hcc := support_subset_Icc F hx
  exact ⟨by linarith, by linarith⟩

/-! ## Hnorm discharge: certified Stage-B windows from unnormalized data -/

/-- **(2,8)**: every coefficient with positive G-norm yields a certified
Stage-B window; the 1120 `hnorm` slot is absorbed into the choice of the
window. -/
theorem exists_certified_classWindow_q28 {w8 : Fin 8 → CompactLogTest}
    {G_true M_true : Matrix (Fin 8) (Fin 8) ℝ} {y : Fin 5 → ℝ} {B : ℝ}
    (hw8 : ∀ i, Function.support (w8 i).test ⊆ Ioo (-B) B)
    (hM : gateMatrix w8 = M_true)
    (hbox : Hbox GLo_q28 GHi_q28 MLo_q28 MHi_q28 G_true M_true)
    (hpos : 0 < Q28.K.mulVec y ⬝ᵥ (G_true *ᵥ (Q28.K.mulVec y))) :
    ∃ W : CompactLogTest, ICgate W.convolutionSquare ≤ -mu_q28
      ∧ Function.support W.test ⊆ Ioo (-B) B := by
  obtain ⟨t, htnorm⟩ := qform_norm_representative G_true (Q28.K.mulVec y) hpos
  refine ⟨spanObj w8 (Q28.K.mulVec (fun i => t * y i)), ?_, ?_⟩
  · refine absolute_spanK_q28 ?_ ?_ hbox
    · rw [gate_qform_span_free w8 (Q28.K.mulVec (fun i => t * y i)) hw8, hM]
    · have hmv := mulVec_smul_pointwise Q28.K y t
      rw [hmv]
      exact htnorm
  · exact spanObj_support w8 _ hw8

/-- **(3,8)**: every coefficient with positive G-norm yields a certified
Stage-B window. -/
theorem exists_certified_classWindow_q38 {w8 : Fin 8 → CompactLogTest}
    {G_true M_true : Matrix (Fin 8) (Fin 8) ℝ} {y : Fin 5 → ℝ} {B : ℝ}
    (hw8 : ∀ i, Function.support (w8 i).test ⊆ Ioo (-B) B)
    (hM : gateMatrix w8 = M_true)
    (hbox : Hbox GLo_q38 GHi_q38 MLo_q38 MHi_q38 G_true M_true)
    (hpos : 0 < Q38.K.mulVec y ⬝ᵥ (G_true *ᵥ (Q38.K.mulVec y))) :
    ∃ W : CompactLogTest, ICgate W.convolutionSquare ≤ -mu_q38
      ∧ Function.support W.test ⊆ Ioo (-B) B := by
  obtain ⟨t, htnorm⟩ := qform_norm_representative G_true (Q38.K.mulVec y) hpos
  refine ⟨spanObj w8 (Q38.K.mulVec (fun i => t * y i)), ?_, ?_⟩
  · refine absolute_spanK_q38 ?_ ?_ hbox
    · rw [gate_qform_span_free w8 (Q38.K.mulVec (fun i => t * y i)) hw8, hM]
    · have hmv := mulVec_smul_pointwise Q38.K y t
      rw [hmv]
      exact htnorm
  · exact spanObj_support w8 _ hw8

/-- **(4,8)**: every coefficient with positive G-norm yields a certified
Stage-B window. -/
theorem exists_certified_classWindow_q48 {w8 : Fin 8 → CompactLogTest}
    {G_true M_true : Matrix (Fin 8) (Fin 8) ℝ} {y : Fin 5 → ℝ} {B : ℝ}
    (hw8 : ∀ i, Function.support (w8 i).test ⊆ Ioo (-B) B)
    (hM : gateMatrix w8 = M_true)
    (hbox : Hbox GLo_q48 GHi_q48 MLo_q48 MHi_q48 G_true M_true)
    (hpos : 0 < Q48.K.mulVec y ⬝ᵥ (G_true *ᵥ (Q48.K.mulVec y))) :
    ∃ W : CompactLogTest, ICgate W.convolutionSquare ≤ -mu_q48
      ∧ Function.support W.test ⊆ Ioo (-B) B := by
  obtain ⟨t, htnorm⟩ := qform_norm_representative G_true (Q48.K.mulVec y) hpos
  refine ⟨spanObj w8 (Q48.K.mulVec (fun i => t * y i)), ?_, ?_⟩
  · refine absolute_spanK_q48 ?_ ?_ hbox
    · rw [gate_qform_span_free w8 (Q48.K.mulVec (fun i => t * y i)) hw8, hM]
    · have hmv := mulVec_smul_pointwise Q48.K y t
      rw [hmv]
      exact htnorm
  · exact spanObj_support w8 _ hw8

/-! ## The defect contract (the 1116c consumption shape) -/

/-- The one-window Stage-B defect gate is EXACTLY the difference of gates:
all legality input is discharged by record 1122.  This fixes the 1116c
model-consumption contract as a single inequality on the true data. -/
theorem defectGate_singleton_eq_sub (g W : CompactLogTest) :
    ICgate (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1))
      = ICgate g.convolutionSquare - ICgate W.convolutionSquare := by
  set R : ℝ :=
    2 * (max (supportRadius g) (supportRadius W) + 1) with hRdef
  have hb : max (supportRadius g) (supportRadius W)
      < max (supportRadius g) (supportRadius W) + 1 := by linarith
  have hgg : Function.support g.convolutionSquare.test ⊆ Ioo (-R) R := by
    refine CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo g ?_
    exact (support_subset_Ioo_of_radius_lt g
      (lt_of_le_of_lt (le_max_left _ _) hb)).trans Set.Ioo_subset_Icc_self
  have hWW : Function.support W.convolutionSquare.test ⊆ Ioo (-R) R := by
    refine CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo W ?_
    exact (support_subset_Ioo_of_radius_lt W
      (lt_of_le_of_lt (le_max_right _ _) hb)).trans Set.Ioo_subset_Icc_self
  exact ICgate_ICdefect _ _ _ _ hgg (fun i _ => hWW)
    (integrableOn_archimedeanIntegrand _)
    (fun i _ => integrableOn_archimedeanIntegrand _)

/-! ## Assembly: the one-window Stage-B instance -/

/-- The T2 instance template: a certified window plus the defect bound
(the 1116c contract) plus the budget yield a literal `ICStageBContraction`.
After this theorem, the ENTIRE remaining content of (iv) is the defect
bound `hdec`. -/
theorem stageBContraction_of_certifiedWindow (g W : CompactLogTest)
    {b a mu epsilon : ℝ}
    (hgsupp : Function.support g.test ⊆ Ioo (-b) b)
    (hWsupp : Function.support W.test ⊆ Ioo (-a) a)
    (hcert : ICgate W.convolutionSquare ≤ -mu)
    (hdec : ICgate (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1)) ≤ epsilon)
    (hbudget : epsilon ≤ mu) :
    ICStageBContraction g where
  ι := Unit
  s := {()}
  w := fun _ => W
  lam := fun _ => 1
  hlam := by
    intro i _
    simp
  mu := fun _ => mu
  epsilon := epsilon
  b := b
  hgsupp := hgsupp
  a := fun _ => a
  hwsupp := by
    intro i _
    exact hWsupp
  hD := hdec
  hcert := by
    intro i _
    exact hcert

/-- The assembly through the 1117 bridge: the certified window, the defect
bound, and the budget give the record-1089 orbit-window semi-local gate. -/
theorem orbitGate_of_certifiedWindow (g W : CompactLogTest)
    {b a mu epsilon : ℝ}
    (hgsupp : Function.support g.test ⊆ Ioo (-b) b)
    (hWsupp : Function.support W.test ⊆ Ioo (-a) a)
    (hcert : ICgate W.convolutionSquare ≤ -mu)
    (hdec : ICgate (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1)) ≤ epsilon)
    (hbudget : epsilon ≤ mu) :
    orbitWindowSemiLocalGate g :=
  orbitWindowSemiLocalGate_of_contraction g
    (stageBContraction_of_certifiedWindow g W hgsupp hWsupp hcert hdec
      hbudget)
    (by simpa using hbudget)

end
end C1T2Assembly
end Source
end ConnesWeilRH
