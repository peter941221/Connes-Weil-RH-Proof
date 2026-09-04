/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1T2Assembly

/-!
# Record 1123 audit: T2 assembly

Focused axiom audit for every public declaration introduced by
`C1T2Assembly`.  The record discharges the T2 normalization slot and fixes
the 1116c defect contract; it asserts no sign and does not claim RH.
-/

open ConnesWeilRH Source C1T2Assembly

#print axioms mulVec_smul_pointwise
#print axioms qform_smul_homogeneous
#print axioms qform_norm_representative_sqrt
#print axioms qform_norm_representative
#print axioms spanObj_support
#print axioms gate_span_smul_homogeneous
#print axioms support_subset_Ioo_of_radius_lt
#print axioms exists_certified_classWindow_q28
#print axioms exists_certified_classWindow_q38
#print axioms exists_certified_classWindow_q48
#print axioms defectGate_singleton_eq_sub
#print axioms stageBContraction_of_certifiedWindow
#print axioms orbitGate_of_certifiedWindow

namespace ConnesWeilRH.Source.C1T2Assembly

open CCM25Concrete.CompactLogConvolution
open C1HboxRationalData
open C1GateLevelTransferClasses
open C1HkerSpan
open C1LocalConfigurationDomination
open C1SameOwnerWeil
open C1GateMatrixRepresentation
open C1OrbitWindowSemiLocalGate
open Matrix
open scoped BigOperators

/-- Fidelity: the assembly returns a literal Stage-B contraction instance
from a certified window, the defect bound, and the budget. -/
example (g W : CompactLogTest) {b a mu epsilon : ℝ}
    (hgsupp : Function.support g.test ⊆ Set.Ioo (-b) b)
    (hWsupp : Function.support W.test ⊆ Set.Ioo (-a) a)
    (hcert : ICgate W.convolutionSquare ≤ -mu)
    (hdec : ICgate (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1)) ≤ epsilon)
    (hbudget : epsilon ≤ mu) :
    ICStageBContraction g :=
  stageBContraction_of_certifiedWindow g W hgsupp hWsupp hcert hdec hbudget

/-- Fidelity: the defect contract reads as the difference of gates. -/
example (g W : CompactLogTest) :
    ICgate (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1))
      = ICgate g.convolutionSquare - ICgate W.convolutionSquare :=
  defectGate_singleton_eq_sub g W

/-- Fidelity: a certified class window exists for any positive-G-norm
coefficient, with the support inherited from the family window. -/
example {w8 : Fin 8 → CompactLogTest}
    {G_true M_true : Matrix (Fin 8) (Fin 8) ℝ} {y : Fin 5 → ℝ} {B : ℝ}
    (hw8 : ∀ i, Function.support (w8 i).test ⊆ Set.Ioo (-B) B)
    (hM : gateMatrix w8 = M_true)
    (hbox : Hbox GLo_q28 GHi_q28 MLo_q28 MHi_q28 G_true M_true)
    (hpos : 0 < Q28.K.mulVec y ⬝ᵥ (G_true *ᵥ (Q28.K.mulVec y))) :
    ∃ W : CompactLogTest, ICgate W.convolutionSquare ≤ -mu_q28
      ∧ Function.support W.test ⊆ Set.Ioo (-B) B :=
  exists_certified_classWindow_q28 hw8 hM hbox hpos

end ConnesWeilRH.Source.C1T2Assembly
