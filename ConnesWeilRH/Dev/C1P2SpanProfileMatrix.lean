import ConnesWeilRH.Dev.C1P2SignedBudget
import ConnesWeilRH.Dev.C1GateMatrixRepresentation
import ConnesWeilRH.Dev.C1ArchimedeanIntegrabilityGeneric

/-!
# Finite-span readback of the selected prime profile

The signed-budget observable is evaluated on a convolution square, not on
the root test itself.  This leaf expands one actual prime-log profile term of
a finite root span into the pair-basis quadratic form.  It is an exact
same-owner algebraic interface; it proves no sign or RH statement.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2SpanProfileMatrix

open C1GateMatrixRepresentation
open C1G8R0OrbitGeometry
open C1OrbitWindowSemiLocalGate
open C1P2BilateralProfile
open C1P2SignedBudget
open C1SameOwnerWeil
open C1ArchimedeanIntegrabilityGeneric
open C1LocalConfigurationDomination
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open Matrix
open MeasureTheory
open scoped BigOperators

noncomputable section

theorem signedProfileTerm_spanObj_eq_pair_profile_quadratic
    {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ) (n : ℕ) :
    signedProfileTerm (spanObj w y) n =
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
        (∑ i ∈ (Finset.univ : Finset (Fin k)),
          ∑ j ∈ (Finset.univ : Finset (Fin k)),
            ((y i * y j : ℝ) : ℂ) *
              bilateralProfile (pairTest w i j) (Real.log n)).re := by
  unfold signedProfileTerm bilateralProfile
  rw [convolutionSquare_spanObj_apply, convolutionSquare_spanObj_apply]
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]

theorem orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos
    {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ)
    {B : ℝ} (hw : ∀ i, Function.support (w i).test ⊆ Set.Ioo (-B) B)
    (hI : ∀ i j, IntegrableOn (archimedeanIntegrand (pairTest w i j))
      (Set.Ioi (0 : ℝ))) :
    orbitWindowSemiLocalGate (spanObj w y) ↔
      y ⬝ᵥ (gateMatrix w *ᵥ y) ≤ 0 := by
  have hgate :
      orbitWindowSemiLocalGate (spanObj w y) ↔
        p2AggregateValue (spanObj w y) ≤ 0 := by
    unfold orbitWindowSemiLocalGate p2AggregateValue
    rw [← finitePrimeSum_eq_bilateralProfile_weighted_sum]
  rw [hgate, p2AggregateValue_spanObj_eq_gate_qform w y hw hI]

theorem orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos_of_support
    {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ)
    {B : ℝ} (hw : ∀ i, Function.support (w i).test ⊆ Set.Ioo (-B) B) :
    orbitWindowSemiLocalGate (spanObj w y) ↔
      y ⬝ᵥ (gateMatrix w *ᵥ y) ≤ 0 := by
  exact orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos w y hw
    (fun i j => pairTest_legality w i j)

theorem sourceRH_of_right_orbitGeometry_spanGateCertificate
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            ∃ (k : ℕ) (w : Fin k → CompactLogTest) (y : Fin k → ℝ) (B : ℝ),
              g = spanObj w y ∧
              (∀ i, Function.support (w i).test ⊆ Set.Ioo (-B) B) ∧
              y ⬝ᵥ (gateMatrix w *ᵥ y) ≤ 0) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_signedBudget
  intro rho hright
  obtain ⟨g, geometry, k, w, y, B, howner, hw, hq⟩ := hproducer rho hright
  have hspanGate : orbitWindowSemiLocalGate (spanObj w y) :=
    (orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos_of_support
      w y hw).mpr hq
  have hgate : orbitWindowSemiLocalGate g := by
    rw [howner]
    exact hspanGate
  have hbudget := (orbitWindowSemiLocalGate_iff_signedBudget geometry).mp hgate
  refine ⟨g, geometry, ?_⟩
  simpa [orbitVisiblePrimeRange] using hbudget

theorem oneWindowICdefect_eq_twoSpan
    (g W : CompactLogTest) (lam : ℝ) :
    ICdefect g ({()} : Finset Unit) (fun _ => W) (fun _ => lam) =
      spanObj ![g, W] ![(1 : ℝ), -lam] := by
  apply CompactLogTest.ext
  ext x
  simp [ICdefect_test, spanObj]
  ring

theorem oneWindowICdefect_gate_iff_twoSpan_qform_nonpos
    (g W : CompactLogTest) (lam B : ℝ)
    (hg : Function.support g.test ⊆ Set.Ioo (-B) B)
    (hW : Function.support W.test ⊆ Set.Ioo (-B) B) :
    orbitWindowSemiLocalGate
        (ICdefect g ({()} : Finset Unit) (fun _ => W) (fun _ => lam)) ↔
      (![1, -lam] : Fin 2 → ℝ) ⬝ᵥ
          (gateMatrix ![g, W] *ᵥ (![1, -lam] : Fin 2 → ℝ)) ≤ 0 := by
  rw [oneWindowICdefect_eq_twoSpan]
  apply orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos_of_support
  intro i
  fin_cases i
  · simpa using hg
  · simpa using hW

end
end C1P2SpanProfileMatrix
end Source
end ConnesWeilRH
