import ConnesWeilRH.Dev.C1FourPointSpanGateCertificate
import ConnesWeilRH.Dev.C1RouteBRhoOwnerPackage3106

/-! Variable-lambda same-owner gate adapter (record 3130).

The fixed-24 adapter is useful for the stored row-B contract, but the
rho-dependent campaign must keep the gate coefficient free.  This module
exposes the exact quadratic expression and its owner-local semi-local gate
for an arbitrary real coefficient.  It proves no numerical sign.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteBVariableLambdaGate3130

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1ArchimedeanIntegrabilityGeneric
open C1FourPointSpanGateCertificate
open C1FourPointSpectralPrefixTransport
open C1GateMatrixRepresentation
open C1LocalConfigurationDomination
open C1OrbitWindowSemiLocalGate
open C1P2SpanProfileMatrix
open C1RouteBRhoOwnerPackage3106
open C1TwoPointSpectralDecomposition
open scoped BigOperators

noncomputable section

def variableLambdaGatePredicate3130 (rho : sourceNontrivialZeroSet)
    (g : CompactLogTest) (lambda : Real) : Prop :=
  ICgate ((fullFunctionalEquationOrbitAnnihilator g rho.1).convolutionSquare) -
      lambda * (ICgate ((fullFunctionalEquationOrbitAnnihilator g rho.1).involution.convolution g) +
        ICgate (g.involution.convolution
          (fullFunctionalEquationOrbitAnnihilator g rho.1))) +
      lambda ^ 2 * ICgate g.convolutionSquare ≤ 0

theorem variableLambdaGatePredicate3130_iff_gate_qform
    {rho : sourceNontrivialZeroSet} (g : CompactLogTest) (lambda : Real) :
    variableLambdaGatePredicate3130 rho g lambda ↔
      dotProduct (![1, -lambda] : Fin 2 → Real)
          ((gateMatrix ![
            fullFunctionalEquationOrbitAnnihilator g rho.1, g]).mulVec
            (![1, -lambda] : Fin 2 → Real)) ≤ 0 := by
  unfold variableLambdaGatePredicate3130
  rw [twoSpan_gate_qform_expand]
  constructor <;> intro h <;> nlinarith

theorem variableLambdaGatePredicate3130_iff_signed_margin
    {rho : sourceNontrivialZeroSet} (g : CompactLogTest) (lambda : Real) :
    variableLambdaGatePredicate3130 rho g lambda ↔
      ICgate ((fullFunctionalEquationOrbitAnnihilator g rho.1).convolutionSquare) +
          lambda ^ 2 * ICgate g.convolutionSquare ≤
        lambda * (ICgate ((fullFunctionalEquationOrbitAnnihilator g rho.1).involution.convolution g) +
          ICgate (g.involution.convolution
            (fullFunctionalEquationOrbitAnnihilator g rho.1))) := by
  unfold variableLambdaGatePredicate3130
  constructor <;> intro h <;> nlinarith

theorem variableLambdaGatePredicate3130_iff_owner_gate_of_support
    {rho : sourceNontrivialZeroSet} (g : CompactLogTest) (lambda : Real)
    (B : Real)
    (hsupport : Function.support g.test ⊆ Set.Ioo (-B) B) :
    variableLambdaGatePredicate3130 rho g lambda ↔
      orbitWindowSemiLocalGate
        (annihilatorDetectorSpanVector
          (fullFunctionalEquationOrbitAnnihilator g rho.1) g lambda) := by
  have hsupp_g : Function.support g.test ⊆ Set.Icc (-B) B :=
    hsupport.trans Set.Ioo_subset_Icc_self
  have hsupp_u : Function.support
      (fullFunctionalEquationOrbitAnnihilator g rho.1).test ⊆
      Set.Icc (-B) B :=
    fullFunctionalEquationOrbitAnnihilator_support_subset_Icc
      g rho.1 hsupp_g
  have hw : ∀ i, Function.support
      ((![fullFunctionalEquationOrbitAnnihilator g rho.1, g] :
        Fin 2 → CompactLogTest) i).test ⊆ Set.Ioo (-(B + 1)) (B + 1) := by
    intro i
    fin_cases i
    · intro x hx
      have hx' := hsupp_u hx
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
    · intro x hx
      have hx' := hsupp_g hx
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  unfold variableLambdaGatePredicate3130
  rw [orbitWindowSemiLocalGate_iff,
    annihilator_span_gate_eq_parabola
      (fullFunctionalEquationOrbitAnnihilator g rho.1) g lambda hw]

theorem variableLambdaGatePredicate3130_iff_owner_gate
    {rho : sourceNontrivialZeroSet} (pkg : RhoOwnerPackage3106 rho)
    (lambda : Real) :
    variableLambdaGatePredicate3130 rho pkg.g lambda ↔
      orbitWindowSemiLocalGate
        (annihilatorDetectorSpanVector
          (fullFunctionalEquationOrbitAnnihilator pkg.g rho.1) pkg.g lambda) := by
  let B : Real := ((pkg.geometry.orbitIndex + 2 : Nat) : Real)
  have hsupport : Function.support pkg.g.test ⊆ Set.Ioo (-B) B := by
    simpa [B] using pkg.geometry.support_bound
  have hsupp_g : Function.support pkg.g.test ⊆ Set.Icc (-B) B :=
    hsupport.trans Set.Ioo_subset_Icc_self
  have hsupp_u : Function.support
      (fullFunctionalEquationOrbitAnnihilator pkg.g rho.1).test ⊆
      Set.Icc (-B) B :=
    fullFunctionalEquationOrbitAnnihilator_support_subset_Icc
      pkg.g rho.1 hsupp_g
  have hw : ∀ i, Function.support
      ((![fullFunctionalEquationOrbitAnnihilator pkg.g rho.1, pkg.g] :
        Fin 2 → CompactLogTest) i).test ⊆ Set.Ioo (-(B + 1)) (B + 1) := by
    intro i
    fin_cases i
    · intro x hx
      have hx' := hsupp_u hx
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
    · intro x hx
      have hx' := hsupp_g hx
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  unfold variableLambdaGatePredicate3130
  rw [orbitWindowSemiLocalGate_iff,
    annihilator_span_gate_eq_parabola
      (fullFunctionalEquationOrbitAnnihilator pkg.g rho.1) pkg.g lambda hw]

end
end C1RouteBVariableLambdaGate3130
end Source
end ConnesWeilRH
