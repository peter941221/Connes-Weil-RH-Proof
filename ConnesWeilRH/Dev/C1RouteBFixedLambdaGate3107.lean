/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1FourPointSpanGateCertificate
import ConnesWeilRH.Dev.C1RouteBRhoOwnerPackage3106

/-!
# Route-B fixed-lambda gate adapter (record 3107)

The row-B contract uses the fixed coefficient `lambda = 24`.  The earlier
four-point certificate proves that a suitable positive coefficient can exist
under a diagonal or determinant hypothesis, but that existential statement
does not specialize to `24`.  This module makes the fixed coefficient an
explicit, same-owner signed inequality.

No numerical sign is asserted here.  The remaining obligation is the exact
signed margin at `lambda = 24` for the owner supplied by the rho-dependent
package.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteBFixedLambdaGate3107

open Matrix
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

/-- The exact fixed-24 gate expression used by the row-B contradiction. -/
def hgate24Predicate3107 (rho : sourceNontrivialZeroSet) (g : CompactLogTest) : Prop :=
  ICgate ((fullFunctionalEquationOrbitAnnihilator g rho.1).convolutionSquare) -
      24 * (ICgate ((fullFunctionalEquationOrbitAnnihilator g rho.1).involution.convolution g) +
        ICgate (g.involution.convolution
          (fullFunctionalEquationOrbitAnnihilator g rho.1))) +
      24 ^ 2 * ICgate g.convolutionSquare ≤ 0

theorem hgate24Predicate3107_iff_gate_qform
    {rho : sourceNontrivialZeroSet} (g : CompactLogTest) :
    hgate24Predicate3107 rho g ↔
      (![1, -24] : Fin 2 → Real) ⬝ᵥ
          (gateMatrix ![
            fullFunctionalEquationOrbitAnnihilator g rho.1, g] *ᵥ
            (![1, -24] : Fin 2 → Real)) ≤ 0 := by
  unfold hgate24Predicate3107
  rw [twoSpan_gate_qform_expand]
  constructor <;> intro h <;> nlinarith

theorem hgate24Predicate3107_iff_signed_margin
    {rho : sourceNontrivialZeroSet} (g : CompactLogTest) :
    hgate24Predicate3107 rho g ↔
      ICgate ((fullFunctionalEquationOrbitAnnihilator g rho.1).convolutionSquare) +
          24 ^ 2 * ICgate g.convolutionSquare ≤
        24 * (ICgate ((fullFunctionalEquationOrbitAnnihilator g rho.1).involution.convolution g) +
          ICgate (g.involution.convolution
            (fullFunctionalEquationOrbitAnnihilator g rho.1))) := by
  unfold hgate24Predicate3107
  constructor <;> intro h <;> nlinarith

/-- The fixed-24 predicate is exactly the semi-local gate on the same owner.

The support radius is taken from the package's actual owner geometry; no
second detector or informal owner substitution enters this equivalence.
-/
theorem hgate24Predicate3107_iff_owner_gate
    {rho : sourceNontrivialZeroSet} (pkg : RhoOwnerPackage3106 rho) :
    hgate24Predicate3107 rho pkg.g ↔
      orbitWindowSemiLocalGate
        (annihilatorDetectorSpanVector
          (fullFunctionalEquationOrbitAnnihilator pkg.g rho.1) pkg.g 24) := by
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
  unfold hgate24Predicate3107
  rw [orbitWindowSemiLocalGate_iff,
    annihilator_span_gate_eq_parabola
      (fullFunctionalEquationOrbitAnnihilator pkg.g rho.1) pkg.g 24 hw]

/-- The determinant route cannot silently choose the row-B coefficient 24.

This scalar witness has a nonnegative determinant (indeed zero), so some
coefficient is feasible, while the fixed coefficient 24 is strictly infeasible.
It is a formal guard against replacing a fixed-lambda obligation by an
existential-lambda theorem.
-/
theorem fixed_lambda24_not_implied_by_discriminant3107 :
    (1 : Real) * 1 - ((2 : Real) / 2) ^ 2 ≤ 0 ∧
      ¬ ((1 : Real) - 24 * 2 + 24 ^ 2 * 1 ≤ 0) := by
  constructor
  · norm_num
  · norm_num

end
end C1RouteBFixedLambdaGate3107
end Source
end ConnesWeilRH
