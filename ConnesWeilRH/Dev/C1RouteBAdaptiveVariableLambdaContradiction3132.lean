import ConnesWeilRH.Dev.C1RouteBVariableLambdaGate3130

namespace ConnesWeilRH.Source.C1RouteBAdaptiveVariableLambdaContradiction3132

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open C1FourPointSpectralPrefixTransport
open C1OrbitWindowSemiLocalGate
open C1RouteBRhoOwnerPackage3106
open C1RouteBVariableLambdaGate3130
open C1TwoPointSpectralDecomposition

noncomputable section

/-- A strict negative Weil value on the exact rho-owner excludes the arbitrary
variable-lambda gate predicate on that same span. -/
theorem negative_owner_rejects_variable_lambda_gate3132
    {rho : sourceNontrivialZeroSet} (pkg : RhoOwnerPackage3106 rho)
    (lambda : ℝ)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet
      (annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator pkg.g rho.1) pkg.g lambda))
    (hneg : C1SameOwnerWeil.qw
      (annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator pkg.g rho.1) pkg.g lambda) < 0) :
    ¬ variableLambdaGatePredicate3130 rho pkg.g lambda := by
  intro hpred
  have hgate : orbitWindowSemiLocalGate
      (annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator pkg.g rho.1) pkg.g lambda) :=
    (variableLambdaGatePredicate3130_iff_owner_gate pkg lambda).mp hpred
  have hqwnonneg : 0 ≤ C1SameOwnerWeil.qw
      (annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator pkg.g rho.1) pkg.g lambda) :=
    qw_nonneg_of_orbitWindowSemiLocalGate _ hvanishes hgate
  exact (not_lt_of_ge hqwnonneg) hneg

end
end ConnesWeilRH.Source.C1RouteBAdaptiveVariableLambdaContradiction3132