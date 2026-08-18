import ConnesWeilRH.Dev.C1PositiveTraceLimitBridge
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity

/-!
# C1PositiveTraceLimitBridgeExit - conditional source-RH consumer

This leaf composes the remainder-aware positive-trace consumer with the
already-closed right-oriented Yoshida detector exit.  It exposes exactly the
remaining analytic producer obligation: one same-owner trace family for each
healthy triple-vanishing test.

The theorem is conditional.  It does not construct the operators, prove the
trace-class estimates, identify the remainder, or claim unconditional RH.
-/

namespace ConnesWeilRH
namespace Source
namespace C1PositiveTraceLimitBridgeExit

open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1HealthyYoshidaSpectralNegativity
open C1PositiveTraceLimitBridge

noncomputable section

/-- A genuine same-owner positive-trace limit family on every healthy
triple-vanishing square supplies the sole sign premise required by the
right-oriented conditional RH exit. -/
theorem sourceRH_of_positiveTraceLimitFamily
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis ι ℂ H)
    (hfamily :
      ∀ g : CompactLogTest,
        CC20VanishesOn C1.healthyCC20TestSpace
          cc20TripleFiniteVanishingSet g →
          PositiveTraceLimitFamily basis g) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_global_spectral_nonneg
  intro g hvanishing
  exact spectral_nonnegative_of_positiveTraceLimitFamily
    (hfamily g hvanishing)

end
end C1PositiveTraceLimitBridgeExit
end Source
end ConnesWeilRH
