import ConnesWeilRH.Dev.C1HealthyTestSpace

/-! # C1WeilExplicit — the explicit healthy Weil `psi`, finite-prime `{2}` slot

Materialises the honest, explicit `WeilFormSymbols.PsiSignStatement`-style formula on
the healthy carrier:

    psi F = poleFunctional F - totalArchimedean F - sum_{n in {2}} finitePrimeTerm n F

built from the genuine healthy components (healthyEval, totalArchimedean, the healthy
finite-prime `{2}` support), plus the finite-prime collapse `{2} -> {prime 2}`.

HONEST SCOPE:  this sets the *formula*; the criterion `psi(conv^2 F) <= 0`
(RH-equivalent) is NOT asserted.  RH NOT claimed.
-/
namespace ConnesWeilRH
namespace Source
namespace C1WeilExplicit

open AnalyticCore
open CCM25Concrete.CompactArchTotal
open CCM25Concrete.CompactLogConvolution
open Dev.WellFormHealthyRepoint
open scoped BigOperators

/-- The healthy explicit full-field psi: pole minus archimedean minus the
   finite-prime sum over the healthy support `{2}`. -/
noncomputable def healthyPsi (F : TestFunction) : Real :=
  (Dev.WellFormHealthyRepoint.healthyEval.poleFunctional F -
    totalArchimedean F) -
      Dev.WellFormHealthyRepoint.healthyEval.sourceFinitePrimeTerm 2 F

/-- `qw` reads psi of the convolution square, materialising `QWDefinitionStatement`. -/
noncomputable def healthyQw (g : CompactLogTest) : Real :=
  healthyPsi (g.convolutionSquare.test)

/-- The healthy finite-prime support over the index `{2}` collapses to the
   single term at the prime `2`. -/
theorem healthyPrimeSum_two (F : TestFunction) :
    (∑ n ∈ ({2} : Finset ℕ),
        Dev.WellFormHealthyRepoint.healthyEval.sourceFinitePrimeTerm n F) =
      Dev.WellFormHealthyRepoint.healthyEval.sourceFinitePrimeTerm 2 F := by
  simp

/-- `healthyPsi` expands to pole - arch - (single finite-prime term at 2): the
   honest explicit formula, up to the index-set collapse. -/
theorem healthyPsi_two (F : TestFunction) :
    healthyPsi F =
      (Dev.WellFormHealthyRepoint.healthyEval.poleFunctional F - totalArchimedean F) -
        (∑ n ∈ ({2} : Finset ℕ),
          Dev.WellFormHealthyRepoint.healthyEval.sourceFinitePrimeTerm n F) := by
  unfold healthyPsi
  rw [<- healthyPrimeSum_two]

end C1WeilExplicit
end Source
end ConnesWeilRH

