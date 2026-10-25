import ConnesWeilRH.Dev.C1RouteAJointSymbolNegativeNeighbourhood3088

/-!
# Route A joint-symbol continuity (record 3091)

This module proves continuity at zero for the actual finite joint symbol.  The
special-function sign margin is intentionally separate.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAJointSymbolContinuity3091

open C1RouteAJointSymbolData3080
open C1G8R0OrbitGeometry
open CC20YoshidaNearZeros
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open Dev
open scoped Topology BigOperators

noncomputable section

theorem routeAPrimePoissonSymbol_continuousAt_zero
    (p : Nat) (hp : Nat.Prime p) :
    ContinuousAt (fun xi : Real => routeAPrimePoissonSymbol p xi) 0 := by
  let r : Real := 1 / Real.sqrt (p : Real)
  have hpcast : (1 : Real) < (p : Real) := by exact_mod_cast hp.one_lt
  have hsqrt : 1 < Real.sqrt (p : Real) := by
    have hsquare := Real.sq_sqrt (show 0 ≤ (p : Real) by positivity)
    have hsqrt_nonneg : 0 ≤ Real.sqrt (p : Real) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (1 - Real.sqrt (p : Real))]
  have hrlt : r < 1 := by
    dsimp [r]
    rw [div_lt_iff₀ (Real.sqrt_pos.mpr (show 0 < (p : Real) by positivity))]
    simpa using hsqrt
  have hden' : 1 - 2 * r + r ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos (show 0 < 1 - r by linarith)]
  unfold routeAPrimePoissonSymbol
  change ContinuousAt (fun xi : Real =>
    (1 - r ^ 2) /
      (1 - 2 * r * Real.cos (Real.log (p : Real) * xi) + r ^ 2) - 1) 0
  apply ContinuousAt.sub
  · apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using hden'
  · fun_prop

theorem routeAJointSymbol_continuousAt_zero_of_c3Sigma
    {rho : sourceNontrivialZeroSet}
    {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hsigma : ContinuousAt Dev.c3Sigma 0) :
    ContinuousAt (routeAJointSymbol geometry) 0 := by
  unfold routeAJointSymbol
  apply ContinuousAt.sub
  · exact hsigma.neg
  · let S := routeAVisiblePrimes geometry
    have hsum_cont : ∀ T : Finset Nat, (∀ p ∈ T, Nat.Prime p) →
        ContinuousAt (fun xi : Real =>
          ∑ p ∈ T, Real.log (p : Real) * routeAPrimePoissonSymbol p xi) 0 := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
          intro _
          simpa using (continuousAt_const : ContinuousAt (fun _ : Real => (0 : Real)) 0)
      | @insert p s hp ih =>
          intro hprime
          simp only [Finset.sum_insert hp]
          exact (continuousAt_const.mul
            (routeAPrimePoissonSymbol_continuousAt_zero p
              (hprime p (by simp [hp])))).add
            (ih (fun q hq => hprime q (by simp [hq])))
    have hsum : ContinuousAt (fun xi : Real =>
        ∑ p ∈ S, Real.log (p : Real) * routeAPrimePoissonSymbol p xi) 0 :=
      hsum_cont S (by
        intro p hp
        exact (Finset.mem_filter.mp hp).2)
    simpa [S] using hsum

end
end C1RouteAJointSymbolContinuity3091
end Source
end ConnesWeilRH
