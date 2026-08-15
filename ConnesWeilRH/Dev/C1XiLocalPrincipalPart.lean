import ConnesWeilRH.Dev.C1XiVerticalFunctional

/-!
# C1XiLocalPrincipalPart - local xi-zero factorization for Gate 2

The total Lean function `logDeriv completedRiemannXi` is assigned a value at a
zero, while a contour argument needs the punctured local meromorphic object.
This module starts that bridge from the analytic order already attached to the
source spectral index: at each xi zero, the completed xi function factors as
`(s - rho)^m * h(s)` with `h(rho) != 0`.

No residue theorem, contour identity, explicit-formula equality, or RH claim
is introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiLocalPrincipalPart

open Filter
open CC20ZetaCounting
open CC20YoshidaNearZeros
open C1SpectralWeil
open C1XiVerticalFunctional
open scoped Topology

/-- Every source xi zero has the exact local analytic factorization dictated
by its analytic multiplicity.  The cofactor is nonzero at the zero, so it is
the correct owner for a later punctured logarithmic-derivative calculation. -/
theorem exists_completedRiemannXi_local_factor
    (rho : sourceNontrivialZeroSet) :
    ∃ h : Complex -> Complex, AnalyticAt Complex h rho.1 ∧ h rho.1 ≠ 0 ∧
      completedRiemannXi =ᶠ[𝓝 rho.1]
        fun s => (s - rho.1) ^ xiMultiplicity rho * h s := by
  obtain ⟨h, hanalytic, hnonzero, hfactor⟩ :=
    (differentiable_completedRiemannXi.analyticAt rho.1).analyticOrderAt_ne_top.mp
      (completedRiemannXi_analyticOrderAt_ne_top rho.1)
  refine ⟨h, hanalytic, hnonzero, ?_⟩
  filter_upwards [hfactor] with s hs
  simpa only [xiMultiplicity, smul_eq_mul] using hs

/-- On the punctured neighborhood of a xi zero, the negative logarithmic
derivative separates into its multiplicity pole and the analytic cofactor.
Unlike the total value of `logDeriv` at the zero, this is the local identity
that a contour calculation may use. -/
theorem exists_negativeXiLogDeriv_local_principal_part
    (rho : sourceNontrivialZeroSet) :
    ∃ h : Complex -> Complex, AnalyticAt Complex h rho.1 ∧ h rho.1 ≠ 0 ∧
      ∀ᶠ s in 𝓝[≠] rho.1,
        negativeXiLogDeriv s =
          -((xiMultiplicity rho : Complex) / (s - rho.1)) - logDeriv h s := by
  obtain ⟨h, hanalytic, hnonzero, hfactor⟩ :=
    exists_completedRiemannXi_local_factor rho
  refine ⟨h, hanalytic, hnonzero, ?_⟩
  have hderiv := hfactor.deriv
  have hcofactor_ne : ∀ᶠ s in 𝓝 rho.1, h s ≠ 0 :=
    (hanalytic.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hnonzero
  filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds,
    hderiv.filter_mono nhdsWithin_le_nhds,
    hanalytic.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hcofactor_ne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with
      s hvalue hderiv hanalyticS hcofactor_ne hsne
  have hlog :
      logDeriv completedRiemannXi s =
        logDeriv (fun z => (z - rho.1) ^ xiMultiplicity rho * h z) s := by
    rw [logDeriv_apply, logDeriv_apply, hderiv, hvalue]
  have hpow_ne : (s - rho.1) ^ xiMultiplicity rho ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr hsne)
  have hpow_diff : DifferentiableAt Complex
      (fun z => (z - rho.1) ^ xiMultiplicity rho) s := by
    fun_prop
  have hshift : logDeriv (fun z : Complex => z - rho.1) s =
      1 / (s - rho.1) := by
    rw [logDeriv_apply, deriv_sub_const]
    simp
  unfold negativeXiLogDeriv
  rw [hlog, logDeriv_mul s hpow_ne hcofactor_ne hpow_diff
    hanalyticS.differentiableAt]
  rw [logDeriv_fun_pow (f := fun z : Complex => z - rho.1) (by fun_prop)
    (xiMultiplicity rho), hshift]
  ring

end C1XiLocalPrincipalPart
end Source
end ConnesWeilRH
