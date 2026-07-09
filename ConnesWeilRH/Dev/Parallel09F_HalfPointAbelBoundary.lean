/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.DirichletEta

/-!
# 09F half-point Abel-boundary audit

This scratch module is owned by the 09F parallel lane.  It does not integrate
the production 05A file.  It isolates the exact Abel-boundary socket needed to
identify Mathlib's half-period `cosZeta` value with the ordered eta boundary.
-/

namespace ConnesWeilRH
namespace Dev
namespace Parallel09F

open Filter
open scoped BigOperators
open scoped Topology

/-- The half-period cosine coefficient used by Mathlib's `cosZeta` L-series. -/
noncomputable abbrev halfPeriodCosCoeff (k : ℕ) : ℂ :=
  Complex.cos (2 * (Real.pi : ℂ) * (1 / 2 : ℂ) * (k : ℂ))

/--
The exact 09F Abel-boundary socket.

It says that the radial Abel boundary of the half-period `cosZeta` L-series
items at `s = 1/2` is Mathlib's analytically continued `cosZeta` value.
-/
def HalfPeriodCosZetaFullLSeriesAbelBoundary : Prop :=
  Tendsto
    (fun x : ℝ =>
      ∑' m : ℕ,
        LSeries.term
          (fun k : ℕ =>
            Complex.cos (2 * (Real.pi : ℂ) * (1 / 2 : ℂ) * (k : ℂ)))
          (1 / 2 : ℂ) m * (x : ℂ) ^ m)
    (𝓝[<] (1 : ℝ))
    (𝓝
      (HurwitzZeta.cosZeta
        (ZMod.toAddCircle (1 : ZMod 2))
        (1 / 2 : ℂ)))

/--
The named 09F socket is strong enough to close the half-point eta analytic
identification through the existing production bridge.
-/
theorem halfPeriodCosZetaFullLSeriesAbelBoundary_closes_09F
    (h : HalfPeriodCosZetaFullLSeriesAbelBoundary) :
    Source.dirichletEtaAnalytic (1 / 2 : ℂ) =
      (Source.dirichletEtaRealHalfOrdered : ℂ) := by
  exact
    Source.dirichletEtaAnalytic_half_eq_ordered_of_full_lseries_cosZeta_half_period_abel_limit
      (by
        simpa [HalfPeriodCosZetaFullLSeriesAbelBoundary, halfPeriodCosCoeff]
          using h)

/--
The 09F Abel-boundary socket is exactly the missing half-period value
identification, because the ordered side of the same radial series is already
proved in `Source.DirichletEta`.
-/
theorem halfPeriodCosZetaFullLSeriesAbelBoundary_iff_value :
    HalfPeriodCosZetaFullLSeriesAbelBoundary ↔
      HurwitzZeta.cosZeta
          (ZMod.toAddCircle (1 : ZMod 2))
          (1 / 2 : ℂ) =
        -(Source.dirichletEtaRealHalfOrdered : ℂ) := by
  constructor
  · intro h
    exact
      Source.cosZeta_half_period_eq_neg_dirichletEtaRealHalfOrdered_of_full_lseries_abel_limit
        (by
          simpa [HalfPeriodCosZetaFullLSeriesAbelBoundary, halfPeriodCosCoeff]
            using h)
  · intro hvalue
    have hordered :=
      Source.tendsto_lseries_cosZeta_half_period_powerSeries_nhdsWithin_lt_ordered
    simpa [HalfPeriodCosZetaFullLSeriesAbelBoundary, halfPeriodCosCoeff, ← hvalue]
      using hordered

/--
Mathlib/API bottom isolated by 09F.

This is the missing Abelian theorem for the concrete half-period cosine
L-series: the radial Abel sum of the L-series terms at `s = 1/2` must recover
the analytically continued `cosZeta` value.  Existing Mathlib proves the
Dirichlet-series formula only in the safe domain `1 < re s`; it does not expose
this radial boundary statement at `s = 1/2`.
-/
def HalfPeriodCosZetaAnalyticContinuationAbelBoundary : Prop :=
  HalfPeriodCosZetaFullLSeriesAbelBoundary

theorem strict_09F_socket_is_analytic_continuation_abel_boundary :
    HalfPeriodCosZetaFullLSeriesAbelBoundary ↔
      HalfPeriodCosZetaAnalyticContinuationAbelBoundary := by
  rfl

/--
Positive-strip eta agreement recovered from the lower paired-term owner.

This is the useful 09F move: it does not cite the final half-point theorem
`Source.dirichletEtaAnalytic_half_eq_ordered`.  Instead it combines the
paired-term analytic continuation theorem with the ordered real paired-term
evaluation at the same positive real parameter.
-/
theorem dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos_from_pair_owner
    {sigma : ℝ} (hsigma : 0 < sigma) :
    Source.dirichletEtaAnalytic (sigma : ℂ) =
      (Source.orderedEtaValue sigma : ℂ) := by
  have hpair :
      (∑' n : ℕ, Source.etaPairTermComplex (sigma : ℂ) n) =
        Source.dirichletEtaAnalytic (sigma : ℂ) :=
    Source.etaPairTermComplex_tsum_eq_dirichletEtaAnalytic_on_re_pos
      (by simpa using hsigma)
  have hordered :
      (∑' n : ℕ, Source.etaPairTermComplex ((sigma : ℝ) : ℂ) n) =
        (Source.orderedEtaValue sigma : ℂ) :=
    Source.etaPairTermComplex_tsum_ofReal_eq_orderedEtaValue hsigma
  exact hpair.symm.trans (by simpa using hordered)

/--
Half-point eta identification derived through the positive-strip agreement,
not by citing the existing final half-point theorem.
-/
theorem dirichletEtaAnalytic_half_eq_ordered_from_positive_strip :
    Source.dirichletEtaAnalytic (1 / 2 : ℂ) =
      (Source.dirichletEtaRealHalfOrdered : ℂ) := by
  have h :=
    dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos_from_pair_owner
      (sigma := (1 / 2 : ℝ)) (by norm_num : 0 < (1 / 2 : ℝ))
  rw [Source.orderedEtaValue_half_eq_dirichletEtaRealHalfOrdered] at h
  simpa using h

/--
The strict Abel-boundary socket closes from the positive-strip paired owner.

This proves the socket without citing `Source.dirichletEtaAnalytic_half_eq_ordered`
directly; the route is through the lower positive-strip agreement above.
-/
theorem halfPeriodCosZetaFullLSeriesAbelBoundary_from_positive_strip :
    HalfPeriodCosZetaFullLSeriesAbelBoundary := by
  apply halfPeriodCosZetaFullLSeriesAbelBoundary_iff_value.mpr
  have hneg :
      -HurwitzZeta.cosZeta
          (ZMod.toAddCircle (1 : ZMod 2))
          (1 / 2 : ℂ) =
        (Source.dirichletEtaRealHalfOrdered : ℂ) := by
    have h := dirichletEtaAnalytic_half_eq_ordered_from_positive_strip
    rw [Source.dirichletEtaAnalytic_half_eq_neg_cosZeta_half] at h
    exact h
  have h := congrArg Neg.neg hneg
  simpa using h

#check HalfPeriodCosZetaFullLSeriesAbelBoundary
#check halfPeriodCosZetaFullLSeriesAbelBoundary_closes_09F
#check halfPeriodCosZetaFullLSeriesAbelBoundary_iff_value
#check HalfPeriodCosZetaAnalyticContinuationAbelBoundary
#check strict_09F_socket_is_analytic_continuation_abel_boundary
#check dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos_from_pair_owner
#check dirichletEtaAnalytic_half_eq_ordered_from_positive_strip
#check halfPeriodCosZetaFullLSeriesAbelBoundary_from_positive_strip
#print axioms halfPeriodCosZetaFullLSeriesAbelBoundary_closes_09F
#print axioms halfPeriodCosZetaFullLSeriesAbelBoundary_iff_value
#print axioms strict_09F_socket_is_analytic_continuation_abel_boundary
#print axioms dirichletEtaAnalytic_ofReal_eq_orderedEtaValue_of_pos_from_pair_owner
#print axioms dirichletEtaAnalytic_half_eq_ordered_from_positive_strip
#print axioms halfPeriodCosZetaFullLSeriesAbelBoundary_from_positive_strip

end Parallel09F
end Dev
end ConnesWeilRH
