/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.DirichletEta

/-!
# The CC20 triple and the zeta-half boundary

This module records the exact lower theorem needed to prove that the CC20
finite-vanishing triple is disjoint from the standard source nontrivial zeros.
The project currently has no proof of `ζ(1/2) ≠ 0`; the disjointness theorem is
therefore parameterized by that precise statement.
-/

namespace ConnesWeilRH
namespace Source

open Filter
open Set
open scoped BigOperators
open scoped Topology

def RiemannZetaHalfNonvanishing : Prop :=
  riemannZeta (1 / 2 : ℂ) ≠ 0

theorem riemannZeta_half_ne_zero_of_dirichletEtaRealHalfOrdered_identity
    (heta :
      (dirichletEtaRealHalfOrdered : ℂ) =
        ((1 : ℂ) - (2 : ℂ) ^ (1 - (1 / 2 : ℂ))) *
          riemannZeta (1 / 2 : ℂ)) :
    RiemannZetaHalfNonvanishing := by
  intro hzero
  have hetaZero : (dirichletEtaRealHalfOrdered : ℂ) = 0 := by
    rw [heta, hzero, mul_zero]
  have hetaNeZero : (dirichletEtaRealHalfOrdered : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt dirichletEtaRealHalfOrdered_pos
  exact hetaNeZero hetaZero

theorem cc20_triple_disjoint_from_standard_source_nontrivial_zeros_of_zeta_half_ne_zero
    (hhalf : RiemannZetaHalfNonvanishing) :
    SourceFiniteSetDisjointFromNontrivialZeros
      RHDefinitionBridge.standard
      cc20TripleFiniteVanishingSet := by
  intro p _hp hzero
  cases p
  · have hz : riemannZeta (0 : ℂ) = 0 :=
      RHDefinitionBridge.standard_mathlib_zeta_zero_of_source_nontrivial_zero
        (0 : ℂ) hzero
    rw [riemannZeta_zero] at hz
    norm_num at hz
  · have hz : riemannZeta (1 / 2 : ℂ) = 0 :=
      RHDefinitionBridge.standard_mathlib_zeta_zero_of_source_nontrivial_zero
        (1 / 2 : ℂ) hzero
    exact hhalf hz
  · have hpole : (1 : ℂ) ≠ 1 :=
      RHDefinitionBridge.standard_mathlib_no_pole_of_source_nontrivial_zero
        (1 : ℂ) hzero
    exact hpole rfl

theorem cc20_triple_disjoint_of_dirichletEtaRealHalfOrdered_identity
    (heta :
      (dirichletEtaRealHalfOrdered : ℂ) =
        ((1 : ℂ) - (2 : ℂ) ^ (1 - (1 / 2 : ℂ))) *
          riemannZeta (1 / 2 : ℂ)) :
    SourceFiniteSetDisjointFromNontrivialZeros
      RHDefinitionBridge.standard
      cc20TripleFiniteVanishingSet :=
  cc20_triple_disjoint_from_standard_source_nontrivial_zeros_of_zeta_half_ne_zero
    (riemannZeta_half_ne_zero_of_dirichletEtaRealHalfOrdered_identity heta)

theorem riemannZeta_half_ne_zero_of_dirichletEtaAnalytic_half_eq_ordered
    (heta :
      dirichletEtaAnalytic (1 / 2 : ℂ) =
        (dirichletEtaRealHalfOrdered : ℂ)) :
    RiemannZetaHalfNonvanishing := by
  apply riemannZeta_half_ne_zero_of_dirichletEtaRealHalfOrdered_identity
  rw [← heta]
  exact dirichletEtaAnalytic_half_eq_factor_mul_riemannZeta

theorem cc20_triple_disjoint_of_dirichletEtaAnalytic_half_eq_ordered
    (heta :
      dirichletEtaAnalytic (1 / 2 : ℂ) =
        (dirichletEtaRealHalfOrdered : ℂ)) :
    SourceFiniteSetDisjointFromNontrivialZeros
      RHDefinitionBridge.standard
      cc20TripleFiniteVanishingSet :=
  cc20_triple_disjoint_from_standard_source_nontrivial_zeros_of_zeta_half_ne_zero
    (riemannZeta_half_ne_zero_of_dirichletEtaAnalytic_half_eq_ordered heta)

theorem riemannZeta_half_ne_zero :
    RiemannZetaHalfNonvanishing :=
  riemannZeta_half_ne_zero_of_dirichletEtaAnalytic_half_eq_ordered
    dirichletEtaAnalytic_half_eq_ordered

theorem cc20_triple_disjoint_from_standard_source_nontrivial_zeros :
    SourceFiniteSetDisjointFromNontrivialZeros
      RHDefinitionBridge.standard
      cc20TripleFiniteVanishingSet :=
  cc20_triple_disjoint_from_standard_source_nontrivial_zeros_of_zeta_half_ne_zero
    riemannZeta_half_ne_zero

theorem riemannZeta_half_ne_zero_of_neg_cosZeta_half_period_abel_limit
    (habel :
      Tendsto
        (fun x : ℝ =>
          ((∑' n : ℕ, ((-1 : ℝ) ^ n * etaHalfTerm n) * x ^ n : ℝ) : ℂ))
        (𝓝[<] (1 : ℝ))
        (𝓝
          (-HurwitzZeta.cosZeta
            (ZMod.toAddCircle (1 : ZMod 2))
            (1 / 2 : ℂ)))) :
    RiemannZetaHalfNonvanishing :=
  riemannZeta_half_ne_zero_of_dirichletEtaRealHalfOrdered_identity
    (dirichletEtaRealHalfOrdered_eq_factor_mul_riemannZeta_half_of_cosZeta_abel
      habel)

theorem cc20_triple_disjoint_of_neg_cosZeta_half_period_abel_limit
    (habel :
      Tendsto
        (fun x : ℝ =>
          ((∑' n : ℕ, ((-1 : ℝ) ^ n * etaHalfTerm n) * x ^ n : ℝ) : ℂ))
        (𝓝[<] (1 : ℝ))
        (𝓝
          (-HurwitzZeta.cosZeta
            (ZMod.toAddCircle (1 : ZMod 2))
            (1 / 2 : ℂ)))) :
    SourceFiniteSetDisjointFromNontrivialZeros
      RHDefinitionBridge.standard
      cc20TripleFiniteVanishingSet :=
  cc20_triple_disjoint_from_standard_source_nontrivial_zeros_of_zeta_half_ne_zero
    (riemannZeta_half_ne_zero_of_neg_cosZeta_half_period_abel_limit habel)

theorem riemannZeta_half_ne_zero_of_full_lseries_cosZeta_half_period_abel_limit
    (hfull :
      Tendsto
        (fun x : ℝ =>
          ∑' m : ℕ,
            LSeries.term
              (fun k : ℕ =>
                ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ))
              (1 / 2 : ℂ) m * (x : ℂ) ^ m)
        (𝓝[<] (1 : ℝ))
        (𝓝
          (HurwitzZeta.cosZeta
            (ZMod.toAddCircle (1 : ZMod 2))
            (1 / 2 : ℂ)))) :
    RiemannZetaHalfNonvanishing :=
  riemannZeta_half_ne_zero_of_dirichletEtaAnalytic_half_eq_ordered
    (dirichletEtaAnalytic_half_eq_ordered_of_full_lseries_cosZeta_half_period_abel_limit
      hfull)

theorem cc20_triple_disjoint_of_full_lseries_cosZeta_half_period_abel_limit
    (hfull :
      Tendsto
        (fun x : ℝ =>
          ∑' m : ℕ,
            LSeries.term
              (fun k : ℕ =>
                ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * (k : ℝ)) : ℝ) : ℂ))
              (1 / 2 : ℂ) m * (x : ℂ) ^ m)
        (𝓝[<] (1 : ℝ))
        (𝓝
          (HurwitzZeta.cosZeta
            (ZMod.toAddCircle (1 : ZMod 2))
            (1 / 2 : ℂ)))) :
    SourceFiniteSetDisjointFromNontrivialZeros
      RHDefinitionBridge.standard
      cc20TripleFiniteVanishingSet :=
  cc20_triple_disjoint_from_standard_source_nontrivial_zeros_of_zeta_half_ne_zero
    (riemannZeta_half_ne_zero_of_full_lseries_cosZeta_half_period_abel_limit
      hfull)

end Source
end ConnesWeilRH
