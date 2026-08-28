/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20Eq115Symmetry
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Fact-1 mass-bound consumption layer for the extracted table

CC20 Fact 1's strict mass inequality `2 * integral_[0, log 2] |chi - tau| <=
epsilon1` will be supplied by a certified quadrature table: a uniform grid
with one per-interval upper bound.  This leaf is the Lean consumption layer
for such a table ("floats generate, Lean verifies the aggregate"):

* `l1_uniform_grid` - on a uniform grid with per-interval bounds, the L1 mass
  is bounded by `step * sum bound`;
* `l1_tail_bound` - the last grid piece, ending exactly at the irrational
  endpoint `log 2`, contributes `boundTail * (log 2 - count * step)`;
* `l1_mono_upper` - a monotone upper-limit lemma for nonnegative integrands;
* `cc20Eq115_halfGapCertificate_of_uniformGrid` - the complete assembly: from
  a grid table for the difference profile plus the analytic caller fields to
  the full Fact-1 half-gap certificate.

The table itself is future data: the joint `chi - tau` enclosure needs a
concrete `CC20EndpointSpectralData` instance, which does not exist yet (the
paper states its endpoint side only asymptotically).  No numerical table is
claimed or stored here.

Reference: equations (115), (121) of <https://arxiv.org/html/2006.13771>;
companion records docs/proofs/1044.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20Eq115MassBound

open MeasureTheory Set
open CC20Concrete
open C1CC20DisplacementKernel C1CC20Eq115Symmetry C1CC20Eq115Table
  C1CC20FiniteRankApproximation C1CC20FiniteRankDifference
  C1CC20FiniteRankHalfGapCertificate C1CC20OperatorGap

/-- On a uniform grid of positive step, an integrand bounded per interval
has L1 mass at most `step * sum bound`.  Integrability and the bound are only
demanded on the tiles actually used. -/
theorem l1_uniform_grid (f : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) (B : ℕ → ℝ) :
    ∀ n : ℕ,
      (∀ j : ℕ, j < n → IntervalIntegrable f volume ((j : ℝ) * δ) (((j : ℝ) + 1) * δ)) →
      (∀ j : ℕ, j < n → ∀ v ∈ Set.Icc ((j : ℝ) * δ) (((j : ℝ) + 1) * δ), f v ≤ B j) →
      IntervalIntegrable f volume (0 : ℝ) ((n : ℝ) * δ) ∧
        ∫ v in (0 : ℝ)..((n : ℝ) * δ), f v ≤ δ * ∑ j ∈ Finset.range n, B j := by
  intro n
  induction n with
  | zero =>
    intro _ _
    refine ⟨?_, ?_⟩
    · rw [intervalIntegrable_iff]
      have h0 : ((0 : ℕ) : ℝ) * δ = 0 := by simp
      rw [h0]
      have hu : Set.uIoc (0 : ℝ) (0 : ℝ) = ∅ := by simp [Set.Ioc_eq_empty_iff]
      rw [hu]
      exact integrableOn_empty
    · have h0 : ((0 : ℕ) : ℝ) * δ = 0 := by simp
      rw [h0, intervalIntegral.integral_same]
      simp
  | succ n ih =>
    intro hint hB
    -- bridge the two spellings `↑(n + 1)` (from the goal) and `↑n + 1` (from
    -- the premise instantiated at `j := n`)
    have hc : ((n + 1 : ℕ) : ℝ) = ((n : ℝ) + 1) := Nat.cast_succ n
    rw [hc]
    have ih' := ih (fun j hj => hint j (Nat.lt_succ_of_lt hj))
      (fun j hj => hB j (Nat.lt_succ_of_lt hj))
    have hlastint := hint n (Nat.lt_succ_self n)
    have hlen : ((n : ℝ) + 1) * δ - (n : ℝ) * δ = δ := by ring
    have hlast : ∫ v in ((n : ℝ) * δ)..(((n : ℝ) + 1) * δ), f v ≤ δ * B n := by
      have hmono := intervalIntegral.integral_mono_on
        (hab := by linarith) (a := (n : ℝ) * δ) (b := ((n : ℝ) + 1) * δ)
        hlastint intervalIntegrable_const (hB n (Nat.lt_succ_self n))
      rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at hmono
      exact hmono
    refine ⟨ih'.1.trans hlastint, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals ih'.1 hlastint]
    calc (∫ v in (0 : ℝ)..((n : ℝ) * δ), f v) +
          ∫ v in ((n : ℝ) * δ)..(((n : ℝ) + 1) * δ), f v ≤
        δ * ∑ j ∈ Finset.range n, B j + δ * B n := by linarith [ih'.2, hlast]
      _ = δ * (∑ j ∈ Finset.range n, B j + B n) := by ring
      _ = δ * ∑ j ∈ Finset.range (n + 1), B j := by rw [Finset.sum_range_succ]

/-- On one interval, a pointwise upper bound gives the length-times-bound
integral bound. -/
theorem l1_tail_bound (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (B : ℝ)
    (hint : IntervalIntegrable f volume a b)
    (hB : ∀ v ∈ Set.Icc a b, f v ≤ B) :
    ∫ v in a..b, f v ≤ (b - a) * B := by
  have hmono := intervalIntegral.integral_mono_on hab hint intervalIntegrable_const hB
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  exact hmono

/-- A nonnegative integrand has a monotone upper limit. -/
theorem l1_mono_upper (f : ℝ → ℝ) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hfin : IntervalIntegrable f volume (0 : ℝ) x)
    (hint : IntervalIntegrable f volume x y)
    (hnonneg : ∀ v ∈ Set.Icc (0 : ℝ) y, 0 ≤ f v) :
    ∫ v in (0 : ℝ)..x, f v ≤ ∫ v in (0 : ℝ)..y, f v := by
  have htail : ∫ v in x..y, (0 : ℝ) ≤ ∫ v in x..y, f v :=
    intervalIntegral.integral_mono_on hxy intervalIntegrable_const hint
      (fun v hv => hnonneg v (Set.Icc_subset_Icc hx le_rfl hv))
  simp only [] at htail
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_zero] at htail
  rw [← intervalIntegral.integral_add_adjacent_intervals hfin hint]
  linarith [htail]

/-- The concrete difference profile is continuous on the ROOT window as soon
as the endpoint side is. -/
theorem continuousOn_cc20Eq115DifferenceProfile (lam : Real)
    (endpointData : CC20EndpointSpectralData)
    (hchi : ContinuousOn (endpointDisplacementProfile endpointData)
      cc20RootDisplacementWindow) :
    ContinuousOn (cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam))
      cc20RootDisplacementWindow := by
  unfold cc20FiniteRankDifferenceProfile
  exact hchi.sub (continuousOn_cc20Eq115Profile lam)

/-- The complete Fact-1 assembly for the extracted table from a uniform-grid
bound table.  The grid must stay inside the ROOT window (`count * step <=
log 2`); the last piece ends exactly at the irrational endpoint.  This is the
consumption layer a certified quadrature table will feed. -/
theorem cc20Eq115_halfGapCertificate_of_uniformGrid
    (lam : Real) (endpointData : CC20EndpointSpectralData)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (hchi : ContinuousOn (endpointDisplacementProfile endpointData)
      cc20RootDisplacementWindow)
    (count : ℕ) (step : ℝ) (hstep : 0 < step)
    (hcover : (count : ℝ) * step ≤ cc20RootLength)
    (bound : ℕ → ℝ) (boundTail : ℝ)
    (hbound : ∀ j : ℕ, j < count → ∀ v ∈ Set.Icc ((j : ℝ) * step) (((j : ℝ) + 1) * step),
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤ bound j)
    (hboundTail : ∀ v ∈ Set.Icc ((count : ℝ) * step) cc20RootLength,
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤ boundTail)
    (hsum : 2 * (step * ∑ j ∈ Finset.range count, bound j +
        (cc20RootLength - (count : ℝ) * step) * boundTail) ≤ gapData.epsilon1) :
    CC20FiniteRankHalfGapCertificate endpointData (cc20Eq115Data lam) gapData := by
  have hfc : ContinuousOn
      (fun v => ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖)
      (Set.Icc (0 : ℝ) cc20RootLength) := by
    refine (continuousOn_cc20Eq115DifferenceProfile lam endpointData hchi).norm.mono ?_
    intro v hv
    exact ⟨by linarith [cc20RootLength_pos, hv.1, hv.2], hv.2⟩
  have hint : ∀ j : ℕ, j < count →
      IntervalIntegrable
        (fun v => ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖)
        volume ((j : ℝ) * step) (((j : ℝ) + 1) * step) := by
    intro j hj
    have hsu : ((j : ℝ) + 1) * step = (j : ℝ) * step + step := by ring
    have hab : (j : ℝ) * step ≤ ((j : ℝ) + 1) * step := by rw [hsu]; linarith
    have hj1 : ((j : ℝ) + 1) * step ≤ (count : ℝ) * step := by
      refine mul_le_mul_of_nonneg_right ?_ hstep.le
      exact_mod_cast Nat.succ_le_of_lt hj
    have hj0 : (0 : ℝ) ≤ (j : ℝ) * step := mul_nonneg (Nat.cast_nonneg' j) hstep.le
    have hsub : Set.Icc ((j : ℝ) * step) (((j : ℝ) + 1) * step) ⊆
        Set.Icc (0 : ℝ) cc20RootLength :=
      Set.Icc_subset_Icc hj0 (le_trans hj1 hcover)
    exact ContinuousOn.intervalIntegrable_of_Icc hab (hfc.mono hsub)
  have htailint : IntervalIntegrable
      (fun v => ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖)
      volume ((count : ℝ) * step) cc20RootLength :=
    ContinuousOn.intervalIntegrable_of_Icc hcover
      (hfc.mono (Set.Icc_subset_Icc (mul_nonneg (Nat.cast_nonneg' count) hstep.le) le_rfl))
  have hgrid := l1_uniform_grid
    (fun v => ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖)
    step hstep bound count hint (fun j hj => hbound j hj)
  have htail := l1_tail_bound
    (fun v => ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖)
    ((count : ℝ) * step) cc20RootLength hcover boundTail htailint hboundTail
  have hmass : 2 * (∫ v in (0 : ℝ)..cc20RootLength,
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖) ≤
      gapData.epsilon1 := by
    have hg2 := hgrid.2
    have ht := htail
    simp only [] at hg2 ht
    rw [← intervalIntegral.integral_add_adjacent_intervals hgrid.1 htailint]
    linarith [hg2, ht, hsum]
  exact cc20Eq115_halfGapCertificate lam endpointData gapData hchi hmass

end C1CC20Eq115MassBound
end Source
end ConnesWeilRH
