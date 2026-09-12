/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1SpectralQwAssembly
import ConnesWeilRH.Dev.C1N1SamplingContest

/-!
# C1A2WindowSplit - the L1 window-split summability brick (record 1362 s3/s3a)

Build preregistration: docs/proofs/1362_A2_to_gate_brick_decomposition.md
(the four consumer statements `windowMass_split_on`, `windowMass_split_off`,
`qw_window_assembly`, `contestForm_windowwise_iff` are LOCKED there, with the
pre-digit s3a amendments, before any build log exists - law-42 discipline).

This leaf is pure summability bookkeeping over the committed spectral
dictionary: the total on-line and off-line spectral masses equal the sums
of their ordinate-window parts (T1/T2), the `qw` ledger re-assembles in
window coordinates (T3), and the committed contest balance (B4.1) becomes
the window-sum contest (T4). No zeta input of any kind is used or needed.

The current Mathlib snapshot ships summability-level reindexing
(`Equiv.summable_iff`, `Summable.comp_injective`) but no value-level
transfer, so this brick carries one small infrastructure lemma
(`hasSum_comp_equiv`, a Finset-net argument); the fiber Fubini itself is
the name-checked `HasSum.sigma`. Every other ingredient is a
name-checked existing lemma (1362 s4 iteration ledger).

Proves no inequality about zeta; certifies nothing toward the gate. The
count-to-energy bridge (L2a-L2c of 1362 s5) is the registered wall and is
NOT part of this leaf. RH is not claimed anywhere.
-/

namespace ConnesWeilRH
namespace Source
namespace C1A2WindowSplit

open CC20YoshidaNearZeros
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1SpectralOnlineSplit
open C1SpectralQwAssembly
open C1SpectralSummability

noncomputable section

/-! ### Ordinate windows (T0) -/

/-- The window index of a zero: which half-open ordinate window `[kW,(k+1)W)`
contains its imaginary part (`Int.floor` of the scaled ordinate). -/
def windowIndex (W : Real) (rho : sourceNontrivialZeroSet) : Int :=
  Int.floor (rho.1.im / W)

/-- The ordinate window of index `k` and width `W`: the fiber of
`windowIndex`. By construction the fibers partition the zero-index set. -/
def windowSet (W : Real) (k : Int) : Set sourceNontrivialZeroSet :=
  {rho | windowIndex W rho = k}

/-- Every zero lies in exactly one ordinate window. -/
theorem windowSet_unique (W : Real) (rho : sourceNontrivialZeroSet) :
    ExistsUnique (fun k => rho ∈ windowSet W k) :=
  ⟨windowIndex W rho, rfl, fun _ hk => hk.symm⟩

/-- Distinct window indices give disjoint window sets. -/
theorem windowSet_disjoint {W : Real} {i j : Int} (hij : i ≠ j) :
    Disjoint (windowSet W i) (windowSet W j) := by
  rw [Set.disjoint_left]
  intro rho h1 h2
  have e1 : windowIndex W rho = i := h1
  have e2 : windowIndex W rho = j := h2
  exact hij (e1.symm.trans e2)

/-- T0: with positive width, window membership is exactly the half-open
ordinate interval characterization (1362 s3a statement). -/
theorem windowSet_mem (W : Real) (hW : 0 < W) (k : Int)
    (rho : sourceNontrivialZeroSet) :
    rho ∈ windowSet W k ↔
      (k : Real) * W ≤ rho.1.im ∧ rho.1.im < ((k : Real) + 1) * W := by
  constructor
  · intro h
    have he : (windowIndex W rho : Real) = (k : Real) := by exact_mod_cast h
    have h1 : (windowIndex W rho : Real) ≤ rho.1.im / W := by
      show (Int.floor (rho.1.im / W) : Real) ≤ _
      exact Int.floor_le _
    have h2 : rho.1.im / W < (windowIndex W rho : Real) + 1 := by
      show _ < (Int.floor (rho.1.im / W) : Real) + 1
      exact Int.lt_floor_add_one _
    rw [he] at h1 h2
    exact ⟨(le_div_iff₀ hW).mp h1, (div_lt_iff₀ hW).mp h2⟩
  · rintro ⟨h1, h2⟩
    show Int.floor (rho.1.im / W) = k
    refine Int.floor_eq_iff.mpr ⟨(le_div_iff₀ hW).mpr h1, ?_⟩
    exact (div_lt_iff₀ hW).mpr h2

/-! ### Reindexing infrastructure (1362 s3a/s4) -/

/-- Value-level transfer of a `HasSum` along an index equivalence. The
current Mathlib snapshot provides `Equiv.summable_iff` and
`Summable.comp_injective` (summability only) but no value-level version,
so the net-of-finsets argument is carried here explicitly. -/
theorem hasSum_comp_equiv {α β E : Type} [AddCommMonoid E] [TopologicalSpace E]
    {f : α → E} {a : E} (e : β ≃ α) (hf : HasSum f a) : HasSum (f ∘ e) a := by
  classical
  unfold HasSum at hf ⊢
  have hT : Filter.Tendsto (fun s : Finset β => s.image e)
      (SummationFilter.unconditional β).filter
      (SummationFilter.unconditional α).filter := by
    show Filter.Tendsto (fun s : Finset β => s.image e) Filter.atTop Filter.atTop
    refine Filter.tendsto_atTop_atTop_of_monotone
      (fun s₁ s₂ hs => Finset.image_subset_image hs) ?_
    intro t
    refine ⟨t.image e.symm, ?_⟩
    rw [Finset.image_image,
      show e ∘ e.symm = id from funext fun x => e.apply_symm_apply x,
      Finset.image_id]
  have hnet : (fun s : Finset β => ∑ b ∈ s, (f ∘ e) b) =
      (fun t : Finset α => ∑ b ∈ t, f b) ∘ (fun s : Finset β => s.image e) := by
    funext s
    exact (Finset.sum_image
      (show Set.InjOn e (↑s) from fun x _ y _ h => e.injective h)).symm
  rw [hnet]
  exact hf.comp hT

/-- Fiber Fubini (HasSum form) for summable real families over the
ordinate-window partition. No sign assumption; unconditional summability
is the whole content. -/
theorem hasSum_fiberwise (h : sourceNontrivialZeroSet → Real)
    (hh : Summable h) (W : Real) :
    HasSum (fun k : Int =>
        ∑' rho : {r : sourceNontrivialZeroSet // r ∈ windowSet W k}, h rho)
      (∑' rho, h rho) := by
  have h1 : HasSum
      (fun p : (k : Int) × {r : sourceNontrivialZeroSet // r ∈ windowSet W k} =>
        h ((Set.sigmaEquiv (windowSet W) (windowSet_unique W)) p))
      (∑' rho, h rho) :=
    hasSum_comp_equiv _ hh.hasSum
  have h2 : ∀ k : Int, HasSum
      (fun c : {r : sourceNontrivialZeroSet // r ∈ windowSet W k} =>
        h ((Set.sigmaEquiv (windowSet W) (windowSet_unique W)) ⟨k, c⟩))
      (∑' rho : {r : sourceNontrivialZeroSet // r ∈ windowSet W k}, h rho) := by
    intro k
    show HasSum (fun c : {r : sourceNontrivialZeroSet // r ∈ windowSet W k} => h c) _
    exact (hh.subtype (fun r => r ∈ windowSet W k)).hasSum
  exact HasSum.sigma h1 h2

/-- Fiber Fubini (value form) for summable real families. -/
theorem tsum_fiberwise (h : sourceNontrivialZeroSet → Real)
    (hh : Summable h) (W : Real) :
    ∑' rho, h rho =
      ∑' k : Int, ∑' rho : {r : sourceNontrivialZeroSet // r ∈ windowSet W k}, h rho :=
  (hasSum_fiberwise h hh W).tsum_eq.symm

/-! ### Window masses (1362 s3 definitions) -/

/-- The critical-line mass carried by one ordinate window. -/
noncomputable def windowOnLineMass (g : CompactLogTest) (W : Real) (k : Int) : Real :=
  ∑' rho : {r : sourceNontrivialZeroSet // r ∈ windowSet W k},
    (onLineSpectralTerm g rho).re

/-- The off-line residual carried by one ordinate window. -/
noncomputable def windowOffLineMass (g : CompactLogTest) (W : Real) (k : Int) : Real :=
  ∑' rho : {r : sourceNontrivialZeroSet // r ∈ windowSet W k},
    (offLineSpectralTerm g rho).re

/-- Summability of the real-part spectral family, on the critical line. -/
theorem summable_onLineSpectralTerm_re (g : CompactLogTest) :
    Summable (fun rho : sourceNontrivialZeroSet => (onLineSpectralTerm g rho).re) := by
  have hF := summable_onLineSpectralTerm g (spectralSummableProp g.convolutionSquare)
  refine Summable.of_norm (Summable.of_nonneg_of_le
    (fun rho => norm_nonneg _) (fun rho => ?_) hF.norm)
  simpa using Complex.abs_re_le_norm (onLineSpectralTerm g rho)

/-- Summability of the real-part spectral family, off the line. -/
theorem summable_offLineSpectralTerm_re (g : CompactLogTest) :
    Summable (fun rho : sourceNontrivialZeroSet => (offLineSpectralTerm g rho).re) := by
  have hF := summable_offLineSpectralTerm g (spectralSummableProp g.convolutionSquare)
  refine Summable.of_norm (Summable.of_nonneg_of_le
    (fun rho => norm_nonneg _) (fun rho => ?_) hF.norm)
  simpa using Complex.abs_re_le_norm (offLineSpectralTerm g rho)

/-! ### The brick: T1-T4 (locked statements, 1362 s3/s3a) -/

/-- **T1 (windowMass_split_on).** The total on-line spectral mass is the
window-indexed sum of the on-line window masses. -/
theorem windowMass_split_on (g : CompactLogTest) (W : Real) :
    onLineSpectralMass g =
      ∑' k : Int, windowOnLineMass g W k := by
  unfold onLineSpectralMass
  rw [Complex.re_tsum
    (summable_onLineSpectralTerm g (spectralSummableProp g.convolutionSquare))]
  exact tsum_fiberwise (fun rho => (onLineSpectralTerm g rho).re)
    (summable_onLineSpectralTerm_re g) W

/-- **T2 (windowMass_split_off).** The total off-line spectral residual is
the window-indexed sum of the off-line window masses. -/
theorem windowMass_split_off (g : CompactLogTest) (W : Real) :
    offLineSpectralMass g =
      ∑' k : Int, windowOffLineMass g W k := by
  unfold offLineSpectralMass
  rw [Complex.re_tsum
    (summable_offLineSpectralTerm g (spectralSummableProp g.convolutionSquare))]
  exact tsum_fiberwise (fun rho => (offLineSpectralTerm g rho).re)
    (summable_offLineSpectralTerm_re g) W

/-- **T3 (qw_window_assembly).** The `qw` ledger of the committed
QwAssembly re-assembles in window coordinates. -/
theorem qw_window_assembly (g : CompactLogTest) (W : Real) :
    C1SameOwnerWeil.qw g =
      ∑' k : Int, (windowOnLineMass g W k + windowOffLineMass g W k) := by
  have hsumG : Summable (fun k : Int => windowOnLineMass g W k) :=
    (hasSum_fiberwise (fun rho => (onLineSpectralTerm g rho).re)
      (summable_onLineSpectralTerm_re g) W).summable
  have hsumG2 : Summable (fun k : Int => windowOffLineMass g W k) :=
    (hasSum_fiberwise (fun rho => (offLineSpectralTerm g rho).re)
      (summable_offLineSpectralTerm_re g) W).summable
  rw [qw_eq_onLineSpectralMass_add_offLineSpectralMass,
    windowMass_split_on, windowMass_split_off,
    ← ((hsumG.hasSum).add hsumG2.hasSum).tsum_eq]

/-- **T4 (contestForm_windowwise_iff).** The committed per-test contest
balance (B4.1) in window coordinates. No analysis: T1+T2+B4.1. -/
theorem contestForm_windowwise_iff (g : CompactLogTest) (W : Real) :
    0 ≤ C1SameOwnerWeil.qw g ↔
      ∑' k : Int, windowOnLineMass g W k ≥
        max 0 (- ∑' k : Int, windowOffLineMass g W k) := by
  rw [← windowMass_split_on, ← windowMass_split_off]
  exact C1N1SamplingContest.contest_balance_iff_qw_nonneg g

end
end C1A2WindowSplit
end Source
end ConnesWeilRH
