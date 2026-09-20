/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Two-sided cosine rule skeleton for the S3 annular tail

Record 1733.  The paper proof reduces the uniform annular kernel-diagonal
bound (the last open S3 producer) to one first moment of the
Hardy-transformed kernel, via the two-sided projection cosine rule applied
to the translated kernel family.  This leaf lands the pure
operator/measure skeleton:

1. the cosine rule `norm_starProjection_le_of_submodule_le` for nested
   orthogonal projections;
2. Bessel over a carrier basis, `tsum_norm_inner_sq_eq_starProjection_normSq`;
3. the abstract annulus-split assembly `annular_lintegral_le_of_pointwise`
   producing the kernel-diagonal hypothesis shape consumed by record 1723's
   `sourceCompressedRoot_squareSum_of_kernelDiagonal_lintegral_bound`.

No carrier object, no root convolution, and no sign is touched here; the
instantiation layer (kernel readback, translation-tail integrals) is the
named next step.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory RCLike

section CosineRule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Cosine rule: if `K ≤ L` are submodules with orthogonal projections, then
the `K`-projection of every vector is bounded by its `L`-projection. -/
theorem norm_starProjection_le_of_submodule_le
    {K L : Submodule ℂ H} [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hle : K ≤ L) (u : H) :
    ‖K.starProjection u‖ ≤ ‖L.starProjection u‖ := by
  have hmem : K.starProjection u ∈ L :=
    hle (Submodule.starProjection_apply_mem K u)
  have hinner : inner ℂ (K.starProjection u) (L.starProjection u)
      = inner ℂ (K.starProjection u) u := by
    have h1 := Submodule.inner_starProjection_left_eq_right (K := L)
      (K.starProjection u) u
    rw [Submodule.starProjection_eq_self_iff.mpr hmem] at h1
    exact h1.symm
  have h0 := Submodule.re_inner_starProjection_eq_normSq (K := K) u
  rw [← hinner] at h0
  -- h0 : re ⟪K.starProjection u, L.starProjection u⟫ = ‖K.orthogonalProjection u‖ ^ 2
  have hcs := re_inner_le_norm (𝕜 := ℂ) (K.starProjection u) (L.starProjection u)
  rw [h0, pow_two] at hcs
  have hnormK : ‖K.starProjection u‖ = ‖K.orthogonalProjection u‖ := by
    rw [Submodule.coe_norm (K.orthogonalProjection u), Submodule.starProjection_apply]
  have hnormL : ‖L.starProjection u‖ = ‖L.orthogonalProjection u‖ := by
    rw [Submodule.coe_norm (L.orthogonalProjection u), Submodule.starProjection_apply]
  rw [hnormK, hnormL] at hcs
  rcases eq_or_lt_of_le (norm_nonneg (K.orthogonalProjection u)) with hzero | hpos
  · rw [hnormK, ← hzero]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_left hcs hpos

end CosineRule

section Bessel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Bessel identity over a carrier basis: summing the squared moduli of the
pairings of `v` against a Hilbert basis of the submodule `K` returns the
squared norm of the orthogonal projection of `v` onto `K`, read through the
real part of the projected self-pairing. -/
theorem tsum_norm_inner_sq_eq_starProjection_normSq
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] {ι : Type*}
    (b : HilbertBasis ι ℂ K) (v : H) :
    ∑' i, ‖inner ℂ ((b i : K) : H) v‖ ^ 2
      = re (inner ℂ (K.starProjection v) (K.starProjection v)) := by
  obtain ⟨p, hpc, hpn⟩ :
      ∃ p : K, (p : H) = K.starProjection v ∧ ‖p‖ = ‖K.orthogonalProjection v‖ :=
    ⟨K.orthogonalProjection v, rfl, rfl⟩
  have hzs : ∀ z : ℂ, ‖z‖ ^ 2 = Complex.re (starRingEnd ℂ z * z) := fun z => by
    have h1 := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := z))
    rw [Complex.ofReal_re] at h1
    -- h1 : Complex.normSq z = Complex.re (starRingEnd ℂ z * z)
    rw [← h1, Complex.normSq_eq_norm_sq]
  -- the basis pairs against `v` exactly as against the projection of `v`
  have horth : ∀ w : H, w ∈ K → inner ℂ (v - (p : H)) w = 0 := by
    intro w hw
    rw [hpc]
    exact K.starProjection_inner_eq_zero v w hw
  have hpairL : ∀ i : ι, inner ℂ (p : H) (b i : H) = inner ℂ v (b i : H) := by
    intro i
    have h0 := horth (b i : H) (Submodule.coe_mem (b i))
    rw [inner_sub_left, sub_eq_zero] at h0
    exact h0.symm
  have hpairR : ∀ i : ι, inner ℂ (b i : H) (p : H) = inner ℂ (b i : H) v := by
    intro i
    have h0 := horth (b i : H) (Submodule.coe_mem (b i))
    have h1 : inner ℂ (b i : H) (v - (p : H)) = 0 := by
      rw [← inner_conj_symm, h0]
      simp
    rw [inner_sub_right, sub_eq_zero] at h1
    exact h1.symm
  -- per-term identity: |⟨b i, v⟩|² = re (⟨p, b i⟩ ⟨b i, p⟩)
  have key : ∀ i : ι, ‖inner ℂ ((b i : K) : H) v‖ ^ 2
      = re (inner ℂ (p : H) (b i : H) * inner ℂ (b i : H) (p : H)) := by
    intro i
    rw [hpairL i, hpairR i, ← inner_conj_symm v (b i : H)]
    exact hzs _
  -- the representation sum, lifted through `re`
  have hsum := b.tsum_inner_mul_inner p p
  simp only [Submodule.coe_inner] at hsum
  have hsummable := b.summable_inner_mul_inner p p
  simp only [Submodule.coe_inner] at hsummable
  rw [← hpc, ← RCLike.reCLM_apply, ← hsum, ContinuousLinearMap.map_tsum reCLM hsummable,
    RCLike.reCLM_apply]
  exact tsum_congr fun i => key i

end Bessel

section Assembly

/-- Abstract annulus-split assembly: if a measurable nonnegative scalar bound
`g` majorizes the per-point diagonal series, vanishes on the inner window
`[-N, N]`, and its two outer wings carry finite `ENNReal` integrals, then
the full diagonal lintegral is bounded by the wing sum.  This is the shape
consumed by record 1723's
`sourceCompressedRoot_squareSum_of_kernelDiagonal_lintegral_bound`. -/
theorem annular_lintegral_le_of_pointwise
    {ι : Type*} {cols : ι → ℝ → ℂ} {g : ℝ → ℝ} {N B₁ B₂ : ℝ}
    (hg : Measurable g) (hgnonneg : ∀ t, 0 ≤ g t) (hB1 : 0 ≤ B₁) (hB2 : 0 ≤ B₂)
    (hN : 0 < N)
    (hzero : ∀ t, -N ≤ t → t ≤ N → g t = 0)
    (hpoint : ∀ t, ∑' i, ENNReal.ofReal (‖cols i t‖) ^ 2 ≤ ENNReal.ofReal (g t))
    (hleft : ∫⁻ t in Set.Iic (-N), ENNReal.ofReal (g t) ≤ ENNReal.ofReal B₁)
    (hright : ∫⁻ t in Set.Ici N, ENNReal.ofReal (g t) ≤ ENNReal.ofReal B₂) :
    ∫⁻ t, ∑' i, ENNReal.ofReal (‖cols i t‖) ^ 2 ≤ ENNReal.ofReal (B₁ + B₂) := by
  -- the middle piece vanishes because g vanishes on [-N, N]
  have hmid : ∫⁻ t in Set.Ioo (-N) N, ENNReal.ofReal (g t) = 0 := by
    rw [lintegral_eq_zero_iff (f := fun t => ENNReal.ofReal (g t))
      (ENNReal.measurable_ofReal.comp hg),
      MeasureTheory.ae_restrict_eq measurableSet_Ioo]
    show Filter.Eventually (fun x => ENNReal.ofReal (g x) = (0 : ℝ → ENNReal) x)
      (MeasureTheory.ae volume ⊓ Filter.principal (Set.Ioo (-N) N))
    rw [Filter.eventually_inf_principal]
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [hzero t (Set.mem_Ioo.1 ht).1.le (Set.mem_Ioo.1 ht).2.le]
    simp
  -- the right half-line splits as the open window plus the right wing
  have hdisj : Disjoint (Set.Ioo (-N) N) (Set.Ici N) := by
    rw [Set.disjoint_left]
    intro t h1 h2
    have hioo : -N < t ∧ t < N := Set.mem_Ioo.1 h1
    exact absurd (le_antisymm hioo.2.le (Set.mem_Ici.1 h2)) hioo.2.ne
  have hsplit : ∫⁻ t in Set.Ioi (-N), ENNReal.ofReal (g t)
      = (∫⁻ t in Set.Ioo (-N) N, ENNReal.ofReal (g t))
          + (∫⁻ t in Set.Ici N, ENNReal.ofReal (g t)) := by
    have hunion : Set.Ioo (-N) N ∪ Set.Ici N = Set.Ioi (-N) := by
      ext t
      constructor
      · rintro (h | h)
        · exact Set.mem_Ioi.2 (Set.mem_Ioo.1 h).1
        · exact Set.mem_Ioi.2 (lt_of_lt_of_le (show -N < N from by linarith) h)
      · intro h
        rcases lt_trichotomy t N with hlt | heq | hgt
        · exact Or.inl (Set.mem_Ioo.2 ⟨h, hlt⟩)
        · exact Or.inr (Set.mem_Ici.2 heq.ge)
        · exact Or.inr (Set.mem_Ici.2 hgt.le)
    rw [← hunion]
    exact lintegral_union (f := fun t => ENNReal.ofReal (g t)) (μ := volume)
      measurableSet_Ici hdisj
  -- split the full line at -N (left wing + right half-line)
  have step1 : ∫⁻ t, ENNReal.ofReal (g t)
      = (∫⁻ t in Set.Iic (-N), ENNReal.ofReal (g t))
          + (∫⁻ t in Set.Ioi (-N), ENNReal.ofReal (g t)) := by
    rw [← Set.compl_Iic,
      lintegral_add_compl (A := Set.Iic (-N)) (fun t => ENNReal.ofReal (g t))
        measurableSet_Iic]
  -- chain: pointwise bound, split at -N, drop the vanishing middle
  calc ∫⁻ t, ∑' i, ENNReal.ofReal (‖cols i t‖) ^ 2
      ≤ ∫⁻ t, ENNReal.ofReal (g t) := lintegral_mono fun t => hpoint t
    _ = (∫⁻ t in Set.Iic (-N), ENNReal.ofReal (g t))
          + (∫⁻ t in Set.Ioi (-N), ENNReal.ofReal (g t)) := step1
    _ = (∫⁻ t in Set.Iic (-N), ENNReal.ofReal (g t))
          + ((∫⁻ t in Set.Ioo (-N) N, ENNReal.ofReal (g t))
              + (∫⁻ t in Set.Ici N, ENNReal.ofReal (g t))) := by
          rw [hsplit]
    _ = (∫⁻ t in Set.Iic (-N), ENNReal.ofReal (g t))
          + (∫⁻ t in Set.Ici N, ENNReal.ofReal (g t)) := by
          rw [hmid, zero_add]
    _ ≤ ENNReal.ofReal B₁ + ENNReal.ofReal B₂ := by
          exact add_le_add hleft hright
    _ = ENNReal.ofReal (B₁ + B₂) := (ENNReal.ofReal_add hB1 hB2).symm

end Assembly

end Dev
end ConnesWeilRH
