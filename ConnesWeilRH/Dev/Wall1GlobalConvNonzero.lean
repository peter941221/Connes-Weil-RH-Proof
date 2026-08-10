/-
Wall-1 strict-positivity seed (axiom-clean, no sorry).

Three leaves are closed here, jointly carrying the load-bearing strict
positive diagonal on the healthy CompactLog/HS carrier:

  1. cc20GlobalLogConvolution_ne_zero: a nonzero Schwartz kernel h gives a
     nonzero global log-convolution operator on cc20GlobalLogCrossingL2.
  2. cc20GlobalLogConvolution_strict: a nonzero such operator has a vector
     u with 0 < ||cc20GlobalLogConvolution h u||.
  3. cc20GlobalConvolutionPositive_strict_diagonal : at a nonzero kernel h
     the PSD convolution-square operator
       cc20GlobalConvolutionPositive h = dag(cc20GlobalLogConvolution h)
                                          o cc20GlobalLogConvolution h
     has a strictly positive Hilbert diagonal:
       exists u, 0 < real(u, cc20GlobalConvolutionPositive h u).
     Together with the existing nonnegative diagonal this is exactly the
     strict-positive content that inhabits fullWeilPositivity on the
     healthy carrier - no window surgery.

Proof of 1 (Fourier multiplier, ref GlobalLogConvolution.lean):
cc20GlobalLogConvolution h (g.toLp 2) = (Schwartz conv h g).toLp 2.  A zero
operator forces every Schwartz convolution h*g = 0; take g = h.  Then the
Fourier transform of conv h h is 0, and by fourier_convolution equals
pairing mul (Fourier h) (Fourier h), so pointwise Fourier h x * Fourier h x
= 0, hence Fourier h = 0, and inverse-Fourier (FourierInvPair) gives h = 0,
a contradiction.  Leaves 2 and 3 are reduction / norm positivity only.

No RH claim: analytic leaves only.
-/
import ConnesWeilRH.Source.CC20Concrete.GlobalLogConvolution
import ConnesWeilRH.Source.CC20Concrete.GlobalConvolutionCrossing

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open scoped FourierTransform InnerProduct InnerProductSpace

/-! The strict seed: global log-convolution by a nonzero Schwartz kernel is a
nonzero operator on cc20GlobalLogCrossingL2. -/
theorem cc20GlobalLogConvolution_ne_zero
    (h : SchwartzMap ℝ ℂ) (hne : h ≠ 0) :
    cc20GlobalLogConvolution h ≠ 0 := by
  intro hzero
  classical
  have hconv_zero (g : SchwartzMap ℝ ℂ) :
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) h g = 0 := by
    have hL : (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) h g).toLp (p := 2) = 0 := by
      have happg : cc20GlobalLogConvolution h (g.toLp 2) = 0 := by
        rw [hzero]
        rfl
      rw [cc20GlobalLogConvolution_toLp] at happg
      simpa using happg
    apply (SchwartzMap.injective_toLp 2)
    simpa using hL
  have hconv_self :
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) h h = 0 :=
    hconv_zero h
  have hpair : SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ) (𝓕 h) (𝓕 h) = 0 := by
    have hf := (SchwartzMap.fourier_convolution (ContinuousLinearMap.mul ℝ ℂ) h h)
    simpa [hconv_self] using hf.symm
  have hzeroFx (x : ℝ) : (𝓕 h) x = 0 := by
    have hval : (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ) (𝓕 h) (𝓕 h) : ℝ → ℂ) x = 0 := by
      simpa using (congrArg (fun S : SchwartzMap ℝ ℂ => (S : ℝ → ℂ) x) hpair)
    rw [SchwartzMap.pairing_apply_apply] at hval
    change (𝓕 h) x * (𝓕 h) x = 0 at hval
    exact mul_self_eq_zero.mp hval
  have hFh : (𝓕 h : SchwartzMap ℝ ℂ) = 0 := by
    ext x
    exact hzeroFx x
  have hFinv : 𝓕⁻ (𝓕 h) = 𝓕⁻ (0 : SchwartzMap ℝ ℂ) := by
    rw [hFh]
  have htozero : h = 0 := by
    simpa using hFinv
  exact hne htozero

/-- A nonzero global log-convolution acts strictly on some Hilbert vector. -/
theorem cc20GlobalLogConvolution_strict
    (h : SchwartzMap ℝ ℂ) (hne : h ≠ 0) :
    ∃ u : cc20GlobalLogCrossingL2, 0 < ‖cc20GlobalLogConvolution h u‖ := by
  classical
  have hGne : cc20GlobalLogConvolution h ≠ 0 := cc20GlobalLogConvolution_ne_zero h hne
  have himg : ∃ u : cc20GlobalLogCrossingL2, cc20GlobalLogConvolution h u ≠ 0 := by
    by_contra hnone
    have halt : ∀ u : cc20GlobalLogCrossingL2, cc20GlobalLogConvolution h u = 0 := by
      intro u
      by_contra hnz
      exact hnone ⟨u, hnz⟩
    exact hGne (ContinuousLinearMap.ext halt)
  rcases himg with ⟨u, hz⟩
  exact ⟨u, norm_pos_iff.mpr hz⟩

/-- The strict positive Hilbert diagonal of the PSD convolution-square operator
at a nonzero kernel: properly converts the nonnegative diagonal into a strictly
positive one, exactly what inhabits ``fullWeilPositivity`` on the healthy
CompactLog/HS carrier. -/
theorem cc20GlobalConvolutionPositive_strict_diagonal
    (h : SchwartzMap ℝ ℂ) (hne : h ≠ 0) :
    ∃ u : cc20GlobalLogCrossingL2,
      0 < (⟪u, cc20GlobalConvolutionPositive h u⟫_ℂ).re := by
  rcases cc20GlobalLogConvolution_strict h hne with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  rw [← cc20GlobalConvolutionPositive_inner_re_eq_norm_sq h u]
  exact sq_pos_of_pos hu
end CC20Concrete
end Source
end ConnesWeilRH
