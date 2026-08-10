/-
Wall-1 strict-positivity seed (axiom-clean, no sorry).

The global log-convolution by a nonzero Schwartz kernel is a nonzero operator
on the log-carrier Hilbert space.  This is the load-bearing strictness seed:
the already-proved PSD diagonal gives 0 <= ||fullBoundaryRootFactor g a c u||^2;
a strictly positive diagonal (a genuinely inhabited fullWeilPositivity on the
healthy CompactLog/HS carrier) needs exists u, F u != 0 for a nonzero test,
which via fullBoundaryRootFactor_eq_globalConvolution reduces to this operator
being nonzero.

Proof (Fourier-multiplier, ref GlobalLogConvolution.lean):
cc20GlobalLogConvolution h (g.toLp 2) = (Schwartz conv h g).toLp 2.
A zero operator forces every Schwartz convolution h*g = 0; take g = h.  Then
Fourier(conv h h) = 0, and by fourier_convolution the left side is
pairing (mul) (Fourier h) (Fourier h), so pointwise
Fourier h x * Fourier h x = 0, i.e. Fourier h = 0.  Since inverse-Fourier of
Fourier h equals h (FourierPair-simp), we get h = 0, contradiction.

No RH claim: single analytic leaf only.
-/
import ConnesWeilRH.Source.CC20Concrete.GlobalLogConvolution

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open scoped FourierTransform

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

end CC20Concrete
end Source
end ConnesWeilRH
