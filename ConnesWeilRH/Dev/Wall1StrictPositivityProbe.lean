import ConnesWeilRH.Source.CC20Concrete.GlobalLogConvolution
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScalePlancherelKernel

/-!  Probe: strict-positivity seed is the Fourier-multiplier injectivity of the
global log convolution by a nonzero Schwartz kernel.  If `cc20GlobalLogConvolution`
with a nonzero `h` is injective, then some `u` has nonzero image, giving a strict
diagonal for `fullWeilPositivity`.  This file records the first exact statement to
close; the closure itself is the analytic seed. -/
namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall1StrictPositivityProbe
open CC20Concrete
noncomputable section
variable (h : SchwartzMap ℝ ℂ)
/-- Statement: global log convolution by a nonzero kernel is a nonzero operator. -/
abbrev injectivityObligation (h : SchwartzMap ℝ ℂ) : Prop :=
  (∀ u : cc20GlobalLogCrossingL2, cc20GlobalLogConvolution h u = 0) -> h = 0
end Wall1StrictPositivityProbe
end Dev
end ConnesWeilRH
