/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20PairingFold
import ConnesWeilRH.Dev.C1CC20RawKernelMass
import Mathlib.MeasureTheory.Group.Integral

/-!
# CC20 displacement-kernel bridge

The paper's raw endpoint kernel depends on the pair `(x, y)` only through
the displacement `y - x`.  This leaf records that owner relation explicitly
and proves the one-variable translation change used before the L1-weighted
correlation fold of equation (121):

    integral_y a(y - x) f(y) = integral_v a(v) f(x + v).

The square-window indicator is kept as a separate definition.  Reordering a
double integral into the pairing readback needs its own Fubini hypotheses and
is deliberately not claimed here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20DisplacementKernel

open MeasureTheory
open CC20Concrete
open C1CC20LpOperator C1CC20RawKernelMass

/-- A translation-invariant two-variable kernel induced by a displacement
profile.  The orientation is the CC20 orientation `y - x`. -/
noncomputable def displacementKernel (a : ℝ -> ℂ) : ℝ × ℝ -> ℂ :=
  fun p => a (p.2 - p.1)

/-- The displacement kernel restricted to the symmetric CC20 square window. -/
noncomputable def windowedDisplacementKernel (a : ℝ -> ℂ) (r : ℝ) :
    ℝ × ℝ -> ℂ :=
  (cc20WindowPair r).indicator (displacementKernel a)

/-- The one-variable change of variables behind the CC20 correlation form.
No integrability premise is needed because the Bochner integral's translation
invariance is valid with its standard zero-on-nonintegrable convention. -/
theorem applyKernel_displacementKernel_eq_translateFold
    (a f : ℝ -> ℂ) (x : ℝ) :
    applyKernel (displacementKernel a) f x =
      ∫ v : ℝ, a v * f (x + v) := by
  unfold applyKernel displacementKernel
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    (integral_add_right_eq_self (fun y : ℝ => a (y - x) * f y) x).symm

/-- The complex displacement profile of the CC20 endpoint kernel. -/
noncomputable def endpointDisplacementProfile
    (data : CC20EndpointSpectralData) (v : ℝ) : ℂ :=
  (data.endpointAdditiveKernel v : ℂ)

/-- The raw CC20 kernel is definitionally the displacement kernel of its
endpoint profile. -/
theorem endpointWindowKernelComplex_eq_displacementKernel
    (data : CC20EndpointSpectralData) :
    data.endpointWindowKernelComplex =
      displacementKernel (endpointDisplacementProfile data) := rfl

/-- The existing square-window endpoint owner is exactly the windowed
displacement kernel of the same profile. -/
theorem endpointKernelOnSquare_eq_windowedDisplacementKernel
    (data : CC20EndpointSpectralData) (r : ℝ) :
    endpointKernelOnSquare data r =
      windowedDisplacementKernel (endpointDisplacementProfile data) r := rfl

/-- The raw CC20 endpoint operator has the translated one-variable form that
the L1-weighted correlation fold consumes. -/
theorem applyKernel_endpointWindowKernelComplex_eq_translateFold
    (data : CC20EndpointSpectralData) (f : ℝ -> ℂ) (x : ℝ) :
    applyKernel data.endpointWindowKernelComplex f x =
      ∫ v : ℝ, endpointDisplacementProfile data v * f (x + v) := by
  rw [endpointWindowKernelComplex_eq_displacementKernel]
  exact applyKernel_displacementKernel_eq_translateFold
    (endpointDisplacementProfile data) f x

end C1CC20DisplacementKernel
end Source
end ConnesWeilRH
