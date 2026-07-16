/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingProjectionCovariance

/-!
# Support-first moving finite-S owner

Compact correlation support is inserted into the literal moving projection
trace before the complete generator is split into channels.  Both the support
sum and the channel sum remain signed under one final real part.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMovingSupportFirst

open scoped BigOperators ComplexConjugate Matrix
open CCM24FiniteSSupportFirstCovariance
open CCM24FiniteSSynchronizedCovariance
open CCM24FiniteSMovingProjectionCovariance

variable {X U V : Type*} [Fintype X] [DecidableEq X]
  [Fintype U] [Fintype V]

/-- Literal moving `E-R` response in support-first, synchronized form.  This
theorem does not permit an absolute value around either inner sum. -/
theorem signedMovingProjectionTraceResponse_support_first_generator
    (outerProjection soninProjection : Matrix X X ℂ)
    (correlation : U → ℂ) (character : U → X → ℂ)
    (channel : V → X → ℂ) (support : Finset U)
    (hzero : ∀ u ∉ support, correlation u = 0)
    (hOuterIdempotent : outerProjection * outerProjection = outerProjection)
    (hSoninIdempotent : soninProjection * soninProjection = soninProjection)
    (hOuterHermitian : ∀ x y,
      outerProjection y x = conj (outerProjection x y))
    (hSoninHermitian : ∀ x y,
      soninProjection y x = conj (soninProjection x y))
    (hDetectorReal : ∀ x,
      conj (correlationMultiplier correlation character x) =
        correlationMultiplier correlation character x) :
    signedMovingProjectionTraceResponse outerProjection soninProjection
        (correlationMultiplier correlation character)
        (completeGenerator channel) =
      (2 * Complex.re
        (∑ u ∈ support, correlation u *
          ∑ v, signedMatrixProjectionCovariance outerProjection
            soninProjection (character u) (channel v)) : ℝ) := by
  rw [signedMovingProjectionTraceResponse_eq_two_re outerProjection
      soninProjection (correlationMultiplier correlation character)
      (completeGenerator channel) hOuterIdempotent hSoninIdempotent
      hOuterHermitian hSoninHermitian hDetectorReal,
    signedMatrixProjectionCovariance_support_first_generator
      outerProjection soninProjection correlation character channel support
      hzero hOuterIdempotent hSoninIdempotent hOuterHermitian
      hSoninHermitian]

end CCM24FiniteSMovingSupportFirst
end CCM25Concrete
end Source
end ConnesWeilRH
