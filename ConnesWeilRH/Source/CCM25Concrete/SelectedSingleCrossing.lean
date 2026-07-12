/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Selected single-crossing finite-prime read-off

The diagonal of one smoothed half-line crossing is constant along an interval
whose length is the translation distance.  This module records that geometric
factor and matches the Euler-log weighted prime-power crossing to the selected
finite-prime atom on the same convolution square.

It does not identify this diagonal integral with an operator trace.  That
trace-class and cyclicity theorem remains a separate finite-`S` obligation.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace SelectedWeilSquare
namespace SelectedWeilSquareOwner

open MeasureTheory
open scoped ArithmeticFunction Interval

/--
The paired crossing diagonal integral at translation length `b`.  The two
summands are the two crossing orientations of the same convolution square.
-/
noncomputable def singleCrossingPairDiagonalIntegral
    (owner : SelectedWeilSquareOwner) (b : ℝ) : ℂ :=
  ∫ _x : ℝ in (0 : ℝ)..b,
    owner.convolutionSquare.test b + owner.convolutionSquare.test (-b)

theorem singleCrossingPairDiagonalIntegral_eq
    (owner : SelectedWeilSquareOwner) (b : ℝ) :
    owner.singleCrossingPairDiagonalIntegral b =
      (b : ℂ) *
        (owner.convolutionSquare.test b +
          owner.convolutionSquare.test (-b)) := by
  simp [singleCrossingPairDiagonalIntegral]
  ring

theorem inv_sqrt_nat_pow_eq_rpow
    {p m : ℕ} (hp : 0 < p) :
    1 / Real.sqrt ((p ^ m : ℕ) : ℝ) =
      (p : ℝ) ^ (-((m : ℝ) / 2)) := by
  rw [Nat.cast_pow, Real.sqrt_eq_rpow, one_div]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [← Real.rpow_neg (by positivity)]
  congr 1
  ring

/--
The Euler-log coefficient `1 / (m * sqrt (p^m))` applied before the crossing
length `m * log p` is inserted.
-/
noncomputable def eulerLogSingleCrossingAtom
    (owner : SelectedWeilSquareOwner) (p m : ℕ) : ℂ :=
  (((1 / Real.sqrt ((p ^ m : ℕ) : ℝ)) / (m : ℝ) : ℝ) : ℂ) *
    owner.singleCrossingPairDiagonalIntegral
      ((m : ℝ) * Real.log (p : ℝ))

theorem eulerLogSingleCrossingAtom_eq_finitePrimeTerm_pow
    (owner : SelectedWeilSquareOwner) {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0) :
    owner.eulerLogSingleCrossingAtom p m =
      owner.finitePrimeTerm (p ^ m) := by
  rw [eulerLogSingleCrossingAtom,
    owner.singleCrossingPairDiagonalIntegral_eq,
    finitePrimeTerm, primePowerValue,
    ArithmeticFunction.vonMangoldt_apply_pow hm,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  simp only [Nat.cast_pow, Real.log_pow]
  have hm_real : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hm_complex : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  push_cast
  field_simp [hm_real, hm_complex]

end SelectedWeilSquareOwner
end SelectedWeilSquare
end CCM25Concrete
end Source
end ConnesWeilRH
