/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal

/-!
# Route-W window/tail normal form for column-energy gates

Record 1503 §3 registers route W (window strip) as the formalizable half of
the attack on the survivor core gate: for a genuine window the compressed
column energy is Hilbert--Schmidt for free, and all the analytic content
sits in the collective tail.  This file isolates the operator-algebraic
normal form behind that registration, at full generality:

* the two-factor pointwise split `‖T u‖² ≤ 2‖T(P u)‖² + 2‖T((id − P) u)‖²`,
* the decomposition theorem — the column-energy gate for `T` follows from
  the window-strip square-sum for `T ∘L P` together with the SAME gate for
  the tail composition `T ∘L (id − P)`.

The theorem is deliberately hypothesis-free beyond linearity: no
idempotence, self-adjointness, or contraction of the window is used, so it
applies verbatim to the record-1494 radial/interior window factors and to
the composite visible-prime windows of the B3 obligation.  No estimate is
proved; RH is not touched.
-/

namespace ConnesWeilRH
namespace Dev

open Source.CC20Concrete.PositiveTrace

section General

variable {ι H G : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- Two-factor split: the energy at one vector is controlled by the window
piece and the tail piece together.  Only linearity is used. -/
private theorem normSq_le_two_window_add_two_tail
    (T : H →L[ℂ] G) (P : H →L[ℂ] H) (u : H) :
    ‖T u‖ ^ 2 ≤
      2 * ‖T (P u)‖ ^ 2 +
        2 * ‖(T ∘L (ContinuousLinearMap.id ℂ H - P)) u‖ ^ 2 := by
  have hsplit : T u =
      T (P u) + (T ∘L (ContinuousLinearMap.id ℂ H - P)) u := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, map_sub]
    abel
  calc
    ‖T u‖ ^ 2 = ‖T (P u) + (T ∘L (ContinuousLinearMap.id ℂ H - P)) u‖ ^ 2 :=
      by rw [hsplit]
    _ ≤ (‖T (P u)‖ + ‖(T ∘L (ContinuousLinearMap.id ℂ H - P)) u‖) ^ 2 := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 2 * (‖T (P u)‖ ^ 2 +
        ‖(T ∘L (ContinuousLinearMap.id ℂ H - P)) u‖ ^ 2) := by
      nlinarith [sq_nonneg
        (‖T (P u)‖ - ‖(T ∘L (ContinuousLinearMap.id ℂ H - P)) u‖)]
    _ = 2 * ‖T (P u)‖ ^ 2 +
        2 * ‖(T ∘L (ContinuousLinearMap.id ℂ H - P)) u‖ ^ 2 := by
      ring

/-- **Route-W decomposition normal form.**  The column-energy gate for `T`
follows from the window-strip square-sum for `T ∘L P` plus the SAME gate
for the tail composition `T ∘L (id − P)`.  For a genuine window the first
input is free (compact-strip Hilbert--Schmidt); the second is the
collective tail — the open mathematics of route T.  The tail input is the
same family of square-sums, so the decomposition can be iterated with
finer windows, pushing all content into the tail. -/
theorem survivorCore_of_windowStrip_of_tailGate
    (basis : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] G) (P : H →L[ℂ] H)
    (hwindow : Summable fun i : ι => ‖T (P (basis i))‖ ^ 2)
    (htail : Summable fun i : ι =>
      ‖(T ∘L (ContinuousLinearMap.id ℂ H - P)) (basis i)‖ ^ 2) :
    Summable fun i : ι => ‖T (basis i)‖ ^ 2 := by
  have hle : ∀ i : ι,
      ‖T (basis i)‖ ^ 2 ≤
        2 * (‖T (P (basis i))‖ ^ 2 +
          ‖(T ∘L (ContinuousLinearMap.id ℂ H - P)) (basis i)‖ ^ 2) := by
    intro i
    have hcomp := normSq_le_two_window_add_two_tail T P (basis i)
    linarith
  exact Summable.of_nonneg_of_le (fun i => sq_nonneg _) hle
    ((hwindow.add htail).mul_left 2)

/-- Iterated decomposition: with a second window `Q` applied to the tail,
the gate for `T` follows from the two window strips and the composite
tail.  This is the recursion that lets finer windows absorb more of the
operator for free, leaving only the collective tail as analytic content. -/
theorem survivorCore_of_twoWindowStrips_of_tailGate
    (basis : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] G) (P Q : H →L[ℂ] H)
    (hwindow1 : Summable fun i : ι => ‖T (Q (basis i))‖ ^ 2)
    (hwindow2 : Summable fun i : ι =>
      ‖(T ∘L (ContinuousLinearMap.id ℂ H - Q)) (P (basis i))‖ ^ 2)
    (htail : Summable fun i : ι =>
      ‖(T ∘L (ContinuousLinearMap.id ℂ H - Q)) ((ContinuousLinearMap.id ℂ H - P) (basis i))‖ ^ 2) :
    Summable fun i : ι => ‖T (basis i)‖ ^ 2 := by
  have hstep := survivorCore_of_windowStrip_of_tailGate basis
    (T ∘L (ContinuousLinearMap.id ℂ H - Q)) P hwindow2 htail
  exact survivorCore_of_windowStrip_of_tailGate basis T Q hwindow1 hstep

end General

end Dev
end ConnesWeilRH
