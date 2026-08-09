/-
Mellin-carrier full free-standing finite-prime support record (A-lane, step 2).

`MellinCertificateProbe` recorded the Mellin square law and the prime-`2` weight
seed.  This file continues the free-standing Mellin chain by giving a
carrier-level `terminal-prime` positivity fact: on the Mellin log-carrier a test
finite-prime term is strictly positive at the prime `2`.

The test `twoTest` is defined directly on the log coordinate (value `1` at `2`),
so all arithmetic is plain real/point-norm reasoning.  It deliberately makes NO
reference to the concrete `TestFunction` carrier or `WeilFormSymbols` — the
Mellin route is a free-standing parallel certificate, not an L657 slot fill.

No RH claim.  Zero `sorry`.  No new `axiom`.
-/

import ConnesWeilRH.Dev.MellinProductCarrier
import ConnesWeilRH.Dev.AmbientPrimeVisibleProbe
import ConnesWeilRH.Dev.MellinCertificateProbe

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace MellinFullRecord

noncomputable section

/-- Per-point norm on the Mellin log-carrier: |t.log x|. -/
noncomputable def pointValue (f : MellinProductCarrier.Test) (x : ℝ) : ℝ :=
  ‖f.log x‖

/-- A log test that is `1` at the log-coordinate `2`. -/
noncomputable def twoTest : MellinProductCarrier.Test where
  log := fun x : ℝ => Complex.ofReal (1 : ℝ)

/-- `|twoTest.log 2| = 1 ≠ 0`, hence the raw point value is non-zero. -/
lemma pointValue_two_ne_zero : pointValue twoTest (2 : ℝ) ≠ 0 := by
  unfold pointValue twoTest
  norm_num

/-- The Mellin log test |·| is non-negative at every point. -/
lemma pointValue_nonneg (f : MellinProductCarrier.Test) (x : ℝ) :
    0 ≤ pointValue f x := by
  unfold pointValue
  exact norm_nonneg (f.log x)

/-- The raw point value at `2` is strictly positive (`‖1‖ = 1`). -/
lemma pointValue_two_pos : 0 < pointValue twoTest (2 : ℝ) := by
  unfold pointValue twoTest
  norm_num

/-- The value at the reciprocal is non-negative, so the two-point sum is
strictly positive. -/
lemma twoSum_pos : 0 < pointValue twoTest (2 : ℝ) + pointValue twoTest ((2 : ℝ)⁻¹) :=
  lt_of_lt_of_le pointValue_two_pos (le_add_of_nonneg_right (pointValue_nonneg twoTest ((2 : ℝ)⁻¹)))

/-- Prime `2` carries von Mangoldt weight Λ(2)=log 2 > 0. -/
lemma vonMangoldt_two_pos : 0 < ArithmeticFunction.vonMangoldt 2 :=
  MellinCertificateProbe.vonMangoldt_two_pos

/-- The finite-prime term at `2` is strictly positive on the Mellin carrier. -/
theorem finitePrimeTerm_two_pos :
    0 < ArithmeticFunction.vonMangoldt 2 *
      ((1 / Real.sqrt (2 : ℝ)) * (pointValue twoTest (2 : ℝ) + pointValue twoTest ((2 : ℝ)⁻¹))) := by
  exact mul_pos vonMangoldt_two_pos
    (mul_pos (by positivity) twoSum_pos)

#print axioms finitePrimeTerm_two_pos

end
end MellinFullRecord
end Dev
end Source
end ConnesWeilRH