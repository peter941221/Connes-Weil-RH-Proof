import ConnesWeilRH.Dev.C1WeilExplicit
import ConnesWeilRH.Dev.Wall14PlateauExplicitComplex

/-!
# M2HealthyPsiPort - legacy M.2 carrier under the complete Weil functional

Keeps the plain plateau carrier that earlier M-2 probes compared by support
width. It does not port their finite-vanishing residual into Lean:

  * `twoSidedCarrier : CompactLogTest` = `Dev.Wall14Plateau.bumpPlateauTest`,
    the explicit two-sided flat-top bump (support `[-1,1]`, plateau
    `[-9/10,9/10]`, additive log coordinate).
  * `m2PsiValue : Real` = `C1WeilExplicit.healthyQw twoSidedCarrier`, the exact
    pole - archimedean - all-visible-prime-power value on the carrier square.

SCOPE (docs/proofs/989 + 990):
  * This makes the plain carrier and its complete source Weil value stateable.
  * The old residual and this plateau have different formulas. No numeric sign
    transfers between them.
  * `healthyQw` value and its sign are NOT closed here and NOT asserted.
RH NOT claimed.
-/
namespace ConnesWeilRH
namespace Source
namespace Dev
namespace M2
namespace HealthyPsi

open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.Dev.Wall14Plateau

/-- The two-sided explicit plateau carrier of width 2 in the log coordinate. -/
noncomputable def twoSidedCarrier : CompactLogTest :=
  bumpPlateauTest

/-- Complete same-owner Weil value on the carrier's convolution square. -/
noncomputable def m2PsiValue : Real :=
  ConnesWeilRH.Source.C1WeilExplicit.healthyQw twoSidedCarrier

/-- The two-sided carrier genuinely touches 0 as `(1 : Complex)`; it is a real
   (non-zero) two-sided bump. -/
theorem twoSidedCarrier_zero : twoSidedCarrier.test 0 = (1 : Complex) := by
  rw [twoSidedCarrier]
  exact bumpPlateauTest_zero_eq_one

/-- The carrier is compactly supported (a genuine `CompactLogTest` witness). -/
theorem twoSidedCarrier_hasCompactSupport : HasCompactSupport
    (fun x : Real => twoSidedCarrier.test x) :=
  twoSidedCarrier.compactSupport

end HealthyPsi
end M2
end Dev
end Source
end ConnesWeilRH
