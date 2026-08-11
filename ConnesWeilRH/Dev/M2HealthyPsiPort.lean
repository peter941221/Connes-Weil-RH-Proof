import ConnesWeilRH.Dev.C1WeilExplicit
import ConnesWeilRH.Dev.Wall14PlateauExplicitComplex

/-!
# M2HealthyPsiPort — M.2/990 numeric healthy-psi as a Lean-expressible carrier

Ports the M-2/990 two-sided finite-vanishing healthy-psi numerics into the Lean
object layer as an *expressible carrier* (RH NOT claimed, no closure):

  * `twoSidedCarrier : CompactLogTest` = `Dev.Wall14Plateau.bumpPlateauTest`,
    the explicit two-sided flat-top bump (support `[-1,1]`, plateau
    `[-9/10,9/10]`, additive log coordinate).  In the 990 width-scan (docs/990)
    this is the **width-2 window**, i.e. the **positive-psi** side: the boundary
    scan finds psi crosses from + to - at window width ~2.8175.
  * `m2PsiValue : Real` = `C1WeilExplicit.healthyQw twoSidedCarrier`, the exact
    pole - archimedean - finite-prime-{2} value on the carrier convolution square,
    the object the 989/990 numerics approximate by `pole - arch - term2`.

HONEST SCOPE (matches docs/proofs/989 + 990):
  * This makes the *carrier* and the *value* expressible/stateable.
  * The **negative-psi family** (window width > ~2.82) needs a width-scaled
    plateau (support strictly wider than `[-1,1]`), which this file deliberately
    does NOT construct; building width-scaled `CompactLogTest` + `HasCompactSupport`
    is concrete follow-on work.
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

/-- The two-sided explicit plateau carrier of width 2 in the log coordinate
   (positive-psi / width-2 window of the 990 scan). -/
noncomputable def twoSidedCarrier : CompactLogTest :=
  bumpPlateauTest

/-- Explicit healthy psi on the carrier's convolution square, mirroring the
   989/990 numeric `psi = pole - arch - finite-prime-{2}`. -/
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
