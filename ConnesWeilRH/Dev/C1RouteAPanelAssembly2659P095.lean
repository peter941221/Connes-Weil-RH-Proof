import ConnesWeilRH.Dev.C1RouteAAmpPin2657P095
import ConnesWeilRH.Dev.C1RouteAPhasePin2658P095
import ConnesWeilRH.Dev.C1RouteAComplexPanelTable2655P095

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-!
# P095 exact panel assembly center (record 2659)

This module translates the pricing audit into kernel-checkable rational
objects.  It proves the exact center product

  amp_center * rotation_center * polynomial_integral

and the first conservative L1 product charge.  The charge is an input to
the later theorem that replaces the centers by the certified balls from
records 2657 and 2658; this module does not claim panel containment.
-/

def panelAssemblyCenter2659P095 : RatPair2542 :=
  pairScale2542 ampValue2657P095
    (pairMul2542 phaseValue2658P095 complexPanelIntegral2648P095)

def panelAssemblyCharge2659P095 : ℚ :=
  ampRadius2657P095 * (pairMagnitude2542 phaseValue2658P095 + phaseRadius2658P095)
      * pairMagnitude2542 complexPanelIntegral2648P095
    + (ampValue2657P095 + ampRadius2657P095) * phaseRadius2658P095
      * pairMagnitude2542 complexPanelIntegral2648P095

theorem panelAssemblyCenter2659P095_replay :
    panelAssemblyCenter2659P095 =
      pairScale2542 ampValue2657P095
        (pairMul2542 phaseValue2658P095 complexPanelIntegral2648P095) := by
  rfl

theorem panelAssemblyCharge2659P095_positive :
    0 < panelAssemblyCharge2659P095 := by
  unfold panelAssemblyCharge2659P095
  norm_num [pairMagnitude2542, ampValue2657P095, ampRadius2657P095,
    phaseValue2658P095, phaseRadius2658P095, complexPanelIntegral2648P095]

theorem panelAssemblyCharge2659P095_nonneg :
    0 ≤ panelAssemblyCharge2659P095 := le_of_lt panelAssemblyCharge2659P095_positive

#print axioms panelAssemblyCenter2659P095_replay
#print axioms panelAssemblyCharge2659P095_nonneg
#print axioms panelAssemblyCharge2659P095_positive

end ConnesWeilRH.Dev
