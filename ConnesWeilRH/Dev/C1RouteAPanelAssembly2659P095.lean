import ConnesWeilRH.Dev.C1RouteAAmpPin2657P095
import ConnesWeilRH.Dev.C1RouteAPhasePin2658P095
import ConnesWeilRH.Dev.C1RouteAComplexPanelTable2655P095
import ConnesWeilRH.Dev.C1RouteAPairMagnitudeProduct2659

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

Correction (record 2660): the record-2658 phase radius is a PER-COORDINATE
radius (`phaseExp_cos_error2646` and `phaseExp_sin_error2646` each bound one
coordinate), so the L1 rotation error is at most `2 * phaseRadius2658P095`.
The original charge carried one radius in each phase slot; both slots now
carry the factor 2.  The charge reads ~3.6e-87, so the fix is numerically
negligible; it is a soundness fix, not a tightening.
-/

def panelAssemblyCenter2659P095 : RatPair2542 :=
  pairScale2542 ampValue2657P095
    (pairMul2542 phaseValue2658P095 complexPanelIntegral2648P095)

def panelAssemblyCharge2659P095 : ℚ :=
  ampRadius2657P095 * (pairMagnitude2542 phaseValue2658P095
      + 2 * phaseRadius2658P095)
      * pairMagnitude2542 complexPanelIntegral2648P095
    + (ampValue2657P095 + ampRadius2657P095) * (2 * phaseRadius2658P095)
      * pairMagnitude2542 complexPanelIntegral2648P095

theorem panelAssemblyCenter2659P095_replay :
    panelAssemblyCenter2659P095 =
      pairScale2542 ampValue2657P095
        (pairMul2542 phaseValue2658P095 complexPanelIntegral2648P095) := by
  rfl

theorem panelAssemblyCenter2659P095_l1_le :
    pairMagnitude2542 panelAssemblyCenter2659P095 ≤
      ampValue2657P095 *
        (pairMagnitude2542 phaseValue2658P095
          * pairMagnitude2542 complexPanelIntegral2648P095) := by
  unfold panelAssemblyCenter2659P095
  have hamp : 0 < ampValue2657P095 := by
    norm_num [ampValue2657P095]
  have hpair := pairMagnitude_mul_le2659 phaseValue2658P095 complexPanelIntegral2648P095
  have hscaled := mul_le_mul_of_nonneg_left hpair (le_of_lt hamp)
  simpa [pairScale2542, pairMagnitude2542, abs_of_pos hamp, mul_add] using hscaled

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
