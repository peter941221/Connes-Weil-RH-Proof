/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1RouteAProducerWired
import ConnesWeilRH.Dev.C1RouteAOwnerNodes

/-!
# The certified L1 enclosure interface (record 2318)

Record 2249 certifies a two-sided enclosure of the stored finite-window
functional at the captured owner (convention A: the stored binary64 operands
are exact; first-order forward-error shadow).  With `q` the instrumented
value and `E` the shadow sum, the exact-real evaluation of the pipeline
satisfies `q - E <= Q <= q + E`, stored as the renders
`q_lo = -1675398609458.8762`, `q_hi = -1675396046388.2737`.  This module
wires that enclosure into the producer margin lane.

Sub-ulp finding (record 2318): the exact shadow upper bound `q + E` sits
`0.0395` ulp of `2^-12` ABOVE the stored render `q_hi` (round-to-nearest),
i.e. `0.1147` ulp above the shortest-decimal transcription
`-1675396046388.2737`.  A Lean pin at that decimal would therefore sit
strictly INSIDE the certified bound and exclude the artifact's own claim
(the record 2314 decimal-pin hazard, here on the margin side).  The shipped
constants round outward by `1e-4` (`0.41` ulp):

* `l1MarginEnclosure2249 = 1675396046388.2736` — a certified lower bound of
  `-Q = |Q|` at the captured owner, `7.2e-5` (`0.295` ulp) below the exact
  shadow bound;
* `l1UpperEnclosure2249 = -1675396046388.2736` — the matching upper
  enclosure of the signed functional, its exact negative.

The consumer `hmargin_of_certified_l1_enclosure` turns the enclosure shape
`q <= l1UpperEnclosure2249` into the producer's signed-margin shape
`l1MarginEnclosure2249 <= -q`; the terminal variant
`a005_item5_terminal_count_free_l1` re-runs the record 2257 count-free
ledger at the certified constant; and the composed producer
`a005_item5_producer_wired_owner_nodes_margin` combines the record 2317
owner-nodes strip interface, this enclosure, the record 2109 known-error
charge and the record 2310 gap split into the item-5 strict signed
inequality `... < -q`, whose residual hypotheses are exactly `hnode`
(the record 2316 node table), the enclosure bound `hq`, the known-error
charge `hcharge`, and the gap split with its two pinned enclosures.

`margin2249` (record 2252) is NOT routed through here: it is the historical
transcription of the render, `0.1147` ulp above the exact shadow bound; its
ledger arithmetic is untouched and no artifact direction is asserted of it.

No producer GO, no gate sign change, no RH claim.
-/

namespace ConnesWeilRH
namespace Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1SpectralWeil
open ConnesWeilRH.Source.C1SpectralSummability
open ConnesWeilRH.Source.CC20YoshidaNearZeros
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

/-- Certified lower bound of `|Q|` at the captured owner from the record
2249 L1 enclosure: the shortest-decimal render `1675396046388.2737` rounded
outward (down) by `1e-4`, covering the exact shadow bound with `7.2e-5`
slack. -/
def l1MarginEnclosure2249 : Real := 1675396046388.2736

/-- Certified upper enclosure of the signed finite-window functional at the
captured owner (record 2249): the exact negative of
`l1MarginEnclosure2249`. -/
def l1UpperEnclosure2249 : Real := -1675396046388.2736

theorem l1UpperEnclosure2249_eq_neg :
    l1UpperEnclosure2249 = -l1MarginEnclosure2249 := by
  norm_num [l1UpperEnclosure2249, l1MarginEnclosure2249]

/-- The outward-rounded certified constant sits below the record 2252
transcription `margin2249` by `1e-4`. -/
theorem l1MarginEnclosure2249_le_margin2249 :
    l1MarginEnclosure2249 ≤ margin2249 := by
  norm_num [l1MarginEnclosure2249, margin2249]

/-- The record 2252 transfer-free ledger re-run at the certified L1
enclosure constant: the full high-shell tail, the known-error sum and the
gap charge sit below `l1MarginEnclosure2249 - eps0FullTail2249` with the
registered slack. -/
theorem transfer_free_charge_le_l1Enclosure_sub_slack :
    highShellTail2248 + knownError2109 + gapCharge2255 <
      l1MarginEnclosure2249 - eps0FullTail2249 := by
  norm_num [highShellTail2248, knownError2109, gapCharge2255,
    l1MarginEnclosure2249, eps0FullTail2249]

/-- Item-5 strict signed inequality at the certified L1 enclosure constant:
the count-free shape of record 2257 with `margin2249` replaced by the
certified `l1MarginEnclosure2249`. -/
theorem a005_item5_terminal_count_free_l1
    {q charge gap B mult : Real}
    (hmun : 0 ≤ mult) (hmult : mult ≤ multProxy2248)
    (hBnn : 0 ≤ B) (hB : B ≤ bUpper2243)
    (hmargin : l1MarginEnclosure2249 ≤ -q)
    (hcharge : charge ≤ 4 * mult * B + knownError2109)
    (hgap : gap ≤ gapCharge2255) :
    charge + gap + eps0FullTail2249 < -q := by
  have htail : 4 * mult * B ≤ highShellTail2248 :=
    four_mul_mult_mul_B_le_highShellTail hmult hB hmun hBnn
  have h := transfer_free_charge_le_l1Enclosure_sub_slack
  linarith

/-- **Certified L1 enclosure interface (record 2318).**  Any functional
value at most the certified upper enclosure `l1UpperEnclosure2249` (record
2249, outward-rounded) satisfies the producer's signed-margin shape at the
certified constant. -/
theorem hmargin_of_certified_l1_enclosure {q : Real}
    (hq : q ≤ l1UpperEnclosure2249) :
    l1MarginEnclosure2249 ≤ -q := by
  have h := l1UpperEnclosure2249_eq_neg
  linarith

/-- **Producer with the owner-nodes strip interface and the certified L1
enclosure (records 2317 + 2318).**  The strip hypothesis is supplied by
`frozenStripHypothesis_of_owner_nodes` (residual: the record 2316 node
table's 101-node bound), the signed margin by the record 2249 enclosure
shape `hq`, the gap by the record 2310 split consumer, and multiplicity by
the record 2274 analytic bound; the conclusion is the item-5 strict signed
inequality `tsum + chargeRest + gap + eps0FullTail2249 < -q` with `-q` the
signed functional value at the captured owner. -/
theorem a005_item5_producer_wired_owner_nodes_margin
    (baseCoefficients corrCoefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ)
    (hnode : ∀ j : ℤ, -(50 : ℤ) ≤ j → j ≤ 50 →
      min (stripSecondNorm ((j : ℝ) / 100)
            (correctedPhysical baseCoefficients modulations) *
           stripNorm ((j : ℝ) / 100)
            (correctedPhysical corrCoefficients modulations))
          (stripSecondNorm ((j : ℝ) / 100)
            (correctedPhysical corrCoefficients modulations) *
           stripNorm ((j : ℝ) / 100)
            (correctedPhysical baseCoefficients modulations))
        ≤ stripGridMax2303)
    {q gap chargeRest windowCharge tailCharge : Real}
    (hq : q ≤ l1UpperEnclosure2249)
    (hcharge : chargeRest ≤ knownError2109)
    (hsplit : gap ≤ windowCharge + tailCharge)
    (hwindow : windowCharge ≤ windowCharge2309)
    (htail : tailCharge ≤ tailCharge2307) :
    (∑' n : Nat, ∑' rho : spectralHeightShell (n + 1),
        spectralNormTerm
          ((correctedPhysicalCompactLogTest baseCoefficients modulations).convolution
            (correctedPhysicalCompactLogTest corrCoefficients modulations))
          rho.1) +
      chargeRest + gap + eps0FullTail2249 < -q := by
  have hstrip : FrozenStripHypothesis
      (correctedPhysicalCompactLogTest baseCoefficients modulations)
      (correctedPhysicalCompactLogTest corrCoefficients modulations) :=
    frozenStripHypothesis_of_owner_nodes baseCoefficients corrCoefficients
      modulations hnode
  have htsum := directProduct_highShell_tsum_bound _ _ hstrip
  have hmult :=
    Source.C1RouteAMultiplicityBound.spectralMultiplicityConstant_le_multProxy2248
  have htail2248 :
      (∑' n : Nat, ∑' rho : spectralHeightShell (n + 1),
          spectralNormTerm
            ((correctedPhysicalCompactLogTest baseCoefficients modulations).convolution
              (correctedPhysicalCompactLogTest corrCoefficients modulations))
            rho.1) ≤ highShellTail2248 :=
    htsum.trans (four_mul_mult_mul_B_le_highShellTail hmult le_rfl
      spectralMultiplicityConstant_nonneg (by norm_num [bUpper2243]))
  have hgap := hgap_of_certified_split hsplit hwindow htail
  have hm := hmargin_of_certified_l1_enclosure hq
  have hmain :
      (∑' n : Nat, ∑' rho : spectralHeightShell (n + 1),
          spectralNormTerm
            ((correctedPhysicalCompactLogTest baseCoefficients modulations).convolution
              (correctedPhysicalCompactLogTest corrCoefficients modulations))
            rho.1) +
        chargeRest + gap + eps0FullTail2249 < l1MarginEnclosure2249 := by
    linarith [htail2248, hcharge, hgap,
      transfer_free_charge_le_l1Enclosure_sub_slack]
  linarith [hmain, hm]

end Dev
end ConnesWeilRH
