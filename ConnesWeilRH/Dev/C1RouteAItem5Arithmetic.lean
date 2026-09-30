import ConnesWeilRH.Dev.C1SpectralSummability

/-!
# Route A item-5 transfer arithmetic (records 2245, 2248, 2249, 2253, 2255)

This module freezes the rational arithmetic of the item-5 strict signed
margin at the 2249 certified standing and proves, with `norm_num`, the
transfer slacks and their strict signed-margin conclusions, plus the
transfer-free full-tail ledger of records 2253/2255/2256:

* the record 2248 high-shell tail `4 * mult * B_upper`, with the multiplicity
  corrected proxy `128.70692502981` and `B_upper = 9506275.102584327`
  (`highShellTail2248`);
* the record 2109 known-error sum (`knownError2109`);
* the count ratios `26/62` (unconditional) and `21/62` (Platt-Trudgian
  import) of record 2245 (withdrawn-route arithmetic, record 2253);
* the record 2249 certified margin lower bound `-q_hi = 1675396046388.2737`
  of the L1 enclosure (`margin2249`);
* the record 2255 ideal-to-discrete gap charge (`gapCharge2255`) and the
  certified full-tail slack (`eps0FullTail2249`);
* the record 2257 count-free assembly: the frozen tail bounds the formal
  bound shape `4 * mult * B` (`four_mul_multProxy_mul_bUpper_le_highShellTail`,
  `four_mul_mult_mul_B_le_highShellTail`), and the terminal inequality
  consumes that shape directly (`a005_item5_terminal_count_free`) with the
  numeric inputs `mult <= multProxy2248` (record 2274 proves the actual
  spectral multiplicity comparison in `C1RouteAMultiplicityBound`) and
  `B <= bUpper2243` (record 2243 composite-EM screen).

The numeric inputs remain artifact-level facts: the 2249 enclosure is a
numeric certificate (first-order error shadow, not Lean-formalized), the
2245 count uses the cited Trudgian and Platt-Trudgian imports, the 2109
known-error sum is a ledger of measured evaluation errors, and the 2255 gap
charge is a refinement-doubling estimate.  What this module certifies is
the arithmetic.  Record 2253 measured that the per-node charge budget
underlying the `owner/62` transfer factor fails by two orders of magnitude,
so the certified ledger is the full-tail fallback: from `margin2249 <=
-qLo`, a charge bounded by the full tail plus the known-error sum, and a
gap bounded by `gapCharge2255`, the strict inequality holds with the
registered positive slack.  No producer GO, no gate sign change, no RH
claim.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAItem5Arithmetic

/-- Record 2248 high-shell tail `4 * mult * B_upper`. -/
def highShellTail2248 : Real := 4894093747.7643

/-- Record 2109 known-error sum. -/
def knownError2109 : Real := 74601530.30234718

/-- Record 2249 certified margin lower bound (`-q_hi` of the L1 enclosure
`results/2249_l1_enclosure.json`). -/
def margin2249 : Real := 1675396046388.2737

/-- Explicit slack of the imported (21/62) channel. -/
def eps0Import2249 : Real := 1673663767000

/-- Explicit slack of the unconditional (26/62) channel. -/
def eps0Uncond2249 : Real := 1673269082000

theorem eps0Import2249_pos : 0 < eps0Import2249 := by
  norm_num [eps0Import2249]

theorem eps0Uncond2249_pos : 0 < eps0Uncond2249 := by
  norm_num [eps0Uncond2249]

/-- The imported transferred charge (21/62 of the tail plus the known-error
sum) sits strictly below the certified margin minus the registered slack. -/
theorem transfer_import_le_margin_sub_slack :
    highShellTail2248 * (21 / 62) + knownError2109 <
      margin2249 - eps0Import2249 := by
  norm_num [highShellTail2248, knownError2109, margin2249, eps0Import2249]

/-- The unconditional transferred charge (26/62) version. -/
theorem transfer_uncond_le_margin_sub_slack :
    highShellTail2248 * (26 / 62) + knownError2109 <
      margin2249 - eps0Uncond2249 := by
  norm_num [highShellTail2248, knownError2109, margin2249, eps0Uncond2249]

/-- Item-5 strict signed-margin inequality, imported channel: for any signed
downward enclosure `qLo` of the finite-window functional with `-qLo >=
margin2249`, and any total charge bounded by the transferred sum, the strict
inequality `charge < -qLo` holds with the registered positive slack. -/
theorem a005_item5_strict_signed_margin_import
    {qLo charge : Real}
    (hmargin : margin2249 <= -qLo)
    (hcharge : charge <= highShellTail2248 * (21 / 62) + knownError2109) :
    charge + eps0Import2249 < -qLo := by
  have h := transfer_import_le_margin_sub_slack
  linarith

/-- Item-5 strict signed-margin inequality, unconditional channel. -/
theorem a005_item5_strict_signed_margin_uncond
    {qLo charge : Real}
    (hmargin : margin2249 <= -qLo)
    (hcharge : charge <= highShellTail2248 * (26 / 62) + knownError2109) :
    charge + eps0Uncond2249 < -qLo := by
  have h := transfer_uncond_le_margin_sub_slack
  linarith

/-- Record 2255 ideal-to-discrete gap charge (refinement-doubling bound
frozen from `results/2255_l1_gaps.json`; the measured total is
`6537949.749302972`, here rounded up to `1e7`). -/
def gapCharge2255 : Real := 10000000

/-- Certified slack of the transfer-free full-tail ledger. -/
def eps0FullTail2249 : Real := 1670000000000

theorem eps0FullTail2249_pos : 0 < eps0FullTail2249 := by
  norm_num [eps0FullTail2249]

/-- The transfer-free charge (the full 2248 high-shell tail plus the
known-error sum plus the 2255 gap charge) sits strictly below the certified
margin minus the registered slack. -/
theorem transfer_free_charge_le_margin_sub_slack :
    highShellTail2248 + knownError2109 + gapCharge2255 <
      margin2249 - eps0FullTail2249 := by
  norm_num [highShellTail2248, knownError2109, margin2249, gapCharge2255,
    eps0FullTail2249]

/-- Item-5 strict signed-margin inequality, transfer-free ledger: for any
signed downward enclosure `qLo` of the finite-window functional with
`-qLo >= margin2249`, any charge bounded by the full high-shell tail plus
the known-error sum, and any ideal-to-discrete gap bounded by
`gapCharge2255`, the strict inequality `charge + gap < -qLo` holds with the
registered positive slack. -/
theorem a005_item5_strict_signed_margin_full_tail
    {qLo charge gap : Real}
    (hmargin : margin2249 <= -qLo)
    (hcharge : charge <= highShellTail2248 + knownError2109)
    (hgap : gap <= gapCharge2255) :
    charge + gap + eps0FullTail2249 < -qLo := by
  have h := transfer_free_charge_le_margin_sub_slack
  linarith

/-- Record 2243 composite-EM screen constant `B_upper` of the direct-product
mass screen (`results/2243_panel_cem_reprice.json`). -/
def bUpper2243 : Real := 9506275.102584327

/-- Upper proxy for `spectralMultiplicityConstant`. Record 2274 proves the
comparison analytically in `C1RouteAMultiplicityBound`. Its original-proxy
theorem also withdraws record 2273's incorrect under-rounding diagnosis. -/
def multProxy2248 : Real := 128.70692502981

/-- The frozen 2248 tail bounds the formal bound shape `4 * mult * B` at the
frozen screen constant and multiplicity proxy. The exact rational product
sits below the corrected frozen tail (the tail is the rounded-up bound), so
this is a strict inequality, not an identity. -/
theorem four_mul_multProxy_mul_bUpper_le_highShellTail :
    4 * multProxy2248 * bUpper2243 <= highShellTail2248 := by
  norm_num [multProxy2248, bUpper2243, highShellTail2248]

/-- Monotonicity of the count-free bound shape: any `mult` at most the 2248
proxy and any nonnegative `B` at most the 2243 screen constant give
`4 * mult * B` at most the frozen high-shell tail. -/
theorem four_mul_mult_mul_B_le_highShellTail
    {B mult : Real} (hmult : mult <= multProxy2248) (hB : B <= bUpper2243)
    (hmun : 0 <= mult) (hBnn : 0 <= B) :
    4 * mult * B <= highShellTail2248 := by
  have hmul := mul_le_mul hmult hB hBnn (le_trans hmun hmult)
  have h4 : (4 : Real) * (mult * B) <= 4 * (multProxy2248 * bUpper2243) :=
    mul_le_mul_of_nonneg_left hmul (by norm_num)
  have hf := four_mul_multProxy_mul_bUpper_le_highShellTail
  linarith

/-- Item-5 terminal inequality consuming the formal count-free bound shape
directly: if the high-shell weighted tsum is bounded by `4 * mult * B` --
the shape delivered by `exists_weightedZeroMeasure_highShell_tsum_bound`
with `mult = spectralMultiplicityConstant` -- with any `mult` at most the
2248 proxy and any nonnegative `B` at most the 2243 screen constant, and
the L1 margin and 2255 gap bound hold, then the strict signed margin
follows with the registered slack.  No count factor enters anywhere. -/
theorem a005_item5_terminal_count_free
    {qLo charge gap B mult : Real}
    (hmun : 0 <= mult) (hmult : mult <= multProxy2248)
    (hBnn : 0 <= B) (hB : B <= bUpper2243)
    (hmargin : margin2249 <= -qLo)
    (hcharge : charge <= 4 * mult * B + knownError2109)
    (hgap : gap <= gapCharge2255) :
    charge + gap + eps0FullTail2249 < -qLo := by
  have htail : 4 * mult * B <= highShellTail2248 :=
    four_mul_mult_mul_B_le_highShellTail hmult hB hmun hBnn
  exact a005_item5_strict_signed_margin_full_tail hmargin (by linarith) hgap

end C1RouteAItem5Arithmetic
end Source
end ConnesWeilRH
