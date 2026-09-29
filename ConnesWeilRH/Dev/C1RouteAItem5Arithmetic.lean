import ConnesWeilRH.Dev.C1SpectralSummability

/-!
# Route A item-5 transfer arithmetic (records 2245, 2248, 2249)

This module freezes the rational arithmetic of the item-5 strict signed
margin at the 2249 certified standing and proves, with `norm_num`, the two
transfer slacks and their strict signed-margin conclusions:

* the record 2248 high-shell tail `4 * mult * B_upper`, with the multiplicity
  proxy `128.70692502980964` and `B_upper = 9506275.102584327`
  (`highShellTail2248`);
* the record 2109 known-error sum (`knownError2109`);
* the count ratios `26/62` (unconditional) and `21/62` (Platt-Trudgian
  import) of record 2245;
* the record 2249 certified margin lower bound `-q_hi = 1675396046388.2737`
  of the L1 enclosure (`margin2249`).

The numeric inputs remain artifact-level facts: the 2249 enclosure is a
numeric certificate (first-order error shadow, not Lean-formalized), the
2245 count uses the cited Trudgian and Platt-Trudgian imports, and the 2109
known-error sum is a ledger of measured evaluation errors.  What this module
certifies is the arithmetic: from `margin2249 <= -qLo` and the transferred
charge bound, the strict inequality `charge < -qLo` holds with an explicit
positive slack.  No producer GO, no gate sign change, no RH claim.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAItem5Arithmetic

/-- Record 2248 high-shell tail `4 * mult * B_upper`. -/
def highShellTail2248 : Real := 4894093747.764274

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

end C1RouteAItem5Arithmetic
end Source
end ConnesWeilRH
