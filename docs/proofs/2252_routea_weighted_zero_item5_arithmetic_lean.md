# 2252 — Lean brick: item-5 transfer arithmetic at the 2249 standing

Date: 2026-09-30

Consumer: the L3 "strict arithmetic" brick of the 2246 statement, and the
item-4 Lean-registration option of the 2248 tail: register the arithmetic
downstream of the Trudgian / Platt-Trudgian imports as a formal brick.

Verdict: **landed**. The arithmetic is machine-checked with the permitted
axioms; the numeric inputs stay artifact-level facts.

## The module

`ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean` freezes the constants and
proves four theorems with `norm_num`:

```text
highShellTail2248 = 4894093747.764274       (2248: 4 * 128.70692502980964
                                             * 9506275.102584327)
knownError2109    = 74601530.30234718
margin2249        = 1675396046388.2737      (2249: -q_hi of the L1 enclosure)
eps0Import2249    = 1673663767000
eps0Uncond2249    = 1673269082000

transfer_import_le_margin_sub_slack :
    tail * (21/62) + knownError < margin2249 - eps0Import2249
transfer_uncond_le_margin_sub_slack :
    tail * (26/62) + knownError < margin2249 - eps0Uncond2249
a005_item5_strict_signed_margin_import :
    margin2249 <= -qLo -> charge <= tail * (21/62) + knownError ->
        charge + eps0Import2249 < -qLo
a005_item5_strict_signed_margin_uncond :  (26/62 variant)
```

The two arithmetic inequalities are strict (the exact slacks are
`943.406...` and `963.747...`), which is what lets `linarith` conclude
the strict signed-margin statements: non-strict hypotheses alone would
not suffice.

## Verification

```text
module + probe build        Build completed successfully (3521 jobs)
full library build          Build completed successfully (4148 jobs)
axiom audit                 transfer_import_le_margin_sub_slack:
                            [propext, Classical.choice, Quot.sound]
                            (same for the other three; no sorryAx)
```

Paired audit probe:
`ConnesWeilRH/Dev/C1RouteAItem5ArithmeticProbe.lean`
(`#print axioms` for all four theorems), run via
`lake env lean` in WSL; logs in `build-logs/routea_item5_*_20260930.log`.

## What this closes and what it does not

Closed: the arithmetic of the item-5 ledger — from the certified margin
lower bound and the transferred charge bound, the strict inequality holds
with explicit positive slack; the 2246 L3 status moves from
`STATEMENT-FIXED` to `ARITHMETIC-PROVED` (conditional on its numeric
inputs).

Not closed: the numeric inputs themselves — the 2249 enclosure is a
first-order-shadow numeric certificate, the 2245/2250 counts rest on the
cited Trudgian `|S(T)|` bound and the Platt-Trudgian import, and the 2109
known-error sum is a measured ledger — none of these are Lean-formalized
here. The per-node charge uniformity of L2 remains open. No producer GO,
no gate sign change, no RH claim.

## Provenance

- module: `ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean`;
- probe: `ConnesWeilRH/Dev/C1RouteAItem5ArithmeticProbe.lean`;
- constants from `results/2248_multiplicity_tightening.json`,
  `results/2245_owner_count_brick.json`,
  `results/2109_known_prefix_margin_ledger.json`,
  `results/2249_l1_enclosure.json`.