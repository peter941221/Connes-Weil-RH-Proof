# 2726 — Route B reopen: the row-B probe meets the named-hypothesis reopen gate (route authority change)

Verdict: ROUTE B REOPENED (scoped) at model grade, authorized 2026-10-17.
The map-103 `DEAD_ON_CURRENT_FAMILY` freeze carried one explicit reopen
clause; the row-B named-hypothesis probe now meets it. The freeze's core
evidence (the 16 registered-pattern rows) is unchanged and remains binding
for those rows. No producer GO, no `SourceRH`, no RH claim; Route A remains
the binding producer lane for `qw(g) >= 0`.

## 1. The reopen clause and its satisfaction

Binding text (AGENTS §2, map README §B): reopen the same-owner four-point B5
family only after "a named-hypothesis probe produces a complete-owner gate at
or beyond the tail-closure index, or proves a q bound strong enough for the
actual gate row and lambda".

The probe (records 2716-2725; all at model grade except the landed Lean
bricks named in §3):

```text
+---------------------------+------------------------------------------------------------+
| clause half               | evidence                                                   |
+---------------------------+------------------------------------------------------------+
| named-hypothesis probe    | 2716: exact 2708-contract repricing of all 35 stored rows; |
|                           | 16 registered-pattern rows stay dead (freeze core          |
|                           | confirmed); 11 non-vertex rows honestly joint-compatible;  |
|                           | 2 P4-screen-admissible at n = 3. The G1 witness index      |
|                           | reduces to n = 3.                                          |
| complete-owner gate       | 2718 sign rig (4/4 claims, mouth margins 3.36% / 2.92%     |
|                           | channel-enclosure grade; roundoff classes alone            |
|                           | 1.7e8 / 8.9e7) + 2719 zero-set identification: stored      |
|                           | lists EQUAL the complete source-zero sets (19 and 48,      |
|                           | residuals 0.0) — the 2718 certificates were already at     |
|                           | the complete owner; the re-measurement clause is a NO-OP.  |
| at the tail-closure index | row B (height 21.022039638771556, N = 5, n = 3): gate      |
|                           | floor lambda >= 15.86 (2716/2717); 2720 PAIR lane closes   |
|                           | the tail constraint at row B's OWN stored index n = 3,     |
|                           | lam_min = 3.2e-19 — eight orders below the gate floor.     |
+---------------------------+------------------------------------------------------------+
```

Row A (height 14.1347, N = 4) remains an absorption reading (tail closes only
at n = 4, lim 0.256), not a gate row; the reopen is scoped to row B.

## 2. Changed hypotheses (why the 2035 obstruction no longer applies)

The 2035 no-go is scoped to its stated owner/hypotheses. Three named changes:

1. Branch admission: the 2708 §5 branch-exact reading replaces the
   vertex-only pattern frame (2030-era); 2718 explicitly supersedes that
   reading of the sign half (the vertex-centered budget does not transfer to
   channel boxes).
2. Complete-owner identification: 2719 certifies the stored lists equal the
   complete zero sets — the 2035-class flip budgets protected a fixed
   under-approximate owner, which is no longer the object.
3. Seed-object correction: 2724 falsifies the `explicitSeed` identification
   (the wired C4/C2 pins are FALSE as written there: 1.89e87x / 3.11e62x over
   the pins) and re-points the pins to the `poweredSeed` object, where the
   2720 constants apply (2725 re-anchored bitwise, margins 0.780% / 2.892% /
   2.892%).

The obstruction itself ("gate rows occur before the same-index tail closes")
is proved inapplicable at row B: gate and tail hold at the same index n = 3.

## 3. Formal bricks landed on the reopened lane (already committed)

```text
+--------+----------------------------------------------------------------+
| record | brick                                                          |
+--------+----------------------------------------------------------------+
| 2722A  | IBP bridge: strip envelopes -> three scalar pins + support      |
| 2722B  | triangle-ladder pin mechanism NO-GO (4.79e7 / 1.08e6 / 5.63e4)  |
| 2722C  | decay-envelope transport (checker 36/36, anchors rel 0.0)       |
| 2722D  | cardinal carrier instantiation (10 -> 7 logical hypotheses)     |
| 2722E  | stored witness data-leg screen (pins bitwise-anchored)          |
| 2722F  | stored row-B capture: 3 finite-data legs PROVED, no radius      |
| 2723   | wired hprefix PROVED from orbit data (kind-shrink 7 -> 9)       |
| 2725   | poweredSeed envelope Lean theorem (12 decls, axiom trio 12/12)  |
+--------+----------------------------------------------------------------+
```

Current best variant: `fourPointContradictionRowBStored2723` with nine named
hypotheses `{hNorm, hIm, hright, hcontractPin, hquarticPin, hquadraticPin,
hgate24, htarget, hzero}` (`hright` is the off-line hypothesis itself).

## 4. Campaign card (bounded; the reason the reopen is execution priority)

```text
owner        stored row-B cardinal owners (record-1980 builder) re-seeded to
             `poweredSeed` (2724 repair object; support radius
             5*(2r+1) ~ 875.7 -> ~105)
premise      the three wired cardinal pins (hcontractPin / hquarticPin /
to remove    hquadraticPin at q 26/1e17, C4 6.1e7, C2 2.9e7)
consumer     fourPointContradictionRowBStored2723 (-> ...2722F -> ...2721C)
criterion    a Lean proof of the pins from a formalized D-ladder + rung
             envelope, standard axiom trio, zero sorry
residual     {l1Mass smoothSeed <= 3, D-table pins k = 1..12} (2725), then
             carrier re-seed (2722D pattern) and the rho-quantified duties
             {hgate24 (model-grade instrument ready), htarget, hzero,
             hNorm/hIm caps}
budget       separate multi-session brick per §2 of the campaign card
stop         any rung that fails to price at the wired constants (2722B), or
             a proven l1Mass > 3.002349604479395 (then re-price, not extend)
```

Numerical anchors for the campaign (all committed artifacts):
D-table `results/2720_p3_certified_strip_constants.json` (`D_k = 4 int_0^{1/2}
|T^(k)|`, interval cells 4096 + sliver); tie `results/2725_envelope_bridge.json`
(46/46); exact committed values: `derivOrderL1 1 smoothSeed = 2`,
`derivOrderL1 2 smoothSeed = 8` (existing Lean modules, §5).

## 5. First execution facts (reconnaissance, this record's session)

The D-table IS the certified enclosure of `derivOrderL1 k smoothSeed` itself:
`derivOrderL1 k smoothSeed = 2 * int_0^1 ||T^(k)|| = 4 * int_0^{1/2} |T^(k)|`
(the second identity is the committed `derivOrderL1_smoothSeed_eq` plus
mirror symmetry). Existing Lean state: order 1 exact (`= 2`) and order 2
exact (`int_abs_iteratedDeriv_two_smoothTransition = 4`, hence `= 8`) are
already proved; the open orders are 3..12 plus the mass `l1Mass = 3`
(committed only `<= 4`; the true value is exactly 3 by the flat-transition
support decomposition `2 + 2 * int_0^1 T = 2 + 1`).

## 6. Non-claims

- The 16 registered-pattern rows of the 2035 freeze remain DEAD at honest
  grade; this reopen does not touch them.
- Route A (`qw(g) >= 0` for the selected detector) remains the binding
  producer lane with its own bottleneck (signed physical-kernel/C3' budget);
  a completed Route B proves RH via the same-span contradiction for
  `h(lambda)`, not via the binding producer statement.
- The reopened lane's product at model grade is a feasibility witness; the
  rho-quantified duties (hgate24, htarget/hzero over genuine zeros) remain
  the analytic wall and are NOT covered by this reopen.
- No producer GO, no `SourceRH`, no RH claim.

## 7. Provenance

Route-authority change per AGENTS §4: `AGENTS.md` §2 and
`docs/map/README.md` updated together in this commit; map-103 §2726 added.
Authorized by Peter 2026-10-17 (strategy review + reopen instruction), after
the ledger of records 2716-2725 summarized above.

Evidence:
- `docs/map/103_four_point_same_span_three_cut_campaign.md` §§2716-2725 (and
  the new §2726 section),
- `docs/proofs/2716_g1_joint_acceptance_repricing.md`,
  `2717_p5_n3_probe.md`, `2718_gate_sign_rig.md`, `2719_g2_complete_owner_id.md`,
  `2720_p3_certified_strip_constants.md`, `2722A`-`2722F`, `2723`, `2724`,
  `2725_powered_seed_envelope.md`,
- `results/2720_p3_certified_strip_constants.json`,
  `results/2725_envelope_bridge.json`.