# 2725 — the powered-seed endpoint envelope is a Lean theorem and `l1Mass smoothSeed <= 3` is load-bearing (l1u = 4 fails the wired pins 10.57x / 7.44x; clearing certified for every l1u <= 3.0023496)

Verdict: the record-2724 re-seed brick is LANDED in both halves.

(a) The Lean brick
`ConnesWeilRH.Source.norm_cardinalSum_poweredSeed_le_endpoint_env`
(`ConnesWeilRH/Dev/C1PoweredSeedEnvelope2725.lean`, 12 declarations)
formalizes the 2720 per-node-rung decay envelope at the exact
`cardinalSum`-at-`poweredSeed` shape; the paired audit is green with the
exact axiom trio on 12/12 declarations, zero `sorry`, linux-native build
3873 jobs (mirror bytes == committed bytes, sha-bound below).

(b) The numeric tie `results/2725_envelope_bridge.json` (checker
`scripts/envelope_bridge_2725.py`, sha-bound) re-anchors the 2720/2722C
certified constants bitwise in the Lean-emitted shape at the mass
constant `l1u = 3` (the 2720 pricing convention) and measures the same
chain at the committed `smoothSeed_l1Mass_le_four` reading `l1u = 4`:

```text
+--------+-------------------------+-------------------------+----------------+
| pin    | l1u = 3 (re-anchored)   | l1u = 4 (same chain)    | verdict        |
+--------+-------------------------+-------------------------+----------------+
| C4     | 60524298.630698465      | 645061739.1447207       | 10.5748x pin   |
| C2     | 28161344.216206506      | 215700251.18533155      |  7.4379x pin   |
| q*(64) | 2.5248153557101123e-16  | 2.5248153557101123e-16  | clears (inert) |
+--------+-------------------------+-------------------------+----------------+
```

At `l1u = 3` all three pins clear with margins `475701.37` /
`838655.78` / `7.518e-18` (i.e. `0.780%` / `2.892%` / `2.892%` of the
pin — the 2722C margins reproduced bitwise). At `l1u = 4` C4 and C2 fail
by `10.5748x` / `7.4379x` over the pins, and `q*(64)` is exactly
unchanged (`l1u`-inert; verified bitwise up to `l1u = 1000`).

The rigorous min-homogeneity law `value(l1u) <= value(3)*(l1u/3)^10`
(per-node, section 4) certifies clearing of BOTH pins for every
`l1u <= 3.002349604479395`, with the same-run scan straddling the true
crossing to `~2e-6`. Therefore the mass premise `l1Mass smoothSeed <= 3`
is **load-bearing**: the committed `<= 4` bound is too weak for this
lane, and the residual numeric obligation of the three wired pins is
`{l1Mass smoothSeed <= 3, D-table pins k = 1..12}`.

## 0. Binding-route audit (start-of-round declaration)

- Consumer: the three cardinal-sum pins of the stored row-B
  contradiction (`fourPointContradictionRowBStored2722F` /
  `...BStored2723`), consumed through the new record-2725 Lean brick
  `norm_cardinalSum_poweredSeed_le_endpoint_env`, whose five numeric
  premises are `l1Mass smoothSeed <= l1u`, `0 <= l1u`,
  `rungs.Nonempty`, `derivOrderL1 k smoothSeed <= D k`, `0 <= D k`
  (`k in rungs`); downstream: selected detector `qw < 0` ->
  same-owner `qw >= 0` -> `SourceRH` -> Mathlib RH.
- Owner: the same stored row-B lists (record-1980 builder,
  `gamma_2 = 21.022039638771556`, `re = 0.55`, `N = 5`) and the
  powered seed `L_pow(s) = L1(s/2)^10`, `seed0 = 3^10` — the 2724
  repair object.
- Premise acted on: none removed at the wiring level. This round
  decides WHICH mass constant the loading pin lane requires
  (`l1u = 3` vs the committed `l1u = 4`) and lands the envelope brick
  the pins will be proved against.
- Failure criterion / stop: a fully green tie run with the clone
  anchored bitwise, the l1u = 4 pin verdicts, the certified clearing
  window, and a verdict; plus the Lean brick's audit census. No
  premise is claimed discharged.

## 1. The Lean brick (what it proves, verbatim shape)

Statement (12 declarations; the ship theorem is the last):

```text
norm_cardinalSum_poweredSeed_le_endpoint_env
  (h1  : l1Mass smoothSeed <= l1u)   (h1n : 0 <= l1u)
  (hne : rungs.Nonempty)
  (hD  : forall k in rungs, derivOrderL1 k smoothSeed <= D k)
  (hDn : forall k in rungs, 0 <= D k)
  (sigma in Icc 0 1) (t : R) :
  ||cardinalSum nodes poweredSeed y (sigma + t*I)||
    <= sum over z in nodes :
         ||y z|| / (||nodeProduct nodes z z|| * ||laplaceAt poweredSeed 0||)
       * prod over w in nodes.erase z :
           sqrt((max |w.re| |1 - w.re|)^2 + (t - w.im)^2)
       * (if t = z.im then exp(max |z.re| |1 - z.re|) * l1u
          else min (exp(max |z.re| |1 - z.re|) * l1u)
                   (inf over k in rungs of
                      exp(max |z.re| |1 - z.re|) * (D k * 2^k / |t - z.im|^k)))^10
```

Supporting leaves: `abs_sub_le_max_endpoint` (the `|sigma - a| <=
max(|a|,|1-a|)` endpoint law from `sigma in [0,1]`),
`norm_sub_node_le_sqrt` (node separation), `norm_nodeProduct_le`
(product norm via `List.norm_prod_le`), the two smoothSeed transform
lemmas (`l1Mass` crude arm and the `derivOrderL1` rung arm, both from
the committed 2722 IBP lemma), the halving coordinate laws
(`halved_im_eq`, `halved_re_abs`), `rung_div_eq`, the powered-seed
ladder `norm_laplaceAt_poweredSeed_sub_le_ladder` (10th power of the
per-node min), and `ladderEnv_nonneg` / `ladderEnv_le` (the sum
assembly).

Build/audit evidence: `C1PoweredSeedEnvelope2725Audit.lean` prints
`#print axioms` on all 12 declarations — the exact trio
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`; linux-native
build footer `Build completed successfully (3873 jobs)`, zero `error:`
lines, zero `declaration uses sorry`.

## 2. The numeric tie: same-run re-anchoring and the shape clone

The tie does not quote the 2720/2722C constants; it re-runs the frozen
2720 engine in-process and anchors bitwise:

- `S2.p3_script_hash_matches_2720_provenance` — the live
  `p3_certified_strip_constants_2720.py` sha256 equals the sha recorded
  in the committed 2720 artifact (`f16ce609…`);
- `S2.d_table_anchor_bitwise` — the certified D-table floats equal the
  committed artifact's, element for element;
- `S2.anchor_C4_bitwise` / `anchor_C2_bitwise` / `anchor_q_bitwise`
  (`rel = 0.0`), `S2.tie_equals_2722C` — the three certified constants
  equal the committed 2722C tie renders.

Then the parameterized clone: `envelope_cell_l1u` is `p3.envelope_cell`
operation for operation with only the crude arm constant parameterized
(`pieces = [3 * Ez]` -> `[l1u * Ez]`), and the clone scan chain at
`l1u = 3` reproduces `p3.scan_channel` bitwise on all three quantities
(`S3.clone_base_bitwise` / `clone_corr_bitwise` / `clone_q_bitwise`) and
on 324/324 point cells (`S3.clone_pointcells_bitwise`), with a pointwise
monotonicity guard (`S3.mono_l1u4_ge_l1u3_pointcells`, 0/324
violations). Coverage re-runs both lanes clean
(`S5.coverage_l1u3_reanchor`, `S5.coverage_l1u4_clean`: `fails = 0`,
worst sampled/envelope `3.302474e-04` — identical readings).

Shape conventions tying the Python envelope to the Lean statement
(documented in the checker header; verified identities):
`exp(max(re, 1-re, 0))` is identically `Real.exp (max |re| |1-re|)`;
the crude arm `3*Ez` is the Lean `E * l1u` at `l1u = 3`; the script's
ladder skip at `tau_lo = 0` is the Lean `if t = z.im`; the script pads
(`PAD_UP` etc.) make the script cell value an upper bound of the sup
over the cell of the pointwise Lean envelope.

## 3. The l1u = 4 lane and the binding classification

`S4.monotone_l1u` — both channel sups rise at l1u = 4
(C4 6.0524299e7 -> 6.4506174e8; C2 2.8161344e7 -> 2.1570025e8), and the
`q*(64)` reading is bitwise invariant under the crude arm
(`S4.q_inert_l1u1000_bitwise`, checked up to `l1u = 1000`), so the
contract pin is not part of the load here.

Binding detail at the argmax cells (artifact
`binding_classification`): at l1u = 3 the C4 argmax cell
`(sigma = 1, t in (22.3, 22.4))` mixes 3 crude-bound nodes with 5
rung-bound nodes (k = 3 at `Im = 0`, k = 4 at `-Im rho`), which is why
the measured C4 growth is `10.6579x` and not the full crude power
`(4/3)^10 = 17.76x`; at l1u = 4 the C4 argmax cell MOVES to
`(22.0, 22.1)` and the C2 argmax cell moves from `(19.6, 19.7)` (3
crude-bound nodes at l1u = 3) to `(19.9, 20.0)` (all three rung k = 1 at
l1u = 4). The sup is over mixed-binding cells and re-pricing moves the
argmax — the measured ratios are therefore per-l1u sup readings, not a
pointwise power law.

## 4. The min-homogeneity law and the certified clearing window

Per node, `Psi(l1u) = min(rho*a, {b_k})` with `rho = l1u/3`, `a = 3*Ez`
and the rung arms `b_k` `l1u`-invariant; for `rho >= 1` every left
argument is at most its `rho`-scaled right counterpart
(`rho*a <= rho*a`, `b_k <= rho*b_k`), so `min(rho*a, b) <= rho*min(a,b)`
and hence, summing the `Psi^10` terms with `l1u`-independent
coefficients (and the tail ladder the same way),

```text
value(l1u) <= value(3) * (l1u/3)^10     pointwise, cellwise, supwise.
```

Therefore the certified lane clears every `l1u <= L*` with
`L* = 3*(pin/value3)^(1/10)`: `L*_C4 = 3.002349604479395`,
`L*_C2 = 3.0088165995432155` (both pins must clear: the binding window
is `l1u <= 3.0023496`). The same-run scan straddles the true crossing
tightly: C4 at `m_lo = 3.0023466021` reads `6.099939000275e+07`
(clears) and at `m_hi = 3.0023526068` reads `6.100061000274e+07` (does
not clear); C2 at `3.0088135907` reads `2.899971000130e+07` (clears) and
at `3.0088196084` `2.900029000130e+07` (does not clear). The rigorous
window is sharp to `~2e-6` relative at both pins.

The reverse inequality is FALSE in general (counterexample `a = 10`,
`b = 1`, `rho = 2`: `min(20, 1) = 1 < 2 = rho*min(10, 1)`), so `L*` is a
one-sided certified bound — above it the lane is open, and the measured
l1u = 4 failure shows the wiring cannot simply take the committed `<= 4`.

Routing consequence: the follow-up Lean brick is
`l1Mass smoothSeed <= 3` (the seed test is nonnegative, so this is the
sharp reading of the committed value anchor `laplaceAt smoothSeed 0 = 3`
through `l1Mass = laplaceAt smoothSeed 0`); with it, `h1` instantiates
at `l1u = 3` and the envelope lane reduces to the 12 certified D-table
pins (`D_1 = 2`, `D_2 = 8` exact committed anchors).

## 5. Honesty line and routing

- `wired_hypotheses_removed = 0`. This round lands the envelope brick
  and decides the mass-constant loading; it discharges no wired
  hypothesis. The three pins remain named hypotheses; the residual
  premise list shrinks to `{l1Mass smoothSeed <= 3 brick, D-table pins
  k = 1..12}` plus the unchanged wiring obstruction
  `{hgate24, hprefix, htarget/hzero bricks, rho caps}`.
- A failed sufficient bound is not a lower bound: the l1u = 4 statement
  is "the envelope lane cannot discharge the pins at l1u = 4", not "the
  pins are false". The pins as obligations survive at `l1u <= 3.0023`.
- The D-table pins stay artifact-grade (numeric certified enclosures in
  the mpf chain, not Lean theorems); the stored binary64 nodes stay
  model-grade with the node-radius transfer brick open.
- No producer GO; no map-103 reopening; no `SourceRH`; no RH claim.
  `DEAD_ON_CURRENT_FAMILY` freeze unchanged — premise-blocker
  accounting inside the frozen family's contradiction audit.

## 6. Evidence

- Ship module: `ConnesWeilRH/Dev/C1PoweredSeedEnvelope2725.lean`
  (sha256 `d04e2ee3d91f46621fa93d98ade8dc0b0d13ba33602cacc1ce63199b88d2d9de`);
  audit `...Audit.lean` (sha256 `a1d9d4d5d34258485a713b5845ec8116e54150411dc48dcf6d2841f433deb89c`);
  audit log: 12/12 axiom-trio records, footer `Build completed
  successfully (3873 jobs)`, 0 `error:`, 0 `uses sorry`.
- Checker: `scripts/envelope_bridge_2725.py` (sha256
  `38e8bfad0bc9e88a123fe2e8d103ce89572adb99f17dd0768d8749b0e41a9ab9`,
  bound in the artifact under `provenance.checker`; any edit invalidates
  the artifact). Staged bytes == working bytes (LF preserved).
- Artifact: `results/2725_envelope_bridge.json` (46/46 checks,
  `verdict = ENVELOPE-BRIDGE-L1MASS3-BEARING`), with provenance sha256
  for the frozen 2720 producer (`f16ce609…`), the 2722c tie artifact
  (`5899ce25…`), the capture module (`2244175c…`), the wired module
  (`40e493fe…`), the ship module and the audit.
- Wired pin literals re-parsed from the committed capture:
  `wiredC4 = 61000000`, `wiredC2 = 29000000`,
  `wiredQ = 13/50000000000000000`.
- Route context: `docs/map/103_four_point_same_span_three_cut_campaign.md`
  (2724 -> 2725 sections), `docs/proofs/2724_seed_object_screen.md`.

## 7. Instrument findings (first-run defects, disclosed)

- Boundary-estimator failure: the first run's clearing bracket used a
  two-point power-law estimate
  `alpha = log(value4/value3)/log(4/3)` (~`8.23`/`7.08`) and FAILED
  (`S4.boundary_C4_bracket` / `_C2_bracket`): the estimate put the
  crossing high, and the measured value at the estimated `m_lo` sat
  above the pin (`6.110250889265e7 > 6.1e7`). The failure is structural:
  the sup moves between cells with different binding mixes (section 3),
  so no smooth two-point law bounds the sup. Restructured to the exact
  one-sided min-homogeneity law above (`Lstar = 3*(pin/value3)**0.1`);
  the old reading is kept on record in the artifact's history and the
  restructure is disclosed in the checker header.
- Script defects fixed before the green run (all caught by the staged
  anchors): a leftover self-comparison in the point-cell loop
  (`bits(r3, mp.mpf(r3))` -> `bits(e3, r3)`), an unused loop variable,
  and explicit `assert ... is not None` guards before the binding dict.
- Lean-probe instrument law (recorded for AGENTS.md): `rw [norm_mul]`
  splits only the LEFTMOST occurrence in the goal; `simp only
  [norm_mul, norm_div]` iterates to fixpoint and splits all; a plain
  equation `rw [h]` rewrites all occurrences normally. Ships the shape
  used by the brick's product-norm leaves.
