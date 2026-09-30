# 2318 — L1-ENCLOSURE-WIRED: the certified record 2249 enclosure enters the producer margin lane; the shipped constants round outward by 1e-4 (0.41 ulp)

The producer theorem of record 2311 carries the signed margin as a hypothesis
`margin2249 <= -q`.  Record 2249 certified the finite-window functional `q`
at the captured owner inside a two-sided first-order shadow enclosure
`q in [q_lo, q_hi]` (artifact `results/2249_l1_enclosure.json`), which
supplies the producer's `hmargin` shape up to one transcription step: the
enclosure is a statement about the exact-real evaluation, while the Lean
lane needs a constant and a consumer.  This record wires that step:

    q <= l1UpperEnclosure2249   (the certified upper enclosure, outward)
      ----------------------------------------------------------------
      l1MarginEnclosure2249 <= -q   (the producer's signed-margin shape)

Verdict: **L1-ENCLOSURE-WIRED**.  Pin check PINNED-L1-ENCLOSURE-VERIFIED,
failures empty; builds 0 errors, 0 sorryAx, axiom trio; the full 2249
instrument re-run reproduces every certified field of the artifact bitwise
(the only three differing fields are the plain-float cross-check
diagnostics, excluded from every Lean pin).  No producer GO, no gate sign
change, no RH claim.

## The sub-ulp finding (why the constants round outward)

The exact-real shadow bound `q + E_total` is not a binary64 number.  Measured
in exact rational arithmetic against the stored artifact (ulp of the
render's binade `2^-12 = 2.44140625e-4`):

+--------------------------------------------------------+---------------+
| reading                                                | ulps          |
+--------------------------------------------------------+---------------+
| exact shadow upper (q + E) - stored render q_hi        | +0.03952598   |
| exact shadow upper - naive decimal -1675396046388.2737 | +0.11472599   |
| shipped upper -1675396046388.2736 - exact shadow upper | +0.29487401   |
| shipped lower  1675396046388.2736 vs stored margin_lo  |  0.3344       |
+--------------------------------------------------------+---------------+

The shortest-decimal transcription `-1675396046388.2737` sits `0.1147` ulp
BELOW the exact shadow upper bound, so a Lean pin at that decimal would sit
strictly inside the certified enclosure and exclude part of the artifact's
own claim (the record 2314 decimal-pin hazard, here on the margin side; the
stored binary64 relations `q + E == q_hi`, `q - E == q_lo`,
`-q_hi == margin_lo`, `-q_lo == margin_hi` all hold bitwise).  The shipped
constants therefore round outward by `1e-4` (`0.41` ulp):

* `l1MarginEnclosure2249 = 1675396046388.2736` — certified lower bound of
  `-q = |Q|`, `0.295` ulp below the exact shadow bound;
* `l1UpperEnclosure2249 = -1675396046388.2736` — certified upper enclosure
  of the signed functional, its exact negative.

Both directions are machine-checked in exact Fractions by the pin script,
and the naive decimal is a measured-rejected control in both directions.

## Theorems (namespace `ConnesWeilRH.Dev`)

+---------------------------------------------+------------------------------------+
| declaration                                 | content                            |
+---------------------------------------------+------------------------------------+
| `l1MarginEnclosure2249`                     | certified |Q| lower bound, def      |
| `l1UpperEnclosure2249`                      | signed functional upper, def       |
| `l1UpperEnclosure2249_eq_neg`               | exact negation                     |
| `l1MarginEnclosure2249_le_margin2249`       | sits 1e-4 below the 2252 render    |
| `transfer_free_charge_le_l1Enclosure_sub_slack` | the 2252 transfer-free ledger  |
|                                             | re-run at the certified constant   |
| `a005_item5_terminal_count_free_l1`         | count-free terminal shape at the   |
|                                             | certified constant                 |
| `hmargin_of_certified_l1_enclosure`         | enclosure -> signed-margin shape   |
| `a005_item5_producer_wired_owner_nodes_margin` | the composed producer           |
+---------------------------------------------+------------------------------------+

New module `ConnesWeilRH/Dev/C1RouteAL1Enclosure.lean` (8 declarations)
imports the record 2311 producer module and the record 2317 owner-nodes
module; it edits neither (both stay byte-frozen, see continuity below).  The
composed producer instantiates the record 2317 strip interface
(`frozenStripHypothesis_of_owner_nodes`), the record 2274 multiplicity
bound, the record 2310 gap split consumer, and this record's enclosure
consumer; its conclusion is the item-5 strict signed inequality
`tsum + chargeRest + gap + eps0FullTail2249 < -q` with residual hypotheses
exactly `hnode` (the record 2316 node table), `hq` (the enclosure bound),
`hcharge` (the record 2109 known-error charge), and the gap split trio.

`margin2249` is NOT routed through here: it is the historical transcription
of the render, `0.1147` ulp above the exact shadow bound; its 2252/2257
ledger arithmetic is untouched and no artifact direction is asserted of it.

## Replay evidence (the full instrument re-run)

The record 2249 instrument was re-run end to end (30 families x 4001 grid,
~190 s; the original run recorded 190.2 s).  Certified fields: **bitwise
identical** — `q`, `E_total`, `q_lo`, `q_hi`, both margin channels, the
ledger readings, all four stored relations, the owner md5s, the GL identity
flag.  Exactly **three fields of the artifact differ**, all plain-float
cross-check diagnostics:

+--------------------------------------+---------------------------------+
| field                                | before -> after (delta)         |
+--------------------------------------+---------------------------------+
| diagnostics.q_plain_2103_pipeline    | rel 1.5737871286495764e-14      |
| diagnostics.rel_lb_diff_mid          | abs 6.820900295631004e-17       |
| diagnostics.rel_lc_diff_mid          | abs 1.1442748970580396e-09      |
+--------------------------------------+---------------------------------+

These three are computed through the un-instrumented plain pipeline
(`base @ vp`, `corr @ vp` via BLAS dgemv, `np.trapezoid`); record 2249
documents `rel_lc_diff_mid ~ 1.96` as a near-cancellation artifact at the
grid midpoint (corr channel O(1e-22)), and none of the three enters any
certified quantity, join, or Lean pin.  Support measurements in the current
environment: a representative dgemv (30 x 4001) is bitwise-stable across
processes and across `OPENBLAS_NUM_THREADS` 1/8/default, so the before/after
difference is attributed to library drift since the 2026-09-29 capture
(not re-derived), not to live nondeterminism.  The freeze semantics: the
artifact bytes on disk are the original frozen ones (md5 `4fb81ff7...`);
the pin script compares them against the re-run copy and asserts
`diff ⊆ {the three volatile fields}` with the deltas above bounded.

## Lean acceptance (record 2318)

+----------------------------------+-------------------------------------+
| artifact                         | reading                             |
+----------------------------------+-------------------------------------+
| C1RouteAL1Enclosure.lean         | new module, 8 declarations          |
| C1RouteAL1EnclosureProbe.lean    | +6 #print axioms                    |
+----------------------------------+-------------------------------------+

Targeted build log `build_2318_step1.log`: `Build completed successfully
(3709 jobs)`, zero `error:` lines, zero `sorryAx`, warning-free for the two
new files.  Root aggregate log `build_2318_root.log`: `Build completed
successfully (4148 jobs)`, 0 errors, 0 `sorryAx`; the replayed probe output
carries the standard axiom trio `[propext, Classical.choice, Quot.sound]`
for all six new theorems.  Plan-count figures are reported verbatim, no
per-module census delta claimed.

Build incidents, both first-run and loud: (i) the first runner invocation
died with exit 127, `lake: command not found` — the resource runner execs
in a non-login shell, so `lake` must be addressed by its absolute elan path;
(ii) the first successful build emitted the record 2317 whitespace linter
warning (`'' starts on column N` = missing final newline) from both new
files — both now end with a trailing newline and the rebuild is
warning-free.

## Pins and checks

The pin check `scripts/routea_l1_enclosure_pin_2318.py` verifies:

+-------------------------------+------------------------------------------+
| check                         | reading                                  |
+-------------------------------+------------------------------------------+
| 2249 artifact frozen          | 4fb81ff7... recorded == live (first      |
|                               | freeze in this record), verdict fields   |
|                               | L1-DISCRETE-ENCLOSURE intact             |
| stored relations              | q+E==q_hi, q-E==q_lo, -q_hi==margin_lo,  |
|                               | -q_lo==margin_hi, all bitwise            |
| exact-Fraction readings       | the sub-ulp table above, recomputed      |
| owner cross-tie               | base d461872e... / corr c37e16a9... ==   |
|                               | record 2316 claimed; 2275 capture root   |
|                               | d83ee0ff... frozen                       |
| continuity                    | arithmetic pins b3fb88c3... (2312),      |
|                               | producer 3b15d733... (2311), owner-nodes |
|                               | 68550f52... (2317), 2317 pin artifact    |
|                               | 408bfb5a... + verdict                    |
| statement guards              | both def literals, negation, order vs    |
|                               | margin2249, ledger re-run, terminal      |
|                               | variant, consumer, producer decl +       |
|                               | hnode binder/bound, the five call        |
|                               | shapes, conclusion, no sorry, trailing   |
|                               | newline (20 booleans, all true)          |
| joins (Fractions)             | negation; l1 lower <= margin2249;        |
|                               | HST+KE+GC < lower - eps0                 |
| consumer replay               | at_bound: -upper == lower;               |
|                               | at_exact_upper: lower <= -exact_upper    |
| replay evidence               | diff vs the re-run copy is exactly the   |
|                               | three documented volatile fields         |
| controls                      | synthetic parse; naive decimal rejected  |
|                               | as unsound (both directions); one-ulp    |
|                               | q_hi mutation detected; sign-flip        |
|                               | literal fails the guard                  |
+-------------------------------+------------------------------------------+

## What this changes for the route

- The producer's `hmargin` input is now discharged by the certified
  enclosure shape: any `q <= -1675396046388.2736` feeds the signed-margin
  shape at the certified constant, with the 2252 transfer-free ledger
  re-run and machine-checked at that constant.
- Producer residual inputs after this record: `hnode` (the record 2316 node
  table, artifact grade), `hq` (this enclosure shape, artifact grade),
  `hcharge` (the record 2109 known-error charge ledger), and the gap split
  trio (window + tail pins of records 2309/2307 via 2310).  The remaining
  unwired lane is `hcharge-rest`, the non-tail charge.
- The selected-owner signed inequality remains the summit.

## Non-claims

- No numeric discharge in Lean: `hq` and `hcharge` remain hypotheses; the
  2249 enclosure is an artifact-grade first-order shadow model (convention A
  of record 2230), not Lean interval arithmetic.
- The outward-rounded constant is `1e-4` (0.41 ulp) smaller in magnitude
  than the render; this is a soundness choice, not a strengthening — the
  certified inequality holds at a constant strictly below the render.
- No producer GO, no gate sign change, no RH claim.

## Provenance and reproduction

- Lean: `ConnesWeilRH/Dev/C1RouteAL1Enclosure.lean` (new, md5
  `e08f71e2683327c138ff5e11dadf1e18`) and its probe (md5
  `f6231e022a7bbbfa7ec7e5714e6bf8f8`).
- Check: `scripts/routea_l1_enclosure_pin_2318.py` (md5
  `e1ed6172758a716986e32bf82484a2d0`) ->
  `results/2318_l1_enclosure_pin.json` (verdict
  PINNED-L1-ENCLOSURE-VERIFIED, failures empty, md5
  `debcb32521fc2993a2427357a0c8d0ac`).
- Upstream artifacts: `results/2249_l1_enclosure.json` (frozen here,
  `4fb81ff76dae5b012c49a29d18d82ea9`), `results/2316_node_values.json`,
  `results/2317_owner_nodes_lean_pin.json`,
  `results/2275_gap_owner_audit.json` (all byte-frozen by the check).
- Logs (WSL mirror): `build_2318_step1.log`, `build_2318_root.log`,
  `build_2318_pin.log`, `build_2318_l1_replay.log`; before/after replay
  copies `2249_l1_before_2318.json` / `2249_l1_after_2318.json`.

Next registered obligation: the non-tail charge lane (`hcharge-rest`, the
record 2109 known-error ledger) feeding the producer; the strip lane still
awaits only the numeric `hnode` instantiation for the captured vectors.