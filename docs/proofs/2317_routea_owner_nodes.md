# 2317 — OWNER-NODES-WIRED: the strip consumer instantiated with the packaged owner pair; the residual strip hypothesis is the 101-node bound

Record 2313's consumer `frozenStripHypothesis_of_certified_nodes` takes two
`CompactLogTest`s, their support bounds, and node min-product bounds at the
101 grid nodes `j / 100`, `-50 <= j <= 50`.  Record 2315 packaged the
corrected width-a^2 owner as a `CompactLogTest` for arbitrary coefficient
and modulation vectors and proved its support bound; record 2316 certified
the 101 node values for the captured vectors.  This record closes the Lean
side of the owner bridge:

    baseCoefficients corrCoefficients : Fin 30 → ℂ,  modulations : Fin 30 → ℝ
      + hnode   (min(D2_b M_c, D2_c M_b) at the 101 nodes j/100, j = -50..50)
      ----------------------------------------------------------------
      FrozenStripHypothesis
        (correctedPhysicalCompactLogTest baseCoefficients modulations)
        (correctedPhysicalCompactLogTest corrCoefficients modulations)

Verdict: **OWNER-NODES-WIRED** — the support bounds are discharged by record
2315, the vectors stay free, and the only residual strip hypothesis is the
raw-owner node bound at the 101 nodes — literally the quantity certified by
the record 2316 node table.  Pin check PINNED-OWNER-NODES-VERIFIED,
failures empty; builds 0 errors 0 sorryAx, axiom trio.  No producer GO, no
gate sign change, no RH claim.

## The theorem (namespace `ConnesWeilRH.Dev`)

+---------------------------------------------+------------------------------------+
| declaration                                 | content                            |
+---------------------------------------------+------------------------------------+
| frozenStripHypothesis_of_owner_nodes        | the instantiation; residual =      |
|                                             | hnode, the 101-node raw-owner      |
|                                             | min-product bound                  |
+---------------------------------------------+------------------------------------+

New module `ConnesWeilRH/Dev/C1RouteAOwnerNodes.lean` imports the record
2315 module and the record 2313 module; it edits neither.  The proof is the
consumer plus the record 2315 facts:

* `refine frozenStripHypothesis_of_certified_nodes _ _ ?_ ?_ ?_` — the two
  support goals close by `correctedPhysicalCompactLogTest_tsupport_subset`
  (record 2315);
* the node goal rewrites the packaged tests back to the raw owner through
  `correctedPhysicalCompactLogTest_toFun baseCoefficients modulations` and
  `... corrCoefficients modulations` (explicit arguments — two
  instantiations share the goal), then closes by `exact hnode j hjlo hjhi`.

The statement keeps ONE shared modulation vector, matching the record 2275
capture shape (two coefficient vectors over the shared corrected families);
the coefficient vectors stay free because the numeric instantiation is
artifact-grade.

## Lean acceptance (record 2317)

+---------------------------------+-------------------------------------+
| artifact                        | reading                             |
+---------------------------------+-------------------------------------+
| C1RouteAOwnerNodes.lean         | new module, 1 declaration           |
| C1RouteAOwnerNodesProbe.lean    | +1 #print axioms                    |
+---------------------------------+-------------------------------------+

Targeted build log `build_2317_step1.log`: `Build completed successfully
(3708 jobs)`, zero `error:` lines, zero `sorryAx`, zero warnings from the
two new files.  Root aggregate log `build_2317_root.log`: `Build completed
successfully (4148 jobs)`, 0 errors, and the replayed probe output carries
the standard axiom trio `[propext, Classical.choice, Quot.sound]` for the
instantiation.  Plan-count figures are reported verbatim, no per-module
census delta claimed.

## Pins and checks

The pin check `scripts/routea_owner_nodes_lean_pin_2317.py` verifies:

+-------------------------------+------------------------------------------+
| check                         | reading                                  |
+-------------------------------+------------------------------------------+
| 2315 module byte-frozen       | b88ce3ef... recorded == live             |
| 2313 module byte-frozen       | 3581e512... recorded == live             |
| 2316 node artifact frozen     | 07d3f9e5... (frozen here first)          |
| 2316 verdict intact           | NODE-VALUES-CERTIFIED,                   |
|                               | all_rows_at_most_pin, pin literal match  |
| 2316 table shape              | 101 contiguous rows, sigma = j/100,      |
|                               | max 2644542.851480454 <= pin             |
| statement guards              | params, hnode binder, min shape, bound   |
|                               | constant, conclusion, consumer call,     |
|                               | both tsupport calls, both toFun          |
|                               | rewrites, the hnode close, no sorry,     |
|                               | trailing newline                         |
| probe                         | #print axioms present                    |
| controls                      | synthetic statement probe; a mutated     |
|                               | `≤ bUpper2243` constant fails the bound  |
|                               | guard; a missing final newline fails the |
|                               | newline guard                            |
+-------------------------------+------------------------------------------+

Build incidents, both first-run and loud: (i) run 1 failed with
`Unknown identifier correctedPhysical` — the owner functions live in the
record 2314 module's auxiliary namespace, so the new module carries the same
`open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit` as the record 2315 module;
(ii) the first successful build still emitted `linter.style.whitespace`
warnings `'' starts on column N` from both new files — the linter reports a
missing final newline this way; both files now end with a trailing newline
and the rebuild is warning-free.

## What this changes for the route

- The strip lane is now fully wired on the Lean side: `FrozenStripHypothesis`
  for the packed owner pair costs exactly the record 2316 node table's
  101-node bound, with everything else discharged by records 2313/2315.
- The remaining strip-lane obligations are: the numeric instantiation of
  `hnode` for the captured vectors (artifact grade — the record 2316 table,
  frozen by hash) and nothing else; then the signed margin and the non-tail
  charge feed the producer alongside the gap closure of record 2310.
- The selected-owner signed inequality remains the summit.

## Non-claims

- No numeric discharge in Lean: `hnode` remains a hypothesis; the artifact
  chain (2275 → 2303 → 2316) is its evidence at artifact grade.
- The producer theorem still takes its four residual inputs (`hstrip` now
  reachable through this instantiation, plus `hmargin`, `hcharge-rest`,
  `hgap` as recorded); no producer GO, no gate sign change, no RH claim.

## Provenance and reproduction

- Lean: `ConnesWeilRH/Dev/C1RouteAOwnerNodes.lean` (new, md5
  `68550f52601ad8b23920ec4f3813c676`) and its probe (md5
  `8e5d8e86d43eafe029ac217c65898522`).
- Check: `scripts/routea_owner_nodes_lean_pin_2317.py` (md5
  `83e2238627dd4cca937871b5590f09f4`) -> `results/2317_owner_nodes_lean_pin.json`
  (verdict PINNED-OWNER-NODES-VERIFIED, failures empty, md5
  `408bfb5a78e482f51fac6963575072b4`).
- Upstream artifacts: `results/2315_owner_test_lean_pin.json`,
  `results/2313_grid_sampling_lean_pin.json`,
  `results/2316_node_values.json` (all byte-frozen by the check).

Next registered obligation: the signed margin (`hmargin`) and the non-tail
charge (`hcharge-rest`) lanes feeding the producer; the strip lane awaits
only the numeric `hnode` instantiation for the captured vectors.