Record 2662: the 190-panel true-ball batch for the (0,3) entry
Date: 2026-10-11

Result

Positive.  All 190 panels of the (0,3) entry tiling now carry a
`panelTrueBall2662P{tag}` theorem: the true panel integral of the ACTUAL
normalized integrand lies in its certified L1 ball around the panel
center constant, at the exact captured parameters.  The batch is
machine-generated from the committed record-2661 P094 pilot template
(`C1RouteAPanelTrueBall2662P094.lean`) by
`scripts/gen_2663_slots.py` + `scripts/gen_2663_panels.py`: every numeric
slot (coefficient, amplitude value/radius, phase value/radius, table
integral, residual upper, deficit) is read back from the committed Lean
literals -- no float display text enters the generator.

Panel 109 (the record-2648/2649/2655 pilot lane) uses its own committed
table module; the other 189 panels use their 2655 table modules.  The
composition module `C1RouteAPanelComposition2662.lean` ties the batch to
the assembly interface.

Build evidence (logs live on disk; `*.log` is repo-ignored)

- `results/log2662_p3.log` and `results/log2663_batch.log`: both end
  "Build completed successfully"; across the two logs 1739 axiom records,
  every one exactly `[propext, Classical.choice, Quot.sound]`, zero
  `sorryAx`, zero error lines, zero "uses sorry".
- All 190 module sources are md5-identical between the Windows tree and
  the WSL workspace that built them (0/190 mismatches; the census is
  `scripts/census_2662_mirror.sh`, whose per-file olean count is the
  acceptance test).
- The earlier failed pilot/p2 runs (`log2662_pilot*.log`, `log2662_p2.log`)
  are kept on disk as record evidence: the pilot's `sorryAx`-tainted P094
  ball and the p2 target-list defect were fixed before the green runs.

Scope

The batch supplies the per-panel hypothesis of the (0,3) partition sum
(record 2663).  It proves nothing about the partition arithmetic itself,
the edge slices, the 2597 containment, any other off-diagonal entry, or
the producer route.