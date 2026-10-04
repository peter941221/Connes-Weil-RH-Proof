# Record 2567 — Replay-mechanism gate: cbv is the only surviving kernel mechanism

Verdict: GATE CLOSED, probe only. On the accepted node5440 sigma=+1/2 replay
content (30 families, paired 160-bit exponential replay), the three candidate
kernel mechanisms for closing the compactExp2547 equalities were timed in one
matched warm session under the heavy resource lease:

```text
+----------+--------+---------+---------+-----------------------------+
| Mechanism| Built  | Wall s  | User s  | Failure mode                |
+----------+--------+---------+---------+-----------------------------+
| cbv      | yes    |   30.82 |   74.97 | -                           |
| decide   | no     |   18.42 |   17.31 | 30/30 Tactic decide failed  |
| rfl      | no     |   14.98 |   16.50 | 30/30 defeq depth surrender |
+----------+--------+---------+---------+-----------------------------+
```

The cbv reading reproduces the accepted 2554 replay-phase measurement
(30.17 s wall / 72.27 s user) within 2-4 percent, which validates the probe
harness. decide and rfl fail fast (about half of cbv wall) precisely because
they surrender early: rfl's defeq check gives up before finishing the
depth-squaring rational arithmetic and reports the equalities as not
definitionally equal, and decide's kernel instance evaluation fails the same
way, leaving every theorem sorryAx-printed. Neither mechanism is usable at
this interface without changing kernel options, which the pre-registered
acceptance rule excluded.

This closes the 2a gate of the 2566 batch structure: cbv is the generation
mechanism for lanes 2b-2d, the 90-110 h sequential-wall projection stands,
and the 64-segment structure governs leases. The 2553-named alternative of a
generic proved rational factor evaluator (replacing the per-instance kernel
evaluation with a proved evaluator function) remains the only lever that can
cut the replay cost itself; designing that evaluator is a new, separate
probe with its own acceptance rule, not a modification of this gate.

## What was run

- scripts/generate_replay_probe_2567.py derives three modules from the
  accepted C1RouteAPairedN05440Plus2553 node module, keeping definitions,
  statements and imports byte-identical and varying only the tactic closing
  the 30 compactExp2547 equality goals (cbv / decide / rfl). A rename
  invariant asserts that everything outside the renamed name tokens is
  byte-identical, so no numeric literal moved (the 2553 incident rule).
- Four sequential heavy-lease invocations: the 2552 baseline module warms
  the page cache, then each variant runs lake env lean directly under
  /usr/bin/time -v (build-logs/2567_baseline.log, 2567_Cbv.log,
  2567_Decide.log, 2567_Rfl.log).
- scripts/validate_replay_probe_2567.py (--mirror, status
  REPLAY_PROBE_READBACK_PASS) encodes the pre-registered semantics: cbv must
  build with all 30 equalities on [propext, Classical.choice, Quot.sound];
  decide and rfl must fail with exactly 30 tactic-error lines each naming
  their tactic; all three modules' definition payloads are independently
  replayed through the 2553 machinery after renaming to the 2548-style edge
  names (check_node's sigma sentinel does not apply to the pruned modules);
  regeneration is byte-checked; a corrupted factor is rejected.
- results/2567_replay_probe_readback.json carries the reports, timings,
  error census, the 2554 reference reading, and source hashes.

## Explicitly not claimed

No production generator or accepted certificate changed. The probe measures
one matched session on one node's replay content; it does not reprice the
full grid, prove membership, or support any RH claim.

Evidence: scripts/generate_replay_probe_2567.py,
scripts/run_replay_probe_2567.sh (the matched-warm sequence; executed as
four direct heavy-lease invocations after the resource runner declined a
bash payload),
scripts/validate_replay_probe_2567.py,
results/2567_replay_probe_readback.json,
build-logs/2567_baseline.log, build-logs/2567_Cbv.log,
build-logs/2567_Decide.log, build-logs/2567_Rfl.log.
