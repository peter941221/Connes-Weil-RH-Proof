Record 2552: matched cost of paired production-state replay

Four actual third-derivative family evaluations at sigma=+1/2 pass both
the existing separate center/radius replay and a paired state replay.
The cases are families 1 and 15 at grid nodes 2701 and 5440. The paired
equality evaluates the rational state once, then projects its center and
radius. Both variants retain the actual weighted-function identity and
third-derivative error transfer. This is a cost probe, not additional
whole-cell coverage.

Reproduction uses generate_batch_cost_2552.py, followed by
run_batch_cost_2552.sh inside one heavy resource-runner lease in the Linux
verification environment. LEAN_LAKE may select the installed lake command.
Each measurement runs lake env lean directly, so a cached target build
cannot skip the concrete proofs. validate_batch_cost_2552.py --mirror PATH
checks the completed logs and exact dependency-source identity.

The matched sequence runs in one WSL session on the 16-logical-CPU
environment. Times include imports and proof elaboration. User CPU time
adds work across threads and can exceed elapsed time.

```text
+------------------+----------+------------+-------------+
| Run              | Wall (s) | User (s)   | RSS (KiB)   |
+------------------+----------+------------+-------------+
| Initial imports  |    51.84 |       1.59 |     3966192 |
| Paired state     |     7.44 |      17.87 |     4639420 |
| Separate fields  |    11.07 |      25.69 |     4754416 |
| Warm imports     |     1.50 |       1.06 |     4004392 |
+------------------+----------+------------+-------------+
```

Paired replay reduces elapsed time by 32.8% and user CPU time by 30.4%
in this run. It is the preferred candidate for the next batch. These are
single matched readings, not a statistical speedup guarantee. The initial
import reading must not be subtracted from warm proof runs. Earlier pilot
invocations had inconsistent page-cache conditions (paired 7.97 s versus
separate 55.87 s); that apparent ratio is not an algorithm speedup.

Acceptance checks all 16 terminal declarations for exactly propext,
Classical.choice and Quot.sound, 196 byte-identical project dependency
sources, and matching build configuration. Independent rational replay
checks every payload; the two node2701 cases in each variant also match
the accepted 2548 inputs, centers, factors and errors exactly. Eight
zeroed-error corruptions are rejected. Evidence is stored in
results/2552_batch_cost_readback.json.

The next scaling gate is a complete 30-family batch with both signs and
actual exterior branches, followed by multi-node scaling. Four interior
family evaluations cannot establish the best batch size, all-grid cost,
whole-cell summation cost or exact coefficient membership. No production
generator or accepted 2551 certificate is changed by this probe.
