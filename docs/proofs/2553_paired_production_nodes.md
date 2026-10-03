Record 2553: complete paired derivative nodes, both signs

Eight complete 30-family node modules now certify actual order-three
derivative errors using paired 160-bit exponential replay. The nodes are
2700, 2701, 5440 and 10239 at sigma=-1/2 and +1/2. They retain the same
stored widths squared, signed modulation and support test. Interior
branches carry positive evaluation errors even when the rounded value is
zero. Exterior branches prove the function and every derivative exactly
zero. This adds node certificates, not whole-cell integral certificates.

The existing 2547/2548 generators now accept optional sigma, paired replay
and grid/order parameters. Their original defaults reproduce the accepted
files byte-for-byte. Two positive-sign nodes reproduce all 60 accepted
2548 family centers, derivative factors and errors exactly.

Reproduction

Generate with scripts/generate_paired_nodes_2553.py. In the Linux verification
environment, run scripts/run_paired_nodes_2553.sh under one heavy resource
lease, with LEAN_LAKE selecting lake if needed. It invokes lake env lean
directly for each module. Read back with
scripts/validate_paired_nodes_2553.py --mirror PATH.

The 16-logical-CPU WSL environment ran the modules sequentially in one
session. User CPU time sums work across threads. The first elapsed reading
contains cold dependency loading and is not a six-family throughput reading.

```text
+-------+-------+--------+----------+----------+-------------+
| Node  | Sigma | Active | Wall (s) | User (s) | RSS (KiB)   |
+-------+-------+--------+----------+----------+-------------+
|  2700 | +1/2  |      6 |    55.64 |    29.19 |     4759576 |
|  2700 | -1/2  |      6 |    11.57 |    29.08 |     4823896 |
|  2701 | +1/2  |     28 |    34.98 |   136.20 |     6170684 |
|  2701 | -1/2  |     28 |    35.36 |   137.90 |     6292844 |
|  5440 | +1/2  |     30 |    35.10 |   139.05 |     6231320 |
|  5440 | -1/2  |     30 |    36.33 |   149.70 |     6281476 |
| 10239 | +1/2  |      1 |     5.08 |     8.82 |     4328340 |
| 10239 | -1/2  |      1 |     4.84 |     8.67 |     4310272 |
+-------+-------+--------+----------+----------+-------------+
```

All 248 terminal declarations use exactly propext, Classical.choice and
Quot.sound. The reader checks independent exact arithmetic, actual support
branches, regeneration, dependency-source byte identity and configuration.
Eight corrupted interior factors and six corrupted exterior centers are
rejected. results/2553_paired_node_readback.json carries the readings and
source/log hashes. These focused checks do not claim a new root integration
build or a full-grid estimate.

Generation incident and correction

The first wrapper replaced a record number globally, which also changed
matching digits inside some exact rational payloads. The initial Lean run
rejected node2701Plus. The replacement now matches declaration identifiers
only, and a separate invariant checks that every numeric token remains
unchanged. Final-source independent arithmetic is checked after renaming,
not merely before it. All eight modules were regenerated and rerun.
No previously accepted proof file was changed.

Scaling decision

scripts/count_grid_work_2553.py counts the strict support inequalities
twice: once by exact integer-range endpoints and once by independent
integer enumeration. For both signs, there are 320440 active endpoint
family evaluations and 320500 active midpoint family evaluations. Sharing
the exponential between endpoint orders zero and three still leaves
640940 active exponentials. The count excludes fourth envelopes, scalar
bounds, signed sums, integral assembly and exact coefficient membership.

The full 30-family batch is feasible at the measured memory level, but
unprofiled full-grid replication is not justified. The next bounded probe
should separate exact exponential replay, derivative-factor normalization
and analytic transfer costs on the same inputs. Its decision is whether a
generic proved rational factor evaluator can remove repeated symbolic
normalization before generating hundreds of thousands of witnesses.
The current route and the remaining exact-owner/signed-budget obligations
are unchanged.
