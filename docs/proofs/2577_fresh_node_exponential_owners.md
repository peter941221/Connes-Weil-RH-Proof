Record 2577: fresh-node exponential owners shared across derivative orders

Verdict: NEW POINT COVERAGE at production nodes 2702 and 2703, both signs.
The generator creates the first order-zero exponential proof at each point
without importing an earlier derivative leaf for that point. The order-two
and order-three modules import that value owner and retain their own factors.
This closes the old requirement that a new shared point already have a
committed standalone 2575 leaf and a 2555 kernel owner.

Object and construction

Let x be a production-grid position, sigma be -1/2 or +1/2, and W_i(x)
be the weighted bump of family i. The owner bounds the distance from
W_i(x) to its stored rational complex center. Each derivative then uses
its own rational multiplier A_k:

  W_i^(k)(x) = A_k(i,x) * W_i(x), k = 2 or 3.

A shared value certificate proves the common input once. It does not
permit sharing A_2 and A_3. The generator compares input, center, error
and position before emitting the proof references. At exterior support
points it shares the all-orders zero theorem instead.

```text
+-------------------------------+
| fresh node value/error proof  |
| no earlier point leaf needed  |
+---------------+---------------+
                |
        +-------+-------+
        |               |
+-------v------+ +------v-------+
| own factor 2 | | own factor 3 |
| derivative 2 | | derivative 3 |
+--------------+ +--------------+
```

The first-owner module carries only position/input/center/error,
exterior zero proofs, BaseError proofs and the production-grid identity.
It contains no derivative factor or derivative-error theorem. Its active
BaseError proof checks compactExp2547 directly with decide +kernel.
Neither derivative module repeats compactExp evaluation.

The generator accepts integer grid indices from 0 through 10240.
The committed execution checks two adjacent indices, 2702 and 2703,
at both signs. This is a parameterized software entry point with four
checked instances, not a proof that every possible generated instance
has already passed Lean.

Numerical scope

The second-order signed sums use the same ideal-correction coefficient
centers and error 1e-28 as records 2575 and 2576. The bounds are:

```text
+-------+-------+---------------------+
| node  | sigma | second signed upper |
+-------+-------+---------------------+
| 2702  | -1/2  | 24.78293182         |
| 2703  | -1/2  | 24.99367675         |
| 2702  | +1/2  |  1.13205122         |
| 2703  | +1/2  |  1.14313167         |
+-------+-------+---------------------+
```

These are pointwise upper bounds on the signed second-order aggregate.
They are not cell integrals or full-grid totals. The third-order leaves
certify individual family errors; this record adds no signed third-order
aggregate, new whole-cell fourth table, or chord-cell assembly.

Independent controls

The validator restores the inherited BaseError proof and independently
replays the exact rational rounded-Horner/squaring arithmetic. It checks
the derivative factor formulas independently at orders two and three,
compares the derivative proof skeleton to the accepted renderer, checks
correction-owner signed rounding, and regenerates all outputs byte-for-byte.
Sixteen mutations alter a factor, proof owner, sign or position; all fail.

The focused build completes with 3924 jobs. All 632 requested targets
have exactly [propext, Classical.choice, Quot.sound]. The source/config
mirror closure checks 749 files. The root build completes with 4148 jobs
and all 22 record-2271 Linux integration tests pass. No 2271-bound source
was changed.

Compilation cost

Command in a configured Linux verification workspace:
  python scripts/measure_node_exp_owner_2577.py --lake LAKE_EXECUTABLE --mirror BUILD_WORKSPACE --repetitions 2

The runner uses one warm-up and two timed compiles for each source, with
alternating order. The value-owner source rechecks the full exponential
proof; derivative sources import its compiled certificate. Imported
infrastructure is warm in both cases. This includes the Lake launcher,
elaboration, tactics and kernel checking. CPU time sums child-thread work
and can exceed wall time. The JSON records warm-up, CPU and fault readings.

Machine: Intel Core Ultra 7 270K Plus, 16 logical CPUs; WSL2 Linux
6.6.87.2, x86_64; Lean 4.30.0. Wall-time means are:

```text
+------------+--------+-------------+-------------+-------------+
| node/sign  | active | value owner | order two   | order three |
+------------+--------+-------------+-------------+-------------+
| 2702-      |     28 |     9.1479s |     9.0823s |    17.6321s |
| 2703-      |     28 |     9.5285s |     9.3858s |    18.1291s |
| 2702+      |     28 |     9.1728s |     9.0659s |    17.4806s |
| 2703+      |     28 |     9.1302s |     9.1459s |    17.3435s |
+------------+--------+-------------+-------------+-------------+
```

First-value checking and order-two reuse each cost about nine seconds on
these four inputs. Record 2576's reuse-only percentage therefore cannot
stand in for complete new-node cost. The timing excludes Python generation,
signed-bound compilation, fourth tables and cell assembly; it is not a
cold end-to-end or full-grid throughput measurement.

The replacement second-chord consumer in record 2574 requires order-two
endpoints and a whole-cell fourth bound, not order-three endpoint leaves.
The order-three instances here test cross-order reuse. Production batches
should request only orders required by their named consumer.


Acceptance boundary and next work

Full-grid numerical certificates, actual exact-interpolant coefficient
membership, base-norm coverage and the RH producer remain open. This
record makes no RH claim. The next cell assembly can use the two new
endpoints, but still needs a certified whole-cell fourth upper at cell
2702 and the 2574 production-coordinate consumer.

Before scaling the batch, certify a continuous span with adjacent endpoint
sharing and measure the complete table/assembly path. The stopped 2562
constant-second construction stays stopped at the 2573 inputs.

Evidence

  scripts/generate_node_exp_owner_2577.py
  scripts/validate_node_exp_owner_2577.py
  scripts/measure_node_exp_owner_2577.py
  ConnesWeilRH/Dev/C1RouteANodeExpOwner2577Audit.lean
  results/2577_node_exp_generation.json
  results/2577_node_exp_validation.json
  results/2577_node_exp_cost.json
