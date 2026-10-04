Record 2576: shared endpoint exponentials across derivative orders

Verdict: SAME NUMERICAL CERTIFICATES, LESS REPEATED COMPILATION on the four
measured endpoints. The warm fixed-input compiler comparison improves
21-28 percent. This record does not certify full-grid runtime or extend
numerical coverage beyond cell 2700 at both signs.

Mathematical object and reuse boundary

For family i at position x, let W_i(x) be its weighted exponential bump.
The order-zero certificate bounds norm(W_i(x)-center_i) by error_i.
Order two and order three multiply that SAME value by DIFFERENT factors:

  W_i''(x) = A_2(i,x)*W_i(x)
  W_i'''(x) = A_3(i,x)*W_i(x).

Primes denote derivatives with respect to x. The expensive exponential
certificate is shared; the derivative multiplier is not. Replacing A_2
by the stored A_3 would change the mathematical object and is rejected.

```text
                       +-------------------------+
                       | checked W_i value/error |
                       | SAME node, sign, owner  |
                       +------------+------------+
                                    |
                       +------------+------------+
                       |                         |
                +------v------+           +------v------+
                | factor A_2 |           | factor A_3 |
                +------+------+           +------+------+
                       |                         |
                +------v------+           +------v------+
                | W_i'' bound |           | W_i''' bound|
                +-------------+           +-------------+
```

The generator compares position, input, center and error against the
committed 2575 order-two point and 2555 order-three owner before emitting
any reuse. It keeps the accepted order-two factor and derivative proof,
then proves the new BaseError by referring to the existing kernel-node
BaseError theorem. There is no new compactExp replay in the derivative
modules. These are ordinary imported proof references, not new axioms or
stored conclusions used as unproved inputs.

Four node/sign pairs give 120 BaseError references, of which 68 are
support-interior exponential certificates and 52 are exterior zero cases.
The four derivative source files shrink from 491976 to 365639 bytes
(25.68 percent). This is not a claim about total repository size.

Proof and numerical invariants

The signed-bound modules preserve the 2575 arithmetic and correction
owner. The coefficient error remains 1e-28. The whole-cell fourth sum,
production-grid summand and conditional integral bounds are unchanged:

  minus second-integral cell upper = 0.031337156561715526
  plus  second-integral cell upper = 0.0014287074027819074.

The shared assembly rechecks the same cell proof with new endpoint names.
All 274 requested axiom audits are exactly
[propext, Classical.choice, Quot.sound]. The validator independently
replays the old order-two and inherited order-three arithmetic, verifies
same-value ownership and signed rounding, compares the derivative proof
skeletons, rejects twelve wrong-factor/owner/sign cases, and regenerates
all ten modules and the generation JSON byte-for-byte. The source/config
mirror closure contains 758 files.

Same-run compiler comparison

Command in a configured Linux verification workspace:
  python scripts/validate_shared_second_chord_2576.py --log BUILD_LOG --mirror BUILD_WORKSPACE --lake LAKE_EXECUTABLE --repetitions 2

BUILD_LOG is the successful focused audit build. BUILD_WORKSPACE contains
the matching source/config and warm compiled dependencies. LAKE_EXECUTABLE
is its Lake executable. The repetitions parameter requests two timed
compilations per variant after one warm-up compilation of EACH case.

Machine: Intel Core Ultra 7 270K Plus, 16 logical CPUs; WSL2 Linux
6.6.87.2, x86_64; Lean 4.30.0. Each measurement invokes lake env lean on
a fixed source file. Axiom-print directives are removed from BOTH
variants; the mathematical declarations remain intact. Alternating the
old/new order reduces ordering bias. The measurements include the Lake
launcher, elaboration, tactics and kernel checking, not pure kernel time.
CPU time and page-fault counts accompany the wall-clock samples in JSON.

```text
+------------+-----------------+----------+----------+---------+
| benchmark  | shape           | before   | after    | delta   |
+------------+-----------------+----------+----------+---------+
| compile    | 2700-, 6 active  |  4.7470s |  3.6978s | -22.10% |
| compile    | 2701-, 28 active | 12.7928s |  9.2438s | -27.74% |
| compile    | 2700+, 6 active  |  4.7214s |  3.7290s | -21.02% |
| compile    | 2701+, 28 active | 12.4328s |  9.1905s | -26.08% |
+------------+-----------------+----------+----------+---------+
```

The sum of the four case means changes from 34.6940s to 25.8611s
(-25.46 percent). These are repeated fixed-input compiles, not newly
certified grid nodes or a full-grid throughput measurement. There are
only two measured repetitions per case, and the imported exponential
certificates are already compiled; their initial construction is outside
this comparison.

Initial instrument reading retained

The initial run had no explicit per-case warm-up. Its first standalone
minus-node-2700 sample was 53.6718s versus 5.0016s on the second identical
input. That isolated wall-time anomaly does not justify an algorithmic
speedup claim. The complete initial timing samples remain in
results/2576_shared_exp_timing_initial.json. Its cause was not measured;
the controlled rerun adds warm-up and CPU/page-fault readings rather than
inventing an explanation or silently dropping the initial data.

Acceptance and remaining work

The focused build succeeds (3933 jobs), the root build succeeds
(4148 jobs), and all 22 record-2271 Linux integration tests pass. No
2271-bound source was edited. Exact coefficient membership, full-grid
numeric tables, base-norm coverage, producer GO and RH remain open.

The next batch needs an arbitrary-node order-zero owner interface and a
continuous-span cost/control run. New nodes still need their first
exponential certificate; reuse only eliminates repeated certification
across derivative orders at the SAME owner. This four-point measurement
cannot be scaled into a whole-grid cost promise.

Evidence

  scripts/generate_shared_second_chord_2576.py
  scripts/validate_shared_second_chord_2576.py
  ConnesWeilRH/Dev/C1RouteACorrectionSecondChordSharedCell2700_2576.lean
  ConnesWeilRH/Dev/C1RouteACorrectionSecondChordSharedCell2700_2576Audit.lean
  results/2576_shared_exp_generation.json
  results/2576_shared_exp_validation.json
  results/2576_shared_exp_timing_initial.json
