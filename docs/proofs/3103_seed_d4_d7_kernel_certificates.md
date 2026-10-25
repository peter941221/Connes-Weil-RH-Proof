# Actual smoothSeed D4/D7 bounds from kernel-checked certificates (3098-3103)

Date: 2026-10-25.

The target is to remove the interval-enclosure hypotheses from the actual
fourth- and seventh-derivative integral bounds. This record uses a new exact
rational certificate ledger. It does not assume that the older exported rows
3040 bound the Lean derivatives, and does not prove that older row comparison.

Status: FORMAL PASS. The Linux ext4 build completed successfully with 4033
jobs. All 8192 cells, the actual integral assembly and both smoothSeed bounds
are verified. The 31 reported axiom declarations use only
`[propext, Classical.choice, Quot.sound]`, with no errors or `sorryAx`.
Evidence: `results/3103_seed_d4_d7_audit.json`.

1. Mathematical owner and conclusion

Let `T = Real.smoothTransition`, the actual transition function used by
`smoothSeed`. Let `D_n` be its derivative budget: four times the integral of
the absolute value of its nth derivative on `[0,1/2]`. The factor four is
proved to agree exactly with `derivOrderL1 n smoothSeed` for every positive
order. No replacement seed or numerical definition is used.

The final declarations in `C1SeedD4D7Certified3103.lean` state:

```lean
theorem smoothSeed_d4_d7_bounds3103 :
    derivOrderL1 4 smoothSeed < (1500 : Real) ∧
      derivOrderL1 7 smoothSeed < (2000000000 : Real)
```

This statement has no enclosure, ledger-comparison or derivative-budget
hypotheses. The separate declarations `transition_integral_four_lt3103` and
`transition_integral_seven_lt3103` state the actual half-interval integral
bounds before the seed conversion.

2. Why the finite data certify the analytic statement

An interval enclosure is a pair of rational lower and upper bounds together
with a proof that the actual value lies between them. The generator proposes
these pairs; Lean checks every arithmetic relation and proves their meaning.
It is analogous to supplying a worked calculation whose every step is checked,
rather than asking the checker to trust the calculator.

```text
Exact definition of T and derivative identities 2731-2732
                         |
                         v
3098: sound rational interval operations and exp initialization
                         |
                         v
3099: checked exp / reciprocal / product derivative recurrences
                         |
              +----------+-----------+
              |                      |
              v                      v
3101: 8192 concrete checks     3100: cell integral comparison
              |                      |
              +----------+-----------+
                         |
                         v
Exact adjacent-cell integral sum + endpoint charge 2756, once
                         |
                         v
3103: actual transition D4/D7 integral bounds
                         |
                         v
3102: reflection and the actual smoothSeed derivative masses
```

On the open interval `(0,1)`, define `P(x) = -1/x + 1/(1-x)`,
`E(x) = exp(P(x))` and `R(x) = 1/(1+E(x))`. Then `T(x) = E(x)*R(x)`.
The checker follows the already-proved derivative identities for these three
functions. Its slots contain actual derivatives, not Taylor coefficients;
the binomial factors in the product recurrences are retained.

For the exponential value, divide the phase by `2^k` until its magnitude is
at most one. The existing order-20 Taylor remainder theorem bounds its
exponential. Then check `k` successive squarings. This avoids evaluating a
huge power in one step. Rational bounds are rounded outward to multiples of
`1/2^256`; every widening is checked again in Lean. The denominator is needed
near the first cell, where reciprocal derivative factors can amplify a tiny
absolute error.

All concrete arithmetic checks use `decide +kernel` or ordinary `decide`.
There is no native evaluator axiom, floating-point sign certificate, external
numeric axiom or assumed special-function value.

3. Partition, prices and endpoint accounting

For cell index `i = 0,...,8191`, the exact endpoints are:

```text
left(i)  = (8192 + 2047*i)     / 33554432
right(i) = (8192 + 2047*(i+1)) / 33554432
width    = 2047 / 33554432

right(i) = left(i+1)
left(0) = 1/4096
left(8192) = 1/2
```

For each derivative order, the per-cell price is an integer number of units
of `1/4096`, rounded upward from four times the cell width times the
derivative interval's absolute upper bound. The checker verifies that price
inequality as well as the derivative enclosure. The total upward rounding
cost is less than two for each derivative order.

The exact generated interior totals are:

```text
+-------+----------------------------+----------------------+
| Order | Interior price             | Final target         |
+-------+----------------------------+----------------------+
| 4     | 5741418 / 4096             | 1500                 |
| 7     | 2427720724767 / 4096       | 2000000000           |
+-------+----------------------------+----------------------+
```

Record 2756 already proves the missing `[0,1/4096]` integral charge is below
`10^-1000` for both orders. The assembly conservatively reserves one unit
for that endpoint, adds it once, and checks that the interior price plus one
is strictly below the target. No neighboring-cell estimate is substituted
for the endpoint proof.

4. Verification and failure controls

Use Lean 4.30.0 and the repository's pinned Mathlib version. Generate the
finite candidates first:

```text
python3 scripts/generate_seed_certificates_3101.py --all
```

This writes 128 source modules of 64 cells each, the aggregate module, and a
generation report. That report is explicitly candidate data, not a formal
PASS. The default generator invocation separately recreates the four-cell
pilot at indices 0, 1249, 2010 and 8191.

Then run the bounded build and audit in a Linux-side workspace:

```text
python3 scripts/seed_d4_d7_audit_3103.py
```

The audit builds four certificate modules concurrently by default; the
`--batch-size` option accepts one through eight according to available
resources. The recorded eight-core run uses `--batch-size 8`. It then builds
the final theorem, paired axiom audit, and existing 3071 arithmetic and 2723
row-B consumer controls. The final analytic declarations must have exactly
`[propext, Classical.choice, Quot.sound]`. Pure computational checks may
have fewer axioms. Missing declarations, extra axioms, `sorryAx`, nonzero
exits, error lines or a missing success footer reject the result.

Four Lean negative controls check rejection of an underpriced fourth-order
charge, an underpriced seventh-order charge, a false initial exponential
enclosure of the correct list length, and an index outside the partition.
The first and last cell are included both in the pilot and the full exact
partition. Eight parser controls exercise the audit's own failure detection.

The result records canonical LF-normalized SHA-256 source hashes. Public
source provenance can therefore be compared with Git blobs independently of
workstation line endings.

5. Effect on the RH campaign

These declarations remove the actual D4/D7 seed-integral obligations. They
do not prove the old 3040 ledger comparisons; the new verified prices replace
that route to these two bounds. They do not supply every derivative order
in the original twelve-order table.

The remaining selected-owner duties are unchanged:

```text
Actual seed D4/D7 bounds
          |
          v
Rung envelope -> the three actual cardinal bounds       OPEN
          |
          v
Transfer from smoothSeed to the poweredSeed carrier     OPEN
          |
          v
Actual rho-dependent targets, zeros, caps and gate      OPEN
          |
          v
Same-owner signed positivity / contradiction -> RH     OPEN
```

Next steps are to instantiate the approved reduced-rung envelope with these
actual seed bounds, determine whether it proves the three wired cardinal
bounds at their existing constants, and then discharge the same carrier and
rho-dependent duties. A numerical envelope reading or a fixed row-B instance
does not supply those proofs.

The relevant continuation is record 2729's decay envelope and the powered-seed
bridge 2725, not the triangle derivative-mass estimate rejected in 2722B.
The three stored thresholds remain `C4 = 61000000`, `C2 = 29000000` and
`q = 26/10^17`. The finite region must cover every point, including cells
crossed by an owner-node height. The exterior estimate must cover both signs
of frequency; for correction degree 55, weight 2 and rung 7 its decay
exponent is `55 + 2 - 10*7 = -13`. These are the next obligations, not
additional conclusions of the present seed certificate.
