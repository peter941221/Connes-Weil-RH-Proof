# 2727 — the D-ladder brick collapses to ONE order: rungs {1,2,3,4} suffice and D_4 has +0.29% slack

Verdict: the record-2726 campaign's residual numeric obligation
`{l1Mass smoothSeed <= 3, D-table pins k = 1..12}` is RE-SCOPED by
measurement to `{l1Mass smoothSeed <= 3, D_4 pin}` — orders 5..12 are
inert for all three wired pins, and the order-4 pin only needs accuracy
within `+0.29%` of the 2720 table value (true value 1266.2243 against
table 1535.1255: the table already carries 21% slack).

## 0. What was measured, and the decision it settles

Consumer: the three wired cardinal pins of the stored row-B
contradiction, consumed through the record-2725 envelope theorem
`norm_cardinalSum_poweredSeed_le_endpoint_env`, whose numeric premises
are `l1Mass smoothSeed <= l1u` (l1u = 3), `rungs.Nonempty`,
`derivOrderL1 k smoothSeed <= D k` for `k in rungs`, and `0 <= D k`.
The decision: WHICH rungs are load-bearing, and how tight the remaining
pin must be.  Both are answered on the frozen 2720 engine with a same-run
full-table bitwise control against the committed artifact.

## 1. Rung-set restriction sweep (`results/2727_rungs_restriction_probe.json`)

Method: re-run `p3.scan_channel` / `p3.q_star_at` with every rung
`k > cut` set to `+inf` (min-inert), i.e. effectively restricted to
`{1..cut}`.  Restriction can only INCREASE the envelope, so a clearing at
a small cut is the strongest reading.  Full-table control: C4*/C2*/q*
reproduce `results/2720_p3_certified_strip_constants.json` bitwise.

```text
+-------------+----------------+----------------------+----------------+
| rungs       | C4*/pin        | C2*/pin              | q/pin          |
+-------------+----------------+----------------------+----------------+
| {1,2,3}     | 0.992202 clear | 1.0379e11  FAIL      | 4.578  FAIL    |
| {1,2,3,4}   | 0.992202 clear | 0.971081  clear      | 0.971083 clear |
| {1..5}      | identical to {1,2,3,4} on all three channels        |
| ...         | (cut 5..12 all bitwise-identical readings)           |
| {1..12}     | identical to {1,2,3,4} on all three channels        |
+-------------+----------------+----------------------+----------------+
```

So the k = 4 rung is exactly the switch that clears C2 and q; every
higher rung is inert for the three pins.  Reading: the committed
certified constants C4*/C2*/q* were driven by rungs <= 4 all along.

## 2. True ladder values and the D_4 margin (`results/2727_d4_margin.json`)

Diagnostic estimates of `derivOrderL1 k smoothSeed = 4 int_0^{1/2} |T^(k)|` by mpmath
quadrature (diagnostic grade, dps 60; orders 1, 2 reproduce the Lean
exact integers 2, 8; order 3 reproduces the Lean bracket
[78.7283384, 78.7283385] to relative 1.5e-7):

```text
+----+------------------+------------------+--------------+
| k  | estimate         | D_table          | D/true       |
+----+------------------+------------------+--------------+
| 1  | 2                | 2.004632473      | 1.00232      |
| 2  | 8                | 8.125733214      | 1.01572      |
| 3  | 78.728326885     | 83.411957294     | 1.05949      |
| 4  | 1266.224319      | 1535.125524      | 1.21237      |
| 5  | 34570.392831     | 60789.264056     | 1.75842      |
| 6  | 1377565.448535   | 5610215.472695   | 4.07256      |
+----+------------------+------------------+--------------+
```

Slack scan at rungs {1,2,3,4} with `D_4 := 1535.125524 * (1 + eps)`
(C4 and C2 are bitwise insensitive in the scanned range; q is the binding
channel):

```text
eps = 0.0000 .. 0.0029 : all three pins clear (q/pin 0.971083 -> 0.999615)
eps = 0.0030           : q/pin 1.000612 FAIL
eps = 0.0040           : q/pin 1.010633 FAIL
```

Bracket: the wired q pin tolerates `D_4 <= 1535.125524 * (1 + ~0.00295)`
= `~1539.66`.  This is conservative: the scan kept the table values for
D_1..D_3 (2.0046, 8.1257, 83.412), while the Lean-proved values are
TIGHTER (2, 8, 78.7283385), which only shrinks the envelope and widens the
tolerance.

## 3. Re-scoped residual (the record-2726 campaign card, amended)

```text
was : {l1Mass smoothSeed <= 3, D-table pins k = 1..12}
now : {l1Mass smoothSeed <= 3 (LANDED, record 2728), D_4 pin}
      D_4 proof target: any C_4 with 1266.2243 <= C_4 <= ~1539.66;
      i.e. a coarse upper bound is sufficient, but it still requires a
      kernel-checked proof.
```

Orders 1 (exact 2, `derivativeL1_smoothSeed_eq_two`), 2 (exact 8,
`derivOrderL1_smoothSeed_two`) and 3 (bracket
`derivOrderL1_smoothSeed_three_mem_Icc`) are already Lean-proved and
TIGHTER than the table, so with `C_4` proved the rung set
`{1,2,3,4}` is fully formal.

## 4. Instrument laws

- Tuple-order control law: `p3.scan_channel` returns
  `(unweighted_sup, weighted_sup)`; the first probe run mis-assigned the
  unweighted value to C4* and the pre-verdict same-run control caught it
  (CONTROL-FAIL, no verdict licensed; the mis-assigned value 1.8106e7 was
  exactly the artifact's `base_sup_unweighted`, confirming the diagnosis).
  This is the 2053 control-fail doctrine working as designed.
- Failure propagation: the resumed checker now returns `PROBE-FAIL` and
  a nonzero process exit on any failed post-control guard. Both branches
  were exercised with an injected failure before rerunning the probe.
- Diagnostic-gate law: a quadrature-grade reference comparison must be
  gated at its own error floor, not at the bracket's width: the first
  order-3 guard (absolute 1e-5) failed on a relative 1.5e-7 agreement;
  the fixed gate is relative 1e-5 with 66x headroom (nth instance of the
  gate-at-the-design's-own-floor law).

## 5. Non-claims

The reduced rung set is measured to suffice; no theorem yet certifies the
finite cell maxima, their domain coverage, or the infinite-frequency tail
at the wired constants. Those envelope-to-pin duties remain after D_4.

Engine-grade measurement on the frozen 2720 engine (stored row B,
same-run bitwise control).  The true values are quadrature-grade
diagnostics.  The wired pins remain named hypotheses; the D_4 Lean pin is
a NEW obligation created by this record's re-scope (previously it was one
of twelve).  No producer GO, no SourceRH, no RH claim; the map-103
reopen (record 2726) stands and the DEAD pattern rows are untouched.

Evidence:
- `scripts/rungs_restriction_probe_2727.py`,
  `results/2727_rungs_restriction_probe.json` (5/5 checks, verdict
  `RUNGS-RESTRICTED-CLEAR-AT-4`),
- `scripts/d4_margin_probe_2727.py`, `results/2727_d4_margin.json`
  (8/8 checks, verdict `D4-SLACK-BRACKET-[0.0029, 0.003]`),
- `results/2720_p3_certified_strip_constants.json`,
- `docs/proofs/2725_powered_seed_envelope.md`.

## 6. Next bounded mathematical target

Owner: the exact `smoothSeed` from `C1ExplicitSmoothSeed`, not a sampled
profile or a substituted seed. Premise: `derivOrderL1 4 smoothSeed <=
1535` (a rational target below the 2720 table value). Consumer: the
2725 poweredSeed envelope at rungs {1,2,3,4}. The diagnostic estimate
1266.224319 merely suggests room; it is not a lower or upper certificate.

Recommended derivation: use `derivOrderL1_smoothSeed_eq` to reduce to
`2 * integral_0^1 |T''''|`. On a finite partition, bound the total
variation of `T'''` (how much its value rises and falls), with endpoint
regions treated analytically. This retains derivative cancellation
inside each monotone piece instead of taking a global supremum.
Existing third-order comparison/certificate modules provide rational
exponential bounds, but do NOT prove the fourth-order sign partition.

Completion: a compiled theorem with this exact owner and no additional
analytic assumptions, plus the standard-trio audit. Initial derivation
budget: one session, <= 30 minutes, <= 4 GiB additional build storage;
no bulk certificate generation. Stop if the analytic bound exceeds
1535 or the sign/endpoint proof has no finite justified partition.
Then preserve the scoped gap rather than enlarging the campaign.
