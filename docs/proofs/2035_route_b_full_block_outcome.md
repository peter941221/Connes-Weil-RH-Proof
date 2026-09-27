# Record 2035 - Route-B full block assault: P4 / P4b / P5 / P6 outcome

Date: 2026-09-27.

Status: OUTCOME OF FOUR NUMERIC PROBES. No theorem, no interval certificate for
the gate moments, no complete-owner statement, no RH claim. Every reading is an
UNDERAPPROXIMATION reading on the record-1980 owner, or an interval statement
about one explicit one-dimensional function (P6 only).

Outcome of the "full assault" batch registered in
[2032](2032_full_block_assault_preregistration.md),
[2033](2033_gate_tail_pairing_preregistration.md) and
[2034](2034_support_radius_robustness_preregistration.md).

```text
phase   probe                                script / artifact
P4      gate-row search over the family       scripts/fourpoint_gate_row_search_2032.py
                                              results/2032_gate_row_search.json
P4c     support-radius robustness of the rows scripts/fourpoint_support_radius_robustness_2034.py
                                              results/2034_support_radius_robustness.json
P4b     gate/tail pairing                     scripts/fourpoint_gate_tail_pairing_2033.py
                                              results/2033_gate_tail_pairing.json
P5      non-vertex lambda screen              same artifact, lambda_screen / lambda_joint_rows
P6      interval bracket for the k = 3 mass   scripts/fourpoint_interval_mass_2033.py
                                              results/2033_interval_mass_w3.json
```

## 1. Bottom line

Mixed, and the split is clean and actionable.

```text
1.  GOOD, and it unblocks a premise.  P4 finds 9 admissible n >= 1 rows with
    the registered gate pattern C > 0, b > 0, det < 0 (gamma_2 at n = 2;
    gamma_3 at n = 2 and n = 3; all three owner cardinalities N = 3, 4, 5),
    plus the n = 0 control at all nine (gamma, N) pairs.  Record 2029 section 7
    reopen condition 1 ("a changed named hypothesis at an admissible n >= 1")
    is therefore satisfied: R-B3 is no longer blocked by the absence of a row.

2.  BAD, and it is the real wall.  On EVERY one of those 9 rows the tail half
    FAILS AT THE lambda -> infinity LIMIT: tau_inf = A0 * q^(2n) is 2.1e10 at
    the gamma_2 rows and 7.4e12 .. 9.7e12 at the gamma_3 rows.  No span
    coefficient can close the tail budget there, because the vertex factor
    (1 + H^4/lambda)^2 is >= 1 and the pure decay is already above 1.
    The tail does close at n = 4 (tau_inf = 2.9e-7 .. 1.0e-4, and tau < 1 at
    the measured vertex lambda for gamma_1 and gamma_2), but at n = 4 the gate
    signs are gone at every measured height.  The gate pattern and a closable
    tail are DISJOINT on this family: PAIR-MISMATCH, paired_rows = [].

3.  BAD for the row's stability.  P4c: only 1 of 15 rows keeps the pattern when
    the support radius is moved by +1 and +2 (RADIUS-FRAGILE).  The rows are
    conditional on the exact visible-prime set, so R-B4 (coverage / R-B0) is a
    prerequisite before ROW-FOUND may be used for routing.

4.  GOOD for R-B1, and now certified.  P6 produces a genuine interval bracket
    for W_3 and recomputes the record-2031 strip bound with the bracket's UPPER
    end: 3.001847e-07 against q = 2^-14 = 6.103515625e-05, margin 203.33x, on
    the full registered 101 x 345 grid.  The bracket contains all four
    record-2031 reference values, at relative width <= 5.0e-03.  MASS-BRACKETED.

5.  The answer to "which block kills Route B on this family" is R-B3, and it is
    killed by an index-scale mismatch, NOT by an unattainable accuracy and NOT
    by the prime book: the derived closure index is n_min = 3 at gamma_1 and
    n_min = 4 at gamma_2/gamma_3, with prime books 2532 and 15040, both inside
    the rig's certified cap 60000.  The wall is that the gate row lives at
    n = 2, 3 and the tail closes at n >= 3, 4 respectively.
```

## 2. P4 - the gate rows

Family: `rho = 0.55 + i*gamma`, `gamma in {14.134725141734693, 21.022039638771556,
30.424876125859513}`, `N in {3,4,5}`, `n in 0..4`, primary `dxi = 0.02` with a
`dxi = 0.01` refinement, support radius `s_n = 2(n+2)`, prime book
`{k prime power : k <= exp(s_n)}` = 24 / 98 / 465 / 2532 / 15040.

45 rows measured; 9 carry the pattern at `n >= 1`; `n = 0` is the control at all
nine `(gamma, N)` pairs. No row at `n = 1` and no row at `n >= 4` carries it.
`|dC|` is the `dxi = 0.02` against `dxi = 0.01` difference of `C`; every row is
sign-stable.

T1 gate rows at n >= 1 (values at dxi = 0.02)

```text
+-----------+---+---+--------------+--------------+--------------+----------------+
| gamma     | N | n | C            | b            | det          | |dC| 0.02/0.01 |
+-----------+---+---+--------------+--------------+--------------+----------------+
| 21.022040 | 3 | 2 | +1.65478e+04 | +4.05740e+07 | -4.68143e+14 | 8.1e-14        |
| 21.022040 | 4 | 2 | +1.72173e+04 | +4.30097e+07 | -4.71851e+14 | 8.2e-14        |
| 21.022040 | 5 | 2 | +1.83009e+04 | +4.65262e+07 | -4.92003e+14 | 8.6e-14        |
| 30.424876 | 3 | 2 | +1.49209e+04 | +7.62937e+07 | -1.24184e+15 | 5.4e-14        |
| 30.424876 | 3 | 3 | +2.75052e+04 | +2.55069e+08 | -1.59724e+16 | 3.3e-10        |
| 30.424876 | 4 | 2 | +1.59191e+04 | +8.01619e+07 | -1.43342e+15 | 6.0e-14        |
| 30.424876 | 4 | 3 | +3.01545e+04 | +2.85399e+08 | -2.01055e+16 | 3.1e-10        |
| 30.424876 | 5 | 2 | +1.70144e+04 | +8.43522e+07 | -1.66934e+15 | 5.8e-14        |
| 30.424876 | 5 | 3 | +3.32675e+04 | +3.18278e+08 | -2.49244e+16 | 2.9e-10        |
+-----------+---+---+--------------+--------------+--------------+----------------+
```

Anchor: at `dxi = 0.02` the anchor block reproduces record 2028's committed
`C` bit-exactly (`anchor_max_dev_C = 0.0`), and at `dxi = 0.01` to
`2.686151e-07` absolute on `C` values of order `1e4`.

Reading of the pattern: it is an `n`-parity/phase phenomenon at two heights, not
a monotone-in-height effect. `gamma_1` (14.135) has it only at `n = 0`;
`gamma_2` (21.022) at `n = 0, 2`; `gamma_3` (30.425) at `n = 0, 2, 3`.

The registered cutoff block fired `CUTOFF-SENSITIVE` on the record-1980 owner:
raising the prime cut from `exp(s_n)` to `exp(s_n + 1)` and `exp(s_n + 2)` flips
the sign of `C` at every `n`. The registered consequence of that block ("an
erratum against the prime book") is NOT what the block can support, and this
record corrects it: the prime book `{k prime power : k <= exp(s_n)}` is a
CONSTRUCTION input fixed by the support radius `s_n = 2(n+2)`, not a measured
quantity, so the block measures the SENSITIVITY of the gate-entry signs to that
input. The real consequence is that R-B0/R-B4 must pin the visible-prime source,
and P4c below does exactly that.

## 3. P4c - support-radius robustness

The 15 rows `(gamma_2, N in {3,4,5}, n = 2)`, `(gamma_3, N in {3,4,5}, n = 2, 3)`
and the `n = 0` control, re-read at support radius `2(n+2) + delta`,
`delta in {-1, +1, +2}`, `dxi = 0.02`. `delta = -1` truncates the book BELOW the
construction's own support radius, so it is inadmissible by construction and is
recorded as a sensitivity direction only.

T3 gate_signs per delta

```text
+--------+---+---+------+-------+-------+-------+----------------+
| gamma  | N | n | d=+0 | d=-1  | d=+1  | d=+2  | moved at +1/+2 |
+--------+---+---+------+-------+-------+-------+----------------+
| 21.022 | 3 | 0 | True | True  | False | False | [1, 2]         |
| 21.022 | 3 | 2 | True | False | True  | False | [2]            |
| 21.022 | 4 | 0 | True | True  | False | False | [1, 2]         |
| 21.022 | 4 | 2 | True | False | True  | False | [2]            |
| 21.022 | 5 | 0 | True | True  | False | False | [1, 2]         |
| 21.022 | 5 | 2 | True | False | True  | True  | []             |
| 30.425 | 3 | 0 | True | True  | False | False | [1, 2]         |
| 30.425 | 3 | 2 | True | False | False | True  | [1]            |
| 30.425 | 3 | 3 | True | False | True  | False | [2]            |
| 30.425 | 4 | 0 | True | True  | False | False | [1, 2]         |
| 30.425 | 4 | 2 | True | False | False | True  | [1]            |
| 30.425 | 4 | 3 | True | False | True  | False | [2]            |
| 30.425 | 5 | 0 | True | True  | False | False | [1, 2]         |
| 30.425 | 5 | 2 | True | False | False | True  | [1]            |
| 30.425 | 5 | 3 | True | False | True  | False | [2]            |
+--------+---+---+------+-------+-------+-------+----------------+
```

Status `RADIUS-FRAGILE`: exactly one row, `(gamma_2, N = 5, n = 2)`, keeps the
pattern at `delta = +1` and `+2`; the other eight found rows lose it at one of
them. No FOUND row is stable in the `delta = -1` direction: 9 of the 15 rows
flip there, and the 6 that keep the pattern are exactly the `n = 0` controls.
That is consistent with the admissibility note.

Consequence: the found rows are conditional on the exact support radius. Under
the route ledger this makes R-B0 (complete owner and exact visible-prime source)
and R-B4 (coverage) prerequisites of any use of ROW-FOUND for routing. It does
not by itself kill the rows: `exp(s_n)` is what the construction says, and the
sensitivity is a statement about the input, not an error.

## 4. P4b - gate/tail pairing: the wall

Per `(gamma, N, n)`, with `H = 3 + |rho|` and the record-2028/1981 decay block
(heights 0..200 on 401 points, `sigma in {0, 1/2, 1}`):

```text
A0    = H^4 * (2 pi)^12 * (C4 * C2)^2      (C4 base fourth order, C2 correction
                                            second order, as in record 2028)
tau   = A0 * q^(2n) * (1 + H^4/|lambda_n|)^2      q = 2^-14
tau_inf = A0 * q^(2n)                             lambda -> infinity limit
```

`tau < 1` is the registered tail half in the rig's units. `tau_inf < 1` is
necessary for `tau < 1` to be reachable by ANY span coefficient, so it is the
scale-free part of the reading.

Anchor: the `q = 1/2` control reproduces record 2028's tail proxies to
`2.22e-16` (`anchor_2028_max_dev`). The record-1981 anchor deviates by
`0.808`, which is expected: record 1981's `lambda_n` are the withdrawn
`dxi = 0.05` rows (record 2029 erratum) and must not be re-read.

Owner scope of this phase (the script's registered list): the reference owner
`(gamma_1, N = 4)` plus every `(gamma, N)` that carries a gate row at `n >= 1`,
i.e. 7 owners. `gamma_1` carries a gate pattern only at `n = 0`, and its
`N = 3, N = 5` rows add nothing to the pairing question, so they are outside
the registered list; the P4 family itself is the full nine `(gamma, N)` pairs.

T2 pairing, n = 2, 3, 4 (the 7 registered owners)

```text
+--------+---+---+-------+-----------+-----------+-----------+------------+--------+
| gamma  | N | n | gate  | tau_q     | lambda    | tau_inf   | lambda_min | closed |
+--------+---+---+-------+-----------+-----------+-----------+------------+--------+
| 14.135 | 4 | 2 | False | 2.049e+11 | 1.367e+03 | 4.968e+07 | -          | False  |
| 14.135 | 4 | 3 | False | 3.164e+02 | 2.142e+03 | 1.851e-01 | 6.525e+04  | False  |
| 14.135 | 4 | 4 | False | 4.938e-07 | 3.354e+03 | 6.895e-10 | 2.269e+00  | True   |
| 21.022 | 3 | 2 | True  | 3.968e+14 | 2.452e+03 | 2.115e+10 | -          | False  |
| 21.022 | 3 | 3 | False | 3.359e+05 | 5.185e+03 | 7.878e+01 | -          | False  |
| 21.022 | 3 | 4 | False | 1.742e-03 | 4.385e+03 | 2.935e-07 | 1.807e+02  | True   |
| 21.022 | 4 | 2 | True  | 4.110e+14 | 2.498e+03 | 2.273e+10 | -          | False  |
| 21.022 | 4 | 3 | False | 5.641e+05 | 4.135e+03 | 8.467e+01 | -          | False  |
| 21.022 | 4 | 4 | False | 1.902e-03 | 4.349e+03 | 3.154e-07 | 1.874e+02  | True   |
| 21.022 | 5 | 2 | True  | 4.366e+14 | 2.542e+03 | 2.500e+10 | -          | False  |
| 21.022 | 5 | 3 | False | 1.896e+06 | 2.353e+03 | 9.315e+01 | -          | False  |
| 21.022 | 5 | 4 | False | 2.165e-03 | 4.275e+03 | 3.470e-07 | 1.965e+02  | True   |
| 30.425 | 3 | 2 | True  | 4.479e+17 | 5.113e+03 | 7.447e+12 | -          | False  |
| 30.425 | 3 | 3 | True  | 5.107e+08 | 9.273e+03 | 2.774e+04 | -          | False  |
| 30.425 | 3 | 4 | False | 3.629e+00 | 6.701e+03 | 1.034e-04 | 1.283e+04  | False  |
| 30.425 | 4 | 2 | True  | 5.278e+17 | 5.036e+03 | 8.511e+12 | -          | False  |
| 30.425 | 4 | 3 | True  | 5.605e+08 | 9.465e+03 | 3.171e+04 | -          | False  |
| 30.425 | 4 | 4 | False | 4.501e+00 | 6.431e+03 | 1.181e-04 | 1.372e+04  | False  |
| 30.425 | 5 | 2 | True  | 6.185e+17 | 4.958e+03 | 9.668e+12 | -          | False  |
| 30.425 | 5 | 3 | True  | 6.232e+08 | 9.567e+03 | 3.602e+04 | -          | False  |
| 30.425 | 5 | 4 | False | 5.480e+00 | 6.211e+03 | 1.342e-04 | 1.464e+04  | False  |
+--------+---+---+-------+-----------+-----------+-----------+------------+--------+
```

`lambda_min` is the smallest `|lambda|` making `tau < 1`; `-` means no such
lambda exists (`tau_inf >= 1`). `closed` is `tau_q < 1` at the MEASURED vertex
`lambda_n = b_n/C_n`.

Read the three bands:

```text
n = 2 rows (gamma_2 and gamma_3, 6 rows)   GATE yes, tau_inf = 2.1e10 .. 9.7e12
                                           -> tail UNREACHABLE at any lambda
n = 3 rows (gamma_3, 3 rows)               GATE yes, tau_inf = 2.8e4 .. 3.6e4
                                           -> tail UNREACHABLE at any lambda
n = 3 row (gamma_1, 1 row)                 gate no,  tau_inf = 0.185
                                           -> tail reachable at lambda >= 6.5e4,
                                              gate already lost at n = 1
n = 4 rows (all 9)                         gate no,  tau_inf = 2.9e-7 .. 1.3e-4
                                           -> tail closed at gamma_1/gamma_2,
                                              gate already lost
```

The last band is the sharpest statement of the mismatch: the tail budget is
drawn down by the factor `q^2 = 2^-28 = 3.7e-9` per unit of `n`, so the budget
crosses 1 exactly one step AFTER the gate pattern dies.

The price of forcing the pair at the gate rows, in `q` units (`q` needed so that
`tau_inf < 1`, i.e. the fourth root of `1/A0` at `n = 2`):

T5 q required for tau_inf < 1

```text
+--------+---+---+------------+------------+--------+-----------+
| gamma  | N | n | A0         | q needed   | log2 q | (2^-14)/q |
+--------+---+---+------------+------------+--------+-----------+
| 14.135 | 4 | 2 | 3.5799e+24 | 7.2700e-07 | -20.39 | 83.96     |
| 14.135 | 4 | 3 | 3.5799e+24 | 8.0852e-05 | -13.59 | 0.7549    |
| 21.022 | 3 | 2 | 1.5239e+27 | 1.6005e-07 | -22.57 | 381.3     |
| 21.022 | 3 | 3 | 1.5239e+27 | 2.9479e-05 | -15.05 | 2.07      |
| 21.022 | 4 | 2 | 1.6378e+27 | 1.5719e-07 | -22.60 | 388.3     |
| 21.022 | 4 | 3 | 1.6378e+27 | 2.9126e-05 | -15.07 | 2.096     |
| 21.022 | 5 | 2 | 1.8017e+27 | 1.5349e-07 | -22.64 | 397.7     |
| 21.022 | 5 | 3 | 1.8017e+27 | 2.8667e-05 | -15.09 | 2.129     |
| 30.425 | 3 | 2 | 5.3662e+29 | 3.6947e-08 | -24.69 | 1652      |
| 30.425 | 3 | 3 | 5.3662e+29 | 1.1093e-05 | -16.46 | 5.502     |
| 30.425 | 4 | 2 | 6.1328e+29 | 3.5734e-08 | -24.74 | 1708      |
| 30.425 | 4 | 3 | 6.1328e+29 | 1.0849e-05 | -16.49 | 5.626     |
| 30.425 | 5 | 2 | 6.9667e+29 | 3.4613e-08 | -24.78 | 1763      |
| 30.425 | 5 | 3 | 6.9667e+29 | 1.0621e-05 | -16.52 | 5.747     |
+--------+---+---+------------+------------+--------+-----------+
```

At the `n = 2` gate rows the contraction factor itself would have to drop by
381x (gamma_2) to 1763x (gamma_3) relative to the priced `2^-14`; R-B1's own
strip bound would then have to shrink by the same factor, and record 2031 shows
`k = 3` is the UNIQUE surviving integration order with a 203x margin. At the
`gamma_3 n = 3` gate rows the gap is smaller but still adverse (5.5x to 5.7x).

Closure index (exact arithmetic on the committed `A0`, no new measurement):

```text
n_min = ceil( log(A0) / (2 log(1/q)) ),  log(1/q) = 14 log 2
      = 3 at gamma_1 / N = 4        prime book at n = 3 -> 2532
      = 4 at gamma_2 and gamma_3    prime book at n = 4 -> 15040
```

Both are inside the rig's certified cap 60000, so the closure index is NOT the
obstacle; the old `n ~ 31` contraction wall does not reappear under the
`q = 2^-14` pricing.

## 5. P5 - the non-vertex lambda screen

Convention bridge first, because the two names differ by a factor 2 and this
record fixes the reading so nobody re-derives a false mismatch:

```text
rig JSON (records 2028 / 2032 / 2033)   b, D, det = C*D - b^2
map 106 and the Lean parabola           gate(lam) = D - lam*B + lam^2*C, B = 2b
witness                                 lam = B/(2C) = b/C
```

So `annihilator_span_gate_eq_parabola` and the rig's
`gate = det/C = D - 2*lam*b + lam^2*C` are the SAME expression; the artifact
field named `b` is `B/2` of the formal statement. No mismatch exists, and
`lambda_n = b_n/C_n` is the vertex.

Reading (artifact blocks `lambda_screen` and `lambda_joint_rows`):

```text
LAMBDA-PAYS   on the C < 0 rows there IS a lambda window with gate(lam) < 0
              (downward parabola) and tau(n, lam) < 1: 8 measured rows,
              log10(lambda) windows starting at 0.5 (gamma_1, n = 4) and
              5.0 (gamma_1, n = 3), through 30.
BUT           the window is on rows where C < 0. The Lean consumer
              C1FourPointSpanGateCertificate.exists_pos_lambda_quadratic_neg_of_det_neg
              takes hC : 0 < C and hB : 0 < B, so a C < 0 row cannot produce a
              lambda witness at all: the gate opens downward and the health
              screen ICgate(g^2) > 0 that record 1931 makes a prerequisite is
              not available.
AND           on every C > 0 gate row the joint set is EMPTY, because
              tau_inf >= 1 already (section 4): the window cannot exist.
```

So `LAMBDA-PAYS` is correct as a statement about the parabola, and it closes
record 2029 reopen condition 2 in the NEGATIVE direction only: the
non-vertex-lambda branch does not rescue the C < 0 rows, and it cannot help the
C > 0 rows. No new witness target is registered.

## 6. P6 - interval bracket for the k = 3 weighted seed mass

Object and instrument as registered in record 2032 section 3:

```text
A_3(a) = integral_0^1 e^(a u) |T'''(u)| du,   T = Mathlib smoothTransition
W_3(a) = e^(-2a) A_3(a) + e^(2a) A_3(-a)
on a sign-certified panel:  integral_p^q |T'''| du = |T''(q) - T''(p)|  (exact)
```

Assembly (instrument note, same day, decision rule unchanged):
`[1e-6, 1 - 1e-6]` is cut into `n_base = 20000` equal panels. Each panel is
handed the mean-value enclosure `T'''(u) in T'''(m) + (u - m) T''''([p,q])`.
If it excludes zero, the panel is charged its exact FTC mass; otherwise it is
charged the rigorous envelope `(q - p) sup|T'''|`. Result: 19728 sign-certified
panels and 272 envelope panels, all of the latter with true mass below 3.3e-6
against a total of 39.4, i.e. at the 1e-7 relative level.

Bracket against the record-2031 reference values:

T4 W_3 bracket at the binding |a|

```text
+-------+------------+------------+------------+----------+-----------+
| |a|   | W3 lower   | W3 upper   | 2031 value | contains | rel width |
+-------+------------+------------+------------+----------+-----------+
| 0.025 | 78.589008  | 78.982990  | 78.982934  | True     | 4.99e-03  |
| 0.225 | 83.217574  | 83.630760  | 83.630285  | True     | 4.94e-03  |
| 0.275 | 85.570201  | 85.992930  | 85.992335  | True     | 4.92e-03  |
| 0.525 | 105.334079 | 105.835774 | 105.834383 | True     | 4.74e-03  |
+-------+------------+------------+------------+----------+-----------+
```

Strip bound recomputed with the UPPER end, on the full registered grid of 101
`sigma` values in `[0,1]` and 345 `t` values in `[28, 200]`:

```text
k = 3 certified bound   3.001847221e-07      at (sigma, t) = (0.00, 28.0)
uncertified 2031 bound  3.001641057e-07      (record 2031, 40-digit float)
q = 2^-14               6.103515625e-05
margin q/bound          203.33x
decision                MASS-BRACKETED
```

The certified upper end exceeds the uncertified value by 6.9e-05 relative, so
the whole 203x margin survives the interval treatment of the one-dimensional
mass.

## 7. Instrument notes, errata and non-claims

```text
1.  P6 instrument, first version (not a reading): the panel builder recursed on
    every panel whose mean-value enclosure straddled zero. That does not
    terminate: the enclosure also straddles zero on both neighbours of a simple
    root, so the recursion branches over the whole underflow region (u <~ 0.01
    and u >~ 0.99) down to the width floor. A point scan for the roots was also
    polluted by cancellation near u = 1 (spurious sign changes at
    u = 0.9895..0.9999). The committed version locates no roots and charges the
    envelope, which is rigorous and has no such failure mode.
2.  P6 soundness fix found during the smoke phase: the a-grid was
    [-0.57, 0.31], but W_3(a) needs A_3(-a), so the a = -0.525 cell asked for
    A_3(+0.525) and silently fell back to the last grid value (an UNDER-estimate
    of an upper bound). The grid is now [-0.60, 0.60] and both lookups RAISE
    rather than degrade when asked outside it.
3.  P6 mirroring: T^(k)(1-u) = (-1)^(k+1) T^(k)(u) is used to evaluate every
    panel with p > 1/2 on the mirrored panel. Without it the panel
    u = [0.999949, 0.999999] carried an envelope mass of 1.18 (3% of the whole
    mass) against a true value near 3e-30: T = 1/(1+exp(hD)) is an interval of
    width 1e-40 near u = 1, T - T^2 straddles zero, and the hD powers amplify.
4.  P6 `--smoke` (RH_INTERVAL_MASS_SMOKE) was executed before the full run and
    truncated every consumer of the grid. The panels and the a-grid are dumped
    to the artifact BEFORE the strip scan, so a scan crash cannot destroy the
    measurement.
5.  Record 2032's log prints `dev_C` against the previous anchor row (an
    off-by-one in the anchor loop); the JSON values are correct. Cosmetic, log
    only.
6.  `results/2034_support_radius_robustness_firstpass-uncorrected.json` is a
    labelled NON-READING: a conditional used `gamma > 25.0` to choose the n-set
    and dropped the gamma_3 / n = 3 rows. The committed file is the corrected
    15-row version.
7.  The `q = 1/2` control column (`tau_half_control`) is astronomically large
    everywhere (2.1e28 at gamma_1 / n = 0). That is a property of the rig's
    unit-threshold convention, not of the route: `beta_s` and
    `multiplicity_rho` remain formal-owner inputs and this is not the Lean tail
    ratio (record 1980's own caveat). The scale-free content of section 4 is
    the ordering of the bands and the `tau_inf >= 1` statement, not the value 1.
8.  The gate pattern is measured on the record-1980 known-zero
    UNDER-APPROXIMATION of the source owner, on one `xi`-grid family
    (`dxi = 0.02` primary, `0.01` refinement), at three heights and three owner
    cardinalities. It is not a theorem, not an interval certificate for the gate
    moments, and not a statement about the formal
    `sourceNontrivialZerosInClosedBallFinset`.
9.  P6 certifies the ONE-DIMENSIONAL mass `W_3` only. The `sigma`-sup and the
    `t`-scan are grids (101 x 345), and the node products `P(z,s)` and the
    weights `c_z` are float evaluations. This is exactly the part record 2031
    flagged as plausible.
10. No COVER statement, no TAIL Lean object, no gate theorem, no RH claim.
```

## 8. Consequence for the route ledger

```text
R-B0 owner            known-zero under-approximation; complete visible-prime
                      source now MANDATORY before ROW-FOUND is used (P4c)
R-B1 q (Cut-1 tail)   PRICED VIABLE and now CERTIFIED on the mass only:
                      k = 3, bound 3.001847e-07, margin 203.33x, MASS-BRACKETED
R-B2 determinant      cheap (record 2030: needs eps < 3.8e-3 .. 9.0e-2, or
                      0.4142 vertex-centred); no longer the binding obstacle
R-B3 tail ratio       THE BINDING WALL on this family: PAIR-MISMATCH. The gate
                      rows sit at n = 2, 3; tau_inf there is 2.1e10 .. 9.7e12,
                      i.e. unreachable at any lambda; the tail first closes at
                      n = 4 where the gate signs are gone. Record 2029 reopen
                      condition 1 is satisfied (rows now exist), and the wall
                      has MOVED from "no admissible row" to "gate index and
                      tail index are disjoint"
R-B4 coverage         OPEN, and now doubly gated: RADIUS-FRAGILE on 14 of 15
                      rows, plus the R-B0 prerequisite
```

Next-step options that this record prices, in order of information per unit of
work:

```text
1.  Change the named hypothesis that sets the index. The wall is a per-unit-n
    decay factor q^2 = 2^-28 against a family whose gate rows sit at n = 2, 3.
    The cheapest discriminating probe is a changed SUPPORT/SIZE hypothesis that
    moves the gate row to n = 4 without changing the owner: same family, larger
    seed support or a shifted support window, re-read only at the n where the
    tail closes (n = 4, one row per (gamma, N)).
2.  Pin R-B0 before any further routing: the visible-prime source and the
    exact support radius. P4c says 14 of 15 rows are radius-conditional, so a
    row count without the pinned book is not routing evidence.
3.  Promote the P6 instrument, not the P6 number, to Lean: W_3 is
    one-dimensional, explicit, has no cancellation and now has a working
    interval bracket with a 5e-3 relative width. That is the only piece of
    Route B whose accuracy question is currently closed.
```

Nothing in this record changes a binding route authority by itself; the route
ledger update that accompanies it is the statement that R-B3 is now the named
binding wall on the record-1980 family, with the mechanism above.
