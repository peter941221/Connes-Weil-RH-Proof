# Record 2029 - Route-B Cut-1 coupling scan: outcome, and erratum on record 1981

Date: 2026-09-27.

Status: OUTCOME + ERRATUM. No theorem, no interval certificate, no RH claim.

Outcome of the pre-registration [2028](2028_coupling_scan_preregistration.md).
Raw artifact: `results/2028_coupling_scan.json`. Log:
`build-logs/20260927_coupling_scan_2028b.log`. The instrument is
`scripts/fourpoint_coupling_scan_2028.py`; the first (buggy, pre-fix) pass is
kept as `results/2028_coupling_scan_firstpass-uncorrected.json` and is NOT a reading.

## 1. Bottom line

Result: BAD for the route as parameterized, with one piece of good news and one
erratum that reaches back into two committed records.

```text
BAD      COUPLING-COLLAPSES fires.
         On the certified route the registered gate pattern
         (C_n > 0, b_n > 0, det_n < 0) holds at n = 0 ONLY.
         n = 1,2,3,4 all have C_n < 0 and b_n < 0.

BAD      CONDITIONING-BLOCKS fires at n = 5.
         The certified route set is empty for n >= 5 (P_5 = 93371 > 60000).
         A (1/2)-contraction closure needs n ~ 31, i.e. ~8x past the last
         certifiable n, and n = 6 shows the decay is not even monotone.

BAD      ERRATUM on record 1981: every committed row with n >= 1 is
         under-resolved.  n = 2 is off by 9.3% on C, n = 3 by 95% on C,
         and n = 4 has its C, b, D signs all flipped.  Record 1982's
         "gate witness at n = 4" is built on the flipped row and dies with it.

GOOD     The determinant cancellation is far milder than record 1982
         reported (depth 1.5e-2 .. 4.7e-1 against the reported 7.6e-4),
         so a determinant certificate is much cheaper than the route
         assumed -- see record 2030.
```

Neither label is a no-go for Route B as a whole. Both are scoped to the seeded
owner of record 1980/1981 (`rho = 0.55 + 14.134725141734693i`, `N = 4`,
`L_p(s) = L_smoothSeed(s/2)^10`) and to the registered vertex witness.

## 2. Verdicts against the registered decision rules (2028 section 4)

```text
COUPLING-HOLDS            did NOT fire.
  lambda_n stays positive, but det_n < 0 does not come with C_n > 0 on any
  measured certified n other than n = 0, so the "every certified n holds the
  pattern" clause fails.

COUPLING-COLLAPSES        FIRED.
  lambda_n changes sign (route-A rows n = 5) and the gate pattern fails on
  certified n = 1..4.  The "geometric closure along large n" form of Cut 1 is
  dead as stated on this owner.

CONDITIONING-BLOCKS       FIRED, at n = 5.
  Certified routes {Ap, B} both drop out at P_5 = 93371 > 60000; n = 7 has no
  route at all (P_7 = 3878366 > 3000000).  n_needed ~ 31 > 4.
```

Measured rows, `dxi = 0.02`, certified route `B` (direct prime channel):

```text
 n   P_n     routes    C_n              b_n              det_n            lambda_n  gate
 0      24   Ap,B,A    +2.372262e+03    +2.683169e+06    -2.555751e+11     1131.06  TRUE
 1      98   Ap,B,A    -5.126748e+03    -7.874941e+06    -7.555081e+12     1536.05  false
 2     465   Ap,B,A    -2.347548e+04    -3.208973e+07    -1.564391e+13     1366.95  false
 3    2532   Ap,B,A    -1.452195e+05    -3.110370e+08    -1.219067e+16     2141.84  false
 4   15040   B,A       -5.017354e+05    -1.683048e+09    -8.991387e+17     3354.45  false
 5   93371   A         +9.424640e+05    -6.513964e+09    -6.401585e+19    -6911.63  false
 6  595877   A         +3.813569e+07    +5.858218e+09    -3.537912e+21      153.62  TRUE*
```

`TRUE*` at n = 6 is route A only, and route A is not certified: its
dual-spline prime interpolation costs 1e-2 .. 1e-1 relative (record 1959),
which is far above the cancellation depth of the n = 6 row. It is recorded,
not read.

Certified-route spread of the direct channel against route A is 1.1e-4 ..
3.8e-4 relative on C, b, D over n = 1..4 (n = 0: 8e-6), so the sign failure is
not a quadrature-route artifact: both routes agree to four digits at every n.

## 3. Erratum 1 - record 1981 rows with n >= 1 are under-resolved

The pre-registered reproduction anchor PASSED: at `dxi = 0.05` this scan
reproduces `results/1981_powered_seed_underapprox.json` to 1.3e-15 .. 2.2e-14
relative on C, b, D, det, lambda over n = 0..4. The artifact identity is not in
question; its *resolution* is.

Refinement, committed-1981 (dxi = 0.05) versus converged grid. Convergence is
established on the grid set, not assumed: `dxi in {0.01, 0.005, 0.002, 0.001}`
agree to <= 1.4e-13 relative on C, b, D, det at every n = 0..4, while
`dxi = 0.02` (the trend grid of section 2) still carries <= 7.3e-7 relative,
worst at the n = 4 determinant. The trend rows below therefore carry a ~1e-6
resolution band, which is four orders of magnitude below the erratum effects
in this table.

```text
 n  field   committed 1981      converged        rel.dev
 0  C       +2.3722835459e+03   +2.3722617326e+03   9.2e-06
 0  det     -2.5822240449e+11   -2.5557513263e+11   1.0e-02
 1  C       -5.1740281921e+03   -5.1267476046e+03   9.2e-03
 1  D       -1.0175050980e+10   -1.0622645244e+10   4.2e-02
 2  C       -2.1286533241e+04   -2.3475484817e+04   9.3e-02
 2  D       -2.7023532475e+10   -4.3198537540e+10   3.7e-01
 2  det     -4.2273239301e+13   -1.5643908941e+13   1.7e+00
 3  C       -7.4103515275e+03   -1.4521947349e+05   9.5e-01
 3  lambda  +1.0892272770e+03   +2.1418407000e+03   9.7e-01
 4  C       +3.0001193334e+06   -5.0173556258e+05   SIGN FLIP
 4  b       +4.3141376310e+09   -1.6830482976e+09   SIGN FLIP
 4  D       +6.1989491411e+12   -3.8536478887e+12   SIGN FLIP
 4  lambda  +1.4379886770e+03   +3.3544532000e+03   1.3e+00
```

Root cause, measured (not inferred). The prime kernel is
`sum 2*Lambda(k)/sqrt(k) * cos(2*pi*xi*log k)`, so on a uniform `xi` grid of
step `dxi` the trapezoid rule resolves only `log k <= 1/(2*dxi)`: 10 at
`dxi = 0.05` against `max log k = 12` at n = 4. The pre-registration (section
6) named this risk before the run; here is the channel decomposition that
localizes it:

```text
 n = 4, dxi = 0.05   arch C = -1.63668602e+05   prime C = +3.16378794e+06   total +3.0001e+06
 n = 4, dxi = 0.02   arch C = -1.64006774e+05   prime C = -3.37728654e+05   total -5.0174e+05
 n = 4, dxi = 0.01   arch C = -1.64006774e+05   prime C = -3.37728789e+05   total -5.0174e+05
 n = 1, dxi = 0.05   arch C = -4.83591526e+03   prime C = -3.38112929e+02   total -5.1740e+03
 n = 1, dxi = 0.02   arch C = -4.83573503e+03   prime C = -2.91012571e+02   total -5.1267e+03
```

The archimedean channel is resolution-stable (2e-3 relative between the two
grids); the whole error sits in the oscillatory prime channel, which flips sign
at n = 4. The direct-channel values in this table are element-wise identical to
the committed `fourpoint_diagonal_sign_1918` rig generator (checked at
`xmax = 50, 1000, 5000` in the same run).

Error bound on the pre-registered prediction: the alias fold-back is
`cos(2*pi*xi*(log k)) -> cos(2*pi*xi*(log k - 1/dxi))`, so the committed 1981
table silently reads every `k > exp(1/dxi) = exp(20)` folded onto a low
frequency. That is not a truncation (which would have a limit) and not a
convergent error: it is why the verdict flipped.

Scope of the erratum:

```text
record 1981  rows n >= 1     superseded by the converged grid of record 2028
             row  n = 0      survives (dev 9.2e-06 on C); its det dev of 1.0e-02
                             is the n-independent arch/density resolution
record 1982  the n = 4 gate row, lambda = 1437.9887, and the 2.573e-6 tail
             proxy all inherit the flipped row and are withdrawn
map 106.30   "gate signs occur at n = 0 and n = 4" -> n = 0 only
map 106.31   the n = 4 gate row is withdrawn; the q screen itself (T = 28,
             q = 2^-14, grid max 3.13e-9) is untouched, because it is a
             property of the base, not of the prime channel
```

Per the standing rule, this is an erratum inside an outcome record, not a
silent re-definition: no threshold was moved and no row was rewritten in
`results/1981_powered_seed_underapprox.json`.

## 4. Erratum 2 - instrument annotation (no verdict depends on it)

The pre-registration section 3 lists three routes `{Ap, B, A}` with caps
`{4000, 60000, 3000000}` and sets `CERTIFIED_ROUTES = (Ap, B)`. The
implementation only ever produces `B` (direct cos sum) and `A` (dual-FFT plus
spline, record 1959); the `Ap` cap is dead code in this scan and the JSON field
`certified_routes` names a route that was never measured. The instrument
section (2028 section 5) is the one that matches the code: "direct (B) for
P_n <= 60000; route A above, labeled". The certified route actually read here
is `B`.

## 5. The prime-power book: n is not a currency

Exact counts (sieved, not predicted), with the committed rig caps:

```text
 n   s_n = 2(n+2)   P_n = #{k prime power : k <= exp(s_n)}    routes available
 0        4                     24                            Ap, B, A
 1        6                     98                            Ap, B, A
 2        8                    465                            Ap, B, A
 3       10                   2532                            Ap, B, A
 4       12                  15040                            B, A
 5       14                  93371                            A           <- certified set empties
 6       16                 595877                            A
 7       18                3878366                            none
 (PNT envelope, not sieved: n = 8 ~ 2.4e7, n = 47 ~ 3.7e40)
```

The tail proxy on the converged grid is

```text
 n        0          1          2          3          4          5          6
 L/lambda^2  2.14e28  2.93e27  9.23e26  9.56e25  1.00e25  6.37e23  2.78e26
```

Per-step geometric decay `(proxy_5/proxy_0)^(1/5) = 0.1243` (0.1470 over
n = 0..4), so a unit-threshold closure with the committed `1/2` contraction
needs `log(2.14e28)/log(8.04) = 31.3` further indices, i.e. `n_needed ~ 31`
(34 if only certified rows are used). The requirement
`beta_s * L_n < multiplicity_rho * lambda_n^2` has threshold `1/beta_s` rather
than 1, but `beta_s` cannot manufacture the ~28 orders of magnitude of slack
that the deficit demands, and n = 6 rising by a factor 292 makes the trend
non-monotone anyway.

Consequence: Cut 1 cannot be paid with `n` on this owner. It must be paid with
`q` (map 106 section 6), which makes R-B1 mandatory rather than optional. But
`q` can only be spent through `q^(2n)`, so the route also needs at least one
admissible `n >= 1` gate row -- and on the converged grid there is none.

## 6. What this scan does not decide

- Not a no-go. The registered Cut-2 pattern `C > 0, b > 0, det < 0` is a
  specific witness (the parabola vertex, `gate = det/C`). On every `C < 0` row
  measured here the parabola opens downward, so `gate(lambda) -> -infinity` and
  a *different, non-vertex* lambda does have `gate < 0`. That construction is
  outside the registered target, its consumer half (`qw(h_n) >= 0`) is not
  established for it, and it is listed here as a named alternative, not as a
  result.
- No formal-owner statement: the owner is the known-zero under-approximation.
- No interval certificate: floats generate data; Lean must verify the constant.
- Nothing about COVER or TAIL Lean objects, nothing about the correctness of
  the target detector construction, no RH claim.

## 7. Reopen conditions

1. A gate row with the registered pattern at some admissible `n >= 1` under a
   *changed* named hypothesis (different seed power/scale, different `N`, or a
   changed owner) -- this scan binds only its own owner.
2. A registered non-vertex lambda witness on the `C < 0` branch, with its own
   `qw(h_n) >= 0` half.
3. Nothing here may be reopened by re-reading the `dxi = 0.05` grid.
