# Record 2005 - Route A A-V probe: evidence correction

Date: 2026-09-26.

Status: correction to the evidence reported in record 2001, found while
auditing the record-2000 instrument for record 2003. No new measurement of a
producer object, no Lean result, no RH claim, and no change to the binding
Route A obligation.

## Verdict

```text
A-V status: UNRESOLVED (not adjudicated)
replaces:   "scoped no-go for A-V", record 2001
```

Record 2001 asserted that certified rows of the minimum-H1 selector have
`C < 0`. The artifact of that run does not support a certification claim at
all: every row was produced with a single certified route, and the family
measured was not the committed owner's family.

## 1. What the artifact actually records

From `results/2000_route_a_variational_probe.json`, the run behind record
2001:

```text
case   routes       spread_C   spread_B01   spread_D   certified   |c| correction
G5-H   ["A", "B"]   0.0        0.0          0.0        false       4.772e+16
G5-W   ["A", "B"]   0.0        0.0          0.0        false       4.843e+16
G7-H   ["A", "B"]   0.0        0.0          0.0        true        2.059e+16
G8-H   ["A", "B"]   0.0        0.0          0.0        true        5.582e+16
```

Three points follow.

1. `spread_D` is exactly `0.0` in all four rows. `route_spread` averages only
   over the certified routes `("Ap", "B")`. With the prime channel carrying
   only `A` and `B`, the certified set is the singleton `{B}`, and the spread
   is the degenerate single-route floor (project law F52): a one-route row
   reports no agreement.
2. The certification predicate of the record-2000 script counted route `A`:
   `len(set(routes) & {"A", "Ap", "B"}) >= 2`. Route `A` is the
   spline-interpolation route that `route_spread` excludes from certification
   (its own docstring records `1e-2 .. 1e-1` relative error on a `1e-3`-level
   residual). The two rows marked `"certified": true` therefore have exactly
   one certified route.
3. Record 2001 states that the G7 and G8 rows are "fully certified by the
   registered instrument, with three live routes". The artifact records two
   routes, `A` and `B`; route `Ap` is absent.

## 2. Why the route set collapsed: the measured family was not the committed owner

The record-2000 family places two copies per node, at `0.86a` and `1.14a`. The
widest copy exceeds the committed width `a`, and the gate instrument's support
radius `max(a) * (n + 2)` grows with it:

```text
case   committed max   committed support   A-V support   committed np   A-V np   route Ap
G5-H   4.9680          9.9360              11.3270       2393           8212     dropped
G5-W   4.8600          9.7200              11.0808       1985           6578     dropped
G7-H   4.9680          9.9360              11.3270       2393           8212     dropped
G8-H   4.7520          9.5040              10.8346       1647           5284     dropped
```

`gate_entries` computes `Ap` only while `n_primes <= 4000`, so all four rows
lost that route. Beyond the certification defect, the gate book of the A-V
probe was built from a strictly larger visible-prime set than the committed
owner's: the measured object was not the committed owner. The A-V
pre-registration of record 1999 required ownership preservation, and this
family does not satisfy it.

## 3. What is NOT wrong: the density evaluation is not roundoff dominated

The A-V corrections have coefficient norms of order `1e+16`, which raises the
question whether the reported gate entries are roundoff. Tested directly for
G7-H by evaluating `L_c = sum_j c_j V_j` in `float64` and again in 80-bit
`longdouble`:

```text
xi      |L_c| float64      |L_c| longdouble   abs diff    rel diff
0.00    3.9080188894e-08   0.0000000391       7.011e-15   1.794e-07
0.25    9.0718729658e-01   0.9071872966       5.291e-14   5.832e-14
0.50    2.0916905537e+00   2.0916905537       4.592e-15   2.196e-15
1.00    2.6355362173e+00   2.6355362173       2.201e-16   8.352e-17
2.00    6.8087777784e-04   0.0006808778       1.747e-19   2.566e-16
4.00    1.2664371308e-09   0.0000000013       1.354e-25   1.069e-16
```

The largest relative deviation is `1.8e-07`, so the evaluated densities are
not roundoff dominated on this sample and the large coefficients are not by
themselves a defect. This correction does not claim that the A-V sign
readings are wrong; it claims they are uncertified.

## 4. Corrected status and consequences

1. A-V produced no certifiable reading. Two rows fail the pin gate
   (`6.55e-06` and `1.77e-06` against `1e-06`), and the other two have a
   single certified route. A verdict asserting a certified sign failure is
   unsupported; the honest status is UNRESOLVED.
2. The standing advice not to formalize A-V is unchanged, but for a different
   reason: the probe cannot be read, not that it failed.
3. Record 2003's support-preserving two-copy family is the instrument a
   re-measurement would need. Its minimum-energy endpoint construction is the
   part that fails to be numerically well defined (record 2003 section 3),
   which is why record 2003 replaced that endpoint with the unit-H1 ray scan.
4. Nothing here changes the binding Route A obligation, the COVER layer, or
   the committed owner results of records 1994 and 1996.
