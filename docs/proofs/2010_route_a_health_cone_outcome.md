# Record 2010 - Route A health-cone shape scan outcome

Date: 2026-09-26.

Status: outcome of the registered record-2006 scan, re-executed under the
instrument of records 2007 and 2009. No theorem, no Lean brick, and no RH
claim.

## 1. Verdict

```text
registered verdict   H-CONE-STRATIFIED / RANK-FLAT / MECH-MIX
instrument           all four anchors pass, 128/128 rows certified,
                     identity checks pass on every row
reproducibility      the re-executed artifact equals the first full run
                     bit-for-bit on C, B01, D, det, W0 over all 128 rows
                     (worst relative deviation 0.0e+00, no flag mismatch)
```

The record-2009 section 5 expectation table is satisfied exactly, so the
first full run and the registered scan are the same measurement.

## 2. Registered tables

Owners: G5-H (gamma_5, scale 0.92), G5-W (gamma_5, scale 0.90), G7-H
(gamma_7, scale 0.92), G8-H (gamma_8, scale 0.88); `delta = 0.10`,
`dxi = 0.008`, two-copy `0.75a / a` family, 17-dimensional feasible fibre.

Health radius per registered rank (largest registered amplitude with a
certified healthy row, in units of the committed correction H1 norm):

```text
owner  rank 1   2     4     6     9     12    14    17
G5-H   none    none  none  0.02  none  0.02  0.02  0.02
G5-W   none    none  none  none  none  none  none  none
G7-H   0.05    0.05  0.05  0.20  0.05  0.05  0.02  0.05
G8-H   0.05    0.80  0.80  0.80  0.05  0.05  0.02  0.05
```

```text
N (pairs with radius >= 0.05)   14      -> H-CONE-STRATIFIED  (2 <= N < 16)
rank winners                    14, 6, 6, 4  -> RANK-FLAT
max relative change of f        1.309   -> MECH-MIX   (MECH_TOL = 0.20)
```

Margin response at the largest registered amplitude, `C(0.80) / C(0)`:

```text
owner  rank 1   2      4      6      9      12     14     17
G5-H   -1571  -2118  -1847  -841   -623   -7596  -315   -1092
G5-W   -4.1e4 -6.9e4 -6.7e4 -1.2e4 -5.2e4 -3.6e5 -4.1e4 -3.0e4
G7-H   -30.3  -45.8  -87.1  -0.30  -31.4  -426   -155   -26.1
G8-H   -33.6  +3.20  +4.26  +4.04  -10.6  -351   -586   -23.0
```

Route robustness, and the D census over all 32 rows of each owner:

```text
owner  healthy_ap  healthy_b  healthy_both  D_Ap<0  D_B<0  C_B<0  det<0
G5-H   4           4          4             32/32   32/32  28/32   9/32
G5-W   0           0          0             32/32   32/32  32/32   0/32
G7-H   16          16         16            32/32   32/32  16/32  17/32
G8-H   21          21         21            32/32   32/32  11/32  22/32
```

Instrument maxima over all 128 rows: `spread_C <= 6.88e-02`,
`spread_D <= 5.96e-04`, `dev_var <= 8.71e-04`, `dev_alg <= 5.82e-13`,
`dev_A_C <= 4.02e-04`.

## 3. What the numbers say

(1) The health cone is stratified. It is neither a sliver nor a ball. At the
two high-ordinate owners a thin shell of radius `0.05` survives at 7 of the 8
registered ranks, and it is joined by a genuinely fat branch of radius `0.80`,
the largest registered amplitude, at G8-H ranks 2, 4 and 6. Both gamma_5
owners are empty: their radius is `0.02` or nothing at every rank.

(2) The improvement direction is the energetic end of the restricted
spectrum, but only at the highest ordinate. Exactly three `(owner, rank)`
pairs have `C(0.80) / C(0) > 1`, all of them G8-H, at ranks 2, 4 and 6, with
factors `3.20`, `4.26` and `4.04`. Every other one of the 29 pairs collapses,
most of them through a sign flip and by factors of `10` to `3.6e5`.

(3) The registered `RANK-*` rule is a rule artifact on this data and is
reported as such. It reads the argmax of `C(0.80) / C(0)` over all registered
ranks, so when every ratio is negative it returns the least-collapsed rank
rather than a margin-increasing one; that is how it produced `14, 6, 6, 4`.
Reading (2) is the informative statement, and no threshold of the registered
rule is changed here.

(4) `MECH-MIX`. On the three margin-increasing rows the negative-mass fraction
`f = mm / A` changes by `+2.3%`, `+36.2%` and `+130.9%` relative to its anchor
value. The improvement is therefore not a pure scaling of the signed measure:
at G8-H rank 6 the negative-mass fraction more than doubles.

(5) Route robustness is not a live risk at this resolution. For every owner
`healthy_ap = healthy_b` equals the registered conjunction, so none of the 41
healthy rows depends on which route is quoted, and `D < 0` holds in `128/128`
rows on both readouts, including all 104 rows where the C margin has already
flipped sign.

(6) One direction is systematically fragile. Rank 14 loses health at the
first registered amplitude `0.02` for all four owners, independently of the
ordinate, so its fragility is a property of that subspace rather than of the
owner.

## 4. A conditioning finding

The record-1919 readout gives the negative-mass fraction `f = mm / A` at the
committed anchors:

```text
owner   A (committed)   f = mm / A   route spread of C   route spread of D
G5-H    +1.4909e+00    7196         6.88e-02 (max)      2.09e-04 (max)
G5-W    +2.5017e-01    86087        3.77e-03            5.96e-04
G7-H    +1.7315e+02    133          3.59e-03            2.21e-04
G8-H    +6.6411e+02    51           6.70e-03            1.35e-04
```

So `A` is the residual of a cancellation of order `f`: at G5-W the positive
and negative parts of the signed measure have mass about `8.6e4` times the net
total. Two consequences.

```text
the obligation     D < 0   is well conditioned: certified-route spread
                           <= 6.0e-04 relative on all four owners
the health witness C > 0   is a cancelled quantity: certified-route spread up
                           to 6.9e-02 relative, and smallest |C| against the
                           largest f at G5-W
```

This is consistent with record 1998 (the gate book is D-dominated) and with
record 1926 (the final-sign no-go), and it identifies why the gamma_5 owners
have no health cone at all: they carry the smallest committed `|C|` against
the largest `f`. It also says where the route-A numeric exposure sits: in the
admissibility check, not in the obligation.

## 5. Scope

This is mechanism reconnaissance for the A-H cone, not core progress. By the
project's core-progress gate it produces no unconditional bound on the actual
selected detector, no new no-go (record 1926's selector no-go stands
unchanged), and no strictly smaller obligation. The scan samples one family,
one resolution, four `(delta, gamma)` points, 8 of 17 ranks and 4 amplitudes.
Nothing here touches the TAIL layer, the COVER layer or any Lean artifact, the
binding obligation is unchanged, and no gate sign, determinant theorem or RH
claim is made.

## 6. Artifacts

```text
scripts/routea_health_cone_2006.py
scripts/routea_health_cone_2006_calibration.py
results/2006_route_a_health_cone.json                (registered scan)
results/2006_route_a_health_cone_smoke.json
results/2006_route_a_health_cone_calibration.json
results/2006_route_a_health_cone_run1_instrument_fail.json
```

## 7. Next

1. Test the energetic branch as a mechanism rather than a sampling accident:
   sweep the ordinate at fixed rank 4 to see whether the margin-increasing
   branch follows a law in gamma, since it appears at gamma_8 only.
2. Price the cancelled witness: since `C > 0` is a residual of order `f`, a
   health certificate for the gamma_5 owners needs a relative accuracy of
   order `1/f`, which is the resolution requirement the A-H cone implies.
3. Reconcile with the binding obligation: check whether the `D < 0` margin on
   the same rows is monotone in the same directions, which would separate the
   well-conditioned obligation from the cancelled witness.