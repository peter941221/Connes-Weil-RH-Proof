# Record 2004 - Route A A-H feasible-fiber ray scan outcome

Date: 2026-09-26.

Status: outcome of the instrument registered in record 2003. No Lean theorem,
no producer closure, and no RH claim.

## Verdict

```text
A-H-CONE-MIXED
```

Two of the four registered owners keep a certified healthy row at
`sigma >= 0.05`; both gamma_5 owners lose health at the first registered
non-zero amplitude. The scan also produced a structural result that the
pre-registration did not anticipate: at gamma_8 the fiber contains a
direction along which the health margin increases monotonically by a factor
3.2 while the determinant stays negative.

## 1. Instrument check (registered)

The registered check is that the `sigma = 0` row reproduces the committed
EXT-convention reference row of records 1994b and 1996 at `dxi = 0.004`
(relative deviation at most `1e-6` on `C`, `B01`, `D`) and is certified.

```text
case   reference C            anchor C              max rel dev   certified
G5-H   +1.494812433412335     +1.494812433412335    6.19e-16      true
G5-W   +0.2559098884994455    +0.2559098884994455   4.26e-11      true
G7-H   +173.2980278055402     +173.2980278055402    6.30e-14      true
G8-H   +664.3518622617412     +664.3518622617412    2.85e-16      true
```

Support preservation and exact feasibility also hold on every row: support
radius and prime-power count are the committed ones, the route list is
`["A", "Ap", "B"]` throughout, the feasible fiber has nullity 17, and the
first canonical direction satisfies `|M d| <= 1.1e-16`.

```text
case   support   np     cond      E_ref      nullity   |M d_1|
G5-H   9.9360    2393   1.86e+04  1.7454e+03   17      6.94e-17
G5-W   9.7200    1985   2.54e+04  2.6772e+03   17      5.55e-17
G7-H   9.9360    2393   1.61e+04  2.6214e+03   17      4.39e-17
G8-H   9.5040    1647   1.94e+04  4.5494e+03   17      1.12e-16
```

## 2. Registered scan

`sigma` is the perturbation's H1 norm in units of the committed correction's
H1 norm `E_ref`; direction 1 is the most energetic direction of the feasible
fiber and direction 2 the next. The scan has 56 rows; all 56 are certified on
three routes, with the committed prime set, and `D < 0` holds in all 56.
Twenty-three rows are healthy. The determinant is negative on all 23 healthy
rows and also on two rows where `C` has just crossed to negative (G5-H,
`sigma = 0.02`, where `|C D| < B01^2`); on the other 31 rows `C < 0` and
`det > 0`.

gamma_5, scale 0.92 (G5-H), committed margin `C = +1.4948`, health radius 0:

```text
dir  sigma    C             D              det            spread_D
1    0.00   +1.4948e+00   -6.3074e+12    -9.4416e+12    3.21e-05   HEALTHY
1    0.02   -5.9247e-02   -1.8072e+18    -3.7684e+17    4.81e-05
1    0.05   -7.8755e+00   -1.1292e+19    +7.0030e+19    4.81e-05
1    0.10   -3.5530e+01   -4.5164e+19    +1.3023e+21    4.81e-05
1    0.20   -1.4569e+02   -1.8065e+20    +2.1481e+22    4.81e-05
1    0.40   -5.8541e+02   -7.2257e+20    +3.4561e+23    4.81e-05
1    0.80   -2.3425e+03   -2.8903e+21    +5.5321e+24    4.81e-05
2    0.00   +1.4948e+00   -6.3074e+12    -9.4416e+12    3.21e-05   HEALTHY
2    0.02   -2.4499e-01   -2.7559e+18    -1.5227e+17    5.25e-05
2    0.05   -1.0282e+01   -1.7226e+19    +1.4477e+20    5.25e-05
2    0.10   -4.6814e+01   -6.8904e+19    +2.7083e+21    5.25e-05
2    0.20   -1.9415e+02   -2.7562e+20    +4.5232e+22    5.25e-05
2    0.40   -7.8589e+02   -1.1025e+21    +7.3397e+23    5.25e-05
2    0.80   -3.1577e+03   -4.4099e+21    +1.1806e+25    5.25e-05
```

gamma_5, scale 0.90 (G5-W), committed margin `C = +0.2559`, health radius 0:

```text
dir  sigma    C             D              det            spread_D
1    0.00   +2.5591e-01   -2.2514e+14    -5.9085e+13    2.37e-05   HEALTHY
1    0.02   -6.0202e+00   -2.2917e+18    +1.2781e+19    1.13e-04
1    0.05   -3.9705e+01   -1.4400e+19    +5.3174e+20    1.12e-04
1    0.10   -1.6057e+02   -5.7704e+19    +8.6234e+21    1.12e-04
1    0.20   -6.4500e+02   -2.3102e+20    +1.3873e+23    1.12e-04
1    0.40   -2.5847e+03   -9.2451e+20    +2.2249e+24    1.12e-04
1    0.80   -1.0347e+04   -3.6989e+21    +3.5638e+25    1.12e-04
2    0.00   +2.5591e-01   -2.2514e+14    -5.9085e+13    2.37e-05   HEALTHY
2    0.02   -1.1121e+01   -2.9644e+18    +3.1260e+19    1.48e-04
2    0.05   -6.8870e+01   -1.8451e+19    +1.2043e+21    1.48e-04
2    0.10   -2.7361e+02   -7.3705e+19    +1.9106e+22    1.48e-04
2    0.20   -1.0899e+03   -2.9462e+20    +3.0416e+23    1.48e-04
2    0.40   -4.3499e+03   -1.1781e+21    +4.8534e+24    1.48e-04
2    0.80   -1.7379e+04   -4.7115e+21    +7.7546e+25    1.48e-04
```

gamma_7, scale 0.92 (G7-H), committed margin `C = +173.298`, health radius
`0.10` in both directions:

```text
dir  sigma    C             D              det            spread_D
1    0.00   +1.7330e+02   -2.0359e+20    -4.2148e+22    2.28e-05   HEALTHY
1    0.02   +1.7050e+02   -2.0910e+20    -4.2938e+22    2.35e-05   HEALTHY
1    0.05   +1.5352e+02   -2.3231e+20    -4.4643e+22    2.61e-05   HEALTHY
1    0.10   +9.1153e+01   -3.1083e+20    -4.4072e+22    3.22e-05   HEALTHY
1    0.20   -1.6134e+02   -6.1730e+20    +4.0430e+22    4.11e-05
1    0.40   -1.1774e+03   -1.8279e+21    +1.6560e+24    4.72e-05
1    0.80   -5.2536e+03   -6.6399e+21    +2.8489e+25    4.94e-05
2    0.00   +1.7330e+02   -2.0359e+20    -4.2148e+22    2.28e-05   HEALTHY
2    0.02   +1.6474e+02   -2.0129e+20    -3.9805e+22    2.39e-05   HEALTHY
2    0.05   +1.3328e+02   -2.2022e+20    -3.6930e+22    2.86e-05   HEALTHY
2    0.10   +3.1131e+01   -3.1150e+20    -2.3268e+22    3.87e-05   HEALTHY
2    0.20   -3.5954e+02   -7.1800e+20    +1.9510e+23    4.99e-05
2    0.40   -1.8864e+03   -2.4268e+21    +3.9001e+24    5.46e-05
2    0.80   -7.9221e+03   -9.4274e+21    +6.4578e+25    5.54e-05
```

gamma_8, scale 0.88 (G8-H), committed margin `C = +664.352`, health radius
`0.10` in direction 1 and `0.80` in direction 2:

```text
dir  sigma    C             D              det            spread_D
1    0.00   +6.6435e+02   -1.1113e+20    -7.6692e+22    1.31e-05   HEALTHY
1    0.02   +6.1137e+02   -1.1739e+20    -7.5202e+22    1.18e-05   HEALTHY
1    0.05   +4.8170e+02   -1.3147e+20    -6.8467e+22    9.91e-06   HEALTHY
1    0.10   +1.3175e+02   -1.6743e+20    -3.3755e+22    6.99e-06   HEALTHY
1    0.20   -1.0700e+03   -2.8616e+20    +2.5047e+23    3.36e-06
1    0.40   -5.4812e+03   -7.1094e+20    +3.3902e+24    1.07e-06
1    0.80   -2.2334e+04   -2.3097e+21    +4.5120e+25    5.41e-07
2    0.00   +6.6435e+02   -1.1113e+20    -7.6692e+22    1.31e-05   HEALTHY
2    0.02   +6.9838e+02   -1.1074e+20    -8.0173e+22    1.37e-05   HEALTHY
2    0.05   +7.4967e+02   -1.1035e+20    -8.5540e+22    1.47e-05   HEALTHY
2    0.10   +8.3581e+02   -1.1023e+20    -9.4964e+22    1.64e-05   HEALTHY
2    0.20   +1.0106e+03   -1.1190e+20    -1.1621e+23    1.98e-05   HEALTHY
2    0.40   +1.3701e+03   -1.2295e+20    -1.7336e+23    2.61e-05   HEALTHY
2    0.80   +2.1287e+03   -1.7591e+20    -3.9234e+23    3.34e-05   HEALTHY
```

## 3. Findings

1. The registered instrument is verified: all four anchors reproduce the
   committed rows to at most `4.3e-11` relative and are certified on three
   routes with the committed prime set.
2. Health is not a knife edge in general. At gamma_7 and gamma_8 the healthy
   set has positive extent in the fiber, reaching `sigma = 0.10` in both
   canonical directions, and at gamma_8 in direction 2 it reaches the largest
   registered amplitude `sigma = 0.80`.
3. The fiber is not one-signed. At gamma_8 direction 2 the margin increases
   monotonically, `C = 664.35 -> 2128.7` (factor 3.20), with `D < 0` and
   `det < 0` certified at every registered amplitude. In direction 1 the same
   owner loses health by `sigma = 0.20`. The committed selector is therefore
   not extremal for health: feasible interpolants with a strictly larger
   margin exist.
4. The two gamma_5 owners lose health at the first registered non-zero
   amplitude `sigma = 0.02`. These are also the two smallest committed margins
   in the set (`+1.4948` and `+0.2559`); the ranking of health radius follows
   the ranking of committed margin over the four registered owners.
5. `D < 0` holds in all 56 rows, including every unhealthy row, so the sign
   the binding obligation asks for survives the whole scan. The determinant
   is negative on all 23 healthy rows and on two further rows where `C` has
   just crossed. Under record 1931 a negative `C` marks the reading as
   not-a-healthy-owner; those 33 rows carry no owner sign information.

## 4. Scope

A-H-CONE-MIXED authorizes the health-cone and dual-certificate desk that
record 2003 reserved for a non-empty verdict. It is not a producer theorem,
and it does not change the binding Route A obligation (`D < 0` on the selected
healthy owner) or the COVER layer.

The result is scoped to: these four owners, `delta = 0.10`, one
support-preserving two-copy family, the two most energetic canonical
directions, and the criterion `C > 0 and D < 0 and det < 0` at the registered
`dxi`. Two limitations matter for the next step.

1. Direction selection is worst-case biased. The registered directions are
   the two most energetic eigenvectors of the restricted Gram, and the
   gamma_8 result shows the fiber also contains margin-improving directions.
   A rank-spread scan over the restricted spectrum is the natural
   follow-up, and it is the first question the health-cone desk should
   settle.
2. Nothing here is a statement about all off-line zeros. The scan samples a
   finite fiber at four registered points of the `(delta, gamma)` plane.

## 5. Evidence

- Pre-registration: `docs/proofs/2003_route_a_health_selector_reregistration.md`
- Instrument: `scripts/routea_health_selector_2003.py`
- Data: `results/2003_route_a_health_selector.json`
