# Record 1996 — gamma_7/gamma_8 full scale sweep: BOTH HEIGHTS HOST

Date: 2026-09-26.

Status: outcome record for the pre-registered case set of
`1996_gamma78_full_sweep_preregistration.md` (commit a966fa70). Rig
`scripts/routea_gamma78_full_sweep_1996.py` (smoke row bit-for-bit
reproduces 1994's gamma_7 sc = 0.90 row). No Lean brick, no gate-sign
theorem, no determinant theorem, no RH claim.

## Verdict (pre-registered rules)

```text
G7_HOST_CONFIRMED + G8_HOST_CONFIRMED

P1 (HOST): CONFIRMED at BOTH heights — each has a certified
    C > 0, D < 0, det < 0 cell at every delta.
P2 (HEIGHT WALL): REFUTED — no height wall through gamma_8 under EXT.
P3 (knot consistency): CONFIRMED — C-sign is a scale knot whose
    position moves with the ordinate; see the maps below.

1994's attribution question is CLOSED: the gamma_7/gamma_8 "collapse"
was a 2-cell sampling artifact. The sampled cells (0.90, 1.00) sit
exactly where those heights' knots read C < 0; each height's health
window exists and was simply not sampled.
```

33/33 rows finite, all with three live routes (n_primes 1368-2894, all
below the 4000 Ap guard — no INSTRUMENT rows in this sweep), pin errors
<= 1.1e-13, cond <= 3.7e+04.

## Host cells (all certified: 3 routes, spread_D < 1/3, pins < 1e-6)

```
height  delta sc    n_primes C           B01          D             det
37.5862 0.10  0.92  2393     +1.7330e+02 -8.2862e+10  -2.0359e+20   -4.2148e+22
37.5862 0.20  0.92  2393     +3.5625e+01 -1.6518e+10  -4.0642e+19   -1.7207e+21
37.5862 0.30  0.92  2393     +1.3423e+01 -6.0141e+09  -1.4823e+19   -2.3514e+20
40.9187 0.10  0.88  1647     +6.6435e+02 -5.3526e+10  -1.1113e+20   -7.6692e+22
40.9187 0.20  0.88  1647     +1.4189e+02 -1.1669e+10  -2.4213e+19   -3.5717e+21
40.9187 0.30  0.88  1647     +5.9790e+01 -4.9668e+09  -1.0286e+19   -6.3964e+20
```

The health window (C > 0 band) is delta-stable at each height, and its
scale position is ordinate-dependent:

```text
ordinate  C-sign over sc = 0.86 0.88 0.90 0.92 0.94   window
gamma_5@EXT (map, delta=0.10, with 1994b cells)
30.4249   -      -    +    +    +  (0.90..0.94; 1.00 one-route +)  wide right
37.5862   -      -    -    +    -                             single 0.92
40.9187   -      +    -    -    -                             single 0.88
```

## Second reading (post-hoc, labeled as such): the corrected 1981
## obligation

Map-103's binding Cut-2 obligation is the single sign `D < 0` with the
healthiness-free consumer (`diagNegWitness`, denominator
`2(|B| + |C| + 1)` always positive). Under that reading, EVERY row of
this sweep passes: D < 0 on 33/33 cells with certified spreads
(<= 3.1e-05), margins |D| from 1.1e+12 to 7.7e+20. The 1994 gamma_7/8
sc = 0.90 rows were already D < 0-certified cells under the corrected
obligation; the 1994 "anomaly" (C < 0, det > 0) only killed the 1902
opposite-gates certificate face, never the corrected consumer.

Why the health screen still gates FORMAL consumption: the committed RH
spine constructs a HEALTHY owner from a hypothetical off-line zero;
1931 forces ICgate(g^2) = C > 0 on healthy detectors, so a C < 0 rig
reading marks the constructed owner as not-an-instance of the spine's
class even though its D < 0 would satisfy the healthiness-free
consumer. Both readings therefore matter and are kept distinct.

## What this changes

- The opposite-gates certificate now has certified hosts at every
  measured ordinate gamma_1 .. gamma_8 (gamma_1..gamma_6 committed
  convention, 1983 + 1994; gamma_7/gamma_8 EXT, this record). No height
  wall exists through gamma_8; the 1994 attribution question is closed
  as a sampling artifact.
- New empirical law for the lane: the C health window is ORDINATE-
  DEPENDENT and single-scale at the higher ordinates (0.92 at gamma_7,
  0.88 at gamma_8) — any future height extension must sweep scale, not
  sample it.
- Route A's owner-class sign question is now empirically clean through
  gamma_8 under EXT; the COVER layer (all rho, analytic) remains the
  open frontier and is untouched by this measurement.

## Files

- pre-registration: `docs/proofs/1996_gamma78_full_sweep_preregistration.md`
- rig: `scripts/routea_gamma78_full_sweep_1996.py`
- results: `results/1996_gamma78_full_sweep.json`

See also: 1994 (2-cell sampling + instrument law), 1994b (control),
1902 (opposite-gates certificate), 1931 (health screen), 1981
(corrected D < 0 obligation), 1983 (height probe).
