# Record 1994 — opposite-gates height audit (gamma_5 rescue + gamma_7/8 extension)

Date: 2026-09-26.

Status: measurement record executing the pre-registered case set of
`1994_opposite_gates_height_preregistration.md` (commit e60c2ed1), plus one
post-hoc control (record 1994b). No Lean brick, no gate-sign theorem, no
determinant theorem, no RH claim.

## Verdict (pre-registered rules)

```text
G5_RESCUED + G7_NONE + G8_NONE + DET_ANOMALY

P1 (gamma_5 hole is a band artifact): CONFIRMED — 6/15 rescue cells read
    C > 0, D < 0 with certified route spreads, sign-stable across all
    three deltas.
P2 (gamma_7/gamma_8 host opposite gates at the sampled cells): FAILS —
    0/2 cells at each height.
P3 (det < 0 uniform): FAILS — 4 height-extension rows read det > 0,
    the first determinant-positive rows in this family.

Attribution of the det > 0 anomaly: UNRESOLVED between height and
    convention (control 1994b reads MIXED). See "Control" below.
```

## What was measured

Rig: `scripts/routea_opposite_gates_height_1994.py` (reusing the committed
r59/r80/r83/r81 owner machinery verbatim; only the kill list, width pools,
and ordinate set were extended for the height rows). Instrument gate from
1983 kept: a row is DEAD if non-finite, cond > 1e8, or pin error > 1e-6.
No row was DEAD: 19/19 finite, pins <= 5.0e-13, cond <= 3.9e+04.

gamma_5 rescue (committed convention: 6-ordinate kills, M = 13):

```
delta sc    n_primes C           B01          D             det           face
0.10  0.86  146      +3.8489e+02 +7.3362e+06  -1.3405e+12   -5.6978e+14   WIRE1
0.10  0.88  162      -7.8742e+01 +1.5296e+07  +1.0110e+12   -3.1357e+14   GAP
0.10  0.90  182      -8.5898e+00 +2.2704e+06  +9.1249e+10   -5.9387e+12   GAP
0.10  0.92  207      +5.7880e+01 +1.6254e+06  -7.6188e+09   -3.0829e+12   WIRE1
0.10  0.94  231      +5.4333e+01 +3.3460e+06  +1.2588e+11   -4.3562e+12   WIRE2
0.20  0.86  146      +8.0092e+01 +1.9042e+06  -2.4215e+11   -2.3021e+13   WIRE1
0.20  0.88  162      -1.9703e+01 +2.3659e+06  +1.6829e+11   -8.9134e+12   GAP
0.20  0.90  182      -1.4621e+00 +3.5834e+05  +1.3966e+10   -1.4883e+11   GAP
0.20  0.92  207      +9.6106e+00 +2.6579e+05  -1.6961e+09   -8.6946e+10   WIRE1
0.20  0.94  231      +9.7202e+00 +5.9870e+05  +2.2580e+10   -1.3896e+11   WIRE2
0.30  0.86  146      +2.7250e+01 +8.1359e+05  -6.9213e+10   -2.5480e+12   WIRE1
0.30  0.88  162      -6.9983e+00 +6.2839e+05  +4.7165e+10   -7.2495e+11   GAP
0.30  0.90  182      -4.7177e-01 +1.0082e+05  +3.8173e+09   -1.1965e+10   GAP
0.30  0.92  207      +2.8190e+00 +7.7706e+04  -6.4635e+08   -7.8603e+09   WIRE1
0.30  0.94  231      +3.1201e+00 +1.9449e+05  +7.3850e+09   -1.4784e+10   WIRE2
```

Facts on the gamma_5 block:

- Opposite gates (C > 0 and D < 0, the 1902 certificate shape): 6/15 cells
  — sc = 0.86 and sc = 0.92 at every delta. The 1983 "hole" at gamma_5 was
  a sampling artifact of the 0.90 rescue band, exactly prediction P1.
- det < 0 on 15/15 cells (the three sc = 0.94 cells are the WIRE2 face,
  C > 0, D > 0, det < 0; the GAP cells have C < 0 automatically driving
  det < 0).
- The C sign is a function of the scale knot, not of delta: the pattern
  (+, -, -, +, +) at sc = 0.86 .. 0.94 is identical at all three deltas.
  D is exactly anti-correlated with C on these rows (C > 0 <=> D < 0).

Height extension (EXT convention: 10-ordinate kills, M = 17, kill pool to
5.4, support radius 10.8):

```
gamma   sc    n_primes routes  C           B01           D             det           note
37.5862 0.90  1985     AApB    -9.8006e+02 -2.4371e+11   -7.7167e+20   +6.9688e+23   certified
37.5862 1.00  5121     AB      -8.1025e+02 -4.1027e+10   -1.0152e+20   +8.0575e+22   1 certified route
40.9187 0.90  1985     AApB    -1.3051e+03 -2.2976e+11   -7.1124e+20   +8.7541e+23   certified
40.9187 1.00  5121     AB      -2.1229e+02 -6.1992e+10   -1.5922e+20   +2.9958e+22   1 certified route
```

All four rows read C << 0 with B01 < 0 and det > 0 — the first
determinant-positive rows ever measured in this family, and the first
negative B01 entries.

## Instrument caveat (must travel with the sc = 1.00 rows)

The sc = 1.00 rows have n_primes = 5121. The committed r59 instrument
drops the exact-transform route Ap above 4000 prime powers
(`gate_entries`: `if len(pset) <= 4000`), and `route_spread` compares the
CERTIFIED_ROUTES pair ("Ap", "B"); with Ap missing it degenerates to the
single surviving certified route and reports spread exactly 0.0. A
degenerate floor reports nothing (law F52 discipline): those two rows are
sign-consistent but INSTRUMENT-LIMITED, not spread-certified. The sc = 0.90
rows carry all three routes with spread_D = 3.1e-05, so the C < 0, det > 0
anomaly itself is certified.

## Control (record 1994b, post-hoc, labels fixed before the run)

`scripts/routea_ext_convention_control_1994b.py`: re-measure gamma_5
(delta = 0.10) through the SAME EXT layer, to separate convention from
height. Pre-fixed labels: CONVENTION_ARTIFACT (C < 0 at both 0.86 and
0.92), HEIGHT_EFFECT (C > 0 at both), MIXED otherwise.

```
sc    n_primes C           B01          D             det           reading
0.86  ~1985    -2.8803e+01 -6.9715e+06  -8.6360e+12   +2.0014e+14   anomaly face, certified
0.92  ~1985    +1.4948e+00 +1.1503e+05  -6.3074e+12   -9.4416e+12   opposite gates HOLD
1.00  5121     +6.9190e-01 -6.0128e+05  -1.8612e+15   -1.2881e+15   opposite gates, 1 route
```

Label: MIXED.

Reading:

- The anomaly face (C < 0, B01 < 0, det > 0) is REPRODUCIBLE at gamma_5 by
  switching to the EXT convention at sc = 0.86 — a cell where the
  committed convention reads C = +384.9. So the collapse is NOT purely
  height-driven.
- But EXT does not uniformly break the C entry: gamma_5 through EXT at
  sc = 0.92 and 1.00 reads C > 0 with opposite gates holding. So it is
  NOT a pure convention artifact either.
- Conclusion: the C sign under EXT is knotted in the scale variable
  (same knot structure the gamma_5 block shows under the committed
  convention), and two cells per height cannot separate height from
  knot position. The height question stays OPEN; deciding it requires a
  full sc sweep at gamma_7 (the 0.86 .. 0.94 grid), which was not
  pre-registered and was not run.

## Health screen (1931) as the new necessary condition

Record 1931 (`not_ICgate_nonpos_of_healthyOrbitGeometry`) forces
ICgate(g^2) > 0 for every healthy detector. The rig's C entry is that
gate value. Therefore every C < 0 row above (the four EXT height rows and
the gamma_5@EXT 0.86 control cell) certifies that the constructed
owner/detector pair is NOT healthy under that convention — the 1902
opposite-gates certificate is dead at those cells before D is even read.
Any future height extension must first pass the C > 0 health screen
across its scale grid; only then does the D < 0 measurement mean anything.

## What this changes

- Route A / 004 recommendation #2 is EXECUTED: the opposite-gates
  certificate is height-robust on the committed convention through
  gamma_6 (1983: gamma_1..gamma_4, gamma_6; 1994: gamma_5 rescued), and
  the extension frontier is now a health-screen + scale-knot problem,
  not a single anomalous reading.
- No change to any Route A or Route B obligation: the committed-convention
  basis (gamma_1 .. gamma_6 owners) is unchanged and now hole-free.
- New instrument law for the lane: rows with n_primes > 4000 are
  single-certified-route by construction (Ap cost guard) and must be
  labeled instrument-limited; spread 0.0 there is not agreement.

## Files

- pre-registration: `docs/proofs/1994_opposite_gates_height_preregistration.md`
- rig: `scripts/routea_opposite_gates_height_1994.py`
- results: `results/1994_opposite_gates_height.json`
- control rig: `scripts/routea_ext_convention_control_1994b.py`
- control results: `results/1994b_ext_convention_control.json`

See also: 1902 (opposite-gates certificate), 1917 (face trichotomy),
1931 (health screen), 1981 (offline owner + diag-only obligation),
1983 (height probe this audit extends).
