# Record 1996 pre-registration — gamma_7/gamma_8 full scale sweep (EXT)

Date: 2026-09-26. Registered BEFORE the run; commit precedes execution.

## Question

1994 left the gamma_7/gamma_8 collapse (C << 0, B01 < 0, det > 0 on all 4
sampled cells) UNATTRIBUTED between height and convention: the 1994b
control showed gamma_5 through the same EXT layer reads the anomaly face
at sc = 0.86 but healthy opposite-gates at sc = 0.92/1.00 (MIXED), so the
C sign is knotted in scale and 2 cells per height cannot decide.

This sweep measures the FULL committed rescue grid at both new heights,
plus the 3 missing gamma_5@EXT knot cells, to answer one question:

```text
Is there ANY scale cell at gamma_7 / gamma_8 whose owner passes the
1931 health screen (C > 0), and if so does any read opposite gates
(C > 0, D < 0, det < 0)?
```

All statements are EXT-scoped: the committed convention (6-ordinate kill
list) does not define an owner above gamma_6, so no claim about the
committed convention at these heights is possible or made.

## Cases (33, all fixed now)

gamma_7 = 37.586178158825671 and gamma_8 = 40.918719012147495 (EXT
ordinates 7/8 from the 1994 rig), each at

```text
sc in {0.86, 0.88, 0.90, 0.92, 0.94}  x  delta in {0.10, 0.20, 0.30}
```

15 cells per height, n = 0, k = 30, xi_max = 40, dxi = 0.004 — identical
instrument to the 1994 EXT rows.

Control completion (gamma_5 = 30.424876125859513210 through EXT,
delta = 0.10): sc in {0.88, 0.90, 0.94} — completing the 1994b knot map
(0.86, 0.92, 1.00 already measured).

## Predictions (fixed before the run)

- P1 (HOST): at least one cell per height reads C > 0; if any such cell
  also reads D < 0 with det < 0, the 1994 anomaly was 2-cell sampling
  and gamma_7/gamma_8 are EXT hosts (height wall refuted at these
  heights).
- P2 (HEIGHT WALL): all 15 cells at a height read C < 0 — certified
  unhealthy across the full grid; the height wall is CONFIRMED at that
  height under EXT.
- P3 (knot consistency): the completed gamma_5@EXT 5-cell map shows a
  sign pattern in sc (not noise), mirroring the committed-convention
  knot structure of 1994's gamma_5 block.

## Verdict rules (fixed before the run)

Per height, over finite non-DEAD rows:

```text
HOST_CONFIRMED     >= 1 CERTIFIED cell with C > 0, D < 0, det < 0
HEALTHY_NO_WIRE    >= 1 cell with C > 0 but no D < 0 cell
HEIGHT_WALL        0 cells with C > 0
```

A CERTIFIED cell requires: density finite, cond <= 1e8, pin errors
<= 1e-6, spread_D < 1/3, AND n_primes <= 4000 (three live routes; the
1994 instrument law — rows above 4000 prime powers lose route Ap and
their spread 0.0 is "one route", not agreement). Rows with n_primes > 4000
are labeled INSTRUMENT and can corroborate signs but never certify.
DEAD row rules identical to 1983/1994 (non-finite, cond > 1e8, pins
> 1e-6).

gamma_5@EXT completion rows are reported but do not gate the verdict
(post-hoc map completion, labeled as such).

## Cost

33 cells x ~22 s = ~12 min single-process in WSL, same as 1994.

No gate-sign theorem, no determinant theorem, no RH claim. This is a
measurement whose outcomes change which experiment class Route A runs
next, nothing else.
