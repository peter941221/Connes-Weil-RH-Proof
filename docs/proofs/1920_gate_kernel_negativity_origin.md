# 1920 — Where the Cut-2 negativity lives: prime oscillations, not the sigma tail

Date: 2026-09-24.

Status: NUMERIC structural scouting (three probe scripts). No Lean brick, no
gate sign proved, no RH claim. Findings: the arch channel's variance-gap
criterion is a SPREAD criterion for the density `W` (holds for bump widths
`c <= 1.3`, fails for concentrated `W` and flips sign for `c >= 1.6..2.0`);
the full kernel's negative mass is created by the visible PRIME sum inside
the sigma-positive central zone (share `>= 99.7%` at `c >= 1.0`, `100.0%` at
`c >= 2.0`); across `c = 1.3 .. 3.0` the prime block alone is strictly
negative on 10/10 rows with criterion ratio `R_prime` in `1.38 .. 2.06`,
while the arch and cross blocks flip positive and the full determinant
becomes a residual of large cancelling blocks.

## Probe A: the arch-channel criterion is a spread criterion

`scripts/fourpoint_gate_kernel_stress_1920.py`. The arch measure is
`mu = sigma(2*pi*xi) * W * dxi`, and `sigma` has its single sign flip at
`u* = 6.289836` (`xi* = 1.0011`), so the sign split of `mu` is a threshold
split. Stress over `W` families (normalized peaks), criterion ratio
`R = (f*Var_- + f*(1+f)*Delta^2) / ((1+f)*Var_+)`, hold iff `R > 1`
(only meaningful when `A = mu(R) > 0`):

```text
+---------------+--------+-----------+----------------+----------+--------+
| W             | gamma  | f         | Var-/Var+      | R        | hold   |
+---------------+--------+-----------+----------------+----------+--------+
| bump c=0.5    | 14.13  | 0.00916   | 5.53e+05       | 5.02e+03 | True   |
| bump c=0.5    | 30.42  | 0.00916   | 1.82e+04       | 1.73e+02 | True   |
| bump c=1.0    | 14.13  | 0.00066   | 5.53e+04       | 3.68e+01 | True   |
| bump c=1.0    | 30.42  | 0.00066   | 2.41e+03       | 3.42e+00 | True   |
| bump c=2.0    | 14.13  | 0.00002   | 1.18e+04       | 4.37e-01 | FAIL   |
| bump c=4.0    | 14.13  | 0.00000   | 6.50e+03       | 2.24e-02 | FAIL   |
| gauss s=0.3   | 14.13  | 0.00003   | 6.21e+00       | 8.55e-03 | FAIL   |
| gauss s=1.0   | 14.13  | 0.16614   | 3.77e+01       | 3.33e+01 | True   |
| gauss s=1.0   | 30.42  | 0.16614   | 1.25e+02       | 9.61e+01 | True   |
| box U=1.20    | 14.13  | 0.01773   | 2.83e-01       | 8.21e-01 | FAIL   |
| box U=2.00    | 14.13  | 0.52098   | 5.84e+00       | 8.01e+01 | True   |
| box U=2.00    | 30.42  | 0.52098   | 1.84e+01       | 1.35e+02 | True   |
+---------------+--------+-----------+----------------+----------+--------+
| gauss s=3.0   | 14.13  | (A < 0, out of class: C > 0 pivot fails)          |
| gauss s=10.0  | 14.13  | (A < 0, out of class)                             |
| box U=5.00    | 30.42  | (A < 0, out of class)                             |
+---------------+--------+-----------+----------------+----------+--------+
```

Verdict: the arch criterion holds exactly when the density has sufficient
SPREAD in the `omega^4`-weighted sense (bump `c <= 1.3`, gauss `s >= 1`,
wide box) and fails for concentrated densities (narrow gauss, wide bump:
`|ghat|^2` width `~ 1/c` shrinks the negative mass to `f -> 0`). `R`
collapses with `c` like `5.0e3 -> 3.7e1 -> 1.7 -> 0.44 -> 0.02`
(`c = 0.5, 1.0, 1.3, 2.0, 4.0` at `gamma = 14.13`). Rows with `A < 0` are
outside the owner class (`C > 0` is a committed pivot) and their negative
mass exceeds the total, so `det > 0` automatically.

## Probe B: block decomposition across widths

`scripts/fourpoint_gate_kernel_wide_1920.py`. Determinants of the three
polarization blocks of `det_full = det_arch + det_prime + det_cross` in the
kernel form (record 1919 machinery; identity self-check `det` vs
`A^2 * Var_nu` at `<= 1.6e-8` over all rows, `<= 3.5e-13` for `c <= 1.3`):

```text
+------+--------+-------------+-------------+-------------+-------------+
| c    | gamma  | det_full    | det_arch    | det_prime   | det_cross   |
+------+--------+-------------+-------------+-------------+-------------+
| 1.3  | 14.13  | -7.03e+05   | -3.49e+05   | -1.12e+05   | -2.42e+05   |
| 1.3  | 21.02  | -9.60e+05   | -2.28e+05   | -4.87e+05   | -2.45e+05   |
| 1.6  | 14.13  | -1.84e+05   | -4.25e+04   | -1.21e+05   | -2.05e+04   |
| 1.6  | 21.02  | -2.20e+05   | +9.15e+04   | -5.27e+05   | +2.16e+05   |
| 2.0  | 14.13  | -6.62e+04   | +3.77e+04   | -1.83e+05   | +7.89e+04   |
| 2.0  | 21.02  | -2.87e+05   | +2.18e+05   | -9.14e+05   | +4.09e+05   |
| 2.4  | 14.13  | -1.18e+04   | +5.33e+04   | -2.38e+05   | +1.73e+05   |
| 2.4  | 21.02  | -1.14e+04   | +2.59e+05   | -1.13e+06   | +8.63e+05   |
| 3.0  | 14.13  | -8.44e+03   | +5.56e+04   | -3.82e+05   | +3.18e+05   |
| 3.0  | 21.02  | -7.88e+04   | +2.69e+05   | -1.89e+06   | +1.54e+06   |
+------+--------+-------------+-------------+-------------+-------------+
```

Criterion ratios (hold iff `R > 1`, computed per block where `A > 0`):

```text
+------+--------+----------+----------+----------+---------+
| c    | gamma  | R_full   | R_arch   | R_prime  | hold    |
+------+--------+----------+----------+----------+---------+
| 1.3  | 14.13  | 3.5129   | 6.2845   | 1.6905   | all     |
| 1.3  | 21.02  | 1.7916   | 1.6877   | 2.0574   | all     |
| 1.6  | 14.13  | 1.5891   | 1.6307   | 1.8320   | all     |
| 1.6  | 21.02  | 1.1423   | 0.7287   | 1.8376   | full+prime |
| 2.0  | 21.02  | 1.1187   | 0.3474   | 1.8369   | full+prime |
| 2.4  | 21.02  | 1.0029   | 0.1929   | 1.5288   | full+prime |
| 3.0  | 21.02  | 1.0102   | 0.0921   | 1.3776   | full+prime |
+------+--------+----------+----------+----------+---------+
```

Readings:

1. `det_prime < 0` on 10/10 rows at every scanned width and height, with
   `R_prime` in `1.38 .. 2.06` — the prime-only channel's variance gap is the
   one structurally robust block.
2. `det_arch` flips positive between `c = 1.3` and `1.6` at `gamma = 21.02`
   and between `1.6` and `2.0` at `gamma = 14.13`; `det_cross` follows the
   arch sign in the wide regime.
3. In the wide regime the full determinant is therefore a residual of large
   cancelling blocks: at `c = 3.0, gamma = 21.02` the prime block `-1.89e6`
   must beat `det_arch + det_cross = +1.81e6` for a net `-7.88e+04` (4% of
   the block scale). This is the mechanism behind the record-1918 boundary
   thinness (`~1e-7` relative margins at `c = 3.0`).
4. `R_full -> 1` from above as `c` grows (`3.51, 1.59, 1.14, 1.01, 1.01` at
   `gamma = 14.13`): the positive and negative parts of the full measure
   become nearly P-equidistributed.

## Probe C: origin of the negative mass

`scripts/fourpoint_gate_kernel_origin_1920.py`. Since `sigma > 0` exactly on
`|xi| < xi*`, every negative value of the full kernel inside that central
zone is created by the visible prime sum. Negative-mass shares:

```text
+------+-----------+-----------+-----------+-----------+---------+--------+
| c    | W_inside  | N_in      | N_out     | N_arch    | N_in/N  | K'0    |
+------+-----------+-----------+-----------+-----------+---------+--------+
| 0.5  | 6.30e-02  | 8.54e-03  | 1.21e-03  | 8.79e-04  | 0.876   | 0.98   |
| 1.0  | 1.32e-01  | 7.86e-02  | 1.99e-04  | 2.02e-04  | 0.997   | 5.85   |
| 1.3  | 1.73e-01  | 1.93e-01  | 1.85e-04  | 8.77e-05  | 0.999   | 9.94   |
| 2.0  | 2.66e-01  | 8.95e-01  | 8.62e-05  | 2.06e-05  | 1.000   | 24.38  |
| 3.0  | 3.99e-01  | 5.23e+00  | 3.48e-05  | 3.50e-06  | 1.000   | 75.19  |
+------+-----------+-----------+-----------+-----------+---------+--------+
```

(`W_inside` = normalized `W` mass on `|xi| < xi*`; `N_arch` = arch-only
negative mass, i.e. the sigma tail; `K'0 = K_prime(0) = 2*sum Lambda(n)/sqrt n`
over the visible set.) The prime kernel amplitude crosses the sigma scale
(`sigma(0) = 5.372`) already at `c = 1.0` and grows to `75.2` at `c = 3.0`,
matching the arch flip point (`K'0 ~ 10 .. 25` when `det_arch` turns
positive).

## Route reading

The Cut-2 obligation `det_full < 0` splits into a robust and a delicate
part at every measured width:

```text
robust:    Q(K_prime) < 0      (prime-only channel; R_prime 1.38 .. 2.06)
delicate:  -Q(K_prime) > Q(sigma) + 2*B(sigma, K_prime)
           (arch + cross domination; both flip positive in the wide regime)
```

`K_prime(xi) = 2*sum_{visible n} (Lambda(n)/sqrt(n)) cos(2*pi*xi*log n)` is
an explicit real trig polynomial oscillating at scales `~ 1/(2c)` against the
width-`~1/c` density `W`; `Q(K_prime) < 0` is an oscillation-versus-smooth-
density statement (positive/negative half-waves sampling a smooth `P^2 W`
weight at shifted locations), which is the natural next analytic target. The
cross-domination inequality is a comparison of three explicit functionals of
the same density.

Consequences for the campaign: (i) the earlier plan to "attack the arch
channel first" is valid only for owners with `c <= 1.3`, where the arch
channel alone holds; for wide owners (`c >= 2`) the arch and cross blocks are
positive and the prime block carries the entire obligation with a thin net
margin; (ii) the instrument-certified window of record 1918 (`c <= 1.3`,
min `|disc|/ddisc_cert = 30.4`) is exactly the window where the arch channel
also holds — no conflict; (iii) any analytic estimate covering wide owners
must be sharp to better than the 4% block-residual at `c = 3.0` unless it is
channel-structural.

No gate sign on the selected owner is proved; all numbers live on the
committed-class bump family with the record-1919 kernel form, whose arch
channel matched the E3 engine to `2.6e-8`.

## Verification

Probe scripts `scripts/fourpoint_gate_kernel_stress_1920.py`,
`scripts/fourpoint_gate_kernel_wide_1920.py`,
`scripts/fourpoint_gate_kernel_origin_1920.py`; artifacts
`results/1920_gate_kernel_stress.json`,
`results/1920_gate_kernel_wide.json`,
`results/1920_gate_kernel_origin.json`; logs
`logs/1920_kernel_stress.log`, `logs/1920_kernel_wide.log`,
`logs/1920_kernel_origin.log` in the Linux-side build mirror. Runtime
`< 1 s` per probe on 16 CPUs; the wide scan carries the record-1919 identity
self-check (`det` vs `A^2 * Var_nu`, relative residual `<= 1.6e-8` over all
rows, `<= 3.5e-13` on the `c <= 1.3` rows). No
Lean module is added or changed by this record.