# 1959 — Committed-owner density probe: `W(0) = 0`, a 1e-3 residual of a 1e3..8e4 cancellation, and the realized map-106 endpoint

Date: 2026-09-25.

Status: NUMERIC probe. One committed rig,
`scripts/fourpoint_owner_density_1959.py` (modes `--calib`, `--refine`,
`--scan`, `--cardinal`; results `results/1959_fourpoint_owner_density.json`,
`results/1959_refinement.json`, `results/1959_scale_scan.json`). No Lean
brick, no gate sign proved, no RH claim.

What is established numerically, and what is not:

```text
+-------------------------------------------------+-----------------------+
| reading                                          | status                |
+-------------------------------------------------+-----------------------+
| W(0) = 0 exactly for every admissible owner      | COMMITTED (not numeric |
|                                                  | -- see 1.1)           |
| density peaks at |xi| = 1.6 .. 3.6, mass beyond   | measured (beyond 4:   |
| |xi| > 4 <= 6.6e-05, beyond 6 <= 6e-41            | <= 6.6e-05)           |
| gate entries are a residual of an arch/prime      | measured (ratio up to |
| cancellation                                      | 7.2e3 on C, 8e4 on D) |
| map 106 section 2 endpoint C > 0, b > 0, det < 0  | realized at 2 knob    |
| realized on the committed owner shape             | points (scale 0.90 at |
|                                                  | k=30, k=40 at scale   |
|                                                  | 1.00) of 36 rows      |
| Cut-2 witness (some nonzero lambda, Q(lam) <= 0)  | 36/36 rows            |
| C > 0 (committed healthiness hypothesis)          | 11/36 rows            |
| robustness of the endpoint in the free knob       | NONE found: b flips   |
|                                                  | sign between near     |
|                                                  | knots (delta scale    |
|                                                  | 0.02 apart)           |
+-------------------------------------------------+-----------------------+
```

## 1. The object, and what of it is committed

### 1.1 The owner and its density

Source-read, not assumed (record 1959 continues 1918/1919/1920 in the
map-106 lane; all line references are to the committed tree):

```text
selectedOwner base correction n
  = SelectedWeilSquareOwner.ofCompactLogTest
      (halfDensityShift ((convolutionIterate base n).convolution correction))
    [ConnesWeilRH/Source/CCM25Concrete/UnscaledYoshidaSelectedOwner.lean:93]
laplaceAt (halfDensityShift f) s = laplaceAt f (s + 1/2)
    [ibid.:54]
laplaceAt (selectedOwner ...).sourceTest (z - 1/2)
  = laplaceAt ((convolutionIterate base n).convolution correction) z
    [ibid.:117]
```

Hence, with `L_raw = laplaceAt ((convolutionIterate base n).convolution
correction)` and `L_f(s) = laplaceAt f (s + 1/2)`,

```text
L_sourceTest(s) = L_base(s + 1/2)^(n+1) * L_corr(s + 1/2)
W(xi) = |L_sourceTest(1/2 - 2*pi*i*xi)|^2
      = |L_base(1/2 - 2*pi*i*xi)|^(2(n+1)) * |L_corr(1/2 - 2*pi*i*xi)|^2
```

`W` is the density of the convolution square of the owner test, i.e. the
`W = |ghat|^2` of record 1919. The Cut-2 entries are its moments against the
four-point quartic `P` of the orbit nodes,

```text
C  = int K * W            b = B01 = int K * W * P
D  = int K * W * P^2      det = C*D - b^2
K(xi) = sigma(2*pi*xi) + 2 * sum_n (Lambda(n)/sqrt n) cos(2*pi*xi*log n)
```

**Why `W(0) = 0` is committed, not measured.** The raw node `1/2` is in the
committed node set `[C1HealthyYoshidaUnscaledOrbit.lean:33]`, its committed
target value is `0` `[ibid.:43]`, and the committed assembly proves

```text
have hhalf : laplaceAt ((convolutionIterate base n).convolution correction)
    (1/2) = 0            [ibid.:567-575, via htargetValues at the node 1/2]
have hbaseTargets : forall w, laplaceAt base w.1 = 1   [ibid.:544-547]
```

With the committed Hermitian pairing `[UnscaledYoshidaSelectedOwner.lean:153]`,
`W(0) = |L_base(1/2)|^(2(n+1)) * |0|^2 = 0` for **every** admissible
`(base, correction, n)`. The probe confirms it at machine level
(`W(0) <= 5e-24` on all 27 rows, mostly 1e-43..1e-52; the designed base has
`L_base(1/2) = 1` to 1.8e-15, matching `hbaseTargets`).

### 1.2 The representative actually measured

The committed `base` is produced by a noncomputable Mathlib-bump construction
and is not a computable object, so the probe measures the **committed shape**
on an explicit admissible representative (mode `design`, the default):

```text
f_j(x) = A_j * phi(x; a_j, k) * exp(i * theta_j * x),   |x| < a_j
phi(x; a, k) = exp(-k/(1 - (x/a)^2))         (C-infinity, compact, Gevrey k)
theta_j = -Im(target node j)                 (per-node carrier frequency)
```

with 8 nodes (4 orbit nodes + `rho + 1/2`, `1/2`, `1`, `3/2`), distinct
per-node widths `a_j` (a single fixed width makes the 8x8 interpolation system
numerically singular: cond 4.3e16, interpolant = pure roundoff; distinct
widths give cond 1.3e4 and pins at 1e-15), amplitudes `A_j` from two 8x8
solves (base targets `1` on all nodes, correction targets
`healthyUnscaledTargetValue`). Structure columns of the 27-row grid:

```text
+-------+-------+---+-------+------+--------+--------+---------+------+-------+
| delta | gamma | n | scale | k    | pinB   | pinC   | xipk    | even | T/g   |
+-------+-------+---+-------+------+--------+--------+---------+------+-------+
| 0.05  | 14.13 | 0 | 1.00  | 30   | 1.4-15 | 5.7-14 | 2.008   | 1.00 | 1.213|
| 0.05  | 14.13 | 1 | 1.00  | 30   | 1.4-15 | 5.7-14 | 2.472   | 1.00 | 1.213|
| 0.10  | 14.13 | 1 | 1.00  | 30   | 1.4-15 | 5.7-14 | 2.472   | 1.00 | 1.213|
| 0.30  | 14.13 | 0 | 1.00  | 30   | 1.7-15 | 1.8-14 | 2.484   | 1.00 | 1.206|
| 0.05  | 21.02 | 0 | 1.00  | 30   | 1.8-15 | 8.5-14 | 3.104   | 1.00 | 1.140|
| 0.05  | 21.02 | 1 | 1.00  | 30   | 1.8-15 | 8.5-14 | 3.568   | 1.00 | 1.140|
| 0.30  | 21.02 | 1 | 1.00  | 30   | 1.9-15 | 1.6-14 | 3.128   | 1.00 | 1.140|
| 0.05  | 14.13 | 2 | 0.50  | 30   | 1.4-15 | 1.7-12 | 1.604   | 0.83 | 1.418|
| 0.30  | 21.02 | 2 | 0.50  | 30   | 5.1-15 | 3.0-12 | 2.076   | 1.00 | 1.693|
+-------+-------+---+-------+------+--------+--------+---------+------+-------+
  pinB = max |L_base - 1|, pinC = max |L_corr - y| at the 8 nodes;
  xipk = the peak abscissa (gamma/2pi = 2.2496 at gamma_1, 3.3458 at
  gamma_2); even = evenness defect max|W - W(-.)| / max|W| <-- the density is
  essentially maximally asymmetric; T/g = T_need / gamma, the strip height at
  which the designed base first satisfies the committed contraction
  (max|L_base| = 1.00..1.44 on the scanned grid).  Gamma_1 = 14.1347...
  and Gamma_2 = 21.0220... are the first two ordinates; rho = 1/2 + delta +
  i*gamma is a HYPOTHETICAL off-line zero, not a zero of zeta.
```

Mass confinement, measured at the peak and at the cuts:

```text
+------------------+-------------+---------+---------+---------+---------+
| row              | peak |xi|    | > 2     | > 4     | > 6     | > 28    |
+------------------+-------------+---------+---------+---------+---------+
| d=.05 g1 n=0 sc=1| 2.008       | 7.4e-01 | 1.8e-26 | 8.1e-53 | 2.8e-53 |
| d=.05 g2 n=0 sc=1| 3.104       | 1.0e+00 | 6.6e-05 | 5.5e-41 | 1.4e-49 |
| d=.05 g1 n=2 .5  | 1.604       | 3.4e-01 | 9.8e-09 | 8.2e-24 | 7.7e-105|
| d=.05 g1 n=0 .9  | 1.940       | 6.1e-01 | 5.2e-21 | 1.0e-46 | 1.6e-53 |
+------------------+-------------+---------+---------+---------+---------+
  fractions of the total mass of W beyond |xi| > cut
```

The density is spread over `|xi| <~ 4` (worst mass beyond 4 is 6.6e-05, at
`gamma_2`), which is what keeps the visible prime book affordable
(`n_primes = 465` at support radius 8, 15040 at radius 12). This contrast
with the cardinal base of section 1.3 is the whole reason the designed family
is usable. The representative is admissible on exactly the committed
hypotheses that are checkable numerically: support (from the window widths),
pins, contraction, and the vanishing at `1/2, 1, 3/2`.

### 1.3 The cardinal mode is a documented limitation, not a verdict

Mode `--cardinal` builds the owner from the committed 1958 cardinal
interpolation formulas (`cardinalRaw` with the actual Mathlib bump seed,
`r = 1`) and cannot produce a gate reading:

```text
+----------------------------+--------------------------------------------+
| pins max |L_base-1|        | 3.3e-16  (exact)                           |
| W(0)                       | 0.0e+00  (exact)                           |
| density peak               | |xi| = 10.44   (gamma/2pi = 2.25)           |
| mass beyond |xi| > 4       | 99.9 %                                     |
| mass beyond |xi| > 8       | 81.8 %                                     |
| mass beyond |xi| > 45      | < 1e-4                                     |
| |L_base| at height 2*pi*30 | 10.6                                       |
| strip contraction, t <= 150| max |L_base| = 1.44e+02, T_need = none     |
+----------------------------+--------------------------------------------+
```

i.e. this explicit interpolation base puts essentially all of its density
outside the `|xi| <~ 4` confinement of the designed family (section 1.2) and
fails the committed strip contraction on the scanned range, so its gate
integrals would be truncation-sensitive and its prime book would extend far
beyond the affordable direct route. Recorded in
`results/1959_cardinal_base_limitation.json`. This is a statement about the
numerical usability of this explicit base, not about the correctness of the
committed construction, whose contraction is produced by a separate
quadratic-bound route.

## 2. Instrument: three routes, one certified pair, and a phase sign

### 2.1 Calibration (`--calib`)

On `f(xi) = exp(-xi^2)`, where `F(x) = int f e^{2 pi i xi x} dxi =
sqrt(pi) exp(-(pi x)^2)` exactly, the dual-grid FFT route is tested alone:

```text
+-----------------+---------------+--------------+-------------+
| grid            | correct sign  | wrong sign   | naive       |
+-----------------+---------------+--------------+-------------+
| [-8,8] n=32000  | rel 5.8e-12   | rel 6.25e-06 | rel 2.00e+00|
| [-8,8] n=32001  | rel 1.16e-11  | rel 6.25e-06 | rel 2.00e+00|
+-----------------+---------------+--------------+-------------+
```

with `Re(fft(f) * dxi * exp(-2 pi i xi_0 x_k)) = int f e^{2 pi i xi x} dxi`
the correct convention, `xi_0` the grid origin and `x_k` the actual dual-grid
frequency. Two traps this probe hit and fixed, both recorded because they
survive a careless test: (i) the phase must be evaluated at the **actual**
frequency `x_k`, not at the requested test point; (ii) on a grid symmetric
about 0 the two sign conventions nearly coincide, so the decisive calibration
grid is asymmetric. The probe's first version carried the wrong sign and
reported order-1 route-A disagreement on the real owner (`C = +10.09` instead
of `+5.05` on the scale-0.90 row); after the fix route A agrees with the
certified pair to `<= 2e-2` on `C` and is still excluded (next paragraph).

### 2.2 Routes

```text
A   phased FFT of the xi-grid (dual grid = fftfreq), spline-interpolated in
    the dual variable to x = log n
Ap  the same samples, no interpolation: per-prime trapezoid on an 8x
    spline-refined xi-grid
B   direct kernel K on the xi-grid, prime sum excluded from K so that
    "arch + prime_B" is not a double count
```

`Ap` and `B` are the certified pair; `A` is recorded but is
interpolation-limited at fixed `xi_max` (it is not convergent in `dxi`) and is
excluded from the error bar. The spread reported in the result JSONs is the
`Ap` vs `B` spread of the **totals**; on rows whose prime book exceeds 4000
entries only `B` is affordable and the spread is reported as 0 with a single
route.

### 2.3 Refinement: the certified pair agrees at `dxi^4`

Five cases x `dxi = 0.008 .. 0.0005` (`xi_max = 8`). Every certified entry is
bit-stable across the whole range (all printed digits identical), and the
`Ap` vs `B` relative difference on the prime channel falls by exactly 16 per
halving of `dxi`:

```text
+----------+-------------+-------------+-------------+-------------+
| dxi      | Ap-B on C   | Ap-B on B01 | Ap-B on D   | 1919 rel    |
+----------+-------------+-------------+-------------+-------------+
| 0.00800  | 4.4e-07     | 7.4e-08     | 1.9e-08     | 6.0e-13     |
| 0.00400  | 2.7e-08     | 4.3e-09     | 1.2e-09     | 4.5e-12     |
| 0.00200  | 1.7e-09     | 2.6e-10     | 7.3e-11     | 2.6e-12     |
| 0.00100  | 1.1e-10     | 1.6e-11     | 4.6e-12     | 2.6e-12     |
| 0.00050  | 6.6e-12     | 1.0e-12     | 2.9e-13     | 1.4e-12     |
+----------+-------------+-------------+-------------+-------------+
  case (delta = 0.05, gamma_1, n = 0, k = 30, scale = 1.0); the quoted
  differences are relative to the prime-channel entry (|prime_C| ~ 690),
  i.e. absolute 3.0e-04 down to 4.5e-09; the "1919 rel" column is
  |det_var - det| / |det| against the channel-split det.
```

At the default `xi_max = 40, dxi = 0.004` the same comparison on the totals is
`5.6e-05` (`C`), `1.9e-06` (`B01`), `1.7e-06` (`D`) on the worst row, i.e.
absolute `1.9e-05` on a `C` of `-0.337` — the same absolute figure the
`xi_max = 8` run gives at the same `dxi`, as it must be if the discrepancy is
a pure `O(dxi^4)` spline effect.

### 2.4 The 1919 identity, and one units trap

`det = A^2 * Var_nu(P)` with `A = mu(R)`, `nu = mu/A`,
`Var_nu(P) = (1+f) Var_+ - f Var_- - f(1+f) Delta^2`, `f = mu_-/A`, is an
identity for any finite signed measure, so it tests that `C, b, D` are the
moments of **one** grid measure. It is homogeneous of degree 2 in the grid
weights: handing over the integrand `K*W` instead of the measure `K*W*dxi`
multiplies `det` by `1/dxi^2`, which reads as a `1e4..1e6` "relative error"
that is really a units error (observed, then fixed). With `dxi` in place the
two algebraic forms of `Var_nu(P)` (two-sided variance and the quartic moment
expansion `Var_nu(v^2 + aa*v)`, `v = (2 pi xi)^2`,
`aa = -2 (gamma^2 - delta^2)`) reproduce the channel-split `det` at
`rel <= 3.3e-05` on 24 of the 27 coarse-grid rows, worst `1.2e-03` (the
`k = 60` row, where the residual's cancellation index `|CD/det|` is 22 and
the certified routes differ by `5.4e-05` on `C`; the propagated bound
`22 * 5.4e-05 = 1.2e-03` matches), and `<= 1.2e-11` on the refined grids.
The check does not re-derive the entries; it verifies that `C, b, D` are the
moments of **one** grid measure, at the accuracy the certified pair's spread
allows.

## 3. The residual structure: the entries are a cancellation remainder

Four contrasted rows, listing the channels separately (and the `D` channel of
one of them):

```text
+-------------------+-------------+-------------+-------------+-----------+
| row               | arch C      | prime C     | full C      | arch/full |
+-------------------+-------------+-------------+-------------+-----------+
| d=.05 g1 n=0 sc=1 | -6.9025e+02 | +6.8991e+02 | -3.3687e-01 | 2.05e+03  |
| d=.05 g1 n=1 sc=1 | -5.3438e+02 | +5.3430e+02 | -7.3768e-02 | 7.24e+03  |
| d=.30 g1 n=1 sc=1 | -9.3803e+00 | +9.3020e+00 | -7.8317e-02 | 1.20e+02  |
| d=.05 g2 n=0 sc=1 | -1.0350e+03 | +1.0358e+03 | +8.0080e-01 | 1.29e+03  |
+-------------------+-------------+-------------+-------------+-----------+
| d=.05 g1 n=1 sc=1 | arch D      | prime D     | full D      | arch/full |
|                   | -2.9152e+09 | +2.9151e+09 | -3.7400e+04 | 7.80e+04  |
+-------------------+-------------+-------------+-------------+-----------+
```

The archimedean channel and the prime channel cancel to 3..5 significant
digits; the deliverable content of the computation is the **sign** of the
remainder. On rows with `n = 0, 1` at the default window the `D` entry
cancels by up to `8e4`. This is why the whole instrument was built around
route agreement and `dxi` stability rather than around absolute accuracy, and
why the representative family is reported with its knobs: at this residual
scale the sign pattern is a property of the window, not a stable property of
the construction.

## 4. Grid readings (27 rows)

`C`, `b`, `D`, `det` are the entries of the measured owner; `lam = b/C`;
`gate_vertex = det/C = Q(b/C)` is the gate at the vertex (defined when
`C != 0`); branch labels: `RAY` = `C < 0, D > 0` (witness at
`lam >= ((b^2 - C*D)^(1/2) - b)/|C|`), `DOOR-A` = `D < 0` with `C > 0`,
`VERTEX` = the map-106 section 2 pattern, `RAY-OR-NONE` = `C < 0` and `D < 0`.
The table prints `C<0` for the `RAY-OR-NONE(C<0)` class. A row with no Cut-2
witness would have to satisfy `C > 0, D > 0, det > 0`; no measured row does.

```text
+-------+-------+---+-------+------+-------------+-------------+-------------+-------------+--------------+
| delta | gamma | n | scale | k    | C           | b           | D           | det         | branch       |
+-------+-------+---+-------+------+-------------+-------------+-------------+-------------+--------------+
| 0.050 | 14.13 | 0 | 1.00  | 30   | -3.3686e-01 | +3.8819e+03 | +4.1369e+06 | -1.6463e+07 | RAY          |
| 0.050 | 14.13 | 1 | 1.00  | 30   | -7.3768e-02 | -4.2122e+01 | -3.7400e+04 | +9.8459e+02 | C<0          |
| 0.100 | 14.13 | 0 | 1.00  | 30   | -8.9816e-02 | +8.0212e+02 | +9.0038e+05 | -7.2427e+05 | RAY          |
| 0.100 | 14.13 | 1 | 1.00  | 30   | -1.9281e-02 | -8.9484e+00 | -1.1216e+04 | +1.3618e+02 | C<0          |
| 0.300 | 14.13 | 0 | 1.00  | 30   | -8.5685e-02 | +3.4619e+01 | +6.4146e+04 | -6.6949e+03 | RAY          |
| 0.300 | 14.13 | 1 | 1.00  | 30   | -7.8317e-02 | -6.0708e+00 | -1.9769e+03 | +1.1797e+02 | C<0          |
| 0.050 | 21.02 | 0 | 1.00  | 30   | +8.0080e-01 | -1.1636e+05 | -3.6362e+09 | -1.6452e+10 | DOOR-A       |
| 0.050 | 21.02 | 1 | 1.00  | 30   | -2.6681e-01 | -5.5669e+03 | -9.6363e+07 | -5.2797e+06 | C<0          |
| 0.100 | 21.02 | 0 | 1.00  | 30   | +1.3482e-01 | -2.5489e+04 | -8.0213e+08 | -7.5784e+08 | DOOR-A       |
| 0.100 | 21.02 | 1 | 1.00  | 30   | -5.2662e-02 | -1.1837e+03 | -2.1331e+07 | -2.7772e+05 | C<0          |
| 0.300 | 21.02 | 0 | 1.00  | 30   | -8.1982e-02 | -1.8517e+03 | -6.0017e+07 | +1.4916e+06 | C<0          |
| 0.300 | 21.02 | 1 | 1.00  | 30   | -7.8724e-02 | -8.5373e+01 | -1.6087e+06 | +1.1935e+05 | C<0          |
| 0.050 | 14.13 | 2 | 0.50  | 30   | -5.3626e+03 | -3.1443e+08 | -1.8438e+13 | +5.9240e+12 | C<0          |
| 0.100 | 14.13 | 2 | 0.50  | 30   | -1.3430e+03 | -7.8751e+07 | -4.6186e+12 | +8.4468e+11 | C<0          |
| 0.300 | 14.13 | 2 | 0.50  | 30   | -1.5006e+02 | -8.7613e+06 | -5.1472e+11 | +4.7728e+11 | C<0          |
| 0.050 | 21.02 | 2 | 0.50  | 30   | -5.2316e+07 | -6.9367e+12 | -1.3842e+18 | +2.4299e+25 | C<0          |
| 0.100 | 21.02 | 2 | 0.50  | 30   | -1.7060e+07 | -2.2875e+12 | -4.5906e+17 | +2.5990e+24 | C<0          |
| 0.300 | 21.02 | 2 | 0.50  | 30   | -6.1842e+06 | -8.4884e+11 | -1.7227e+17 | +3.4485e+23 | C<0          |
| 0.050 | 14.13 | 0 | 0.70  | 30   | -6.5483e+03 | -3.8391e+08 | -2.2520e+13 | +8.1994e+13 | C<0          |
| 0.050 | 14.13 | 0 | 0.80  | 30   | -7.1981e-01 | -6.5328e+05 | -3.6792e+10 | -4.0029e+11 | C<0          |
| 0.050 | 14.13 | 0 | 0.90  | 30   | +5.0545e+00 | +2.9649e+04 | -8.0441e+07 | -1.2857e+09 | VERTEX       |
| 0.050 | 14.13 | 0 | 1.10  | 30   | +4.7487e+00 | -1.6739e+05 | -5.5255e+14 | -2.6239e+15 | DOOR-A       |
| 0.050 | 14.13 | 0 | 1.20  | 30   | -2.5651e-01 | -2.4535e+04 | -6.3509e+13 | +1.6290e+13 | C<0          |
| 0.050 | 14.13 | 0 | 1.00  | 20   | -3.2035e+00 | -1.5570e+03 | +7.4455e+06 | -2.6276e+07 | C<0          |
| 0.050 | 14.13 | 0 | 1.00  | 40   | +9.8445e-01 | +2.3050e+03 | -7.1143e+06 | -1.2317e+07 | VERTEX       |
| 0.050 | 14.13 | 0 | 1.00  | 60   | -4.0796e-01 | -2.1032e+04 | -1.1354e+09 | +2.0837e+07 | C<0          |
+-------+-------+---+-------+------+-------------+-------------+-------------+-------------+--------------+
```

Census: `C > 0` on 5/27 rows; `b > 0` on 5/27; the map-106 section 2 pattern
`C > 0, b > 0, det < 0` on **2/27**; a Cut-2 witness (some nonzero `lam` with
`Q(lam) <= 0`) on **27/27**. Rows with `C < 0` are not instances of the
committed producer interface (its healthiness hypothesis is
`0 < ICgate(g.convolutionSquare)`, i.e. `C > 0`
`[C1C3CarrierTransport.lean:2012]`), so they are sign-map entries, not
instances: `C > 0` is not implied by the producer's interpolation, support and
contraction hypotheses, exactly as map 106 section 1 warns.

## 5. The endpoint instances

```text
+------+-------+-------+---+-------+------+-------------+-------------+-------------+
| case | delta | gamma | n | scale | k    | C           | b           | det         |
+------+-------+-------+---+-------+------+-------------+-------------+-------------+
| a    | 0.050 | 14.13 | 0 | 0.90  | 30   | +5.0545e+00 | +2.9649e+04 | -1.2857e+09 |
| b    | 0.050 | 14.13 | 0 | 1.00  | 40   | +9.8445e-01 | +2.3050e+03 | -1.2317e+07 |
+------+-------+-------+---+-------+------+-------------+-------------+-------------+

+------+-------------+-------------+-------------+-------------+
| case | D           | lam = b/C   | gv = det/C  | gv/C        |
+------+-------------+-------------+-------------+-------------+
| a    | -8.0441e+07 | +5.8660e+03 | -2.5436e+08 | 5.03e+07    |
| b    | -7.1143e+06 | +2.3414e+03 | -1.2511e+07 | 1.27e+07    |
+------+-------------+-------------+-------------+-------------+
  gv = the gate at the vertex, Q(lam) = det/C; the last column is the ratio
  |gv| / |C|, i.e. how far the vertex gate sits below the pivot scale.
```

Both endpoint rows have `D < 0`, so `det = C D - b^2 < 0` is **automatic**
given `C > 0`: in the regime `C > 0, D < 0` the map-106 section 2 determinant
condition costs nothing, and the binding obligations are `C > 0` and `b > 0`
alone. Both rows also give `lam = b/C > 0` and a strictly negative gate at the
vertex, which is the shape the committed vertex identity consumes
(`exists_nonzero_lambda_quadratic_nonpos_iff` assumes `0 < C`, and
`exists_pos_lambda_quadratic_nonpos` gives a positive `lam` when `D < 0`).

## 6. Scale scan: the endpoint is a knife-edge in the free knob

Nine points at `(delta = 0.05, gamma_1, n = 0, k = 30)`, window scale
`0.82 .. 0.98`:

```text
+-------+-------------+-------------+-------------+-------------+----------+
| scale | C           | b           | D           | det         | branch   |
+-------+-------------+-------------+-------------+-------------+----------+
| 0.82  | -1.2822e+01 | -1.3457e+05 | -7.7429e+09 | +8.1169e+10 | C<0      |
| 0.84  | +7.6386e+00 | -2.7996e+04 | -1.7232e+09 | -1.3947e+10 | DOOR-A   |
| 0.86  | +3.7233e+00 | -4.5375e+03 | -3.1005e+08 | -1.1750e+09 | DOOR-A   |
| 0.88  | -2.9848e+00 | -2.0467e+04 | +9.9989e+06 | -4.4873e+08 | C<0      |
| 0.90  | +5.0545e+00 | +2.9649e+04 | -8.0441e+07 | -1.2857e+09 | VERTEX   |
| 0.92  | +1.3285e-01 | -7.1724e+03 | -4.3876e+06 | -5.2027e+07 | DOOR-A   |
| 0.94  | +2.5773e+00 | -1.0043e+04 | -1.2017e+06 | -1.0396e+08 | DOOR-A   |
| 0.96  | -3.7285e+00 | +2.1562e+04 | -1.4133e+05 | -4.6441e+08 | C<0      |
| 0.98  | +3.6875e+00 | -8.3266e+03 | -1.4457e+07 | -1.2264e+08 | DOOR-A   |
+-------+-------------+-------------+-------------+-------------+----------+
```

`C > 0` on 6/9 points (so healthiness is a majority-but-not-uniform property
of the knob, and `C` changes sign twice), while `b > 0` on 2/9 (`0.90`,
`0.96`) and both at once on 1/9. `b` changes sign between adjacent knots
(`0.86: -4.5e+03` -> `0.88: -2.0e+04` -> `0.90: +2.96e+04` -> `0.92:
-7.2e+03`), i.e. the pivot sign of the committed owner shape is not a
continuous property of the window on the 0.02 scale. The same qualitative
picture holds along the other knob (`k = 20, 30, 40, 60`: `b < 0, > 0, > 0,
< 0`) and along `delta` at fixed scale.

Direction for the mainline: the endpoint signs are *reachable* on the
committed owner shape, so the sign side of the map-106 section 2 endpoint is
not a structural barrier — but no Lipschitz/monotone mechanism for them is
visible in these measurements, so a proof cannot be expected from the sign
analysis alone. The two numerical instances are witnesses that the interface
is non-vacuous, not evidence for a robust lemma.

## 7. Open obligations (unchanged by this record)

```text
1  any proof that the ACTUAL committed base/correction (not the explicit
   representative) realizes C > 0, b > 0 at some parameter point;
2  hence the whole map-106 section 2 sign endpoint as a theorem;
3  the joint tail/smallness budget  beta_s * L_n < multiplicity_rho * lam^2
   with the actual lambda_n = b/C (untouched here; lam ~ 2.3e+03..5.9e+03 on
   the endpoint rows);
4  the cardinal (committed bump) base remains numerically unusable
   (section 1.3); a computable admissible base with a certified contraction
   constant is still the missing analytic object of this lane;
5  no gate sign, no determinant sign, no producer witness, and no RH claim is
   made by this record.
```

## 8. Reproduce

```text
python3 scripts/fourpoint_owner_density_1959.py                 # 27-row grid
python3 scripts/fourpoint_owner_density_1959.py --refine        # + dxi study
python3 scripts/fourpoint_owner_density_1959.py --scan          # + knob scan
python3 scripts/fourpoint_owner_density_1959.py --calib         # phase test
python3 scripts/fourpoint_owner_density_1959.py --cardinal      # limitation
```

Runs in the WSL ext4 mirror; numpy/scipy only. The rig documents its sources,
its levers (F1..F4) and its conventions in the file header.