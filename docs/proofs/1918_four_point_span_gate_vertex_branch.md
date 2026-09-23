# 1918 — Four-point span gate: the sign probe selects the vertex branch

Date: 2026-09-23.

Status: NUMERIC branch selection plus FORMAL wiring of the selected branch.
On a committed-class detector family every measured case lies in the third
branch of the record-1917 trichotomy (`D > 0`, discriminant strictly
positive), so the span gate witness is the vertex `lambda = B'/(2*C)` with a
strictly negative value there; that branch is now formal in the record-1917
module. The cross-determinant inequality on the selected owner, the joint
high-shell margin, and the RH contradiction remain open. This record is a
project derivation and probe, not an originality or RH claim.

## Owner and result

Probe scope: the committed owner `u = fullFunctionalEquationOrbitAnnihilator
g rho` against `g`, with `g` a smooth bump of width `c` on the log-line and
`rho = (0.5 + delta) + i*gamma` at the first two Riemann heights. The probe
prices the three gate entries `D = ICgate(u.square)`, `C = ICgate(g.square)`,
`B01 = ICgate(u*star*g)`, `B10 = ICgate(g*star*u)`, and classifies the branch
of `Q(lam) = D - lam*(B01 + B10) + lam^2*C` per case.

Measured result, 18 of 18 cases: `D > 0` in every archimedean engine, and the
discriminant `B'^2 - 4*C*D` (with `B' = B01 + B10`) is strictly positive under
the certified engine pair. Hence the live branch is the vertex branch, the
witness coefficient is

```text
lambda = B' / (2*C),   Q(lambda) = (4*C*D - B'^2) / (4*C) = det / C,
det = D*C - (B'/2)^2 < 0,
```

and the span gate is *strictly* negative there. On the probed family the
vertex tracks `lambda ~ 0.46 .. 0.59 * K^4` with `K = 3 + norm(rho)`, and the
relative indefiniteness margin `B01^2/(D*C) - 1` (the exact `margin_rel` under
the cross-term symmetry `B01 = B10`, measured to `<= 2.8e-12`) ranges over
`[5.0e-5, 0.116]`.

Formal content, added to `C1FourPointSpanGateCertificate.lean` (same module
and owner as record 1917, already committed):

1. `gate_quadratic_at_vertex`: for `C > 0`,

   ```text
   D - (B/(2*C))*B + (B/(2*C))^2*C = -(B^2 - 4*C*D)/(4*C).
   ```

2. `exists_pos_lambda_quadratic_neg_of_det_neg`: a positive cross sum
   `0 < B`, a positive pivot `0 < C`, and a strictly negative gate
   determinant `D*C - (B/2)^2 < 0` supply `0 < lam` with
   `D - lam*B + lam^2*C < 0`; the witness is the vertex `B/(2*C)`.

3. Wires on a healthy detector, mirroring the record-1917 pair:
   `exists_pos_lambda_orbitWindowSemiLocalGate_of_annihilator_det_neg`
   (strictly negative span gate at a positive coefficient) and
   `exists_pos_lambda_gate_and_prefix_of_annihilator_det_neg`, which carries
   the committed finite-prefix bound
   `sum spectralTerm <= -xiMultiplicity rho * lam^2` at the *same* coefficient
   and owner.

The record-1917 `D < 0` diagonal wires remain formal as the fallback branch.
Under the committed cross-term symmetry the determinant hypothesis of the new
wires reads `ICgate(u.square) * ICgate(g.square) - ICgate(u*star*g)^2 < 0`,
which is exactly the probe's `D*C - B01^2 < 0`.

## Exact remaining obligation (Cut 2, measured branch)

```text
positive cross sum:  ICgate(u*star*g) + ICgate(g*star*u) > 0
gate determinant:    ICgate(u.square) * ICgate(g.square)
                       - ((ICgate(u*star*g) + ICgate(g*star*u)) / 2)^2 < 0
```

on the selected healthy detector, plus the Cut 1 joint margin at
`lambda = B'/(2*C)`. The determinant inequality is a scored
Cauchy-Schwarz-style failure of the gate form on `span{u, g}`; on the probed
family it holds with relative margin `B01^2/(D*C) - 1` as small as `5.0e-5`,
so any analytic route to it must be sharp to that order.

## Instruments and adjudication (law F79)

Five reading paths per gate entry: E1 real-space quadrature of the assembled
pair convolution; E3 the committed sigma identity `arch = ∫ sigma(2*pi*xi) *
Re Fhat d xi` with `Fhat` from an FFT of the assembled convolution; E4 the
same identity with the *analytic* `Fhat` built from the committed Laplace
chain (`laplaceAt u(s) = prod_j (s_j - s) * laplaceAt g(s)`,
`Fhat(ξ) = conj(Lu(conj s)) * Lu(s)` at `s = -2*pi*i*xi`); E5 a small-y series
plus closed tail; W0 an exact-answer rescaling calibration on `F = s*(g*star*g)`.

Calibration and adjudication, measured:

+-----------------------------------------------------------+----------------+
| check                                                     | reading        |
+-----------------------------------------------------------+----------------+
| W0, s = 1e3, 1e6, 5e8 (exact answer)                      |                |
|   E3 relative error                                       | 0 .. 3.8e-16   |
|   E1 relative error                                       | -1.05e-7 stable|
|   E5 relative error                                       | -2.45e-6 stable|
+-----------------------------------------------------------+----------------+
| u*star*u entries, deviation from certified E4             |                |
|   E3 (certified pair disagreement)                        | <= 9.22e-8     |
|   E1                                                      | up to 3.86e-2  |
|   E5                                                      | up to 1.86e-1  |
+-----------------------------------------------------------+----------------+
| structural checks across all 18 cases                     |                |
|   annihilation residual at the four orbit points          | <= 2.29e-5     |
|   Laplace multiplier residual off-orbit                   | <= 8.27e-7     |
|   Laplace product on the numeric pair convolution         | <= 2.93e-8     |
|   cross-term symmetry B01 vs B10                          | <= 2.8e-12     |
+-----------------------------------------------------------+----------------+

Reading: W0 certifies E3 on its own exact-answer family at machine precision
and exposes a fixed `1.05e-7` bias in E1 there, while the `u*star*u` shape
(`max F` up to `6.5e9`) collapses E1 up to `3.9%` and E5 up to `19%`; E4, an
independent `Fhat` route, ties E3 to `9.2e-8` on every case. The certified
reading is therefore the `{E3, E4}` pair. This is law F79: scale calibration
does not certify a shape; the analytic-`Fhat` engine is the per-shape arbiter.
An earlier pass of this probe (all-engine classifier) read the case
`c = 1.0, delta = 0.05, gamma = 14.13` at `disc = -2.9e7` (NO-WITNESS) from
the E1-poisoned `D`; the certified pair gives `disc = +1.221e7`. The branch
verdicts in this record use the certified pair throughout.

## Probe table

Engines: `D_cert` = E4 (E3 fallback), `C`, `B01`, `B10` from E3; `disc =
B'^2 - 4*C*D_cert`; `margin_rel = disc/(4*C*D_cert)`;
`Q_vertex = -disc/(4*C)`; `lam_vertex = B'/(2*C)`. "cert" marks the
certified-pair sensitivity bar `|disc| > 10 * ddisc_cert`; the thinnest case
clears it by `30x`. A deliberately pessimistic `1e-5` relative envelope on the
shared inputs (bar `ddisc_cons`) is cleared by 15 of 18 cases; the three
`c = 1.3, gamma = 21.02` cases clear it only by `1.6x`, which is the honest
sharpness warning recorded above.

gamma = 14.1347:

```text
+--------------------+-------------+-------------+------------+-------------+-------------+
| case               | D_cert      | disc        | margin_rel | Q_vertex    | lam_vertex  |
+--------------------+-------------+-------------+------------+-------------+-------------+
| c=0.8 d=0.05       | 3.7126e+08  | 4.4554e+07  | 1.160e-01  | -4.3075e+07 | 4.0029e+04  |
| c=0.8 d=0.10       | 3.7132e+08  | 4.4554e+07  | 1.160e-01  | -4.3075e+07 | 4.0032e+04  |
| c=0.8 d=0.30       | 3.7198e+08  | 4.4557e+07  | 1.158e-01  | -4.3078e+07 | 4.0064e+04  |
| c=1.0 d=0.05       | 6.4933e+08  | 1.2213e+07  | 1.147e-02  | -7.4472e+06 | 4.0024e+04  |
| c=1.0 d=0.10       | 6.4943e+08  | 1.2213e+07  | 1.147e-02  | -7.4473e+06 | 4.0027e+04  |
| c=1.0 d=0.30       | 6.5047e+08  | 1.2214e+07  | 1.145e-02  | -7.4478e+06 | 4.0059e+04  |
| c=1.3 d=0.05       | 1.1394e+09  | 2.8112e+06  | 8.663e-04  | -9.8700e+05 | 4.0019e+04  |
| c=1.3 d=0.10       | 1.1396e+09  | 2.8112e+06  | 8.661e-04  | -9.8701e+05 | 4.0022e+04  |
| c=1.3 d=0.30       | 1.1414e+09  | 2.8115e+06  | 8.648e-04  | -9.8710e+05 | 4.0054e+04  |
+--------------------+-------------+-------------+------------+-------------+-------------+
```

gamma = 21.0220:

```text
+--------------------+-------------+-------------+------------+-------------+-------------+
| case               | D_cert      | disc        | margin_rel | Q_vertex    | lam_vertex  |
+--------------------+-------------+-------------+------------+-------------+-------------+
| c=0.8 d=0.05       | 9.8574e+09  | 3.8883e+07  | 3.814e-03  | -3.7593e+07 | 1.9562e+05  |
| c=0.8 d=0.10       | 9.8580e+09  | 3.8883e+07  | 3.813e-03  | -3.7593e+07 | 1.9562e+05  |
| c=0.8 d=0.30       | 9.8652e+09  | 3.8884e+07  | 3.811e-03  | -3.7593e+07 | 1.9570e+05  |
| c=1.0 d=0.05       | 1.5672e+10  | 1.3216e+07  | 5.142e-04  | -8.0587e+06 | 1.9556e+05  |
| c=1.0 d=0.10       | 1.5673e+10  | 1.3216e+07  | 5.142e-04  | -8.0586e+06 | 1.9557e+05  |
| c=1.0 d=0.30       | 1.5684e+10  | 1.3214e+07  | 5.137e-04  | -8.0577e+06 | 1.9564e+05  |
| c=1.3 d=0.05       | 2.7222e+10  | 3.8462e+06  | 4.961e-05  | -1.3504e+06 | 1.9553e+05  |
| c=1.3 d=0.10       | 2.7224e+10  | 3.8461e+06  | 4.960e-05  | -1.3504e+06 | 1.9554e+05  |
| c=1.3 d=0.30       | 2.7244e+10  | 3.8452e+06  | 4.955e-05  | -1.3500e+06 | 1.9561e+05  |
+--------------------+-------------+-------------+------------+-------------+-------------+
```

Structural readings. `B01` scales as `gamma^4` to `0.1%` (ratio `4.8869` vs
`(21.022/14.135)^4 = 4.8925` at `c = 0.8`), `C` is height-independent, so
`lam_vertex = B01/C` inherits the `gamma^4` law; `disc` varies by at most a
factor `1.4` across heights at fixed width and decreases with width (from
`4.5e7` at `c = 0.8` to `2.8e6` at `c = 1.3`), while `D` scales as `gamma^8`
to within `11%`, which is whence the margin trend `margin_rel ~ gamma^-8` and
`c`-decay comes. The vertex is width- and
abscissa-stable to a few percent, so on this family the Cut-1 coupling ratio
`(K^4 + lam)^2 / lam^2 = (1 + K^4/lam)^2` is an explicit O(1) factor
(`~9.9` at `gamma = 14.13`, `~7.3` at `gamma = 21.02`): no `lambda`-growth is
left in the joint margin, which reduces to selecting `n` with every factor
explicit.

## Channel split of the determinant

The gate entries are sums of an archimedean part (the committed sigma
identity) and a finite-prime part, so the `2 x 2` determinant splits as

```text
det_full = det_arch + det_prime + det_cross,
det_arch  = D_a*C_a - B_a^2,        det_prime = D_p*C_p - B_p^2,
det_cross = D_a*C_p + C_a*D_p - 2*B_a*B_p
```

(the polarization of the determinant form). On the 18 probed cases **each of
the three blocks is separately strictly negative**, so the indefiniteness is
not an inter-channel cancellation accident: the archimedean channel alone is
already reverse-Cauchy-Schwarz, and the arch share `det_arch/det_full` ranges
over `0.237 .. 0.809`, the prime share from `0.7%` up to `51%` as the width
grows. The arch block is built from the committed `sigma` symbol
(`sigma(u) = log(pi) - Re psi(1/4 - i*u/2)`, sign flip theorem-grade at
`u* = 6.289836`); the prime block is a finite explicit sum over the visible
prime powers of the support. This split is the structural lead for the
analytic route to the determinant inequality.

+----------------------+--------------+--------------+--------------+-----------+
| case                 | det_full     | det_arch     | det_prime    | cross     |
+----------------------+--------------+--------------+--------------+-----------+
| c=0.8 d=0.05 g=14.13 | -1.1138e+07  | -9.0051e+06  | -7.6494e+04  | -2.06e+06 |
| c=0.8 d=0.05 g=21.02 | -9.7208e+06  | -7.5433e+06  | -2.5075e+05  | -1.93e+06 |
| c=1.0 d=0.05 g=14.13 | -3.0533e+06  | -2.1781e+06  | -7.3827e+04  | -8.01e+05 |
| c=1.0 d=0.05 g=21.02 | -3.3039e+06  | -1.7901e+06  | -4.2663e+05  | -1.09e+06 |
| c=1.3 d=0.05 g=14.13 | -7.0280e+05  | -3.4867e+05  | -1.1241e+05  | -2.42e+05 |
| c=1.3 d=0.05 g=21.02 | -9.6155e+05  | -2.2776e+05  | -4.8684e+05  | -2.47e+05 |
+----------------------+--------------+--------------+--------------+-----------+
```

(abscissa `d = 0.05` representative; the other abscissas shift every entry by
less than `0.1%`. All four quantities are strictly negative in all 18 cases.)

## Boundary scan (scouting extension)

A width/height scan on the same family (`scripts/fourpoint_diagonal_sign_1918_boundary.py`,
abscissa `0.05`, widths `1.3 .. 3.0`, heights `21.0220, 30.4249`, 10 cases,
~2 minutes) keeps the vertex verdict on all 10 cases — the determinant sign
does not flip in the tested window — while the relative margin decays from
`4.96e-5` to `~1e-7` and the certified-pair sensitivity (which grows like the
`1e-6` relative pair disagreement on the now `~1e12`-scale `D`) overtakes
`|disc|` beyond width `~2.0`.

```text
+--------+----------+-------------+------------+-------------+--------+
| width  | height   | det         | margin_rel | disc        | cert   |
+--------+----------+-------------+------------+-------------+--------+
| 1.3    | 21.0220  | -9.6155e+05 | 4.961e-05  | +3.846e+06  |  29.6x |
| 1.3    | 30.4249  | -4.1802e+06 | 1.122e-05  | +1.672e+07  |   7.6x |
| 1.6    | 21.0220  | -2.2353e+05 | 4.695e-06  | +8.941e+05  |   6.4x |
| 1.6    | 30.4249  | -1.0424e+06 | 1.139e-06  | +4.170e+06  |   1.5x |
| 2.0    | 21.0220  | -2.9648e+05 | 2.281e-06  | +1.186e+06  |   5.4x |
| 2.0    | 30.4249  | -1.8917e+06 | 7.570e-07  | +7.567e+06  |   1.7x |
| 2.4    | 21.0220  | -3.5062e+04 | 1.136e-07  | +1.402e+05  |   0.3x |
| 2.4    | 30.4249  | -5.2996e+05 | 8.932e-08  | +2.120e+06  |   0.3x |
| 3.0    | 21.0220  | -1.5260e+05 | 1.584e-07  | +6.104e+05  |   0.5x |
| 3.0    | 30.4249  | -1.8976e+06 | 1.024e-07  | +7.590e+06  |   0.3x |
+--------+----------+-------------+------------+-------------+--------+
```

Reading: (i) the vertex branch is not a knife-edge of the height at fixed
narrow width, but its margin decays steeply in width (roughly quartic or
steeper) and in height (`~gamma^-8`); (ii) sign-level verdicts from this
instrument are trustworthy only up to width `~2.0` at these heights — beyond
that `cert < 10x` and even `cert < 1x`, an instrument-limit (F77-family)
reading, not a mathematical sign flip. Any analytic route to the determinant
must therefore be exact-ish or structural rather than lossy, which is what the
channel split above provides.

## Verification

```text
lake build ConnesWeilRH.Dev.C1FourPointSpanGateCertificate
lake build ConnesWeilRH.Dev.C1FourPointSpanGateCertificateAudit
python3 scripts/fourpoint_diagonal_sign_1918.py
python3 scripts/fourpoint_diagonal_sign_1918_certify.py
python3 scripts/fourpoint_diagonal_sign_1918_boundary.py
```

The owning build completed in 3809 jobs with zero `error:` lines and no
warnings in the two touched files; the paired audit prints exactly
`[propext, Classical.choice, Quot.sound]` for all eleven public declarations
(seven from record 1917, four new) with no `sorryAx`. The probe ran in 494 s
under the resource-aware runner on a temporary WSL verification copy; the
certified post-analysis reruns in seconds on the stored JSON; the boundary
scan ran 10 cases in 128 s. Artifacts:
`results/1918_fourpoint_diagonal_sign_certified.json` (raw per-case readings
plus the certified classification and the channel split) and
`results/1918_fourpoint_diagonal_sign_boundary.json`, regenerateable from the
three scripts.

No gate sign on the selected owner, no joint margin, and no RH statement is
proved here. RH NOT claimed.