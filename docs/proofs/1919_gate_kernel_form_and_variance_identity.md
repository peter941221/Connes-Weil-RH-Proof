# 1919 — Gate kernel form and the determinant variance identity

Date: 2026-09-23.

Status: EXACT ALGEBRA plus NUMERIC verification on the committed rig. The
whole Cut-2 gate functional on the annihilator-detector span is a single
spectral pairing with an explicit kernel, and the span determinant equals
`A^2 * Var_nu(P)` for the signed measure `mu = K * W * dxi`, with an exact
sign-decomposition identity and a sufficient criterion. Every identity below
is verified to floating-point precision on four probed cases; the sign
`det < 0` itself is NOT proved, no Lean brick lands here, and no RH statement
is made. This record is a project derivation and probe.

## The kernel form (exact)

For a real correlation entry `F = A*star*B` with spectral transform
`Fhat = conj(Ahat)*Bhat` (the rig's `pair_direct` convention), the committed
gate functional splits into the archimedean sigma-identity integral and the
finite-prime sum. Both are linear in `Fhat`. Writing

```text
sigma(u) = log pi - Re psi(1/4 - i*u/2)
K(xi)    = sigma(2*pi*xi) + 2 * sum_{visible n} (Lambda(n)/sqrt(n)) * cos(2*pi*xi*log n)
```

(the `n`-sum over prime powers with `log n <= S_pair = 2*c`, the exact visible
set of the span), both parts collapse to one pairing:

```text
ICgate(F) = integral K(xi) * Fhat(xi) dxi,
```

the prime leg by the inverse-Fourier identity
`integral cos(2*pi*xi*t) * Fhat(xi) dxi = (F(t) + F(-t))/2`, the arch leg by
the committed sigma identity (rig F75). On the owner pair
`u = fullFunctionalEquationOrbitAnnihilator g rho`, the Laplace multiplier
`prod_j (s_j - s)` is the real even quartic

```text
P(xi) = P(omega),  omega = 2*pi*xi,
P(omega) = (delta^2 + gamma^2 + omega^2)^2 - 4*gamma^2*omega^2
         = (delta^2 + gamma^2 - omega^2)^2 + 4*delta^2*omega^2  > 0,
```

because the orbit nodes are the symmetric set `{+-delta +- i*gamma}`. Hence
`uhat = P * ghat` (with `P` real), and with `W = |ghat|^2 >= 0`:

```text
C   = ICgate(g.square)      = integral K * W          dxi
B01 = ICgate(u*star*g)      = integral K * P * W      dxi
D   = ICgate(u.square)      = integral K * P^2 * W    dxi
```

All three integrals are moments of the single signed measure

```text
mu = K * W * dxi,     W >= 0 even,   K even,   mu(R) = C = A > 0.
```

The recorded channel split (arch / finite-prime / cross) is the polarization
of these integrals in `K = sigma + K_prime`: the map `K -> (A, B01, D)` is
linear in `K`, so the 1918 `det_split` blocks are the three expansion terms.

## The determinant as a signed variance (exact)

`mu` is symmetric, so `B10 = B01` automatically; the 2x2 form on the span has
`D = <P,P>`, `B01 = <P,1>`, `C = <1,1>` under the pairing `integral f * h dmu`,
and the determinant is the squared "area" of that parallelogram:

```text
det = D*C - B01^2 = (1/2) * integral integral (P(xi) - P(eta))^2 dmu(xi) dmu(eta).
```

This identity is sign-agnostic: it holds for any symmetric signed `mu`.
Normalize `nu = mu/A` (total mass 1) and split `mu = mu_+ - mu_-` with masses
`P_m, N_m`; set

```text
f = N_m / A > 0,   Delta = mean_+(P) - mean_-(P).
```

Then `nu = (1+f) * nu_+ - f * nu_-`, `mean_nu(P) = m_+ + f*Delta`, and

```text
Var_nu(P) = (1+f) * [Var_+ + f^2*Delta^2] - f * [Var_- + (1+f)^2*Delta^2]
          = (1+f) * Var_+ - f * Var_- - f*(1+f) * Delta^2.        (identity)
```

Therefore, since `det = A^2 * Var_nu(P)` and `A^2 > 0`:

```text
det < 0   <=>   f * Var_- + f*(1+f) * Delta^2  >  (1+f) * Var_+
det < 0   <=    f * Delta^2 > Var_+            (sufficient; drops f*Var_-).
```

Reading: `det < 0` is a **variance gap** between the negative and positive
parts of the explicit measure `mu`: the negative part must out-spread the
positive part, either through its own variance or through the separation of
means.

## Moment form: one bracket inequality

`P` is a quadratic in `u = omega^2 = (2*pi*xi)^2`:

```text
P = u^2 + a*u + b,   a = -2*(gamma^2 - delta^2),   b = (delta^2 + gamma^2)^2,
```

so with signed moments `m_k = integral u^k dnu`:

```text
det = A^2 * [ (m4 - m2^2) + 2*a*(m3 - m1*m2) + a^2*(m2 - m1^2) ].
```

The Cut-2 obligation on the selected owner is thus one explicit inequality in
five signed moments of the measure `K*W*dxi` — an object whose only
owner-dependent input is the nonnegative spectral density `W`.

## Probe and readings

Script `scripts/fourpoint_gate_kernel_form_1919.py` (imports the record-1918
rig verbatim): four certified cases, `W` via the same padded-FFT grid as the
E3 engine, `K` via `sigma_vec` plus the visible prime powers, `P` cross-checked
against the committed `poly_P` on the imaginary axis (max rel. error 3.3e-16).
Artifact `results/1919_gate_kernel_form.json`.

```text
+---------------------+-----------+----------+-----------+-----------+-----------+-----------+-----------+----------+--------------+
| case / channel      | A         | f        | m_+       | m_-       | Delta     | Var_+     | Var_-     | fD^2/V+  | det (kernel) |
+---------------------+-----------+----------+-----------+-----------+-----------+-----------+-----------+----------+--------------+
| c=0.8 g=14.13 full  | 2.5858e-1 | 0.11416  | 3.9661e+4 | 3.6433e+4 | 3.2274e+3 | 1.260e+6  | 1.460e+9  | 0.944    | -1.1138e+07  |
| c=1.0 g=14.13 full  | 4.0999e-1 | 0.19221  | 3.9728e+4 | 3.8184e+4 | 1.5438e+3 | 1.460e+6  | 1.007e+8  | 0.314    | -3.0532e+06  |
| c=1.0 d=0.30 full   | 4.0999e-1 | 0.19221  | 3.9763e+4 | 3.8220e+4 | 1.5430e+3 | 1.460e+6  | 1.007e+8  | 0.313    | -3.0535e+06  |
| c=1.3 g=21.02 full  | 7.1206e-1 | 0.27099  | 1.9501e+5 | 1.9308e+5 | 1.9289e+3 | 1.882e+6  | 1.109e+7  | 0.536    | -9.6007e+05  |
+---------------------+-----------+----------+-----------+-----------+-----------+-----------+-----------+----------+--------------+
| c=0.8 g=14.13 arch  | 2.1427e-1 | 0.00178  | 3.9272e+4 | 2.7672e+4 | 1.1600e+4 | 1.261e+6  | 1.108e+11 | 0.190    | -9.0051e+06  |
| c=1.0 g=14.13 arch  | 3.0588e-1 | 0.00066  | 3.9449e+4 | 2.1946e+4 | 1.7503e+4 | 6.500e+5  | 3.597e+10 | 0.311    | -2.1781e+06  |
| c=1.0 d=0.30 arch   | 3.0588e-1 | 0.00066  | 3.9484e+4 | 2.2004e+4 | 1.7481e+4 | 6.495e+5  | 3.598e+10 | 0.310    | -2.1783e+06  |
| c=1.3 g=21.02 arch  | 4.5809e-1 | 0.00019  | 1.9460e+5 | 1.1451e+5 | 8.0092e+4 | 1.578e+6  | 7.498e+09 | 0.778    | -2.2776e+05  |
+---------------------+-----------+----------+-----------+-----------+-----------+-----------+-----------+----------+--------------+
```

Identity residuals (relative, from the probe log):

```text
+---------------------+---------------------+---------------------+---------------------+
| case / channel      | P-form vs 2x2 det   | moment form         | k-form vs engine    |
+---------------------+---------------------+---------------------+---------------------+
| c=0.8 g=14.13 full  | -1.00e-15           | -1.84e-15           | -7.95e-07           |
| c=1.0 g=14.13 full  |  6.33e-14           |  6.77e-14           | -6.74e-06           |
| c=1.0 d=0.30 full   |  2.49e-14           |  3.31e-14           | -6.75e-06           |
| c=1.3 g=21.02 full  | -1.50e-11           | -6.44e-12           | -1.55e-03           |
+---------------------+---------------------+---------------------+---------------------+
| c=0.8 g=14.13 arch  | -2.90e-15           | -2.28e-15           |  1.66e-10           |
| c=1.0 g=14.13 arch  | -1.07e-14           | -2.59e-14           |  1.45e-09           |
| c=1.0 d=0.30 arch   | -1.37e-14           | -2.01e-14           |  1.45e-09           |
| c=1.3 g=21.02 arch  |  1.56e-11           | -3.02e-12           |  2.59e-08           |
+---------------------+---------------------+---------------------+---------------------+
```

The P-form and moment-form residuals are the pure identity checks (same grid
data, two evaluations). The engine column is the declared discretization gap:
the arch k-form is the same sigma-FFT sum as the E3 engine (residuals 1e-10 to
2.6e-8 from summation order), while the full k-form integrates on the padded
grid to `|xi| <= 1000` against the E4 analytic window `|xi| <= 200`, and the
residual tracks that truncation/aliasing at the width of the bump.

Raw log excerpt:

```text
[full K] identity vs same-grid 2x2 det: P-form rel -1.00e-15, moment-form rel -1.84e-15; vs engine rel -7.95e-07; criterion full True suff(f*D^2>Var+) False (f*D^2=1.189e+06 Var+=1.260e+06)
[arch] identity vs same-grid 2x2 det: P-form rel -2.90e-15, moment-form rel -2.28e-15; vs engine rel 1.66e-10; criterion full True suff(f*D^2>Var+) False (f*D^2=2.394e+05 Var+=1.261e+06)
```

Structural readings:

1. The criterion `f*Var_- + f*(1+f)*Delta^2 > (1+f)*Var_+` holds on all 8
   channel-case rows, and the sufficient form `f*Delta^2 > Var_+` FAILS on all
   8 (`f*Delta^2/Var_+` ranges 0.19 to 0.94): the negative-spread term is
   essential, not decorative, in every measured row.
2. `m_+` and `m_-` pin near `gamma^4` (3.97e4 vs `gamma^4 = 3.99e4`;
   1.95e5 vs 1.95e5): `W` concentrates where `omega << gamma`, so
   `P ~ gamma^4` on the mass. The relative width `sqrt(Var_+)/m_+` is 2.8%
   (gamma = 14.13) and 0.70% (gamma = 21.02).
3. The arch channel alone satisfies the criterion with a very different
   balance: `f` between 1.9e-4 and 1.8e-3 (the sigma measure is nearly
   mass-balanced) but `Var_-` between 7.5e9 and 1.1e11 — the sigma tail's
   negative mass is thin and far-spread. The finite primes thicken the
   negative mass (`f` up to 0.27) while the mean gap `Delta` shrinks
   (8e4 at c=1.3 arch vs 1.9e3 full).
4. The kernel form makes the two channel blocks one object: same `W`, same
   `P`, only the kernel `K` split additively.

## What this changes

The Cut-2 obligation on the selected owner is no longer "estimate three gate
entries" but a single inequality about the sign decomposition of an explicit
measure:

```text
remaining:   f * Var_-(P) + f*(1+f) * (mean_+ P - mean_- P)^2 > (1+f) * Var_+(P)
             for  mu = K * W * dxi,  W = |ghat|^2 >= 0 the owner's density,
```

equivalently the five-moment bracket of the previous section. The kernel `K`
is fully explicit (committed sigma plus a finite prime-power sum), and `P` is
an explicit real quartic; the only owner-dependent input is the nonnegative
density `W`. This also explains the record-1918 channel split as pure
linearity in `K`, and explains why the boundary scan's margin thins with width
and height: `f*Var_-` scales with the spread of the sigma tail against the
shrinking relative width of `W`.

No gate sign is proved. The probe lives on the committed-class family, not on
the selected owner; law F79 still governs which engines certify shape.

## Verification

Build/probe evidence: `logs/1919_kernel_form.log` in the Linux-side build
mirror (runtime < 1 s per run, four cases x two channels), artifact
`results/1919_gate_kernel_form.json` (6.7 kB). Residuals and criterion rows as
tabulated above; `P` vs committed `poly_P` max rel. error 3.3e-16. The
record-1918 rig `scripts/fourpoint_diagonal_sign_1918.py` is imported
verbatim; no engine was modified. The kernel-form script is
`scripts/fourpoint_gate_kernel_form_1919.py`. No Lean module is added or
changed by this record.