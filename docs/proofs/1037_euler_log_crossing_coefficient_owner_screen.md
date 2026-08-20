# 1037 - Euler-log crossing coefficient-owner screen

Date: 2026-08-19.

Status: **PASS for the finite coefficient owner; no new detector and no RH
claim.**  The screen independently evaluates the logarithmic-derivative
coefficient and the two half-line crossing orientations on one root.  It
passes `m = 1, 2, 3` for `p = 2, 3` and finds no mixed-prime term in the
commuting finite Euler product.

This is directly relevant to the active C1 consumers (same-owner cutoff
remainder/readback and global spectral nonnegativity): it removes the
prime-power normalization ambiguity before a candidate positive detector is
allowed to enter either consumer.  It does not provide the missing remainder
estimate, global positivity, the finite-vanishing criterion, or RH.

## Formal owner

The repository already contains the exact Lean readback in:

```text
ConnesWeilRH/Source/CCM25Concrete/SelectedSingleCrossing.lean:63-79
ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingKernel.lean:390-417
```

The core declarations are:

```lean
eulerLogSingleCrossingAtom owner p m
  = (1 / (m * sqrt (p^m))) *
      singleCrossingPairDiagonalIntegral owner (m * log p)

eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow
  : weighted_pair_traces owner p m
      = owner.finitePrimeTerm (p ^ m)
```

The first equality supplies the logarithmic `1 / m` coefficient before the
crossing length is inserted.  The kernel theorem then supplies the same-owner
identity

```text
pair trace at b = b * (F(b) + F(-b)),
F = g^* * g,
b = m log(p).
```

Consequently the coefficient readback is exactly

```text
p^(-m/2) * log(p) *
  (F(m log(p)) + F(-m log(p))).
```

Source links:

```text
https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedSingleCrossing.lean
https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingKernel.lean
```

## What the screen checks

The Python owner in
`1037_euler_log_crossing_coefficient_owner_screen.py` constructs one smooth
compact-log root `g` satisfying the three Laplace constraints at
`0`, `1/2`, and `1`.  The same object is used for:

```text
g                         (moment constraints and mass)
g^* * g                   (all F values)
left crossing             (forward orientation)
right crossing            (reverse orientation)
finitePrimeTerm(p^m)      (the readback target)
```

There are four checks:

1. For `T_p(t) = I - t p^(-1/2) U_log(p)`, the numerical integral of
   `T'_p(t) T_p(t)^(-1)` agrees with
   `-sum_{m >= 1} p^(-m/2) U_{m log(p)} / m`.
2. Direct two-stage quadrature of both crossing orientations agrees with
   `b * (F(b) + F(-b))`.
3. Multiplying by `p^(-m/2) / m` agrees with the finite prime term for
   `p = 2, 3` and `m = 1, 2, 3`.
4. For the product of the `p = 2` and `p = 3` factors, the direct product
   logarithmic derivative agrees with the sum of local logarithmic
   derivatives.  The residual is the mixed-prime cancellation check.

The product test matters because expanding a raw inverse can display mixed
words.  A logarithmic derivative must cancel those words; otherwise it would
not be the Euler logarithm owner used by the formal readback.

## WSL2 reproduction

The run uses the Ubuntu-24.04 WSL2 ext4 verification mirror and NumPy only:

```text
python3 -B docs/proofs/1037_euler_log_crossing_coefficient_owner_screen.py
```

Default numerical parameters are `grid-size=256`, `step=0.06`,
`basis-size=12`, Gauss order `260`, Euler-flow quadrature order `160`, and
series order `64`.

Observed output:

```text
1037 Euler-log crossing coefficient-owner screen
formal_owner=SelectedCrossingKernel.eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow
owner_contract=g -> g^* * g -> both crossing orientations -> finitePrimeTerm
primes=(2, 3) max_power=3
owner_mass=1.000000000000e+00
owner_support_bound=1.710000000000e+00
owner_triple_vanishing_residual=2.140167820741e-09

local_series_error=8.354650304909e-12
mixed_log_derivative_error=1.115760330919e-15
mixed_integrated_additivity_error=4.440892098501e-16
```

Prime-power rows:

```text
+-----+-----+----------------------+----------------------+----------------------+
| p   | m   | b                    | crossing_error       | coefficient_error    |
+-----+-----+----------------------+----------------------+----------------------+
| 2   | 1   | 6.931471805599e-01   | 0.000000000000e+00   | 0.000000000000e+00   |
| 2   | 2   | 1.386294361120e+00   | 1.798063292470e-16   | 1.798063292470e-16   |
| 2   | 3   | 2.079441541680e+00   | 2.039967332274e-16   | 2.163712101075e-16   |
| 3   | 1   | 1.098612288668e+00   | 1.756167721417e-16   | 3.041771720106e-16   |
| 3   | 2   | 2.197224577336e+00   | 3.006086400129e-16   | 1.127282400048e-16   |
| 3   | 3   | 3.295836866004e+00   | 0.000000000000e+00   | 0.000000000000e+00   |
+-----+-----+----------------------+----------------------+----------------------+
```

The aggregate values are:

```text
max_crossing_identity_error=3.006086400129e-16
max_prime_power_coefficient_error=3.041771720106e-16
mixed_prime_readback_error=1.827199855161e-16
```

The root's triple-node residual is `2.14e-9`, below the screen tolerance
`2e-8`.  The small `p=3, m=3` value is retained in the output rather than
being dropped: visibility and coefficient correctness are separate checks.

## Interpretation

The screen passes the exact obstruction that rejected the 1036 candidate:
there is no extra detector factor at `m=2`, and the crossing length supplies
the missing factor `m log(p)` so that `1/m` reduces to `log(p)`.

The mixed-prime test also passes, so the local logarithmic owner is additive
over the commuting prime translations.  This does **not** show that a
positive trace limit exists.  It only says that any later detector must use
this coefficient owner (or prove an equivalent owner) if it is to read back
the finite-prime part of the Weil functional.

## Formal verification boundary

The numerical file is not imported by Lean.  The existing import-facing audit
is:

```text
ConnesWeilRH/Dev/SelectedCrossingKernelAudit.lean
```

Run:

```text
lake build ConnesWeilRH.Dev.SelectedCrossingKernelAudit
```

The audit checks the exact theorem and its dependency set.  The numerical
screen and the Lean theorem are complementary: the former catches orientation
or implementation mistakes in a concrete owner, while the latter is the
formal proof of the finite coefficient identity.

## Next steps

1. Keep this Euler-log/crossing owner fixed when designing any replacement
   positive detector.
2. Prove or screen the same-owner cutoff remainder/readback needed by the
   active RH root; do not introduce `PositiveTraceLimitFamily` from this
   coefficient check alone.
3. After a remainder candidate survives, audit its global spectral
   nonnegativity and finite-vanishing consumer separately.

RH remains unproved.
