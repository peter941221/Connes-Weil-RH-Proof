# 2338 - Exact analytic interpolation repair enclosure

Date: 2026-10-01

Status: EXACT-FINITE-NODE-REPAIR-ENCLOSED-ONLY.

## Object and existence argument

Record 2337 proves that the stored coefficient vectors do not satisfy their
mandatory targets exactly. This record constructs a different, explicitly
priced ideal coefficient pair in the SAME 30-family basis. The live owner is
not replaced. The repair is not a float solve of a stored matrix, nor a cast of
an ideal solve back to float.

For the fixed captured nodes z_i and analytic physical basis f_j, define
A_ij = integral f_j(x) exp(z_i*x) dx, with each basis radius equal to the
exact stored width squared. Every one of the 900 entries is re-enclosed by
the 2337 integrator at 320 bits. The right-hand sides are 1 for base and the
prescribed captured target y_i for correction. They prescribe interpolation;
they do not store a kernel sign or RH conclusion.

```text
A b_ideal = 1           A c_ideal = y
          |                       |
          +-----------+-----------+
                      v
B_ideal(z_i) = 1       C_ideal(z_i) = y_i
                      |
                      v
H_ideal(z_i) = B_ideal(z_i)^(n+1) C_ideal(z_i) = y_i
```

The acb_mat preconditioned solve encloses the exact solution. As a separate
invertibility check, a midpoint matrix X is used only as a candidate inverse,
and the certified row norm eta = ||I-XA||_infinity satisfies eta < 1/2.
Then I-(I-XA) is invertible by its convergent geometric series, so A is
invertible and the prescribed exact coefficient pair exists uniquely. This
argument does not treat a small residual as proof of invertibility.

The matrix entries enclose actual analytic integrals, not the stored matrix
operands of the older 2237 solve radius. No approximate-solve option is used.
Coefficient balls enclose the unique ideal coefficients; they must not be
interpreted as new exact stored numbers.

## Certified repair prices

The infinity norm is the largest absolute row sum. For a candidate inverse X,
its bound is ||X||_infinity/(1-eta). Applying that bound to the stored residual
gives a coarse coefficient-repair bound. Per-coefficient differences from the
certified ideal solve yield tighter transform-change prices.

```text
+-------------------------------------------+------------------------+
| Quantity                                  | Reading / outward pin  |
+-------------------------------------------+------------------------+
| Maximum matrix component radius           | about 2.2134e-64       |
| eta = ||I-XA||_infinity                    | about 4.5323e-38       |
| Certified inverse norm upper pin          | 6.78e17                |
| Stored right-hand-side residual row bound | about 7.0269e-9        |
| Coarse coefficient repair upper pin       | 4.758e9                |
| Base transform-change upper pin           | 1.26e-7                |
| Correction transform-change upper pin     | 1.63e-4                |
+-------------------------------------------+------------------------+
```

The coefficient bound is an absolute bound on coefficients with very large
magnitudes, not a functional error. All quoted pins are rounded outward and
checked against exported rational upper endpoints.

For each family radius R_j and all 0 <= Re(z) <= 1, any Im(z), its transform
magnitude is <= 2 R_j exp(-30+R_j). Multiplying this by each certified
coefficient-change magnitude and summing proves the two transform-change
prices. These uniform bounds are NOT integrable full-line tail bounds.
They cannot simply be integrated over all frequencies or inserted as a
signed-kernel charge. The source product, derivatives, and decay still have
to be charged at that consumer.

## Scope and next obligation

This repairs finite-node realization on the chosen captured node list. It does
not prove that rho is a source zero or that the list contains every required
source zero. It does not verify the far-tail contraction of the new base.
The support cover from 2336 remains the same; no 2R prime-book shortcut is
licensed. The signed-kernel owner transfer is UNPRICED and has not happened.
No frozen map-103 gate campaign is reopened.

The next mathematical decision is whether a signed consumer can pay this exact
repair while retaining the complete composed-owner prime book and full-line
error budget. A small matrix residual or small relative coefficient movement
cannot answer that question.

Validation: six solve/norm adversarial tests pass, including a singular matrix,
a deliberately wrong inverse, and a complex-modulus row sum. The enriched
replay reproduces all prior certified numeric fields bitwise. Source hashes
match. Both solves use the explicit rigorous precond algorithm, never approx.
No Lean certificate import, producer GO, or RH claim.

## Evidence and primary documentation

- scripts/routea_exact_interpolation_repair_2338.py and paired selftest.
- results/2338_exact_interpolation_repair.json, including all 30 coefficient pairs.
- build-logs/2338_exact_interpolation_repair.log and build-logs/2338_repair_selftest.log.
- Official python-flint acb_mat solve/inv documentation, retrieved 2026-10-01:
  https://python-flint.readthedocs.io/en/latest/acb_mat.html
