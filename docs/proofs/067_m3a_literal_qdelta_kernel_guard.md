# 067 M3A Literal `Q delta` Kernel Guard

Date: 2026-07-12

Result: the literal formula `K_I(v,u) = Q delta(max(u/v,v/u))` cannot be
implemented as an ordinary Hilbert-Schmidt function kernel. The singular
principal term must be separated first.

## Source Identity

CC20 Theorem `thmqkey1` gives

```text
D_infinity o Q(xi * xi^*)
  = <xi, (-2 Id + K_I) xi>.
```

In logarithmic coordinates, the source distribution has the structure

```text
Q delta(exp(|x|)) = -2 Dirac_0 + regular_even_part.
```

The `-2 Dirac_0` term is exactly the `-2 Id` operator in the quadratic-form
identity. It is not part of the compact Hilbert-Schmidt remainder.

## Guard

Do not define the M3A owner with

```text
kernel := Q delta(max(u/v,v/u))
```

unless the definition explicitly means the distribution after subtracting its
`-2 Dirac` component. A Dirac mass is not a measurable function on
`sqrt(I) × sqrt(I)` and cannot satisfy the ordinary integral

```text
∫∫ ‖kernel(u,v)‖² dρ(u)dρ(v) < ∞.
```

Therefore a literal `Q delta` field would fail the Hilbert-Schmidt gate before
any Lean proof and would double-count the essential `-2 Id` term.

## Correct Target

The valid M3A owner must expose:

```text
Q delta = -2 delta_(rho=1) + k_I
k_I : sqrt(I) × sqrt(I) -> ℂ
Measurable (uncurry k_I)
Integrable (fun (u,v) => ‖k_I u v‖^2)
kernelAction(k_I) = K_I
```

The source symmetry of `k_I` may then prove self-adjointness separately. The
generic compact-kernel theorem in Connes--van Suijlekom, arXiv:2511.23257,
Theorem 3.1, applies only after this subtraction.

## Decision

```text
literal Q-delta function kernel: rejected
regular-part M3A route: still open
M3A milestone U5A: pending
```

This guard rejects an implementation error, not the corrected archimedean
route. The next proof obligation is an explicit formula and square-integrable
majorant for `k_I`.
