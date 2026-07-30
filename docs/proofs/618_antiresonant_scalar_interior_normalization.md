# Proof 618: antiresonant scalar interior normalization

## Result

Proof 618 removes the scalar normalization from the sole survivor isolated by
Proof 617.

Let

```text
E         = radialSupportProjection,
N         = normalizedPrimeEulerInverse(p),
rho_p     = primeSchurMarkovScalar(p),
V_scalar  = rho_p^(-1) N,
R         = E N^dagger E.
```

Because `rho_p` is real, Lean proves

```text
V_scalar^dagger = rho_p^(-1) N^dagger.
```

Combining this with the signed radial reduction gives the exact active
pullback

```text
signedRow * V_scalar^dagger * E
  = rho_p^(-1) * signedRow * R.
```

The identity also holds after the actual new suffix frame:

```text
signedRow * V_scalar^dagger * newFrame_S
  = rho_p^(-1) * signedRow * R * newFrame_S.
```

## Why this matters

```text
+----------------------------+-------------------------------------------+
| layer                      | outcome                                   |
+----------------------------+-------------------------------------------+
| scalar right inverse       | isolated as the bounded scalar rho_p^-1   |
| radial exterior renewal    | already annihilated by Proof 617          |
| compressed interior R      | sole operator-valued survivor             |
| metric/forward cancellation| still open                                |
| Bone 1 uniform factor      | still open                                |
+----------------------------+-------------------------------------------+
```

The known estimate `rho_p^(-1) <= 8` means the scalar itself is harmless.
The remaining difficulty is entirely operator-valued: one must control the
same-object row `signedRow * R` uniformly in `(p,S)`.

## Boundary

This proof does not invert the geometric boundary crossing, bound `R`, or
split the metric and forward terms before their cancellation is visible.
Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.

## Verification

The focused source and import-facing audit build passed in the Ubuntu-24.04
WSL2 ext4 mirror with `3383` jobs.  Every audited declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.
