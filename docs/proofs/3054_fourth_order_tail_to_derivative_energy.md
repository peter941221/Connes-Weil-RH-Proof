# Fourth-order spectral tail controls only the high-frequency derivative energy (record 3054)

Date: 2026-10-19.

Status: paper-level consequence of the existing owner tail contract and the
Fourier-Plancherel identity. No new Lean theorem or selected-owner sign result.

## Exact transform readback

Let `g` be the selected compact-log test, with

```text
M = integral_R |g(x)|^2 dx
D = integral_R |g'(x)|^2 dx
G(t) = laplaceAt g (i*t) = integral_R exp(i*t*x) g(x) dx.
```

The source theorem `laplaceAt_involution` states
`L(g.involution,s) = conjugate(L(g,-conjugate(s)))`. On `s=i*t`,
`-conjugate(s)=s`, so the convolution-square identity gives

```text
laplaceAt (g.convolutionSquare) (i*t) = |G(t)|^2.
```

This is the precise reason the `FourthOrderSpectralTail` field of
`OrbitG8Geometry` controls the modulus square of the selected test transform
on the critical line.

## Tail consequence

Write `rho = beta + i*gamma`, let `T` and `epsilon` be the geometry's tail
parameters, and put

```text
T_* = max(T, 1, 2*|gamma|).
```

Specialize `FourthOrderSpectralTail` to `z = 1/2 + i*t` for `|t| >= T_*`.
Both functional-equation distance factors are the same:

```text
|z-rho| = |(1-conjugate(z))-rho|
         = sqrt((1/2-beta)^2 + (t-gamma)^2).
```

Consequently the tail certificate implies

```text
|t-gamma|^2 * |G(t)| < epsilon.
```

Since `|t-gamma| >= |t|/2` when `|t| >= 2*|gamma|`,

```text
|G(t)| <= 4*epsilon/|t|^2,       |t| >= T_*.
```

## Plancherel split

With the unnormalized transform `G(t)=integral exp(i*t*x)g(x)dx`,
Plancherel gives

```text
M = (1/(2*pi)) * integral_R |G(t)|^2 dt,
D = (1/(2*pi)) * integral_R t^2*|G(t)|^2 dt.
```

Split the derivative integral at `T_*`. The low-frequency part satisfies
`t^2 <= T_*^2`; the high-frequency estimate above gives

```text
D <= T_*^2*M + (16*epsilon^2)/(pi*T_*),
D/M <= T_*^2 + (16*epsilon^2)/(pi*T_* * M),    M > 0.
```

This is a bridge from the existing fourth-order tail field to the derivative
energy in record 3053. It also isolates the obstruction: the tail field does
not control the low-frequency contribution except by the coarse factor
`T_*^2`. Since `T_* >= 2*|Im rho|`, this upper bound alone cannot establish
`D/M < 5*(K-4)` for large-height zeros. That failure is a failure of this
estimate to close the threshold, not proof that the actual owner violates the
threshold.

## What would sharpen it

The missing input is a same-owner bound on the low-frequency Fourier mass,
for example an estimate of

```text
integral_{|t| < T_*} t^2*|G(t)|^2 dt
```

in terms of `M` with a coefficient independent of the full tail threshold.
The finite Laplace interpolation pins are point evaluations away from the
critical Fourier line; they do not immediately provide this band-energy
bound. Record 3055 makes the limitation precise for the interpolation-only
class by constructing support-preserving null perturbations with unbounded
derivative-to-mass ratio; it explicitly does not preserve the full geometry's
tail field. Any proposed transfer must preserve the exact selected owner and
use both the actual interpolation nodes and its tail constraint. The
fourth-order tail alone gives no low-frequency estimate beyond the displayed
`T_*^2` bound.

Evidence:

- `ConnesWeilRH/Source/CC20YoshidaFullProduct.lean`, theorem
  `laplaceAt_involution`, supplies the involution transform law.
- `ConnesWeilRH/Source/CC20YoshidaConvolution.lean`, theorem
  `laplaceAt_convolution`, supplies transform multiplicativity.
- `ConnesWeilRH/Dev/C1SpectralTailBound.lean` defines the exact
  `FourthOrderSpectralTail` quantifiers used by `OrbitG8Geometry`.
- `ConnesWeilRH/Dev/C1XiCenterTwoGammaDerivativeEnergy.lean` defines the
  derivative-energy quantity used in record 3053.
- `docs/proofs/3055_finite_laplace_pins_do_not_bound_derivative_energy.md`
  gives the scoped interpolation-only counterfamily and its boundary.

The derivation uses the classical Plancherel theorem with the stated Fourier
normalization. It is not currently formalized as a Lean bridge in this repo.
