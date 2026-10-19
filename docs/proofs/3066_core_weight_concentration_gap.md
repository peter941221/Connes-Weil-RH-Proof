# Core-window reduction does not imply concentration (record 3066)

Date: 2026-10-19.

Status: source-level direction audit. Record 3065 validly removes the two
frequency regions outside a fixed window for one fixed hypothetical zero.
This audit identifies a further condition needed before interpreting the
remaining sequence as a concentration argument. It is not a no-go theorem and
does not change the binding Route-A producer target.

## Exact base information in the construction

The base is produced by
`exists_affine_base_with_unit_targets_and_quadratic_decay` in
`Dev/C1P2BaseSeminormBound.lean`. Its contract supplies:

```text
support(base) inside the chosen interval
laplaceAt(base, z) = 1 for each z in the finite target set
|t/(2*pi)|^2 * |laplaceAt(base, sigma+i*t)| <= C
```

Because the target set contains `1/2`, the actual core factor satisfies
`B(1/2)=1`. The interface supplies no pointwise bound
`|B(1/2+i*t)|<=1` on the core interval, and no positivity of the base test.
The separate half-contraction theorem proves `|B|<=1/2` only for `|t|>=T`.

## Consequence for record 3065

The annulus estimate is valid: on `T<=|t|<=T*`, its proof uses the proved
half-contraction, and the outer tail uses the explicit fourth-order estimate.
Neither argument needs a bound on the remaining interval `[-T,T]`.

However, the sequence

```text
Q_core,n = (1/(2*pi))*integral[-T,T]
             m_(S_n)(t) * |B(1/2+i*t)|^(2*(n+1)) * |D(1/2+i*t)|^2 dt
```

cannot be treated as a Laplace-style concentration at `t=0` from the current
premises. A normalized value `B(1/2)=1` alone does not imply that this point
is a local maximum of `|B|`; the factor can grow exponentially with `n` at
other core frequencies where `|B|>1`. Even if one later proves `|B|<=1`, a
concentration limit still needs control of the equality set `|B|=1`, the
vanishing order near it, and the changing symbol `m_(S_n)`.

Thus record 3065 remains a valid reduction to a fixed-window signed sequence,
but not a limiting formula for that sequence. Its no-lower-bound obstruction
is stronger than a missing estimate at the single point `t=0`.

## The positive-base shortcut is incompatible with the pinned values

The transform convention in `CC20YoshidaConvolution.lean` is
`B(s)=integral exp(s*x)*b(x) dx`. Consider the natural attempt to obtain the
core bound by requiring `b` to be real and nonnegative. Since the target set
contains `1/2`, `1`, and `3/2`, its pinned values give
`B(1/2)=B(1)=B(3/2)=1`. Define the probability measure
`dmu(x)=exp(x/2)*b(x) dx`; its total mass is `B(1/2)=1`. For
`Y(x)=exp(x/2)`, the other two pins give `E_mu[Y]=1` and `E_mu[Y^2]=1`, so
`Var_mu(Y)=0`. Hence `Y=1`, and therefore `x=0`, almost everywhere for mu.
But mu has a continuous density supported in an interval, so it cannot be a
unit point mass. This contradicts its total mass one. Thus the existing three
real pins rule out a nonzero nonnegative smooth base. Positivity cannot be
added as the simple route to a characteristic-function modulus bound; another
core-envelope mechanism would be needed.

There is a precise consequence for the usual global L1 estimate. Put
`f(x)=exp(x/2)*b(x)`. The pin at `1/2` gives `integral f=1`, so
`integral |f| >= 1`. Equality in the integral triangle inequality would force
`f` to be real nonnegative almost everywhere; the three-pin variance argument
rules that out. Therefore every admissible smooth base satisfies
`integral |exp(x/2)*b(x)| > 1`. This does NOT prove that
`|B(1/2+i*t)|>1` at any frequency: cancellation can keep a Fourier transform
below one despite total variation above one. It does prove that the direct
bound `|B(1/2+i*t)| <= integral |exp(x/2)*b(x)|` cannot supply the needed
unit core envelope, and raising that crude bound to the orbit power gives a
base greater than one rather than a decaying factor.

## Next mathematical gate

Before deriving a limit or a core lower bound, inspect the exact constructed
base and determine whether its affine interpolation mechanism admits a
certified core-envelope theorem such as `|B(1/2+i*t)|<=1`, or a weaker
owner-specific upper envelope with a characterized maximizer set. If neither
follows from the construction, keep `Q_core,n` as a varying signed integral
and seek a direct same-owner credit-deficit inequality. Any added base
constraint must preserve the existing finite interpolation targets and the
half-contraction/tail bounds.

This is a scoped direction gate, not permission to replace the selected base,
freeze `S_n`, or discard signed cancellation. The binding producer remains
the selected-detector signed physical-kernel/C3' budget recorded in root
`AGENTS.md`.

Evidence:

- `Dev/C1P2BaseSeminormBound.lean`, theorem
  `exists_affine_base_with_unit_targets_and_quadratic_decay`.
- `Source/CC20YoshidaConvolution.lean`, theorem
  `exists_laplaceAt_vertical_half_contraction_of_quadratic_bound`.
- `Source/CC20YoshidaConvolution.lean`, definition `laplaceAt`, fixes the
  positive-exponent bilateral Laplace convention used in the variance argument.
- `docs/proofs/1738_selected_orbit_joint_symbol_and_tail_sampling.md`, exact
  same-owner joint Fourier formula.
- `docs/proofs/3065_core_window_reduction_under_orbit_growth.md`, valid
  annulus/tail estimates and varying-core conclusion.
