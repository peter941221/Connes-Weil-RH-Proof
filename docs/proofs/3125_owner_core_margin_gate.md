# 3125 - Same-owner finite-core margin gate

Date: 2026-10-27.

Status: scoped direction gate. The existing owner data proves high-frequency
tail control, full Fourier mass normalization, and a strictly positive
deficit for the actual owner. It does not prove the finite-core signed lower
bound required by the growing-orbit reduction. No RH conclusion follows.

## The exact target

For one fixed `OrbitG8Geometry rho g`, let

```text
G(xi) = routeAOrbitTransform geometry xi
m(xi)  = routeAJointSymbol geometry xi
Qcore(T) = (1/(2*pi)) * integral_{|xi| <= T} m(xi) * |G(xi)|^2 dxi.
```

For the epsilon schedule in record 3064, the whole-line sign proof reduces to

```text
Qcore(T) >= E_ann + E_tail,
```

with the same owner used in `G`, `m`, the visible-prime set, and the tail
certificate. The right side is nonnegative and tends to zero in the fixed-
owner growing-orbit reduction. A lower bound `Qcore(T) >= -o(1)` is not enough:
the detector can remain strictly negative while converging to zero.

## What the current Lean fields actually imply

1. `FourthOrderSpectralTail` in
   `ConnesWeilRH/Dev/C1SpectralTailBound.lean` quantifies only points with
   `T <= |z.im|`, `1 <= |z.im|`, and `2*|rho.im| <= |z.im|`. Its derived
   theorems `spectralTerm_norm_tail_instance_of_fourthOrderTail` and
   `spectralTail_norm_shellSum_le_of_fourthOrderTail` are dyadic high-shell
   bounds. They do not quantify over `|xi| <= T`.

2. The same owner has an exact total Fourier-mass identity in
   `ConnesWeilRH/Dev/C1RouteAReadbackNormalization3094.lean`:

   ```text
   integral_R |G(xi)|^2 dxi = 2*pi*(g.convolutionSquare.test 0).re.
   ```

   This is a mass normalization, not a signed lower bound. It gives no way to
   replace `m(xi)` by its positive part on the core.

3. The actual owner is nonzero, and the local negative-symbol mechanism is
   formalized in `C1RouteANegativeEnergyWitness3093.lean`. Therefore a
   pointwise nonnegative-square argument is unavailable. The exact different
   physical gate in `C1ActualWeilUnavoidableDeficit3122.lean` also proves a
   strictly positive deficit integral for every nonzero owner. This reinforces
   the need for cancellation-sensitive positive credit; it does not provide
   that credit.

4. A repository-wide exact search found no declaration that consumes
   `OrbitG8Geometry.raw_square_tail` and returns either
   `integral_{|xi| <= T} xi^2*|G(xi)|^2`, a lower bound for `Qcore`, or a
   same-owner credit-minus-deficit margin. The closest records are 3054,
   3055, 3058, 3065, 3066, 3080, 3094, and 3122; each explicitly preserves
   the finite-core obligation.

## First-principles consequence

The tail certificate is an exterior constraint. The core target is a signed
weighted integral. The missing implication would have to connect these two
different objects:

```text
exterior decay of G
        + finite interpolation pins
        + support and moving visible-prime owner
        + exact symbol readback
        ------------------------------------------------
        -> quantitative positive credit on the same finite core.
```

No inequality in the current API supplies that arrow. Adding a generic
`D/M` estimate would only bound an auxiliary continuous term and would not
prove the required signed credit. Adding `|B(1/2+i*xi)| <= 1` would also be
unsound: the base interface proves `B(1/2)=1` and half-contraction only for
`|xi| >= T`, not a unit envelope on the core (record 3066).

## Stop condition and next admissible move

Stop this branch until one of the following is supplied for the actual moving
owner:

```text
1. A certified lower bound for Qcore(T), with the complete owner prime set;
2. A theorem that converts the existing pins plus raw_square_tail into such a
   lower bound, including the low-frequency mass and signed symbol;
3. A changed construction hypothesis that proves a core envelope or a
   positive-credit mechanism, followed by an owner-preserving audit.
```

Any future numeric probe must price `Qcore`, `E_ann`, and `E_tail` in one run,
with both frequency signs, the exact visible-prime owner, and a continuum
error certificate. A sampled core integral or a fixed-prime-set estimate is
not an admissible replacement.

Evidence:

- `ConnesWeilRH/Dev/C1SpectralTailBound.lean`
- `ConnesWeilRH/Dev/C1G8R0OrbitGeometry.lean`
- `ConnesWeilRH/Dev/C1RouteAJointSymbolData3080.lean`
- `ConnesWeilRH/Dev/C1RouteAReadbackNormalization3094.lean`
- `ConnesWeilRH/Dev/C1RouteANegativeEnergyWitness3093.lean`
- `ConnesWeilRH/Dev/C1ActualWeilUnavoidableDeficit3122.lean`
- `docs/proofs/3054_fourth_order_tail_to_derivative_energy.md`
- `docs/proofs/3055_finite_laplace_pins_do_not_bound_derivative_energy.md`
- `docs/proofs/3065_core_window_reduction_under_orbit_growth.md`
- `docs/proofs/3066_core_weight_concentration_gap.md`
