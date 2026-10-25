# Forced near-collision cost in the healthy orbit data (record 3063)

Date: 2026-10-19.

Status: exact owner-specific necessary interpolation cost. It does not prove
the existence of off-line zeros near the critical line and is not an RH
no-go.

## A forced pair with different target values

Let `rho` be a source nontrivial zero with `Re(rho) != 1/2`, and write
`g = |Re(rho)-1/2| > 0`. The healthy unscaled target owner contains both

```text
s1 = rho,
s2 = 1-conj(rho).
```

The prescribed interpolation values are `F(s1)=1` and `F(s2)=-1`; the
second is the functional-equation companion value proved in
`C1HealthyYoshidaUnscaledOrbit`. Their exact distance is

```text
delta_rho = |s1-s2| = |2*Re(rho)-1| = 2*g.
```

Both nodes have real part in `(0,1)`. Thus the owner itself contains a
different-value near-collision whenever a hypothetical off-line zero lies
close to the critical line. No unknown zero-zero spacing is needed for this
pair.

## L1 cost lower bound

Let `F(s)=integral exp(s*x)*f(x) dx` with `supp(f) subset [-B,B]`, where
`B>0`, and suppose `F(s1)=1`, `F(s2)=-1`. Along the segment between the two
nodes the real part lies in `[0,1]`, so

```text
|F'(s)| = |integral x*exp(s*x)*f(x) dx|
        <= B*exp(B)*||f||_1.
```

Integrating the derivative along the segment gives

```text
2 = |F(s1)-F(s2)|
  <= 2*g*B*exp(B)*||f||_1,
||f||_1 >= 1/(B*exp(B)*g).
```

For the fixed-bump family, `B<=3/4`, so its mass is at least
`4/(3*exp(3/4)*g)`. For the existing `smoothSeed` actual-owner correction,
whose support is in `[-2,2]`, this gives at least `1/(2*exp(2)*g)`.

## Consequence for a quadratic strip constant

Suppose in addition that the same `f`, supported in `[-B,B]`, has a quadratic
strip constant `C` satisfying

```text
|F(i*t)| <= 4*pi^2*C/t^2,  t != 0.
```

This is the critical-line specialization of the record-3060 strip bound. By
Plancherel, with `M=||f||_2^2`,

```text
M = (1/(2*pi))*integral |F(i*t)|^2 dt.
```

On `|t|<=b0`, `|F(i*t)|<=||f||_1` and `||f||_1^2<=2*B*M`; choose
`b0=pi/(4*B)` so this low-frequency part costs at most `M/2`. On the two
tails, the displayed quadratic decay costs at most
`16*pi^3*C^2/(3*b0^3)`. Hence

```text
M <= 32*pi^3*C^2/(3*b0^3),
||f||_1 <= 64*B^2*C/sqrt(3),
C >= sqrt(3)*||f||_1/(64*B^2)
  >= sqrt(3)/(64*B^3*exp(B)*g).
```

The last inequality applies to any proposed construction that supplies this
same quadratic strip bound. In particular, for fixed support size its cost
cannot remain uniformly bounded as `rho` approaches the critical line.

## Route interpretation

Formal update (record 3096): `raw_factor_inverse_gap_mass` now proves the
inverse-gap L1 bound on the actual `orbitRawFactor geometry`, with
`B=geometry.orbitIndex+2`. The separate L1-to-quadratic-strip-constant
comparison remains a paper-level deduction. The new proof and audit
are documented in `docs/proofs/3096_detector_parameter_gate.md`.

This pins a real degeneration parameter in the RH contradiction owner:
`g=|Re(rho)-1/2|`. Any proof using this normalized interpolation correction
with support radius uniformly bounded over all off-line `rho` cannot have a
uniform strip constant; the necessary constant diverges at least like `1/g`.
It does not rule out a rho-dependent correction with growing support, because
the producer may allow its orbit index and support to vary with `rho`. It also
does not show that any actual off-line zero has small `g`.

The fixed-bump upper price has `delta_rho` among its node separations, so it
inherits a factor at least of inverse-gap type; the whole Vandermonde cost can
be much worse. The existing `smoothSeed` correction has node-product
denominators and the same necessary L1 blow-up. A valid next step must either
use the rho-dependent margin quantitatively in the full prime/archimedean
budget, or replace this interpolation owner with one whose normalization does
not force a unit jump across the collapsing pair.

Evidence:

- `ConnesWeilRH/Dev/C1HealthyYoshidaUnscaledOrbit.lean` defines the healthy
  target values `1` at `rho` and `-1` at its companion.
- `ConnesWeilRH/Source/CCM25Concrete/UnscaledYoshidaSelectedOwner.lean`
  proves the companion relation used by the healthy interpolation.
- `ConnesWeilRH/Dev/C1ExplicitHealthyCorrectionBudget.lean` gives the
  actual-owner `smoothSeed` correction and support bound `[-2,2]`.
- `docs/proofs/3062_near-collision_interpolation_cost_lower_bound.md` gives
  the general two-node derivative argument and the record-1738 Plancherel
  bridge.
