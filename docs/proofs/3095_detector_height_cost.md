# 3095 - The unit detector target forces a height budget

Status: FORMAL necessary bound on the actual selected detector. No positive
Weil sign or RH conclusion.

A compact-log detector is a smooth function that vanishes outside a bounded
interval. Its Laplace transform integrates the function against `exp(s*x)`.
The detection pin makes this transform equal one at a selected complex node.
The first derivative's L1 mass is the integral of the derivative's magnitude;
it measures the total amount of variation available to maintain that pin.

For a test `f`, support radius `B >= 0`, strip bound `|Re(s)| <= A`, and
`|laplaceAt(f,s)| >= 1`, the new theorem proves:

```text
|Im(s)| <= exp(A*B) * derivOrderL1(1,f).
```

The proof applies the existing integration-by-parts estimate from record 2722
at derivative order one, then uses `|Im(s)| <= |s|`. No numerical value or
special-function approximation is an input.

The theorem `selected_detector_height_le` instantiates the bound on the
actual `geometry : OrbitG8Geometry rho g`. Record 3092 now exposes its existing
interpolation pin as `routeAOwner_laplaceAt_rho_eq_one`. With
`L = geometry.orbitIndex + 2`, this gives:

```text
|Im(rho)| <= exp(|Re(rho)-1/2| * L) * derivOrderL1(1,g).
```

The parameterized no-go is precise: a fixed test with a fixed support and
first-derivative budget cannot have unit targets at arbitrarily large heights
inside a fixed strip. It does not assert that off-line zeros exist at such
heights, or prevent the test, support, and derivative budget from varying with
`rho`. It is not a uniformity requirement on a future RH proof.

Source: `ConnesWeilRH/Dev/C1DetectorHeightCost3095.lean` and paired audit.
Integration evidence and the reproducible command are recorded in 3096.
