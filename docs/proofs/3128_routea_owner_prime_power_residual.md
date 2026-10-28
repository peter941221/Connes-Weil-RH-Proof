# Record 3128: Route-A owner-specific prime-power residual

Status: residual named and coordinate-normalized; no sign or bound proved.

## Definitions

For one `OrbitG8Geometry rho g` and angular frequency `xi`, the module

```text
ConnesWeilRH/Dev/C1RouteAOwnerPrimePowerResidual3128.lean
```

defines three quantities:

```text
routeAInfinitePrimePowerKernel geometry xi
  = sum over p in routeAVisiblePrimes geometry
      log(p) * routeAPrimePowerExpansion p xi

routeAActualFinitePrimeKernel geometry xi
  = primeKernel3120 (globalPrimeIndexSet g.convolutionSquare)
      (xi / (2*pi))

routeAOwnerPrimePowerResidual geometry xi
  = infinite kernel - actual finite kernel.
```

The finite kernel is tied to the same `g` carried by the geometry. The
`xi/(2*pi)` argument is the explicit conversion from Route-A angular
frequency to the cycle-frequency coordinate used by the 3120 physical kernel.

## Proved identities

The theorem

```text
routeAActualFinitePrimeKernel_eq_coordinateNormalizedSum
```

reads the actual finite owner kernel as

```text
sum over q in globalPrimeIndexSet g.convolutionSquare
  primeWeight3120(q) * cos(xi * log(q)).
```

The theorem

```text
routeAInfinitePrimePowerKernel_eq_actual_add_residual
```

proves the exact signed decomposition

```text
infinite kernel = actual finite kernel + owner residual.
```

The audit file is

```text
ConnesWeilRH/Dev/C1RouteAOwnerPrimePowerResidual3128Audit.lean
```

Both audited theorems depend only on `[propext, Classical.choice, Quot.sound]`.

## Boundary

The residual is now explicit and owner-specific, but it is not priced. No
claim is made that it vanishes, has a fixed sign, or is small enough for the
finite-core margin. The next admissible proof target is a signed bound for this
residual on the selected owner, with both frequency signs and the actual moving
prime-power set retained.
