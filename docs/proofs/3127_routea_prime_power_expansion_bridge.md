# Record 3127: Route-A prime-power expansion bridge

Status: completed algebra bridge; producer and RH remain open.

## What was proved

For a prime `p` selected by the same `OrbitG8Geometry` owner and a real
frequency `xi`, define

```text
z(p, xi) = p^(-1/2) * exp(i * log(p) * xi).
```

The Lean theorem

```text
ConnesWeilRH.Source.C1RouteAPrimePowerExpansion3127.routeAPrimePoissonSymbol_eq_primePowerExpansion
```

proves

```text
routeAPrimePoissonSymbol p xi
  = 2 * Re (sum_{k >= 0} z(p, xi)^(k+1)).
```

The series is the complete infinite prime-power expansion for one prime.

## Proof structure

```text
prime p, frequency xi
          |
          v
  norm z(p, xi) < 1
          |
          v
  geometric series sum = z / (1 - z)
          |
          v
  Complex.div_re + exp(i*theta) = cos(theta) + i*sin(theta)
          |
          v
  exact Poisson rational multiplier
```

The contraction uses `p > 1`, so the proof does not accept a non-prime or a
fixed surrogate parameter. The denominator positivity is derived from
`1 - z != 0`, which follows from the same strict norm bound.

## Evidence

Source:

```text
ConnesWeilRH/Dev/C1RouteAPrimePowerExpansion3127.lean
```

Audit:

```text
ConnesWeilRH/Dev/C1RouteAPrimePowerExpansion3127Audit.lean
```

The audit output is:

```text
'ConnesWeilRH.Source.C1RouteAPrimePowerExpansion3127.routeAPrimePoissonSymbol_eq_primePowerExpansion' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Scope boundary

This record does not prove any of the following:

```text
infinite prime-power expansion = finite globalPrimeIndexSet sum
omitted prime-power residual = 0
omitted prime-power residual has a usable signed bound
Route-A finite-core lower bound Qcore(T) >= E_ann + E_tail
```

The next owner obligation is therefore to define the omitted residual for the
same geometry and price it with its sign retained. Until that is done, the
3122 physical-gate deficit result cannot be transported to Route A.
