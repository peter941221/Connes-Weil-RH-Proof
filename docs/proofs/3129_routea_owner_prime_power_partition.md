# Record 3129: Route-A owner prime-power partition

Date: 2026-10-27.

Status: arithmetic partition implemented; residual and continuum margin remain
unpriced.

The Lean module

```text
ConnesWeilRH/Dev/C1RouteAOwnerPrimePowerPartition3129.lean
```

proves the following owner-preserving facts:

```text
actual globalPrimeIndexSet
        |
        +-- every index is a prime power
        +-- every index lies inside the geometry cutoff
        +-- its prime base lies in routeAVisiblePrimes
        v
routeAPrimePowerClosureWithinCutoff
```

The closure is then classified into three bookkeeping classes at the
membership level:

```text
prime-power closure
        |
        +-- actual globalPrimeIndexSet
        +-- cutoff-internal owner omissions
        +-- cutoff-external infinite prime-power tail
```

The module also proves the arithmetic read-off
`vonMangoldt (p^(k+1)) = log p`.  The 3120 coefficient readback remains in the
separate physical-kernel module and is not imported here.  This module does
not prove closure equality with the actual owner, a residual sign, or an
integral bound.

The companion probe is

```text
scripts/routea_owner_prime_power_partition_probe_3129.py
```

It requires an actual owner manifest containing the moving
`globalPrimeIndexSet`, visible-prime list, cutoff, and owner digests.  Without
that manifest it emits `CONTROL-FAIL / OWNER-DATA-MISSING`.  Even with a
structurally valid manifest, it remains `CONTROL-FAIL` until an independent
continuum integral certificate is supplied and separately audited.

Evidence:

- `ConnesWeilRH/Dev/C1RouteAOwnerPrimePowerPartition3129.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerPrimePowerPartition3129Audit.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerPrimePowerResidual3128.lean`
- `ConnesWeilRH/Dev/C1G8R0OrbitGeometry.lean`
- `ConnesWeilRH/Dev/C1RouteAJointSymbolData3080.lean`
- `ConnesWeilRH/Dev/C1RouteBPrimeFourierReadback3120.lean`
