# Record 3130: Route-A owner residual margin bridge

Date: 2026-10-29.

Status: Lean-verified on 2026-10-29 with the project Lean 4.30.0 toolchain.

## What was added

`ConnesWeilRH/Dev/C1RouteAOwnerResidualMargin3130.lean` defines the finite owner symbol, its energy density, and the owner residual energy density. It proves:

```text
routeAJointSymbol
  = routeAActualOwnerSymbol - routeAOwnerPrimePowerResidual

routeAFrequencyEnergyDensity
  = routeAActualOwnerEnergyDensity
    - routeAOwnerResidualEnergyDensity
```

It also states the whole-line integral decomposition under explicit `Integrable` premises for the actual and residual densities. These premises are intentional: the bridge does not invent a residual estimate or hide a continuum-integrability obligation.

## Why this matters

3128 named the owner-specific residual but did not connect it to the finite-core margin. Record 3130 turns that missing connection into one explicit target: prove an owner-specific integrability or bound for the residual density, then the finite-owner margin can be compared against its signed integral.

The theorem does not prove `Qcore(T)`, `SourceRH`, or RH. It also does not show the residual is small, nonnegative, or zero.

## Verification

The targeted native-WSL build generated the dependency chain through `C1RowBStoredCapture2722F`, `C1RouteBPoweredSeedCarrier3110`, `C1RouteBSignedPrimeCut3119`, `C1RouteBPrimeFourierReadback3120`, `C1RouteAOwnerPrimePowerResidual3128`, and this module. The source compiled without `sorry` diagnostics.

The audit file `C1RouteAOwnerResidualMargin3130Audit.lean` printed exactly:

```text
[propext, Classical.choice, Quot.sound]
```

for all three exported theorems. The native build required copying the repository `lean-toolchain` into the temporary WSL tree; without it Lean 4.33 was selected instead of the required Lean 4.30.0. This is a build-environment lesson, not a project-source dependency.
