# 3170: Route-A owner residual absolute bound

Status: Lean-verified on 2026-10-29 with the project Lean 4.30.0 toolchain.

This record adds `C1RouteAOwnerResidualBound3170.lean`. It defines a
conservative owner-specific allowance as the sum of:

```text
prime-base allowance + finite-owner kernel absolute allowance
```

The file proves the finite kernel is bounded by the sum of absolute finite
kernel coefficients and transfers the existing 3080 prime-part allowance to
the infinite prime-power expansion using the exact 3127 identity.

The exported residual theorem is:

```text
|routeAOwnerPrimePowerResidual geometry xi|
  <= routeAJointSymbolPrimeAllowance geometry
     + routeAActualFinitePrimeKernelAllowance geometry
```

This is a feasibility bound only. It does not prove the allowance is below the
finite-owner margin, does not prove residual integrability, and does not imply
SourceRH or RH.

Verification used a Linux-native WSL2 workspace with:

```text
leanprover/lean4:v4.30.0
Lean (version 4.30.0)
```

The audit file `C1RouteAOwnerResidualBound3170Audit.lean` reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```
