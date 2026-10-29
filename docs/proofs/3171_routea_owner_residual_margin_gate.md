# 3171: Route-A owner residual margin gate

Status: Lean-verified on 2026-10-29 with the project Lean 4.30.0 toolchain.

This record combines the 3170 residual allowance with the finite-owner kernel
allowance. It proves the parameterized same-owner implication:

```text
finite-owner allowance + residual allowance <= -c3Sigma xi
                                                              |
                                                              v
                                                routeAJointSymbol geometry xi >= 0
```

The premise is deliberately explicit. No numerical margin is supplied, no
residual integrability is inferred, and no SourceRH or RH conclusion follows
from this record alone.

Scope correction: this gate is a conservative diagnostic bridge, not the
binding producer. `routeAOwnerResidualAllowance` already contains the finite
kernel allowance, so the theorem's displayed margin condition counts that
allowance twice. The existing 3080 theorem
`routeAJointSymbol_lower_bound` gives the stronger direct lower bound using
only `routeAJointSymbolPrimeAllowance`. The live Route-A exit consumes the
same-owner finite signed physical-kernel budget through
`OrbitPhysicalKernelNodeCertificate`; future work should target that
certificate instead of strengthening this pointwise frequency bound.

The WSL2 audit reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```
