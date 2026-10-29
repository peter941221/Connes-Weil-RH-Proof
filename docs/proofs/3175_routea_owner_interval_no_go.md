# 3175: Route-A owner interval certificate no-go guard

Status: `LEAN-VERIFIED` on 2026-10-29 under the project Lean 4.30.0
toolchain.

This theorem closes one producer-boundary question. It does not construct a
certificate, produce numerical intervals, prove `SourceRH`, or claim RH.

## The audited theorem

```text
ConnesWeilRH.Source.C1RouteAOwnerNodeIntervalCertificate3175
  .no_owner_node_interval_certificate_of_right_off_line_zero
```

For an owner-specific `OrbitG8Geometry rho g`, assuming

```text
rho.1.re != 1 / 2
1 / 2 < rho.1.re
```

the theorem concludes:

```text
not Nonempty (RouteAOwnerNodeIntervalCertificate geometry)
```

`OrbitG8Geometry` is the exact detector/zero/frequency owner used by the
consumer. A `RouteAOwnerNodeIntervalCertificate` is a proved lower/upper
interval for that same signed physical-kernel node plus its aggregate upper
budget. A midpoint interval, another detector, or a support norm is a
different object and cannot discharge this contract.

## Proof chain

```text
+--------------------------------------------------------------+
| same-owner interval certificate                              |
+------------------------------+-------------------------------+
                               v
+--------------------------------------------------------------+
| orbitWindowSemiLocalGate...                                  |
| ICgate g.convolutionSquare <= 0                              |
+------------------------------+-------------------------------+
                               v
+--------------------------------------------------------------+
| healthy geometry under a right-hand zero                     |
| ICgate g.convolutionSquare > 0                               |
+------------------------------+-------------------------------+
                               v
                         linarith contradiction
```

The result is a guard: it rejects the simultaneous assumption of a right-hand
off-line zero and a genuine same-owner interval certificate. It does not
supply the missing producer data.

The remaining producer obligation is:

```text
same-owner source-transform enclosure
        + signed physical-kernel enclosure
        + coefficient enclosure
        + finite-window and full-line/tail enclosure
        + exact orbitVisiblePrimeRange support
        ------------------------------------------------
        = lower[n], upper[n], aggregate_upper <= 0
```

## Lean artifacts and evidence

```text
ConnesWeilRH/Dev/C1RouteAOwnerNodeIntervalCertificate3175.lean
ConnesWeilRH/Dev/C1RouteAOwnerNodeIntervalCertificate3175Audit.lean
build-logs/3175_wsl_build.log
build-logs/3175_wsl_audit.log
```

The WSL2 ext4 gate was checked with:

```text
lean-toolchain = leanprover/lean4:v4.30.0
Lean (version 4.30.0)
```

The focused target completed with 3796 jobs; the audit completed with 3797
jobs. The audit output was:

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

The complete target and audit logs contain no `error:`, `sorry`, `admit`, or
`sorryAx` hits. Existing linter warnings are non-blocking.

## Nonclaims

- This record does not prove or disprove RH.
- It does not construct a `RouteAOwnerNodeIntervalCertificate`.
- It does not show that every future Route-A selector fails.
- It does not transfer Route-B, row-B, midpoint, or norm results to the
  selected Route-A owner.
