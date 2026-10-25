# Same-owner rho-dependent Route-B package (3106)

Date: 2026-10-25.

Record 3105 showed that fixed row-B caps cannot cover arbitrary heights. The
existing G8 construction already provides a rho-dependent owner for every
right-half hypothetical off-line zero. Record 3106 packages that construction
without changing its owner.

For a fixed `rho`, `RhoOwnerPackage3106 rho` contains:

```text
g          : CompactLogTest
geometry   : OrbitG8Geometry rho g
healthy    : HealthyYoshidaDetectorData rho g
```

The same `g` appears in all three fields. Lean proves:

```text
g = selectedOwner geometry.base geometry.correction geometry.orbitIndex
sourceTest

laplaceAt g (w - 1/2) = negativeSourceOrbitValue rho w
  for every source functional-equation orbit node w

support(g) ⊆ (-(orbitIndex+2), orbitIndex+2)
```

It also transports the height and inverse-gap costs to this exact package.
Thus target identity, support, healthy data and necessary budget costs no
longer rely on an informal “same owner” assertion.

This closes the owner-identity and construction layer of the parameterized
Route-B continuation. It does not prove `hgate24`, the three cardinal pins,
the row-B caps for arbitrary rho, or the final semi-local positivity. Those
remain the actual RH core.

Verification completed on Linux ext4: 3809 jobs, seven audited declarations,
no error lines or `sorryAx`, and the standard axiom trio on every declaration.
The reproducible checker is
`scripts/routeb_rho_owner_package_audit_3106.py` and the portable result is
`results/3106_routeb_rho_owner_package_audit.json`.
