# Proof 442: Canonical synchronized Euler energy

Date: 2026-07-20

## Result

The selected compact Weil square determines its own finite prime-power family.
For that family, the genuine synchronized prime-power mode energy has a
support-only polynomial bound:

```text
canonicalSynchronizedEulerModeEnergy owner
  <= 2 * (owner.supportRadius + log 3)
       * (1 + owner.supportRadius + log 3)
```

The source file is:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCanonicalEulerEnergy.lean
```

The focused declaration audit is:

```text
ConnesWeilRH/Dev/CCM24FiniteSCanonicalEulerEnergyAudit.lean
```

## Same-family construction

`FinitePrimePowerFamily.ofSelectedOwner` maps the exact nonzero prime-power
support of one selected square to canonical `(p,m)` coordinates.  Its visible
prime list is deduplicated.  Every visible base satisfies

```text
p < owner.globalIndexBound
owner.globalIndexBound < 3 * exp owner.supportRadius
```

The elementary harmonic estimate then gives

```text
canonicalEulerSquareEnergy owner
  <= 2 * log(owner.globalIndexBound)
       * (1 + log(owner.globalIndexBound))
```

and hence the support-radius bound above.

## Actual mode ledger

The module now defines

```lean
canonicalSynchronizedEulerModeEnergy
```

as the sum, over the same visible-prime list, of

```text
sum' n, integral alpha in [0,1],
  parameterizedPrimeEulerModeBoundaryEnergy alpha p n
```

The existing synchronized mode calculation proves

```lean
canonicalSynchronizedEulerModeEnergy_le_canonicalEulerSquareEnergy
```

by summing the exact one-prime geometric majorants.  The support-radius
theorem follows without changing the selected family.

## Boundary

This is a diagonal square-energy result.  It does not bound a coherent sum of
translated boundary vectors.  The repository keeps the identical-mode guard:

```text
analysis square = n
coherent synthesis square = n^2
```

Therefore the remaining analytic producer must use the complete numerator and
the Burnol boundary geometry before taking an absolute value.  The completed
relative trace, Gate 3U, the finite-`S` sign, Burnol's identity, and RH remain
open.
