# Proof 680: Same-Domain Root Sandwich for the Signed Radial Owner

## What changed

`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerRootSandwich.lean`
adds `RadialSignedOwnerRootS2Producer`.  It combines the existing
`CommonRootS2Producer` (common Hilbert--Schmidt root) with bounded left and
right maps on the original `finiteSCarrier`, and records the exact response
identity

```text
base.response = leftSandwich
  * radialSignedPhysicalOwner p S
  * rightSandwich.
```

The producer therefore consumes the complete signed owner, not one of its
carrier projections.

## Exact readback

Using Proof 679, the response has the same-domain normal form

```text
base.response
  = leftSandwich * (E * (-threeBranch)) * rightSandwich
    + leftSandwich * radialSoninBoundaryCrossing p S * rightSandwich.
```

The upper three-branch term and lower radial boundary term remain coupled as a
signed owner until a later source theorem supplies an estimate.

## Legality results

The module proves, from the common-root fields only:

- trace-class along the named source basis;
- compactness after supplying a target Hilbert basis;
- the generic ordinary-trace norm bound without branchwise absolute values.

It also exposes a direct consumer form: any supplied uniform bound on the
common root energy and on the left factor gives a uniform ordinary-trace bound
for the complete signed owner, with the same fixed constant as the generic
common-root theorem.

These are interface and legality results.  They do not prove the missing
route-uniform Gate 3U bound, finite-`S` sign, Burnol identity, or RH.

## Verification

Commands run in the Ubuntu-24.04 WSL2 ext4 mirror under the shared Lake lock:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
  ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerRootSandwich

flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
  ConnesWeilRH.Source.CCM25Concrete

flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
  ConnesWeilRH.Dev.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerRootSandwichAudit
```

Results:

```text
+----------------------+-------+--------+
| target               | jobs  | result |
+----------------------+-------+--------+
| focused source       | 3471  | PASS   |
| CCM25Concrete        | 3955  | PASS   |
| focused audit        | 3472  | PASS   |
+----------------------+-------+--------+
```

The six audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`.
