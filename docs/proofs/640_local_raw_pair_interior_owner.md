# Proof 640: local raw-pair owner of the signed interior

## Result

Proof 640 connects the existing actual local raw-defect Hilbert--Schmidt pair
to the genuine antiresonant signed interior.  This is an exact fixed-suffix
operator identity, not a uniform estimate.

Let

```text
P = suffixActualBandLocalRawDefectPairData,
L = suffixActualBandLocalRawDefect,
T = suffixEulerFrameTransition,
R = suffixEulerFrameReverseTransition,
rho = primeSchurMarkovScalar.
```

The repository definition fixes the pair orientation:

```text
P.traceProduct = P.left^dagger * P.right = L.
```

Swapping the two Hilbert--Schmidt legs reverses this product rather than
preserving it:

```text
P.swap.traceProduct
  = P.right^dagger * P.left
  = P.traceProduct^dagger
  = L^dagger.
```

The new pair owner applies the exact bounded sandwich and scalar cofactor:

```text
InteriorPair
  = smulRight(-rho^-1,
      boundedSandwich(T^dagger, R^dagger, P.swap)).

InteriorPair.traceProduct
  = -rho^-1 * T^dagger * L^dagger * R^dagger
  = signedCompressedInteriorOwner.
```

The final equality is Proof 623's existing two-sided cofactor identity.  No
cyclic trace rewrite, commutation, norm inequality, or inverse-Gram premise is
used.

## Carrier guard

The original `pairedBoundaryBasis` is a basis only for

```text
WithLp 2 (B x B).
```

The local defect pair itself lands in the larger nested carrier

```text
WithLp 2 ((WithLp 2 (B x B)) x (WithLp 2 (B x B))).
```

The new owner therefore accepts a separate Hilbert basis for this full target
carrier.  Reusing the smaller basis would be a type-level carrier mismatch.

## Boundary

This result gives a genuine Hilbert--Schmidt pair owner for each fixed
`(p,S)` after the existing support and prolate summability witnesses are
provided.  It does not make those witnesses uniform in the suffix, and it
does not prove a family-uniform bound for either pair leg or its trace
product.  Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and RH remain
open.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalPairOwner.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalPairOwnerAudit.lean
```

## Verification

The independent Ubuntu-24.04 WSL2 ext4 build passed:

```text
+------------------------------------------+------+--------+
| target                                   | jobs | result |
+------------------------------------------+------+--------+
| Proof 640 source                         | 3391 | PASS   |
| Proof 640 focused audit                  | 3392 | PASS   |
+------------------------------------------+------+--------+
```

The three audited operator theorems depend exactly on
`[propext, Classical.choice, Quot.sound]`.
