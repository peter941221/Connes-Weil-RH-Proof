# Proof 698: Completed-History Composition Guard

## What is established

The completed physical terminal assembly has two components:

```text
terminal = rightLeg ∘ inclusion ∘ survivor ∘ input
target   = rightLeg ∘ endpoint - rightLeg ∘ inclusion ∘ survivor
```

The exact Lean identity is:

```text
terminal + target ∘ input = rightLeg ∘ endpoint ∘ input
```

The new theorem
`PhysicalBoundaryDaggerReadoutContract.exists_completed_readout_of_physicalBoundaryDaggerTarget`
therefore constructs a bounded readout of the completed rectangular column
only for the composed endpoint `(rightLeg ∘ endpoint) ∘ input`.

The companion theorem
`PhysicalBoundaryDaggerReadoutContract.exists_completed_readout_of_physicalTarget_of_denseRange`
uses `DenseRange input` and `DenseRange.equalizer` to extend that equality to
the uncomposed endpoint. This is a valid consumer bridge, but the dense-range
premise is still a source obligation.

## Why the stronger conclusion is invalid

The contract has source type `H` and the endpoint has source type `H`, but the
terminal equation is an equality of maps whose right side already contains
`input : H ->L H`. The algebra reconstructs that same composed map. Removing
`input` would require an additional theorem such as surjectivity of `input`
or an independent factorization of the endpoint through the completed column.
Neither is present, and assuming one would alter the source contract.

```text
component contract  --->  endpoint ∘ input
                              |
                              +-- not endpoint itself

Gate 3U consumer    --->  ambient/full endpoint control
```

## Radial consequence

The finite radial bridge has the independent structure

```text
complete cofactor = readout ∘ finite radial column
```

and Douglas proves this exactly when

```text
||complete cofactor x||² <= bound² ||finite radial column x||²
```

The finite-column construction from Proof 639 gives a prefix and a translated
tail. It proves pointwise convergence after fixing the source vector, but not
uniform operator boundedness or the required kernel containment. Hence it
cannot be promoted to the missing Gate 3U producer.

## Verification status

Proof 697's focused source, audit, `CCM25Concrete` aggregate, and full WSL2
build passed. The declarations use only
`[propext, Classical.choice, Quot.sound]`. No Gate 3U, finite-S sign, Burnol
identity, or unconditional `_root_.RiemannHypothesis` theorem follows.
