# Proof 544: Julia Schur contractivity producer

Result: good.  The Schur transfer contract is now produced automatically for
the actual parameterized finite-S Julia input.  Gate 3U and RH remain open.

## What It Is

This proof adds a lower-level contractivity producer (contractivity =
operator norm at most one) for the normalized Schur frame:

```text
normalizedSchurFrame^dagger normalizedSchurFrame <= I
```

The new source module is:

```text
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSJuliaSchurContractivity.lean
```

The route-facing adapter in
`CCM24FiniteSActualJuliaInput.lean` now exposes:

```text
parameterizedPrimeEulerProjectedJuliaInput_normalizedSchurFrame_contract

SuffixPrimeEulerProjectedJuliaSchurFrameStepData.ofGeneratedContract
```

The constructor removes only the explicit `transfer_contract` argument from
the step-data construction.  It still requires the weighted range-sine estimate
and the readback equality as explicit source inputs.

## Why It Works

The proof separates the algebra into three layers:

```text
strict complementary contraction
          |
          v
graph coordinate lives in the projection complement
          |
          v
(P + X) (I + X^dagger X)^(-1/2) is contractive
          |
          v
projection * Euler transport * graph frame
          |
          v
normalizedSchurFrame is contractive
```

The key structural point is orthogonality (orthogonality = zero cross terms):

```text
P X = 0
X^dagger P = 0

(P + X)^dagger (P + X)
  = P + X^dagger X
  <= I + X^dagger X
```

After conjugating by `(I + X^dagger X)^(-1/2)`, the graph frame has norm at
most one.  The concrete prime Euler transport contributes the known upper
bound `1 + a_p`, and the normalizer contributes `(1 + a_p)^-1`, so the
product is again contractive.

## Lean Producers

The focused audit checks these six declarations:

```text
ProjectedUnitaryColligation.graphFrame_norm_le_one

ProjectedUnitaryColligation.schurFrame_eq_projection_comp_euler_comp_graphFrame

PrimeEulerProjectedJuliaInput.normalizedSchurFrame_norm_le_one

PrimeEulerProjectedJuliaInput.normalizedSchurFrame_contract

parameterizedPrimeEulerProjectedJuliaInput_normalizedSchurFrame_contract

SuffixPrimeEulerProjectedJuliaSchurFrameStepData.ofGeneratedContract
```

The `#print` output for `ofGeneratedContract` shows the important boundary:
it auto-fills `transfer_contract`, but `rangeSine_weighted_le` and
`rangeSine_readback` remain parameters.  Therefore this is not a hidden
Gate 3U producer.

## Verification

Verified in the Ubuntu-24.04 WSL2 ext4 mirror:

```text
Ubuntu-24.04 WSL2 ext4 verification mirror
```

```text
+------------------------------------------+-------+--------+
| target                                   | jobs  | result |
+------------------------------------------+-------+--------+
| focused source modules                   | 3239  | PASS   |
| focused axiom audit                      | PASS  | PASS   |
| CCM25Concrete aggregate                  | 3814  | PASS   |
| full repository                          | 3895  | PASS   |
+------------------------------------------+-------+--------+
```

All six audited declarations use exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The new source and focused audit contain no `sorry`, `admit`, or user axiom
declaration, and the touched Proof 544 Lean files have no line longer than 100
characters.  Existing repository linter warnings are unchanged.

## Boundary

This proof closes only the Schur transfer-contract producer.  It does not
prove the weighted `rangeSine` estimate, the fixed-source Julia physical
readout equality, Gate 3U, the finite-S sign, Burnol's identity, or
`_root_.RiemannHypothesis`.
