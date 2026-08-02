# Proof 714: Seven-Step Execution Guard

## Result

The seven-step execution was started with an interface audit. The first
focused Lean build exposed two independent mismatches in Proof 713:

```text
Proof 712 output:
  rightLeg o endpoint
    = readout o completedRectangularBoundaryColumn

Proof 697 consumer input:
  rightLeg o endpoint
    = readout o completedRectangularBoundaryColumn o sourceInput
```

The missing `sourceInput` cannot be inserted by rewriting. The identity input
would make the domains match, but its Hilbert-basis energy premise is not a
valid infinite-dimensional energy ledger:

```text
Summable (fun i => ||sourceBasis i||^2)
```

For an orthonormal basis this is `Summable (fun _ => 1)`, which fails on an
infinite index type. The actual fixed physical source operator does have a
Hilbert--Schmidt energy bound, but Proof 712's uncomposed endpoint equality
does not imply the consumer's composed equality for that operator.

## Correct decomposition

```text
Lane 1  corrected Gate interface
  fixedPhysicalSourceInput energy
        |
Lane 2  actual completed physical readout producer
        |
Lane 3  translated convolution analytic representatives
        |
Lane 4  original-root Fourier analyticity/nonvanishing
        v
Gate 3U signed finite-S-uniform bound
        v
finite-S sign -> Burnol identity -> RH
```

Lane 1 cannot be completed until Lane 2 supplies a readout equality on the
actual source operator, or until the Gate consumer is generalized to consume
an uncomposed endpoint together with the correct physical energy ledger.

## Verification evidence

The modified source was synchronized to the Ubuntu-24.04 WSL2 ext4 mirror.
The dependency build reached the new Gate module and failed only at the new
interface boundary; all preceding dependencies built. The decisive Lean goals
were:

```text
readout o column = readout o column o input
unknown identifier hscaledInputEnergy
```

The attempted source edit was reverted. No invalid theorem was retained.

## Next executable targets

1. Add a consumer for the uncomposed endpoint equality, with the actual
   fixed-source Hilbert--Schmidt energy as a separate input.
2. Prove the source-specific completed physical readout equality, keeping the
   terminal survivor and all orientation residuals explicit.
3. Construct translated analytic representatives and original-root Fourier
   analyticity as independent producers.
4. Only then instantiate the Gate 3U signed uniform estimate.

Gate 3U, the finite-S sign, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.
