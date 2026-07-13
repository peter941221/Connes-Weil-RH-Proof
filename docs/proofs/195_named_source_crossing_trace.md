# Proof 195: Compact trace equals the named source-window crossing trace

Status: accepted crossing-layer milestone. The compact finite-prime trace now
equals the named source-window trace. The whole-line trace conversion,
semilocal metric variation, remainder control, sign gate, and RH remain open.

## Closed obligations

Proof 194 isolated three missing same-object facts:

```text
(C_(g*))† = C_g,
range(C_g T_b S†) subset range(E),
C_g C_(g*) = C_(g*) C_g.
```

`SelectedCrossingOperatorBridge.lean` now proves all three without an added
axiom or stored trace conclusion:

```text
fourier_compactLogTest_involution
  -> globalLogConvolution_involution_inner_core
  -> globalLogConvolution_involution_eq_adjoint
  -> adjoint_globalLogConvolution_involution

kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval
  + leftKernelGlobalRestrictionOperator_eq_globalTranslatedConvolution
  -> leftKernelAdjoint_range_factorization
  -> kernelIntervalProjection_zeroExtension
  -> sourceCyclicProjectionProduct_eq_uncompressed

fourierMultiplier_comm
  -> fourier_globalLogConvolution
  -> globalLogConvolution_comm
  -> sourceCyclicUncompressedProduct_eq_namedSourceCrossingProduct
```

The range factorization is the critical guard. It proves

```text
E L† = C_g T_b S†,
```

so `E E†` is removed only after its input is explicitly factored through
`E`. No global support claim is assumed, and `J_b` is never commuted through a
convolution operator.

## Result

`pairData_trace_eq_namedSourceCrossingProduct` proves

```text
Tr_kernel(pairData.traceProduct)
  = Tr_source(S C_g C_(g*) T_b S†).
```

This connects the same compact `A†B` trace used by
`SelectedCrossingKernel` to the positive convolution order on the source
window. The compact trace therefore retains its existing finite-prime atom
read-off while no longer depending on the projection shortcut rejected in
proof 194.

## Remaining bottom

The next equality is a trace identity between different Hilbert spaces:

```text
Tr_source(S A T_b S†)
  = Tr_global(A T_b S† S)
  = Tr_global(A J_b),

A = C_g C_(g*).
```

The second equality uses the already proved boundary-projection identity. The
first still needs legal Hilbert--Schmidt or trace-class data for the two-space
cycle. It is not an operator equality: `S A T_b S†` acts on the source
interval, while `A J_b` acts on the whole line.

## Verification

In an isolated WSL ext4 verification copy:

```text
lake build ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge \
           ConnesWeilRH.Dev.SelectedCrossingOperatorBridgeAudit

Build completed successfully (2979 jobs).
```

The focused audit reports only:

```text
propext
Classical.choice
Quot.sound
```
