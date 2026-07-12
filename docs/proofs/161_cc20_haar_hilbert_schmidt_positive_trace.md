# CC20 Haar Hilbert--Schmidt Positive Trace

Date: 2026-07-12

## Result

The source-correct Haar operator from `RegularKernelHaarL2.lean` now has the
same Hilbert--Schmidt and positive-trace legality layer as the earlier
Lebesgue-measure prototype.  The new declarations are:

```text
cc20CompactHaarComplexL2Operator_basis_normSq_summable
cc20CompactHaarComplexBasisHilbertSchmidtData
cc20CompactHaarComplexPositiveTrace_re_nonnegative
```

The proof uses the actual source measure `d rho / rho`, the same regular
kernel, compact-domain continuity, finite-basis Bessel bounds, and
`summable_of_sum_le`.  It does not store a source conclusion or use RH as a
premise.

## Verification

The WSL2 verification mirror reuses the existing `.lake` cache after a full
Windows-to-WSL source sync:

```text
lake build ConnesWeilRH.Source.CC20Concrete.RegularKernelHaarL2
lake env lean ConnesWeilRH/Dev/RegularKernelSourceBridgeAudit.lean
```

Both commands pass.  The import-facing audit prints the three declarations and
their axiom dependencies are only:

```text
propext
Classical.choice
Quot.sound
```

## Boundary

This is an analytic operator/trace legality layer, not the CC20 theorem
`thmqkey1`.  The separate diagonal `-2 Dirac_0` distribution, its quadratic
form as `-2 Id`, the full source trace read-off, finite-prime/pole terms, and
RH remain open.
