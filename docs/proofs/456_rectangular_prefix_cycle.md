# Proof 456: Rectangular finite-prefix cycle

## Result

Proof 456 replaces the previously forbidden infinite-dimensional rectangular
trace cycle by an exact two-prefix ledger.  For `A : H -> G`, `B : G -> H`,
and independent source/target prefix sizes, Lean proves

```text
Tr M_G(A B)
  = Tr M_H(B A)
    + Tr(target product defect)
    - Tr(source product defect).
```

The two defects record the failure of the rectangular prefix matrices to
preserve composition on their respective carriers.

## Actual quadratic response

Applying the ledger to the four base/jet/frame/dual factor pairs gives

```text
Tr M_global(actualBandQuadraticRootResponse)
  = Tr M_source(actualBandQuadraticCycledResponse)
    + actualBandQuadraticRectangularBoundaryTrace.
```

The four boundary discrepancies keep the signs

```text
jet/base + base/jet - base/base + dual/frame.
```

Using `quadratic = firstJet - endpoint`, the final endpoint ledger is

```text
Tr M_global(rootSandwichedBandResponse)
  = Tr M_global(actualBandFirstJetRootResponse)
    - Tr M_source(actualBandQuadraticCycledResponse)
    - actualBandQuadraticRectangularBoundaryTrace.
```

Thus the existing family-uniform first-jet owner and the source completed
response are now connected to the literal ambient endpoint without an
infinite rectangular trace cycle.

This is the finite-prefix bridge between the ambient quadratic endpoint and
the source-carrier completed response from Proofs 440--444.  No raw
rectangular leg is declared Hilbert--Schmidt, and no infinite trace cycle is
used.

## Boundary

Proof 456 is an exact carrier bridge, not a uniform estimate.  The next
producer must combine the source completed-response owner with the four
rectangular boundary discrepancies and Proof 455's root-cycle defect before
taking an absolute value.  Gate 3U, the finite-`S` sign, Burnol's identity,
and `_root_.RiemannHypothesis` remain open.
