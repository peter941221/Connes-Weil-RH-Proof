# 1258 - G8 readback bridge boundary

Date: 2026-09-10.

Status: `FORMAL-BOUNDARY-AUDIT`; no `qw` sign or RH claim is made.  The
consumer is the binding healthy-`CompactLog`, detector-specific B5 route.

## 1. What is already connected

The G8 leaf now proves, on one fixed source owner,

* `g8SourceCutoffPairData_ordinaryTrace_eq_fourChannelLedger`: every finite
  cutoff trace splits into base, cross, adjoint-cross, and leakage channels;
* `sourceCompression_g8AdjointShearGram_cross_eq_targetResponse`: the
  uncut cross channel is the existing
  `finiteEulerTargetCommutatorResponse`;
* `sourceCompression_g8AdjointShearGram_eq_survivorBoundaryGram`: the full
  uncut compression factors through the terminal survivor and the finite
  visible-prime boundary sum;
* `g8SourceCutoffPairData_traceProduct_isTraceClass` and
  `g8SourceCutoffPairData_traceProduct_isPositive`: the cutoff source trace is
  legal and has nonnegative real part.

These are formal Lean results with the standard three axioms only.

## 2. The exact missing equation

The finite-prime ledger currently available elsewhere is

```text
projectionResponse
  = selectedEulerLogBoundaryPairOperatorSum + selectedEulerBoundaryResidual,
Tr(selectedEulerLogBoundaryPairOperatorSum)
  = sum of the finite visible-prime terms.
```

The G8 sequence, however, has the source-side form

```text
J* C_n* (I + N_S) W_g (I + N_S*) C_n J,
```

and its cross channel is `J* C_n* N_S W_g C_n J`.  No current declaration
identifies this cutoff expression with `projectionResponse`, with the literal
Euler-boundary sum, or with an explicitly controlled residual.  In particular,
the existing identity for the uncut cross channel only removes `C_n`; it does
not prove a cutoff-to-uncut limit, and the existing Euler-boundary trace
theorem lives on the projection-response owner rather than on this G8
cutoff owner.

Therefore the two fields of `G8SameOwnerReadbackData` cannot currently be
constructed from the repository's existing theorems.  Adding another adapter
would merely restate this missing equation.

## 3. Decision

The next substantive brick must be a genuine same-owner mathematical result:
an internal correction and a finite-cutoff trace identity that converts the G8
cutoff trace into the finite visible-prime terms plus a remainder, followed by
the remainder/limit proof.  Until that operator formula exists, no additional
Lean interface and no numerical campaign is authorized.  This is a precise
translation boundary, not a no-go theorem for a future semilocal owner.

RH is not claimed.
