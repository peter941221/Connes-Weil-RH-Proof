# Proof 190: Global Log Smoothed Crossing Trace-Class Producer

## Route obligation

Provide the first genuine trace-class producer for the global logarithmic
crossing without storing a trace conclusion or mixing witnesses.

## Producer

For a translation length `b`, smoothing vectors `k` and `h`, define

```text
R_(k,h) u = <h,u> k
J_b(k,h) = (I-P_+) U_b P_+ R_(k,h)
```

in `GlobalLogCrossingTraceClass.lean`.  The identity

```text
J_b(k,h) = rankOne ((I-P_+) U_b P_+ k) h
```

is proved from `InnerProductSpace.comp_rankOne`, so the smoothing and crossing
remain attached to the same vectors and the same `b`.

The canonical public specialization is
`cc20SourceTestSmoothedCrossing p b`.  It sets both smoothing vectors equal to
the exact global `L2` representative `cc20LogPullbackLp p` of one
`PositiveIntervalCompactTest p`; no second source-test witness is introduced.

## Trace-class proof

For a Hilbert basis `e_i`,

```text
||J_b(k,h)e_i||²
  = ||(I-P_+)U_bP_+ k||² * |<h,e_i>|².
```

The coefficient series is summable by the Hilbert-basis Bessel inequality;
the fixed crossing norm is a finite scalar.  This proves
`cc20SmoothedCrossing_basis_normSq_summable`.  The existing
`PositiveTrace.BasisHilbertSchmidtData` then supplies trace-class legality of
the positive composition and nonnegativity of its ordinary diagonal trace.

## Verification target

The retained-cache WSL verification passed:

```text
lake build ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossingTraceClass
Built ... GlobalLogCrossingTraceClass (2953 jobs)

lake env lean ConnesWeilRH/Dev/GlobalLogCrossingTraceClassAudit.lean
axioms: propext, Classical.choice, Quot.sound

lake build ConnesWeilRH.Source.CC20Concrete
Build completed successfully (3506 jobs)
```

The audit checks declarations through `@`, so the printed types expose hidden
premises as well as the reported axioms.

## Boundary

This is a rank-one smoothing producer, not yet the full Schwartz convolution
crossing.  It does not identify the trace with the selected diagonal integral,
does not provide the finite-prime read-off, and does not rewire the RH route.
The next producer should replace the rank-one smoother with the same-object
Schwartz convolution once its half-line kernel-energy estimate is available.

The exact ordinary trace calculation now sharpens this boundary:

```text
Trace(J_b o rankOne(k,h)) = <h,J_b k>.
```

Consequently the rank-one producer cannot be reused as the operator whose
trace is `b(F(b)+F(-b))`; that scalar belongs to the convolution-smoothed
crossing `C_h* C_h J_b`.
