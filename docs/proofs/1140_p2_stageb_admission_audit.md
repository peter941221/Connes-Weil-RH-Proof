# Record 1140 - P2 Stage-B admission audit

Date: 2026-09-05.

Status: FORMAL boundary result; P2 remains open.  Consumer: the healthy
`CompactLog`, B5-shaped detector-specific semi-local chain ending at
`sourceRH_of_orbitWindowSemiLocalGate`.  RH is not claimed.

This record audits the three-part P2 work order.  The existing Stage-B code is
kept as an assembly interface.  It packages a certified window, a defect bound,
and a budget into `ICStageBContraction`; it does not produce the defect bound.
The concrete q28 class-window producer remains separately open: record 1139's
closed-table checkpoint still uses `native_decide`, so its public Hbox theorem
has not passed the standard-axiom audit.

## Formal admission check

The new theorem
`C1T2Assembly.no_stageB_budget_of_qw_negative` proves the following.  If the
same detector has `qw g < 0`, if a window has certified gate at most `-mu`, and
if the one-window defect satisfies `epsilon <= mu`, then `False` follows.
The proof uses only the existing same-owner identity

```text
qw(g) = -archimedeanTerm(g.square) - finitePrimeSum(g.square)
```

and the exact defect identity

```text
gate(defect) = gate(g.square) - gate(W.square).
```

Thus the already-formal negative detector branch implies
`0 < gate(g.square)`.  A negative window certificate plus the proposed budget
would imply `gate(g.square) <= 0`.  The contradiction is a kernel-checked
boundary result, not a numerical experiment.

## Consequence for the work order

The Stage-B interface remains useful for final assembly, but the requested
defect estimate cannot be obtained from detector negativity, window
certificate, and budget bookkeeping.  A real P2 producer must supply an
additional inequality whose proof uses the detector construction and the
zero-configuration data.  High-frequency quadratic Laplace decay alone does
not have the required conclusion: it is a different hypothesis from the gate
of the defect, which includes the archimedean integral and all visible prime
powers.

The concrete work is therefore split as follows:

1. Replace the 1139 `native_decide` checkpoint by a kernel-checked, generated
   rational certificate, then prove the true M-side interval bounds.
2. Keep the existing 1123 assembly and use it only after an independently
   proved detector-specific defect inequality is available.
3. Treat that inequality as the P2 admission gate.  Any proposed producer must
   state its norm, control the visible prime evaluations, and prove the budget
   without assuming `qw(g) >= 0` or an equivalent gate statement.

No route selection changes.  This record narrows the open P2 obligation and
prevents a circular closure through the Stage-B interface.

## P2-α first brick (2026-09-05)

`C1P2DefectControl.lean` now proves the non-circular finite-prime half:

```lean
|finitePrimeSum F| ≤
  ∑ n ∈ globalPrimeIndexSet F, B n
```

from per-index bounds `|finitePrimeTerm F n| ≤ B n`.  The specialized theorem
`abs_finitePrimeSum_defect_le_of_termBounds` applies this directly to the
one-window defect used by `C1T2Assembly`.  The index set is the owner's exact
finite visible set, so this step introduces no density or infinite-prime
interchange.  The per-term bounds and the archimedean integral bound remain
open producer obligations.  The follow-up theorem
`abs_ICgate_le_of_archimedeanBound_and_termBounds` combines those two channels
by the real triangle inequality, leaving precisely those independent bounds as
the P2 producer inputs.  The per-index envelope
`primeTermNormEnvelope` and theorem
`abs_finitePrimeTerm_le_primeTermNormEnvelope` are now also formal: every
real prime-term readout is bounded by the norm of its exact complex term,
without assuming a sign for von Mangoldt.  The uniform-bound adapter
`primeTermNormEnvelope_le_of_uniformTestBound` reduces the envelope further to
the two-point bound `2 * A` whenever the defect test is uniformly bounded by
`A`.  The companion theorem
`abs_archimedeanTerm_le_of_zeroAndIntegralBounds` now supplies the other
channel: an explicit bound on the zero-point value and the integral of the
integrand norm bounds `archimedeanTerm` by their coefficient-weighted sum.
Finally, `defect_test_norm_le_of_uniformBounds` proves that the singleton
defect inherits the uniform bound `G + H` from the detector square and the
certified window square.  This is the direct norm bridge needed to feed a true
correction estimate into the finite-prime envelope.
The combined theorem
`abs_finitePrimeSum_defect_le_of_uniformSquareBounds` now carries this bridge
through the exact finite visible-prime sum, yielding the explicit coefficient
bound with `2 * (G + H)`.
The remaining P2 producer task is therefore to derive these concrete pointwise
and integral bounds from the true correction construction.

## Verification

The owning and audit modules build successfully with the resource-aware runner:
`Build completed successfully (3658 jobs)`, zero `error:` lines.  The audit
includes all eight P2-α/β declarations; each uses only
`[propext, Classical.choice, Quot.sound]`.  The attempted
one-shot `norm_num` replacement for 1139 was reverted after it left the 666-term
comparison goal unsolved; no compiler axiom is claimed as a fix.
