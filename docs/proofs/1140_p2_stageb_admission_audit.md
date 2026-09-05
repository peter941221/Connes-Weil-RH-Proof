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
The generic supplier `compactLogTest_norm_le_zeroSeminorm` further provides a
canonical uniform bound for every `CompactLogTest`, namely its zero-order
Schwartz seminorm.  Concrete correction work can therefore target these
seminorms directly.
The support-side theorem `index_lt_of_support_subset_Icc` turns an exported
support interval `[a,b]` into the explicit cutoff
`ceil(exp(max(|a|,|b|))) + 1`; its companion set inclusion applies this cutoff
to `globalPrimeIndexSet`.  This keeps the visible-prime owner finite and tied
to the detector's actual support endpoints.
The convolution-square corollary first symmetrizes `[a,b]` to
`[-R,R]`, `R = max(|a|,|b|)`, and then applies the exact square-support lemma;
it gives the corresponding cutoff for `globalPrimeIndexSet g.convolutionSquare`.
The canonical specialization
`abs_finitePrimeSum_defect_le_of_zeroSeminorms` removes the auxiliary `G,H`
assumptions entirely and expresses the prime-side budget using only the two
zero-order Schwartz seminorms of the detector and window squares.
For the full finite Stage-B family,
`defect_test_norm_le_of_uniformFamilyBounds` proves the weighted bound
`G + Σ |λᵢ| Hᵢ`; this is the norm shape consumed by multi-window contraction.
The gate consumer `abs_ICgate_defect_le_of_uniformFamilyBounds_and_arch` now
combines that family bound with an independent archimedean estimate and emits
the complete explicit defect budget.  No positivity or `qw` sign is used in
this estimate.
Its budget corollary
`ICgate_defect_le_of_uniformFamilyBounds_and_arch_budget` has the exact
Stage-B direction: an explicit budget below `epsilon` yields
`ICgate(defect) ≤ epsilon`.
The archimedean channel is now attached to the same owner as well:
`archimedeanIntegralNorm` stores the integral of the density norm,
`archimedeanIntegralNorm_nonneg` proves it is nonnegative, and
`abs_archimedeanTerm_le_of_zeroSeminorm_and_integralNorm` combines it with the
owner's zero-order Schwartz seminorm.  This removes the auxiliary integral
variable from the canonical interface while leaving its concrete analytic
upper bound as the genuine producer task.
The two same-owner consumers
`abs_ICgate_defect_le_of_uniformFamilyBounds_and_integralNorm` and
`ICgate_defect_le_of_uniformFamilyBounds_and_integralNorm_budget` inline this
channel into the full Stage-B estimate, so the final admission interface no
longer carries an independent `harch` field.
The support theorem
`defect_globalPrimeIndexSet_subset_range_of_common_Ioo_support` also carries a
common open support interval through the finite family defect and produces an
explicit finite cutoff for its visible-prime set.
The theorem
`abs_finitePrimeSum_defect_le_of_uniformFamilyBounds_and_commonSupport` then
replaces the exact-set prime sum by that explicit range, using only
nonnegativity of the norm envelopes.  This is a finite-budget adapter and
does not assert a sign for the gate.
The coefficient readback `primeTermNormEnvelope_eq_realCoefficient_mul` and
the arithmetic lemma `vonMangoldt_sqrtWeight_le_log_of_one_le` now reduce each
positive-index envelope to the real `Λ(n)/√n` coefficient and then to `log n`.
`primeTermNormEnvelope_le_of_logBound` exposes the resulting scalar adapter for
a producer that supplies a cutoff-local logarithmic bound.
The all-index corollary `primeCoefficientNorm_le_log_of_nat` matches the
complex-norm coefficient in the explicit range sum, including the zero index.
Finally, the one-window consumers
`stageBContraction_of_uniformSquareBounds_and_integralNorm_budget` and
`orbitGate_of_uniformSquareBounds_and_integralNorm_budget` connect this
canonical budget to the actual Stage-B contraction and orbit-window gate
interfaces.  Their explicit budget and certified-window hypotheses remain
genuine producer obligations.
`P2OneWindowBudgetWitness` packages these fields on the same detector owner,
and `sourceRH_of_healthyDetector_p2OneWindowBudgetWitness` composes the packed
witness with the existing detector contradiction.  The open mathematical task
is therefore isolated to constructing this witness for each right-oriented
off-line zero.
`P2CanonicalOneWindowBudgetWitness` further eliminates the auxiliary `G,H`
pointwise fields by constructing them from the zero-order Schwartz seminorms;
its consumers therefore require only the canonical scalar budget, support,
window certificate, and margin.
The pinned consumer
`sourceRH_of_pinnedOrbitDetector_p2CanonicalOneWindowBudgetWitness` carries the
formal orbit support interval and visible-prime cutoff alongside that canonical
witness, so the remaining producer is attached to one explicit `g,n` owner.
The remaining P2 producer task is therefore to derive these concrete pointwise
and integral bounds from the true correction construction.

## Verification

The owning and audit modules build successfully with the resource-aware runner:
`Build completed successfully (3659 jobs)`, zero `error:` lines.  The audit
includes all thirty-eight P2-α/β declarations; each uses only
`[propext, Classical.choice, Quot.sound]`.  The attempted
one-shot `norm_num` replacement for 1139 was reverted after it left the 666-term
comparison goal unsolved; no compiler axiom is claimed as a fix.
