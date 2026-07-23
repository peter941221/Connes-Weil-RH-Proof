# Proof 499: raw completed Schur cocycle

Date: 2026-07-22

## Result

The result is good as an exact algebraic reduction, but it does not close
Gate 3U.  The raw actual-band quadratic remainder now has a literal
list-level Schur--Markov cocycle whose local term combines the first jet and
the ordered endpoint before any absolute value is taken.

Write

```text
Raw(S) = suffixActualBandRawQuadraticCycledResponse(S),
rho_S  = suffixEulerSchurMarkovScalar(S).
```

Lean proves

```text
Raw([])=0,

CompletedDefect(p,S)
  =rho_S * LocalRawDefect(p,S),

LocalRawDefect(p,S)
  =rho_p * Raw(p::S)-G_(p,S) Raw(S) R_(p,S),

CompletedCocycle(S)=rho_S * Raw(S).                 (RC.1)
```

Under an explicitly supplied complex-linear cyclic trace contract, the same
cocycle collapses to

```text
traceLike(Raw(S))
  =sum over the ordered suffixes of
     rho_p^(-1) traceLike(LocalRawDefect(p,suffix)). (RC.2)
```

The complete scalar `rho_S` is cancelled only after Lean has produced it on
both sides of the equality.  Proof 498's estimate is never divided by
`rho_S`.

```text
+---------------------------------------------------+----------------------+
| layer                                             | status               |
+---------------------------------------------------+----------------------+
| empty-family raw remainder                        | closed               |
| local first-jet-minus-endpoint completion         | closed               |
| list-level completed cocycle                      | closed               |
| algebraic relative trace readout                  | closed               |
| ordinary-trace legality for every local cycle     | open                 |
| physical/Julia synthesis factorization            | open                 |
| uniform relative Gate 3U bound                    | open                 |
| finite-S sign / Burnol identity / RH              | open                 |
+---------------------------------------------------+----------------------+
```

## 1. Literal raw owner

The new suffix-level definitions use the actual source Sonin carrier and the
same frame, dual-frame, normalized Euler inverse, and root-convolution maps as
the finite-family route.  The readback theorem is

```lean
theorem suffixActualBandRawQuadraticCycledResponse_eq_actual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixActualBandRawQuadraticCycledResponse owner lambda
        family.visiblePrimes =
      sourceActualBandFiniteEulerRemainderResponse owner lambda family
```

Thus `Raw(family.visiblePrimes)` is not a surrogate recurrence.  It is the
existing actual-band remainder on the literal arithmetic family.

At the empty list, the normalized inverse is the identity, the source band
kills the source inclusion, and the target frame and dual frame both reduce
to that inclusion.  Lean consequently proves

```lean
suffixActualBandRawQuadraticCycledResponse_nil_eq_zero
```

without an analytic premise.

## 2. Complete before differencing

The local term is defined from the scaled raw owner:

```lean
noncomputable def suffixActualBandLocalCompletedDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixActualBandScaledRawResponse owner lambda (p :: S) -
    suffixEulerFrameTransition lambda p S ∘L
      suffixActualBandScaledRawResponse owner lambda S ∘L
        suffixEulerFrameReverseTransition lambda p S
```

Here `suffixActualBandScaledRawResponse(S)=rho_S Raw(S)`.  The theorem

```lean
suffixActualBandLocalCompletedDefect_eq_firstJet_sub_endpoint
```

proves that every local term is already

```text
local completed defect
  =local first-jet defect-local ordered-endpoint defect. (RC.3)
```

This ordering matters.  Taking separate absolute values of the first jet and
endpoint would discard the cancellation which Proofs 496--498 preserved in
the complete outer, reflected-outer, second-support, and prolate response.

The exact suffix factorization is

```lean
suffixActualBandLocalCompletedDefect_eq_suffixScalar_smul_raw
```

and gives

```text
CompletedDefect(p,S)=rho_S * LocalRawDefect(p,S).   (RC.4)
```

Only the one-prime positive scalar occurs inside `LocalRawDefect`; the full
finite-family scalar is not inserted there.

## 3. Operator cocycle

The generic paired cocycle keeps forward and reverse histories on their
literal sides:

```text
C([])=base,
C(p::S)=G_(p,S) C(S) R_(p,S)+CompletedDefect(p,S).
```

For the actual transitions, Lean proves the operator identity

```lean
suffixActualBandCompletedDefectCocycle_eq_scaledRaw
```

which is equation `(RC.1)`.  This proof uses only the definitions and the
one-step recurrence; it does not use a trace, cyclicity, or positivity.

The arithmetic-family readback is

```lean
suffixActualBandCompletedDefectCocycle_eq_scaledSourceRemainder
```

so the terminal cocycle is exactly `rho_S` times the existing source
remainder.

## 4. Algebraic trace collapse

The theorem

```lean
traceLike_pairedCompletedCocycle_eq_collapsed
```

accepts the trace laws as explicit arguments:

```text
traceLike(x+y)=traceLike(x)+traceLike(y),
traceLike(xy)=traceLike(yx),
traceLike(x * scale_p)=rho_p traceLike(x).
```

It moves a paired forward/reverse history around one local term and uses

```text
R_(p,S) G_(p,S)=rho_p I.                         (RC.5)
```

The actual specialization first yields

```text
traceLike(rho_S Raw(S))=CompletedCollapsedTrace(S).
```

Complex linearity and `(RC.4)` then give

```text
CompletedCollapsedTrace(S)=rho_S RelativeCollapsedTrace(S).
```

Finally, positivity of `rho_S` proves it is nonzero, so cancellation on both
sides yields `(RC.2)` through

```lean
traceLike_suffixActualBandRawResponse_eq_relativeCollapsed
```

This is the correct algebraic place to cancel `rho_S`.  It does not turn
Proof 498's absolute estimate

```text
abs Tr(rho_S Raw(S))<=P
```

into the missing relative estimate

```text
abs Tr(rho_S Raw(S))<=rho_S P.
```

## 5. Ordinary-trace boundary

The global hypothesis

```lean
hcyclic : forall x y, traceLike (x*y)=traceLike(y*x)
```

is an abstract ring contract.  Ordinary trace on an infinite-dimensional
Hilbert space is not defined on every bounded endomorphism, and cyclicity may
only be used after the relevant products are proved trace class.  The existing
fixed-family legality theorem for the complete four-branch response does not
automatically provide local trace-class factorizations for every suffix term
in `(RC.2)`.

Therefore Proof 499 does not instantiate `traceLike` with unrestricted
ordinary trace.  A valid successor must either:

```text
prove trace-class legality and the required local cycles term by term;

or

construct one source-specific completed physical readout whose already-legal
trace is identified with the whole relative recurrence at once.
```

The second route is preferable because it preserves the signed cancellation
before any local total-variation estimate.

## 6. Diagonal-energy shortcut is rejected

The existing canonical synchronized Euler energy is a scalar ledger:

```lean
noncomputable def canonicalSynchronizedEulerModeEnergy
    (owner : SelectedWeilSquareOwner) : ℝ :=
  ((ofSelectedOwner owner).visiblePrimes.map (fun p =>
    ∑' n : ℕ,
      ∫ alpha : ℝ in 0..1,
        parameterizedPrimeEulerModeBoundaryEnergy alpha p n)).sum
```

Its type contains no source-Sonin vector family, synthesis map, or theorem
identifying the relative local raw defects with orthogonal Julia coordinates.
Consequently it cannot by itself control the coherent sum in `(RC.2)`.

The finite Lean guard is exact:

```text
identicalModes_analysisSquareLedger:     diagonal energy =N,
identicalModes_coherentSynthesisNormSq:  synthesis norm^2=N^2,
identicalModes_coherentSynthesisGap:     gap factor=N.
```

Proof 348 gives the source-compatible version: nearby prime-log crossing
modes are coherent, so their local Hilbert--Schmidt energy grows like
`X/log(X)` while the corresponding diagonal Euler ledger stays `O(1)`.

Evidence:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCanonicalEulerEnergy.lean
  CCM24FiniteSWeightedTranslationBessel.lean

docs/proofs/
  430_weighted_translation_square_ledger.md
  348_prime_cluster_local_s2_obstruction.md
```

This guard does not reject a future source-specific completed factorization.
It rejects only the unsupported step

```text
diagonal scalar energy
  -X-> norm of an unproved coherent physical synthesis.
```

## 7. Lean ownership and verification

The source and audit are

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSRawCompletedSchurCocycle.lean

ConnesWeilRH/Dev/
  CCM24FiniteSRawCompletedSchurCocycleAudit.lean
```

The focused Ubuntu 24.04 ext4 build passed:

```text
+------------------------------------------+-------+--------+
| target                                   | jobs  | result |
+------------------------------------------+-------+--------+
| Proof 499 focused axiom audit            |  3287 | PASS   |
| CCM25Concrete aggregate                  |  3776 | PASS   |
| full repository                          |  3857 | PASS   |
+------------------------------------------+-------+--------+
```

All fourteen audited declarations use exactly

```text
[propext, Classical.choice, Quot.sound].
```

The new source and audit emit no new linter warning.  The remaining build
warnings are replayed repository warnings; the WSL localhost-proxy notice is
external to the repository.

## 8. Boundary

Proof 499 closes the algebraic relative readout, not its ordinary-trace local
legality or its analytic estimate.  The next source theorem must construct a
same-carrier factorization from the relative local raw defects to the complete
outer/reflected-outer/second-support/prolate physical owner and a genuinely
orthogonal completed Julia history.  Only then may the canonical Euler mode
energy enter a Cauchy--Schwarz estimate.

Gate 3U, the finite-S sign, negative-owner integration, Burnol's identity,
and `_root_.RiemannHypothesis` remain open.
