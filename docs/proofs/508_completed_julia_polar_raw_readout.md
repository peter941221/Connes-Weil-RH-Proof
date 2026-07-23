# Proof 508: completed-Julia polar/raw readout

## Result

Proof 508 closes the polar/raw readout bookkeeping on the actual finite-S
source-Sonin carrier. It gives an unconditional physical polar readout, a
bounded correction for any separately supplied complete mismatch readout, and
the exact four-term adjoint normal form of the raw adjacent intertwinement.
It does not provide the missing raw Douglas domination, Gate 3U, a finite-S
sign, Burnol's identity, or an unconditional proof of RH.

```text
+------------------------------------------------------+------------------+
| item                                                 | status           |
+------------------------------------------------------+------------------+
| moving-boundary projection and norm bound            | proved           |
| polar physical readout                               | proved           |
| polar readout * ambient analysis = polar adjoint     | proved           |
| raw correction for a complete mismatch readout       | proved           |
| raw correction norm bound                             | proved           |
| raw adjoint pointwise norm bound                      | proved           |
| three-branch commutator skew-adjointness              | proved           |
| cycled raw response adjoint physical form             | proved           |
| adjacent raw adjoint four-term physical normal form   | proved           |
| raw Douglas producer / Gate 3U / finite-S sign        | still open       |
| Burnol identity / RH                                  | still open       |
+------------------------------------------------------+------------------+
```

The Lean owner is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaPolarRawReadout.lean
```

## Physical polar readout

The ambient boundary carrier is the L2 product of the Euler-analysis column
and its moving-boundary coordinate. The right projection is the second product
coordinate, so the readout

```text
P_S = -(newSuffixFrame(S))^dagger detector rightProjection
```

uses only the actual boundary channel. The source frame is isometric and the
right projection is contractive; hence

```text
||P_S|| <= ||detector||
P_S * ambientBoundaryAnalysis = polarIntertwiningDefect^dagger.
```

This is a genuine carrier statement. It does not identify the polar defect
with the raw defect and does not assume a Douglas factorization.

## Raw correction forced by a complete readout

Suppose a separately supplied data record contains a readout `M` for the
complete polar-minus-raw mismatch, with

```text
M * ambientBoundaryAnalysis = (polarDefect - rawDefect)^dagger
||M|| <= bound.
```

Then the difference `P_S - M` factors exactly through the same analysis column
as `rawDefect^dagger`, and

```text
||P_S - M|| <= ||detector|| + bound.
```

Applying this factorization pointwise yields the corresponding raw-adjoint
norm bound. Thus any future family-uniform complete readout must also control
the raw row on the same ambient antiresonant and moving-boundary coordinates.

## Four-term raw normal form

The source-specific raw response is the difference between the forward and
new-suffix cycled responses. The three-branch commutator is skew-adjoint, and
the cycled response adjoint is therefore

```text
-forwardEndpointCoframe^dagger * C3 * sourceInclusion
+sourceInclusion^dagger * C3 * forwardCoframe.
```

Taking the adjacent difference gives exactly four terms: two from the old
suffix and two from the new suffix, all with the Euler transition adjoint in
the correct side. The statement is an algebraic normal form only; no estimate
of the four terms separately is asserted.

## Remaining gap

The active producer must still identify the complete raw row with a bounded
readout against the summed physical energy, uniformly in the visible prime
list. The four-term expansion is intended as the source interface for that
producer. It must preserve the signed polar-minus-raw cancellation before any
absolute-value estimate.

## Verification

The focused audit is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaPolarRawReadoutAudit.lean
```

The Ubuntu 24.04 WSL2 verification batch passed:

```text
+------------------------------------------+-------+--------+
| target                                   | jobs  | result |
+------------------------------------------+-------+--------+
| Proof 508 source build                   |  3324 | PASS   |
| Proof 508 focused axiom audit            |  3325 | PASS   |
| CCM25Concrete aggregate                  |  3785 | PASS   |
| full repository                           |  3866 | PASS   |
+------------------------------------------+-------+--------+
```

The audit checks the principal declarations and their axiom sets; the
expected axiom set is exactly `[propext, Classical.choice, Quot.sound]`.

No `sorry`, `admit`, user axiom, Gate 3U conclusion, sign claim, Burnol claim,
or RH proof is introduced by this proof.
