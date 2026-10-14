# Record 2702: captured owner exact interval bridge

Status: LEAN-INTERFACE-PASS; ANALYTIC-SOUNDNESS-PREMISE-OPEN.

The new consumer connects the exact interval interface from record 2586 to the
live `capturedActualCorrectionOwner2584`. Given the explicit premise that every
owner coordinate lies in its 2338 exact interval, Lean derives membership in
the 2570 correction coefficient box for all 30 coordinates.

This is a genuine owner-facing bridge, but it does not prove the premise. The
missing work is still a directed analytic proof that the exact moment-system
solution lies in the stored 2338 intervals. No producer, SourceRH, or RH claim
is made.

Evidence: `C1RouteACorrectionCapturedOwnerExactInterval2702.lean` and its
audit companion. The owner interface, box closedness, center membership, and
conditional fixed-point transfer compile under Lean 4.30; all four axiom
readbacks contain only `[propext, Classical.choice, Quot.sound]` and no
`sorryAx`.

The companion 2600 candidate-inverse membership theorem now proves all 900
coordinates by reducing each payload rectangle to its degenerate point form.
Its Lean 4.30 axiom readback also contains only the standard axiom trio. This
establishes membership of the selected lower-corner matrix in the stored
rectangles; it does not establish that the candidate is the inverse of the
analytic moment matrix.

The remaining analytic obligations are unchanged: prove that the actual
captured correction owner lies in the 2338 intervals, and discharge the
contraction-map invariance, finite-displacement, and actual-owner fixed-point
premises. The 49-entry manifest facade and the 2600 static-defect consumer have
not yet passed a complete build in this verification run.

Verification follow-up, 2026-10-14: under Linux-native Lean 4.30, the 2600
Row02 module builds successfully in 3912 Lake jobs. Its row theorem
`candidateInverseDefectEntryBound2600_row_02` reads back exactly
`[propext, Classical.choice, Quot.sound]`. The 2702 four-declaration audit and
the 2600 candidate-inverse membership audit also read back only this standard
axiom trio. The 2351 exact-rational checker reruns as
`EXACT_NEUMANN_AND_BOX_PASS`, with eta `5.873158307277732e-38` and maximum
box-radius ratios `0.9999999438559326` and `0.999999941431241`. These external
arithmetic readings do not prove that the analytic matrix-integral intervals
contain their Lean-defined values.

The attempted combined build of the 2600 static-defect audit and the 2695
49-entry facade exited with status 1 after reporting progress at 4269 of 5936
jobs; the cause was not established and no final audit was produced. Those two
targets remain UNVERIFIED. The Row02 module, 2702 bridge, and candidate-inverse
module used for the successful checks had source hashes matching mainline. No
producer GO, `SourceRH`, or RH claim follows from these checks.
