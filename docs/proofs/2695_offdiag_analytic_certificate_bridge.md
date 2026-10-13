# Record 2695 - off-diagonal analytic certificate bridge

Status: INTERFACE SPLIT; ONE POINTWISE PREMISE DISCHARGED; NO PRODUCER OR RH CLAIM.

The existing integrated certificate `2601` required the full 30 by 30
analytic containment premise. Record `2646` already proves that the diagonal
entries come from the certified diagonal partition `2645`, and the existing
assembly theorem `entry03Mem2663` closes `(0,3)`. Record 2695 composes those
interfaces:

```text
one proved entry: (0,3)
49 manifest-listed caller assumptions + 820 other caller assumptions
869 explicit pointwise memberships remain
                 |
                 v
      socket_diagonal_split2646
                 |
                 v
full analytic containment (30 x 30)
                 |
                 v
capturedActualCorrectionOwner2584_realizes_of_analytic_interval_certificate2601
```

The primary bridge theorem is
`capturedActualCorrectionOwner2584_realizes_of_offdiag_analytic_interval_certificate2695`.
The companion split theorem consumes `entry03Mem2663` directly. It accepts 49
`h_manifest` memberships for generated entries and 820 `h_remaining`
memberships for all other coordinates, so 869 pointwise memberships remain
explicit, down from 870. The generated chains are not imported as Lean
declarations; their results remain caller-supplied premises. The bridge's
other explicit premises are candidate-inverse interval membership, the
defect-entry identity, and the operator defect identity. A Lean build and
axiom audit have not yet been run for this module.

The scope is deliberately narrow. This bridge does not prove the 869
caller-supplied off-diagonal memberships, the defect-entry identity, the
operator defect identity, the selected-detector signed C3' budget,
`chargeRest`, the signed infinite tail, Producer GO, `SourceRH`, or RH.

Evidence:

- `ConnesWeilRH/Dev/C1RouteACorrectionAnalyticOffDiagCertificate2695.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionAnalyticOffDiagCertificate2695Audit.lean`
- `ConnesWeilRH/Dev/C1RouteAAnalyticContainmentBridge2646.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionAnalyticCertificate2601.lean`
