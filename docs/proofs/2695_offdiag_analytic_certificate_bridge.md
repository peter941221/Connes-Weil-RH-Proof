# Record 2695 - off-diagonal analytic certificate bridge

Status: 52 OFF-DIAGONAL MEMBERSHIPS WIRED; 818 REMAIN; NO PRODUCER OR RH CLAIM.

The existing integrated certificate `2601` required the full 30 by 30
analytic containment premise. Record `2646` already proves that the diagonal
entries come from the certified diagonal partition `2645`, and the existing
assembly theorem `entry03Mem2663` closes `(0,3)`. Record 2695 composes those
interfaces:

```text
two separate proved entries: (0,3), (11,9)
51 imported manifest proofs + 818 remaining caller assumptions
52 of 870 off-diagonal positions closed
818 explicit pointwise memberships remain
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
The companion split theorem consumes `entry03Mem2663` directly. Its general
form accepts 51 `h_manifest` memberships and 818 `h_remaining` memberships.
The concrete form supplies the 51 manifest memberships through the imported
proof-producing assemblies, leaving 818 off-diagonal memberships as caller
assumptions. Together with the separate `(0,3)` theorem, 52 of 870
off-diagonal positions are therefore wired. Entry `(11,9)` was freshly
regenerated, exact-reconstructed, byte-gated, and Lean-audited under the
standard axiom trio; the updated facade and integrated consumer still require
a Linux-native rebuild before this count is promoted to a compiled integration
result. The bridge's other explicit
premises are candidate-inverse interval membership, the defect-entry identity,
and the operator defect identity. A Lean build and axiom audit have not yet
been completed for this integration.

The scope is deliberately narrow. This bridge does not prove the 818
caller-supplied off-diagonal memberships outside the manifest, the defect-entry identity, the
operator defect identity, the selected-detector signed C3' budget,
`chargeRest`, the signed infinite tail, Producer GO, `SourceRH`, or RH.

Evidence:

- `ConnesWeilRH/Dev/C1RouteACorrectionAnalyticOffDiagCertificate2695.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionAnalyticOffDiagCertificate2695Audit.lean`
- `ConnesWeilRH/Dev/C1RouteAAnalyticContainmentBridge2646.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionAnalyticCertificate2601.lean`
