# Proof 1252 — positivity of the G8 base and leakage channels

Status: FORMAL-CHANNEL-POSITIVITY (Lean), 2026-09-10.

The two diagonal terms in the same-owner finite-window G8 ledger now have
independent positivity proofs.  Writing

```text
C = fullBoundaryPositiveOperator * sourceInclusion,
N = finiteEulerPulledObliqueShear,
W = detectorOperator,
```

the base channel is exactly `(C)† W C`, while the leakage channel is exactly
`(N† C)† W (N† C)`.  Both follow from the existing detector positivity theorem
and the continuous-linear-map `adjoint_conj` lemma.  The proof stays on the
healthy source owner and uses the concrete finite cutoff; it introduces no
external subtraction and no new positivity assumption.

This closes only the two diagonal signs in the four-channel finite-window
ledger.  The cross and adjoint-cross channels are not separately nonnegative,
and no channel trace has yet been identified with `qw`; the L4 projection-limit
and A4 finite-visible-prime obligations remain open.

Audit evidence: `/home/peter/rh/build-logs/1252_g8_channel_positivity_retry4.log`.
The owning module and audit build completed successfully (3922 jobs), with
standard axioms only and no `error:` or `sorryAx`.

RH is not claimed.
