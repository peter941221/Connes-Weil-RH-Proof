# Boundary-product commutator Leibniz rule

Date: 2026-09-17

The theorem `ambientProduct_commutator_eq_leibniz_sum` proves the exact
operator identity

`[A B, P] = A [B, P] + [A, P] B`,

where the commutator is `T P - P T` and `P` is the source-Sonin projection.
This is the induction step for the actual finite Euler boundary factors,
whose ambient part is a finite composition of transports, adjoint transports,
and Schur projections.

Combined with record 1520, it reduces the remaining B4 estimate to finitely
many atomic source-projection commutators, with bounded surrounding factors.
No atomic decay or Hilbert--Schmidt estimate is proved here; WO-B, S3, and RH
remain open.

Validation: owning build log
`/home/peter/rh/build-logs/1665_commutator_leibniz.log`; paired audit log
`/home/peter/rh/build-logs/1666_commutator_leibniz_audit.log`.  Both completed
with zero `error:` and zero `sorryAx`; the audit has only the standard three
axioms.
