# Source-orthogonal factors reduce to the complementary column

Date: 2026-09-17

The theorem `sourceSoninComplement_comp_commutator_sourceOrthogonal_eq`
handles the second structural branch of the B4 atomic target.  If an ambient
factor `M` has no Sonin component on the included source,
`P M J = 0`, then its complementary commutator has the exact form

`(I - P) (M P - P M) J = (I - P) M J`.

Together with record 1523, every factor with a known source projection is
therefore reduced either to zero (source-range) or to its already-defined
complementary column (source-orthogonal).  Only factors with a genuinely
mixed source projection require the analytic commutator estimate.

This is an exact operator reduction; it supplies no square-summability for
the remaining complementary column and does not close B4, S3, G8, or C3.

Validation: owning build log
`/home/peter/rh/build-logs/1670_commutator_orthogonal.log`; paired audit log
`/home/peter/rh/build-logs/1671_commutator_orthogonal_audit.log`.  Both completed
with zero `error:` and zero `sorryAx`; the audit has only the standard three
axioms.
