# Source-complement commutator normal form

Date: 2026-09-17

The theorem `sourceSoninComplement_comp_ambientFactor_comp_sourceInclusion_eq_commutator`
proves the exact identity

`(id - P) M J = (id - P) (M P - P M) J`.

It uses only `P J = J` and `P² = P`.  Thus the remaining B4 complement term
from records 1517–1518 is precisely the root-gap operator applied to the
source-projection commutator of the ambient boundary factor.  This identifies
the analytic object that must be estimated and rules out treating the
complement as an unrelated arbitrary column.

The result is a formal normal form only.  It supplies no commutator decay or
Hilbert--Schmidt estimate, so WO-B, S3, and RH remain open.

Validation: owning build log
`/home/peter/rh/build-logs/1659_commutator_bridge.log`; paired audit log
`/home/peter/rh/build-logs/1660_commutator_bridge_audit.log`.  Both completed
with zero `error:` and zero `sorryAx`; the audit has only the standard three
axioms.
