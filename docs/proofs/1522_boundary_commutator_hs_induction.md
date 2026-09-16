# Boundary commutator Hilbert--Schmidt induction consumer

Date: 2026-09-17

The theorem `ambientProduct_commutator_sourceBasis_normSq_summable_of_leibniz`
is the Hilbert--Schmidt consumer for the Leibniz identity from record 1521.
For bounded ambient maps `A`, `B`, a bounded postcomposition `D`, a source
map `N`, and a source Sonin orthonormal basis, summability of the two atomic
families

`D A [B,P] J N e_i` and `D [A,P] B J N e_i`

implies summability of the product family `D [A B,P] J N e_i`.  The proof is
an exact operator rewrite followed by `PositiveTrace.summable_normSq_add`;
it controls the whole basis sum and does not estimate vectors one at a time.

This closes the formal induction layer needed to pass from atomic
source-projection commutators to every finite Euler boundary factor.  The
atomic commutator-root estimates themselves are still open, so B4 and the
overall S3/G8/C3 route remain analytically unresolved.

Validation: owning build log
`/home/peter/rh/build-logs/1667_commutator_induction.log`; paired audit log
`/home/peter/rh/build-logs/1668_commutator_induction_audit.log`.  Both completed
with zero `error:` and zero `sorryAx`; the audit has only
`[propext, Classical.choice, Quot.sound]`.
