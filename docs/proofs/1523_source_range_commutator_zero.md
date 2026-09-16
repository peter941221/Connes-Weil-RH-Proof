# Source-range factors have zero complementary commutator

Date: 2026-09-17

The theorem `sourceSoninComplement_comp_commutator_sourceRange_eq_zero` proves
the zero branch of the B4 atomic target.  If an ambient factor `M` satisfies
`P M J = M J`, then

`(I - P) (M P - P M) J = 0`.

The proof is pointwise: `P J = J` and the source-range hypothesis identify
both terms inside the commutator, after which the complementary projection
annihilates zero.  Thus any factor already known to return the included source
carrier contributes no B4 commutator energy at all.

This is a formal structural reduction, not an assertion that the physical
boundary factors satisfy the premise.  The factors containing the Euler
transport and Schur blocks still need either this source-range certificate or
an actual atomic Hilbert--Schmidt estimate.

Validation: owning build log
`/home/peter/rh/build-logs/1669_commutator_zero_source_range.log` completed with
zero `error:` and zero `sorryAx`; the paired audit declaration uses only
`[propext, Classical.choice, Quot.sound]`.
