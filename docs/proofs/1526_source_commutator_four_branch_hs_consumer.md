# Four-branch Hilbert--Schmidt consumer for the source commutator

Date: 2026-09-17

The theorem `sourceSoninCommutator_sourceBasis_normSq_summable_of_threeBranch`
now turns four branch estimates into the full B4 source-commutator estimate.
For a bounded postcomposition `D` and source-side map `N`, square-summability
of the outer, second-support, reflected-outer, and prolate branch columns on
one source basis implies square-summability of

`D [P,M] J N`.

The proof is the exact three-branch owner followed by repeated
`PositiveTrace.summable_normSq_add`; the prolate branch is handled with its
signed negative.  No branch is dropped and no vectorwise limit is substituted
for the basis sum.

This completes the formal recombination layer for B4.  The four branch
Hilbert--Schmidt estimates for the actual Euler/Schur factors remain the
analytic input, so B4, S3, G8, and C3 are still open.

Validation: owning build log
`/home/peter/rh/build-logs/1674_commutator_four_branch.log`; paired audit log
`/home/peter/rh/build-logs/1675_commutator_four_branch_audit.log`.  Both
completed with zero `error:` and zero `sorryAx`; the audit has only the
standard three axioms.
