# 047 - Selected-detector sign: energy and prime-discrepancy audit

Date: 2026-09-20.

Authority: supporting candidate screen under 003/004/006/007. The healthy
CompactLog B5 route, the S3 status in 045/046, and the open selected-detector
nonnegativity are unchanged. This record registers PAPER evidence from
[1736](../proofs/1736_detector_sign_translation_energy_and_prime_discrepancy.md),
not a formal no-go or a new endpoint supplier.

## The actual consumer

`C1HealthyYoshidaSpectralNegativity.healthy_sourceRH_of_right_detector_specific_qw_nonneg`
consumes a nonnegative Weil value for the same detector supplied under a
hypothetical right-hand off-line zero. Its finite visible prime set must
follow that test's support. The contradiction belongs in the proof; a
package that assumes both signs is not analytic source data.

## Two screened mechanisms

Record 1736 derives from the committed square and functional:

    qw(g) = translation difference energy
              + visible-prime difference energy
              - (K + 2*sum visible weights)*||g||_2^2,
    K = log(8*pi) + EulerGamma + pi/2.

Positive summands do not supply the required lower energy threshold.
The exact triple-vanishing family
`g_L=D(D+1/2)(D+1) h(x/L)` has derivative-to-mass ratio `O(L^(-2))`.
It gives a paper counterexample to uniform positivity with a FIXED
arithmetic truncation, including a fixed finite prime set with all powers.
This does not refute the actual support-dependent B5 target.

The same record cancels the continuous prime main term exactly:

    qw(g) = Q_cont(g) + 2*integral R(y)*H_g'(y) dy,
    R(y) = Psi(exp y) - (exp y - 1),
    H_g(y) = exp(-y/2)*Re(g.convolutionSquare(y)).

The continuous-only form is negative on sufficiently wide members of the
same admissible family. The actual discrepancy integrand also changes
sign: `R<0` before `log 2`, while `R(log 5)=log 60-4>0` and `H_g'<0`
on the relevant small intervals for sufficiently large `L`.

Both candidate mechanisms remain NEEDS-ANALYSIS on the selected orbit.
The missing result is a lower energy estimate or an integrated signed
discrepancy estimate proved from raw selected-orbit data. Introducing either
as a hypothesis would restate the open sign problem.

## Mellin-null and Euler-resolvent follow-up

Record [1737](../proofs/1737_mellin_null_corrections_and_euler_resolvent_tail.md)
adds PAPER screening of the proposed Mellin-invisible correction. On a
finite-dimensional moment model, such corrections leave the compressed form
unchanged; existence of a positive completion is equivalent to its positivity.
An exact triple-vanishing translated-bump pair prevents removal of the naive
two-prime product Gram's mixed shifts by moment-null and scalar corrections.
This is a scoped identity obstruction, not a selected-detector no-go.

The actual Euler-log owner instead admits the exact identity

    prime_p(g) = log(p)*((1-1/p)*||(I-p^(-1/2)U_log(p))^(-1)g||^2 - ||g||^2).

Its square enters qw with a negative sign. The inverse has an explicit
geometric right tail with amplitude given by a weighted periodization C_p.
Compactness of this inverse requires every Laplace value at
`1/2 + 2*pi*i*k/log(p)` to vanish, not merely the three real moments.
The selected-orbit estimate for this boundary energy remains open. No route,
formal brick status, or endpoint supplier changes.

## Actual selected-orbit joint energy and tail samples

Record [1738](../proofs/1738_selected_orbit_joint_symbol_and_tail_sampling.md)
inserts the committed half-density-shifted convolution orbit into the combined
Gamma/prime Fourier symbol. The symbol is negative near zero and nonnegative
outside a finite threshold for each fixed finite prime set; its selected
weighted integral still has no sign estimate. This screens pointwise-symbol
positivity only, not the integrated selected B5 target.

The same record derives a quantitative inverse-tail bound from the existing
construction theorem's root-level tail conjunct: a finite sample block on
raw Re(s)=1 plus an explicit O(J^(-3)) squared-sample remainder. The full
joint energy instead reads raw Re(s)=1/2. The finite samples, the remainder's
uniform accounting across visible primes, and the positive-versus-negative
energy comparison remain open. These are PAPER deductions with no new formal
status or endpoint supplier. Bounds for inverse tails alone do not bound the
whole resolvent or prove the required sign.

The section-7 source audit of 1738 further identifies an exact finite-sample
annihilation option: insert prescribed Re(s)=1 lattice points as raw route
zeros before choosing the convolution order. Correction is chosen before n
for fixed nodes. Covering the actual visible primes still requires a
support/cutoff closure, not supplied by existential interpolation, and the
interior sign estimate remains open. This is a PAPER candidate, not a new
producer or route ruling.

Section 8 of 1738 extracts the actual sufficient order certificate and
combines it with safe prime coverage: an integer n must lie above
log(((6*pi)^2*(C(P)+1))/epsilon)/log(2) and at most log(P)/2-2.
A divided-difference argument also proves growing L1 interpolation cost.
Section 9 then supplies the missing Plancherel bridge
`C >= sqrt(3)*||correction||_1/64`. With Bertrand's postulate, the resulting
factorial lower bound rules out arbitrarily large cutoff closure for fixed
rho and epsilon under the specific exact-all-prime-zero, uniform-contraction,
safe-support certificate combination. This is a PAPER scoped asymptotic
obstruction, not a formal no-go, exclusion of every finite cutoff, or a B5
impossibility. Weighted suppression and the actual integrated sign stay open.

Section 10 corrects the priority of that candidate: moving the exterior
cutoff makes the inverse tail arbitrarily small for fixed g while transferring
exactly its lost energy to the interior. Small exterior energy alone cannot
improve the sign. The next sign mechanism must control the complete form;
exact lattice cancellation is not a necessary B5 obligation. Rechecked
fixed-window positivity and lowest-eigenvalue continuity sources do not
supply that missing selected sign.

## Evidence boundary

These are paper calculations, with convergent integral manipulations,
exact differential-polynomial norm identities, and small-prime arithmetic.
There is no numerical experiment and no new Lean acceptance claim.
The counterfamily is not a healthy negative detector and is not an RH
counterexample. No universal B1 campaign or frozen producer is reopened.
