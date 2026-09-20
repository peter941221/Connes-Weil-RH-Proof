# Record 1782 — CCM24 critical profile enters the annular two-IBP consumer

Date: 2026-09-21

## Purpose

Advance the healthy `CompactLog` B5 S3 branch by replacing the abstract
annular `theta` input with the concrete CCM24 critical Mellin profile. This is
an instantiation step for the mass-face tail estimate; it is not a sign proof
and not an RH claim.

## Formal result

`ConnesWeilRH/Dev/C1G8R3CriticalProfileTwoIBP.lean` proves
`annular_ccm24CriticalMellinLogProfile_v_tail_le`. For a Schwartz source and
an oscillatory integral built from the concrete profile, the weighted tail is
bounded by the L1 norm of the formal second-chain-rule profile with the exact
two-IBP constant. The first derivative is the carrier derivative theorem; the
second derivative is the landed differentiated formula from the digamma page.

The paired Audit prints the declaration's axioms. Acceptance log:
`/home/peter/rh/build-logs/critical-profile-ibp-v4.log`; it reports a
successful 2970-job build and only `[propext, Classical.choice, Quot.sound]`.

## Boundary

This does not yet identify the actual theta as scattering phase times a
Fourier profile. That remaining product requires the scattering phase's
second-derivative readback and weighted Schwartz integrability. Those are the
next obligations before the translation-tail identities and the 1723 endpoint
consumer.

Classification: formal project contribution; no originality or RH claim.
