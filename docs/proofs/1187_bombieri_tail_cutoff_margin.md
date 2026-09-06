# 1187 — Spectral-tail cutoff below the Bombieri main-term margin

## Status

**FORMAL support lemma; the same-owner decomposition remains open.**

The shell-tail theorem `exists_spectralHeightShell_normTail_lt` gives, for
every positive real margin, a finite shell cutoff whose norm tail is smaller
than that margin. Combining it with the strict finite-form result from record
1186 yields `exists_spectralTail_normTail_lt_bombieriQuadraticForm_of_eigen`:
every nonzero reciprocal Bombieri eigenvector admits a cutoff whose same-owner
spectral tail is strictly below `Re⟨w,Hw⟩`.

This removes the independent tail-domination inequality from the eventual
producer design. The producer still has to prove the exact `qw` decomposition
at the chosen cutoff; no equality is assumed here.

## Acceptance

Focused batch `p2-tail-under-margin-r1.log` completed successfully (3665 jobs),
with no `error:` or `sorryAx`; the audit reports only
`[propext, Classical.choice, Quot.sound]`.
