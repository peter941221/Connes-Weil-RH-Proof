# Proof 542: non-polar gap factor bridge

Result: good, but Gate 3U is still open.

Proof 541 introduced the remaining local producer interface:

    non-polar gap = adjacent leftCoDefect * gap rightFactor.

The existing Proof 511--512 joint producer consumes the equivalent local
polar/raw mismatch factor.  Proof 542 proves these are the same factor
obligation because Proof 504 established the exact operator identity:

    nonpolar gap = route/polar raw mismatch defect.

At a fixed bound the conversion is exact and costs nothing:

    non-polar gap factor
      <-> mismatch co-defect factor.

For a uniform family, the existing reverse producer then supplies the
physical domination owner with the explicit bound:

    physical domination bound = 8 * gap-factor bound.

The factor family itself is still not constructed.  Therefore this proof
does not close the source-specific Gate 3U estimate, the finite-S sign,
Burnol's identity, or RH.

## Verification

Verified in the Ubuntu-24.04 WSL2 ext4 mirror:

    +------------------------------------------+-------+--------+
    | target                                   | jobs  | result |
    +------------------------------------------+-------+--------+
    | focused source target                    |  3329 | PASS   |
    | focused axiom audit                      |  3330 | PASS   |
    | CCM25Concrete aggregate                  |  3812 | PASS   |
    | full repository                          |  3893 | PASS   |
    +------------------------------------------+-------+--------+

The focused audit checks nine bridge declarations.  All nine use exactly:

    [propext, Classical.choice, Quot.sound]

The Proof 542 source and audit contain no `sorry`, `admit`, or user
`axiom`/`constant` declaration, and have no line longer than 100 characters.
Existing repository linter warnings are unchanged; the WSL localhost-proxy
notice is external to the Lean build.
