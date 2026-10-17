# Record2735: rational negative-exponential interface

The existing certified20-term Taylor theorem supplies rational expressions
that enclose exp(w) whenever0<=w<=m. This entry proves the exact inverse
ordering for exp(-w): the inverse of the upper positive box is a lower
bound, and the inverse of the lower positive box is an upper bound.

Scope: one generic real w and natural scaling m. No interval endpoint
rounding, cell replay, D4/D7 integral, or RH producer claim. Previous
turn was PROGRESS: exact-real interval jet containment was pushed in
04e3442b.


## Verification

Focused Linux-native build:

    lake build ConnesWeilRH.Dev.C1RationalNegativeExp2735Audit

Build completed successfully (3655 jobs). The single theorem audit uses
exactly [propext, Classical.choice, Quot.sound]. The checker passes all
seven gates: footer, no errors, no new-module warnings, declaration/audit
identity, source-copy hashes and the standard axiom footprint.

    python3 scripts/check_rational_negative_exp_2735.py --workspace WORKSPACE

This closes only the sign-correct inverse interface for rational Taylor
boxes. It does not certify machine endpoint rounding, finite cell replay,
integration, D4/D7, cardinal pins, carrier transfer or RH.
