# Record 2499 extension — weighted-curvature monotonicity door

The 2499 exponent-split inputs now have a formal consumer-side door.  The
theorem `weightedCurvature2348_mono_bounds2499` proves that increasing the
zero-, first-, or second-derivative upper bound can only increase
`weightedCurvature2348` (the coefficients `2*|sigma|` and `sigma^2` are
nonnegative).  Its audit builds successfully in 3738 jobs and reports only
`[propext, Classical.choice, Quot.sound]`.

This removes a repeated algebraic obligation from the future 9,994 local
branches.  It does not prove any exponential bound or hcell payload; those
branch-specific rational inequalities remain open.  No producer GO or RH
claim is made.
