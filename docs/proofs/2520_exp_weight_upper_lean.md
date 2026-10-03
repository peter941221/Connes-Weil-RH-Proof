# Record 2520: formal exponential weight upper

`C1RouteAExpWeightUpper2520.lean` proves, for the two producer rows
`sigma = ±1/2`,

`Real.exp (|sigma| * stripRadius2303) ≤ 64`.

The proof reduces the argument to a Taylor remainder bound at one-fifth of
the exponent, then raises the rational upper `229/100` to the fifth power.
This isolates one analytic factor needed by the 2519 cell inequalities.  It
does not prove those inequalities or close the producer margin.
