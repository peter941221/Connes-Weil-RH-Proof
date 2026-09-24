# 1929 — Finite source-basis minimum selector

## Formal result

`C1VariationalFiniteDimensionalSelector.lean` now adds
`exists_min_norm_euclidean_coefficient`. For a finite family of source vectors
and any attainable target, it constructs a coefficient vector in
`EuclideanSpace` whose finite linear combination reaches the target and whose
Euclidean coefficient norm is minimal among all such combinations.

The proof uses the actual finite-dimensional coefficient space, not an
infinite `Finsupp` norm that has not been defined. Its interpolation map is the
finite sum `c -> sum_i c_i • vectors_i`; the affine-fibre minimum is supplied
by the previously audited Hilbert selector. The paired audit remains limited
to `[propext, Classical.choice, Quot.sound]`.

## Route-A use

The existing sparse source theorem provides finite supports of size at most
the node count. The new result is the correct selector core for those finite
supports. Combined with 1928, the physical derivative cost can be bounded by
the selected source-basis derivative weights times the minimizing coefficient
size.

## What is not proved

This does not prove that the resulting coefficient cost is uniformly small in
the selected orbit parameters, and it does not prove the grouped residual is
strictly negative. A derivative upper bound alone has no sign information.
The strict residual margin remains an independent same-owner inequality and
must be proved or killed by a reproducible counterexample.

Evidence level: FORMAL for the finite-basis selector; PROJECT CANDIDATE for
the source-basis instantiation and signed margin.
