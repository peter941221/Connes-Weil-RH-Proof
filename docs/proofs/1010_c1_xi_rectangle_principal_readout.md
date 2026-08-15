# 1010 Finite Xi Rectangle Principal Readout

Date: 2026-08-14

## Result

The finite-factor Gate 2 rectangle chain now has a complete principal-part
readout and a same-owner conversion to the source spectral index.

```text
zero-free rectangle boundary
        |
        | regularized Cauchy identity
        v
factor-owned finite principal kernel
        |
        | interior/exterior rectangle residue calculation
        v
strictly interior divisor-support sum
        |
        | finite embedding from the same divisor owner
        v
finite source-zero spectral sum
```

The relevant modules are:

```text
ConnesWeilRH/Dev/C1XiFiniteRectanglePrincipalPart.lean
ConnesWeilRH/Dev/C1XiFiniteRectangleSupportReindex.lean
ConnesWeilRH/Dev/C1XiFiniteHeightRectangle.lean
ConnesWeilRH/Dev/C1XiFiniteHeightVerticalFold.lean
```

Their public endpoint is:

```lean
xiRectangleBoundaryIntegral_xiContourKernel_eq_neg_finiteSourceSpectralSum_of_factor_support
```

It proves, for one closed-ball xi factorization owner and a standard rectangle
contained in its open factorization ball whose four edges avoid xi zeros,

```text
B_rectangle(xiContourKernel F)
  = -2*pi*i *
      sum_{rho in factor-owned source zeros strictly inside rectangle}
        spectralTerm(F, rho).
```

## Why The Rectangle Calculation Is Legal

The contour kernel is not differentiable across an interior xi zero, so
Cauchy-Goursat cannot be applied to it on the whole rectangle.  The earlier
regularization result instead removes only the differentiable remainder.

For each finite principal pole, the new calculation separates the two legal
geometric cases:

```text
strictly inside rectangle              outside closed rectangle
             |                                      |
             v                                      v
four zero-free strips reduce to          Cauchy-Goursat on the whole
a centered square around the pole        rectangle gives zero
             |
             v
2*pi*i
```

Boundary points are excluded by the actual four closed edge segments, not by
the full horizontal or vertical support lines. This is essential: a zero on
the same line but outside the segment is harmless; a zero on a segment makes
that edge integral undefined.

The factor-owned support is then converted through
`xiClosedBallSupportToSourceZero`. Its filtered image is exactly
`xiClosedBallSourceZerosInsideRectangle`; each divisor multiplicity times the
centered Laplace weight is rewritten using
`factor_weight_eq_spectralTerm_of_mem_sourceZeros`.

## Finite-Height Critical-Strip Specialization

`C1XiFiniteHeightRectangle` specializes the rectangle to

```text
0 < Re(s) < 1
-T < Im(s) < T.
```

The two vertical edges are xi-zero-free because every source nontrivial zero
has real part strictly between zero and one. The additional hypothesis
`xiHeightBoundaryAvoidsZeros T` rules out xi zeros on the two horizontal
segments. It has one further necessary effect: a member of the pre-existing
closed truncation `finiteHeightZeros T` has `|Im rho| <= T`; equality would put
the xi zero on a horizontal boundary and contradict that hypothesis. Thus the
closed truncation is exactly the strict-interior, same-factor-owned family.

The public endpoints are:

```lean
xiClosedBallSourceZerosInsideRectangle_eq_finiteHeightZeros
xiRectangleBoundaryIntegral_xiContourKernel_eq_neg_finiteSpectralSum
```

The second theorem proves the finite statement

```text
B_rectangle(xiContourKernel F)
  = -2*pi*i * finiteSpectralSum(F, T).
```

It retains the finite factorization owner, the factor-ball containment, and
the horizontal zero-free condition.

The same module now also proves the zero-free-height producer and packages it
into a concrete sequence:

```lean
exists_xiHeightBoundaryAvoidsZeros_gt
xiZeroFreeHeights_boundaryAvoidsZeros
nat_lt_xiZeroFreeHeights
```

For every real lower bound `B`, the first theorem selects `T > B` outside the
finite set of values `|Im rho|` for `rho` in a bounded source-zero window. The
recursive sequence then satisfies both `xiHeightBoundaryAvoidsZeros T_n` and
`n < T_n`, so it escapes every bounded height window. It does not choose a
single factorization valid across all heights or take a contour limit.

## Quantitative Height Selection

`C1XiQuantitativeHeight` upgrades exact avoidance to a finite, explicit
separation. For every `B >= 0`, it sets

```text
S_B = {|Im rho| : rho in finiteHeightZeros(B + 2)}
delta_B = 1 / (4 * (#S_B + 2)).
```

The endpoint

```lean
exists_quantitative_xiHeightBoundaryAvoidsZeros
```

chooses `T` in `(B, B + 1)` so that every `rho` in
`finiteHeightZeros (B + 2)` satisfies

```text
delta_B <= |T - |Im rho||.
```

The proof places `#S_B + 1` equally spaced candidates in that unit interval.
An ordinate can lie within `delta_B` of at most one candidate, so assigning a
nearby ordinate to every candidate would inject `#S_B + 1` objects into a set
of size `#S_B`, a contradiction. Any xi zero on either horizontal edge has
absolute imaginary part `T < B + 2`, so the same separation proves
`xiHeightBoundaryAvoidsZeros T`.

```text
finite visible ordinates S_B
        |
        +-- #S_B + 1 grid candidates in (B, B + 1)
        |
        +-- one candidate remains delta_B away from every ordinate
                         |
                         v
             quantitative xi-zero-free height T
```

The dyadic Jensen bridge is now closed at the exact base heights used by the
finite grid:

```text
#S_(2^(n+2)) <= spectralMultiplicityConstant * 3^(n+1).
```

Its Lean endpoint is:

```lean
xiHeightForbiddenOrdinates_dyadic_card_le
```

The proof keeps analytic multiplicity intact until the last step:

```text
distinct visible ordinates
        <= finite source-zero cardinality
        <= finite analytic multiplicity
        <= dyadic Jensen bound.
```

The reciprocal consequence is also formalized:

```lean
xiHeightSeparation_dyadic_lower_bound
```

It states exactly:

```text
1 / (4 * (spectralMultiplicityConstant * 3^(n+1) + 2))
  <= xiHeightSeparation(2^(n+2)).
```

This still does not bound the regular part of `xi'/xi`, the cofactor term, or
a contour edge. The next load-bearing theorem must turn this selected-height
separation into a cross-height logarithmic-derivative estimate.

The same chosen upper height now has a genuine zero-free complex tube. Define

```text
r_B = min(delta_B, 1 / 2).
```

The endpoint

```lean
exists_quantitative_xiHeightBoundaryAvoidsZeros_tube
```

returns the same `T` and proves, for every real `x`,

```text
completedRiemannXi(z) != 0
  whenever z belongs to Metric.ball (x + T*I) r_B.
```

The proof is geometric. If a zero lay in such a ball, its imaginary ordinate
would be within `r_B` of `T`. The `1 / 2` cap puts that zero in the already
finite `B + 2` height window; the `delta_B` part then contradicts the selected
separation.

```text
selected upper height T
        |
        +-- ball radius min(delta_B, 1/2)
        |       |
        |       +-- height remains below B + 2
        |       +-- distance from every visible zero >= delta_B
        |
        v
  zero-free upper horizontal tube
```

This is a prerequisite for a local logarithmic-derivative argument, but it is
not a lower bound for `|xi|`, a bound on its analytic cofactor, or a bound for
`xi'/xi`. The theorem is stated for the upper line; a lower-line use must be
transported explicitly through the xi functional equation. That transport is
now supplied by:

```lean
exists_quantitative_xiHeightBoundaryAvoidsZeros_tubes
```

It returns the same selected `T` and radius `r_B` for both horizontal lines:

```text
Metric.ball (x + T*I) r_B   is xi-zero-free
Metric.ball (x - T*I) r_B   is xi-zero-free.
```

The lower statement maps a putative lower-tube zero `z` to `1-z`. This lies in
the upper tube centered at `(1-x) + T*I`, with exactly the same distance; the
functional equation `xi(1-z) = xi(z)` then contradicts the upper-tube result.
Thus both contour edges have one owner-selected height and one quantitative
radius, rather than two independently selected zero-free heights.

The fully assembled dyadic producer is:

```lean
exists_dyadic_quantitative_xiHeightBoundaryAvoidsZeros_tubes
```

For every natural number `n`, it returns one height satisfying

```text
2^(n+2) < T < 2^(n+2) + 1
```

and both zero-free tubes with the exact explicit radius

```text
r_n = min(1 / (4 * (spectralMultiplicityConstant * 3^(n+1) + 2)), 1 / 2).
```

```text
dyadic Jensen count
        |
        v
explicit ordinal gap delta_n
        |
        v
same-height upper/lower zero-free tubes at r_n
        |
        v
remaining: quantitative minimum-modulus or xi'/xi estimate
```

This is the complete finite-packing and zero-free-geometry contribution. It
does not turn an analytic nonvanishing statement into a lower bound for
`|xi|`: a nonzero holomorphic function can be arbitrarily small. Therefore
the next step cannot be skipped by compactness or by the finite factor owner.

For each positive zero-free height, `XiHeightRectangleFactorData` then holds
the cofactor, its factorization, its zero-free boundary, and the rectangle
containment in the same object. The owner uses the explicit ball
`Metric.ball (0 : Complex) |T + 2|`; the elementary estimate
`||s|| <= |Re s| + |Im s| < T + 2` contains the whole critical-strip
rectangle. Its two producer/readout endpoints are:

```lean
exists_xiHeightRectangleFactorData_gt
XiHeightRectangleFactorData.xiRectangleBoundaryIntegral_readout
```

Thus the finite formula now consumes one height-specific owner rather than
independently selected `T`, `g`, factorization, and boundary hypotheses.

## Finite-Height Vertical Fold

`C1XiFiniteHeightVerticalFold` closes the exact fold of the two vertical
edges, after and only after those two sides have been combined. Its public
endpoint is:

```lean
criticalStripVerticalBoundaryIntegral_eq_rightLineIntegral
```

For every positive height with `xiHeightBoundaryAvoidsZeros T`, it proves:

```text
i * integral[-T,T] xiContourKernel(F, 1 + i*t)
  - i * integral[-T,T] xiContourKernel(F, i*t)
= integral[-T,T] verticalIntegrand(F, 1, t).
```

The first integral is the upward right side and the second is the upward left
side. The finite rectangle boundary gives the left side the opposite
orientation, so their difference is the vertical part of its boundary
functional. The proof changes the left parameter by `t |-> -t`, invokes the
xi functional equation at `1 - (1 + i*t)`, and only then introduces the
reflected Laplace weight through `xiRightLineKernel`.

This keeps the one-weight residue rule intact:

```text
local residue              one centered Laplace weight
two vertical sides folded  one reflected right-line weight pair
```

No horizontal edge is estimated or discarded. In particular, this finite
identity supplies neither a bound for `xi'/xi` nor a rectangle contour limit.

## Finite Rectangle Assembly

`C1XiFiniteHeightRectangleAssembly` joins the finite residue readout and the
vertical fold without changing the height-specific factor owner. Its endpoint
is:

```lean
XiHeightRectangleFactorData.horizontal_add_foldedRightLine_eq_neg_finiteSpectralSum
```

For one `D : XiHeightRectangleFactorData`, it states:

```text
horizontalBoundary(F, D.height)
  + foldedRightLineIntegral(F, D.height)
= -2*pi*i * finiteSpectralSum(F, D.height).
```

The explicit horizontal term is the lower horizontal integral minus the upper
horizontal integral. The right-line term is precisely the fold from the prior
section. Therefore the remaining contour limit has a fixed, non-negotiable
shape:

```text
finite spectral sum
        ^
        | finite rectangle identity
        |
horizontal edge term + folded right-line term
        |                         |
        |                         +-- right-line convergence still open
        +-- xi'/xi-weighted edge decay still open
```

This is an exact finite equation, not an assertion that either summand tends
to a limit.

## Quartic Test Weight And Conditional Horizontal Bound

The test-weight half of the horizontal estimate is now closed independently
of any xi factorization owner. The endpoint

```lean
exists_uniform_centeredLaplaceWeight_vertical_quartic_decay_on_criticalStrip
```

produces, for every `CompactLogTest F`, a nonnegative constant `C` such that

```text
|T / (2*pi)|^4 * |centeredLaplaceWeight(F, sigma + i*T)| <= C
```

for every `0 <= sigma <= 1` and every real `T`. This is the compact-support
Mellin/Fourier decay of the test, transported through the log-to-positive
coordinate bridge and recentered at `Re(s) = 1/2`.

`C1XiHorizontalDecay` keeps the logarithmic-derivative input explicit through
the predicate:

```lean
xiHorizontalLogDerivEnvelope T M
```

It says that the same nonnegative `M` bounds
`negativeXiLogDeriv(sigma - i*T)` and
`negativeXiLogDeriv(sigma + i*T)` for every `0 <= sigma <= 1`. Under that
input, the public endpoint is:

```lean
exists_quartic_horizontalBoundary_bound_of_logDerivEnvelope
```

and it proves that some nonnegative test constant `C` satisfies

```text
|| horizontalBoundary(F, T) ||
  <= 2 * M * C / |T / (2*pi)|^4.
```

The factor `2` is exactly the triangle inequality for the lower and upper
unit-length horizontal segments. The `T^-4` factor comes only from the
compact-log test weight; the quotient is valid because the theorem requires
`T > 0`.

For a selected height with `xiHeightBoundaryAvoidsZeros T`, the envelope is
now a theorem rather than an extra premise:

```lean
exists_xiHorizontalLogDerivEnvelope
exists_quartic_horizontalBoundary_bound_of_xiHeightBoundaryAvoidsZeros
XiHeightRectangleFactorData.exists_quartic_horizontalBoundary_bound
```

The first endpoint composes the two zero-free horizontal parameterizations
with `negativeXiLogDeriv`, obtains continuity from the punctured xi API, and
uses compactness of `[0, 1]` to choose a finite common `M(T)`. The other two
endpoints feed that height-local `M(T)` into the quartic product estimate.

```text
selected zero-free height T
        +-- continuity on two compact segments
        |       -> finite log-derivative envelope M(T)  CLOSED, height-local
        |
        +-- centered test weight C / |T/(2*pi)|^4    CLOSED
                         |
                         v
             horizontal boundary <= 2*M(T)*C / |T/(2*pi)|^4
```

This is not yet a horizontal-edge limit. `XiHeightRectangleFactorData` has a
cofactor and a finite envelope for each individual height, but no theorem
compares `M(T)` or the cofactors as the selected heights grow. A valid next
theorem must produce a sub-quartic cross-height envelope, for example an
`O(T log T)` bound along the zero-free sequence; only then can this product
estimate force the horizontal term to zero.

## Evidence

The isolated WSL2 ext4 command was:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.C1XiFiniteRectangleSupportReindexProbe
```

It completed successfully with `3533` jobs. The probe audited:

```text
xiRectangleBoundaryIntegral_rectangleSimplePole_eq_zero_of_not_mem_rectangle
xiRectangleBoundaryIntegral_rectangleSimplePole_eq_two_pi_I_of_center
xiRectangleBoundaryIntegral_rectangleSimplePole_eq_two_pi_I_of_strictlyInside
rectangleBoundaryAvoidsFiniteSupport_of_xiRectangleBoundaryAvoidsZeros
xiRectangleBoundaryIntegral_xiClosedBallPrincipalKernel_eq_sum_of_strictlyInside
xiRectangleBoundaryIntegral_xiContourKernel_eq_sum_of_strictlyInside
mem_xiClosedBallSourceZerosInsideRectangle_iff
sum_xiClosedBallSourceZerosInsideRectangle_eq_sum_support
xiRectangleBoundaryIntegral_xiContourKernel_eq_neg_finiteSourceSpectralSum_of_factor_support
```

Each new public declaration depends only on:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`.

The same isolated clone then verified the assembly command:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.C1XiFiniteHeightRectangleAssemblyProbe
```

It completed successfully with `3536` jobs. Both
`xiRectangleBoundaryIntegral_eq_horizontal_add_foldedRightLine` and
`XiHeightRectangleFactorData.horizontal_add_foldedRightLine_eq_neg_finiteSpectralSum`
depend only on `[propext, Classical.choice, Quot.sound]`; there is no
`sorryAx`.

The finite-height specialization and zero-free sequence were verified with:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.C1XiFiniteHeightRectangleProbe
```

It completed successfully with `3534` jobs. Its ten audited declarations are
`xiRectangleBoundaryAvoidsZeros_criticalStripRectangle`,
`exists_xiHeightBoundaryAvoidsZeros_gt`,
`xiZeroFreeHeights_boundaryAvoidsZeros`,
`nat_lt_xiZeroFreeHeights`,
`criticalStripRectangle_subset_ball_zero`,
`exists_xiHeightRectangleFactorData_gt`,
`XiHeightRectangleFactorData.xiRectangleBoundaryIntegral_readout`,
`abs_im_lt_of_mem_finiteHeightZeros_of_xiHeightBoundaryAvoidsZeros`,
`xiClosedBallSourceZerosInsideRectangle_eq_finiteHeightZeros`, and
`xiRectangleBoundaryIntegral_xiContourKernel_eq_neg_finiteSpectralSum`; each
depends only on `[propext, Classical.choice, Quot.sound]`.

The quantitative height-selection bridge was verified with:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.C1XiQuantitativeHeightProbe
```

It completed successfully with `3535` jobs. The audit covered `gridGap_pos`,
`xiHeightTubeRadius_pos`,
`exists_point_Ioo_away_from_finset`,
`exists_quantitative_xiHeightBoundaryAvoidsZeros`, and
`xiHeightForbiddenOrdinates_dyadic_card_le`, and
`xiHeightSeparation_dyadic_lower_bound`, and
`dyadicXiHeightTubeRadius_pos`,
`exists_quantitative_xiHeightBoundaryAvoidsZeros_tube`, and
`exists_quantitative_xiHeightBoundaryAvoidsZeros_tubes`, and
`exists_dyadic_quantitative_xiHeightBoundaryAvoidsZeros_tubes`; every
declaration depends only on `[propext, Classical.choice, Quot.sound]`, with no
`sorryAx`.

The vertical fold was verified from a fresh WSL2 ext4 Git clone whose
`git rev-parse --show-toplevel` was the verification directory itself:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.C1XiFiniteHeightVerticalFoldProbe
```

It completed successfully with `3535` jobs. Its import-facing audit reports:

```text
criticalStripVerticalBoundaryIntegral_eq_rightLineIntegral
  [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`.

The quartic weight chain was verified with:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.C1XiContourDecayProbe
```

It completed successfully with `3522` jobs. The probe audited the quartic
Fourier-Mellin estimate, its uniform Mellin producer, both CompactLog Laplace
transports, and
`exists_uniform_centeredLaplaceWeight_vertical_quartic_decay_on_criticalStrip`.
All five declarations depend only on:

```text
[propext, Classical.choice, Quot.sound]
```

The finite-height envelope bridge and the conditional horizontal product
estimate were verified with:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.C1XiHorizontalDecayProbe
```

It completed successfully with `3538` jobs. The import-facing audit covered
`exists_xiHorizontalLogDerivEnvelope`,
`exists_quartic_horizontalBoundary_bound_of_logDerivEnvelope`,
`exists_quartic_horizontalBoundary_bound_of_xiHeightBoundaryAvoidsZeros`, and
`XiHeightRectangleFactorData.exists_quartic_horizontalBoundary_bound`; each
depends only on `[propext, Classical.choice, Quot.sound]`. There is no
`sorryAx`.

## Boundary

This is a finite local rectangle readout with an unbounded sequence of
height-specific factorization owners, an exact fold of its vertical sides, and
a height-local horizontal product estimate. It does not supply a uniform
cofactor bound, a cross-height `xi'/xi` envelope or growth rate, a
horizontal-edge limit, a contour-limit estimate, a finite-to-infinite
spectral-sum limit, an arithmetic-side contour readback, the Gate 2 equality,
or an RH claim.

The next valid consumer must retain the same finite factor owner while proving
the rectangle-limit comparison. It must not replace this result with the
circle theorem or add the reflected Laplace weight to the local residue; one
`xiContourKernel` residue has exactly one centered Laplace weight.
