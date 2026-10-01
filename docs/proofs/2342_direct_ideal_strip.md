# 2342 - Direct ideal-source strip enclosure on exact nodes

Date: 2026-10-01.

Result: the direct upper is 1852190.2152630097..., below the unchanged
2644542.8515 pin (ratio 0.7003820014534598). It covers the whole real
sigma interval [-1/2,1/2], conditional on the analytic moment-solve and
one-sided chord proofs recorded in 2338 and 2341. The numerical node
chain is an external Arb/Acb interval calculation, not a Lean certificate.

精确网格（exact grid）指节点由有理数公式定义，不是先用浮点数取近似再补偿。
区间算术（interval arithmetic）把每次运算结果连同误差一起包围，类似称重时
同时保留重量上下限；本轮不再借用旧 2303 的采样数字。
凸性（convexity）在这里表示指数权重在两端之间不超过两端值的直线平均，因而
只认证两个端点就能控制整个 sigma 区间，不是把未采样点当作已经测过。

## Why a direct calculation replaces the old transfer problem

2341 still needed the theorem that the 2303 stored nodal sums were upper
bounds, and the identity of its reconstructed linspace with the original
coordinates. 2342 does not use either of those sums or coordinates.

The source is exactly the finite-family object repaired in 2338: all 30
coefficient rectangles enclose the unique analytic moment-matrix solution.
Each physical radius is the exact square of the captured binary64 width.
The computation neither casts ideal coefficients to binary64 nor adds a
P-only polynomial. No live healthy-detector instantiation is implied.

For each exported rational coefficient interval [lo,hi], the decoder lifts
the rational midpoint and adds an outward ball of radius (hi-lo)/2. Real
and imaginary rectangles are decoded separately. This is a superset of
the coefficient enclosure, not a new solve. Dependency between coefficients
is discarded only by enlarging the represented set, which is conservative.

## Exact nodal chain

Let R_i be a family's exact radius, theta_i its real modulation, and c_i
one of the repaired complex coefficients. Define

  phi_R(x) = exp(-30/(1-(x/R)^2)) for |x|<R, and 0 otherwise;
  F(x) = sum_i c_i phi_(R_i)(x) exp(i theta_i x).

Both base and correction are evaluated this way. The support is contained
in [-R,R], R=max_i R_i. The extension by zero is smooth at the support
edges. R does not change the selected-square support from record 2336.

Inside a family put u=x/R_i and q=1-u^2. The analytic derivative chain is

  e1 = -60 u / (R_i q^2),
  e2 = -60 (q^-2 + 4 u^2 q^-3) / R_i^2,
  term'' = term * (e2 + e1^2 - theta_i^2 + 2 i theta_i e1).

Every operation in the values, derivatives, complex sums, modulus,
exponential weight and quadrature accumulator is Arb/Acb arithmetic.
The membership test |x|>=R_i uses exact Fractions, so no approximate
comparison decides whether a point is inside support. Interior q must
be certified positive; if precision cannot establish it the run refuses.

The grid is

  x_j = -R + 2R j/(N-1), N=120001, j=0..N-1.

No numpy linspace or coordinate-error allowance occurs. The complex
family contributions are added before taking the modulus. The modulus
upper is weighted by exp(sigma x_j), and the positive trapezoid sum is
accumulated in enclosing balls. Thus roundoff is enclosed along the
actual chain rather than estimated retrospectively by a few output ulps.

## Continuous-x and continuous-sigma bounds

For k=0 and k=2 define

  M_(F,k)(sigma) = integral exp(sigma x) |F^(k)(x)| dx.

k=0 measures the function; k=2 measures its second derivative. These are
weighted L1 norms: weighted total magnitudes, not signed Weil values.
The endpoint point sums receive the one-sided 2341 chord allowance

  panel = (h^2/12)(2R) exp(|sigma|R)
          * (m_(k+2) + 2|sigma| m_(k+1) + sigma^2 m_k),

where h=2R/(N-1), and m_j is the analytic sup bound on |F^(j)|.
The ladder uses the ideal coefficient moduli and exact radii, retaining
the carrier theta_i terms. Derivative bounds are those independently
checked by the integer polynomial recurrence in the 2341 test suite.
The bound needs no zero-count and makes no lower-integral assertion.

For sigma=(1-t)(-1/2)+t(1/2), 0<=t<=1, convexity of exp implies

  exp(sigma x) <= (1-t)exp(-x/2) + t exp(x/2).

Multiplication by the nonnegative |F^(k)(x)| and integration prove

  M_(F,k)(sigma) <= max(M_(F,k)(-1/2), M_(F,k)(1/2)).

This covers every intermediate sigma, not merely a sampled grid. Denote
the four endpoint-maximum uppers by B0,B2,C0,C2 for base/correction.
The same raw strip min-product convention as 2340 then gives

  min(M_(base,2)(sigma) M_(correction,0)(sigma),
      M_(correction,2)(sigma) M_(base,0)(sigma))
  <= min(B2 C0, C2 B0).

All products and comparisons in this final step use exact Fractions of
the exported dyadic upper endpoints. No Fourier scaling, prime-kernel
conversion or signed-value interpretation is inserted in this bound.

## Readings and scope
The maximum endpoint uppers are B0=2.7790943781644725...,
B2=9044.943447179203..., C0=231.26420261406076...,
C2=666472.5853917701.... The smaller product is C2 B0.
The upper is intentionally coarser than the conditional 2341 figure:
the new grid has half as many intervals and the global endpoint maxima
discard correlations. The decision is whether the independently computed
bound stays below the frozen pin, not whether it reproduces 2341's number.

2342 removes reliance on the legacy nodal-upper and coordinate identity
premises for this captured repaired source. It does not establish rho is
a source zero, completeness of a required zero list, far-tail contraction,
healthy detector data, or a signed/full-kernel bound. It is not a universal
rho-parametric construction. No Lean import or consumer handoff is claimed.

## Validation

- 15/15 controls pass, including exact rectangle containment at two
  precisions, support boundaries, independent mpmath derivatives,
  modulation/radius terms, complex cancellation, the actual 30-family
  midpoint source at five control nodes, malformed rectangles,
  exact product reconstruction, source/input/helper hashes and scope flags.
- Full 192-bit replay is byte-identical.
- Full 256-bit control at the same 120001 rational nodes stays below the
  pin; all 40 real/imaginary components at the five control nodes overlap.
  This is a precision control within the same arithmetic engine, not an
  independent proof engine. The mpmath reference test is separate.
- The coarse 101-node smoke run does not fit the pin; its panel term is
  large by design. No coarse smoke result is used in the full verdict.

Evidence: scripts/routea_direct_ideal_strip_2342.py,
scripts/routea_direct_ideal_strip_selftest_2342.py,
results/2342_direct_ideal_strip.json,
results/2342_direct_ideal_strip_precision256.json,
results/2342_direct_ideal_strip_validation.json.
Logs: build-logs/2342_direct_ideal_strip.log,
build-logs/2342_selftest.log, build-logs/2342_replay.log,
build-logs/2342_precision256.log.

## Next steps

1. Formalize or rigorously import the exact-grid point-to-continuum chain
   and identify the reconstructed coefficient function with the 2338 ideal
   source. Completion requires the same function, not matching hashes alone.

2. Recheck the exact analytic finite-node realization against the healthy
   source premises. Completion requires the required vanishing and selected
   marked values on the actual owner, with tail conditions kept separate.

3. Price the complete composed-support signed prime-kernel functional for
   that owner. The bound above is a norm supplier, not the producer sign;
   the 4R support cover and source-zero/zero-list premises remain binding.
