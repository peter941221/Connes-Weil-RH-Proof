# Record 2302: local frequency magnitudes and sampled-weight proxy

## Result and scope

The degree-six local frequency Taylor model covers the transform magnitudes
between sample locations under its declared arithmetic model. All three
sampled-weight proxies are below the 1e7 diagnostic budget. The finest proxy
is 404928.783977559, or 0.04049288 times budget. This is not a continuous
functional integral certificate: kernel and annihilator weights are still
sampled at cell centres, and outer arithmetic remains unpriced.

Evidence: `results/2302_local_frequency_taylor_screen.json` and
`scripts/routea_local_frequency_taylor_screen_2302.py`. All 30 captured
families, coefficient hashes, 25 carrier groups and 41136 prime powers remain
unchanged. The regenerated coefficient table reproduces record 2301's hash;
the order-zero evaluator reproduces its execution bitwise.

```text
cell width | cell count | sampled-weight proxy | budget ratio
-----------+------------+----------------------+-------------
0.020      |  4000      | 494430.118212007     | 0.04944301
0.010      |  8000      | 412090.869335935     | 0.04120909
0.005      | 16000      | 404928.783977559     | 0.04049288
```

These prices must not be described as an improvement from record 2301's
0.10275924 price: the comparison objects differ. Record 2301 includes execution
in its difference radius. Record 2302 compares the original captured bump
transform with the exact regenerated polynomial transform; numerical
derivative errors enlarge the polynomial's magnitude bounds instead. A strict
value for that exact polynomial's final weighted integral is not supplied.

## Objects and derivation

Let G be the Fourier transform of the exact regenerated polynomial components
at their represented physical panel coordinates. G is an analytic function
of frequency even though its physical components are piecewise polynomials.
Let H bound every represented physical coordinate and M bound the sum of
the components' absolute integrals. The run reads H = 6.55360000000000255,
M_base = 53.62947449 and M_corr = 87088.25642.

The frequency derivative of order j inserts the factor (-2 pi i y)^j into
the physical integral. Here y is the physical coordinate, not frequency.
Consequently |G^(j)| <= M (2 pi H)^j. The degree-six real-frequency Taylor
remainder on a cell of radius d is at most

R_cell = M (2 pi H d)^7 / 7!.

No exp(2 pi H d) inflation is needed: the exponential factor has unit modulus
on the real frequency line, and the integral Taylor remainder uses that fact.
The model forms full complex carrier sums before taking any magnitude. Its
cell bound is the sum of (|computed derivative| + derivative error) d^j/j!
for j=0..6 plus R_cell. A conservative complex L1 norm, |Re|+|Im|, avoids
introducing an unpriced hypot evaluation; it is applied after cancellation.

Ideal frequency cells are rational intervals covering [-40,40]. The stored
midpoints are exact binary64 numbers. Their maximum displacement from ideal
midpoints is determined with exact Fraction arithmetic and added to d.
At width 0.005, d = 0.00250000000000852651. The two remainder prices are
1.30368196788e-9 / 2.11703341460e-6.

These remainders enlarge the cell magnitude bound, not the original-to-
polynomial difference radius. For example, if a comparison function has
magnitude at most 1 at the centre and varies by at most 0.1 in the cell, its
cell magnitude bound becomes 1.1; a separate approximation error of 0.001
does not become 0.101. The same distinction applies to this price.

## Derivative execution model

Multiplication by y is assembled with the recurrence
P_(j+1)(t) = (c + r t) P_j(t), where c and r are represented panel centre and
half-length, and t ranges over [-1,1]. This avoids unpriced general power
calls and reconstructs the derivative integrand without changing the owner.
Moment degrees extend from six to twelve using the same 48-term Horner
series; the original seven moment slots reproduce bitwise.

Order zero retains extended arithmetic and the original pairwise sequence.
Higher orders use explicitly cast binary64 matrix products, which are much
cheaper but receive their own larger error allowances. Their errors are
multiplied by d^j/j! in the cell bound. They are not silently assigned the
extended format's unit roundoff.

Let B_j = M (2 pi H)^j. Polynomial construction uses the extended gamma_8j
allowance. Pi representation and repeated prefactor multiplication are
charged separately. The panel chain uses gamma_(96+16j), with extended unit
roundoff at j=0 and binary64 unit roundoff at j>0. Pairwise addition has the
appropriate unit roundoff and depth; all factor products use safe magnitudes.
Conservative nonzero underflow floors are retained in the admitted captured
class. This remains a declared arithmetic/BLAS model, not a source-level or
machine proof of every rounding assumption.

## Controls and next obligation

Twenty-four independent 100-digit controls integrate the original stored
coefficients times exact powers of physical y. They cover both channels,
frequencies -3.605/0/3.605 and derivative orders 0/1/3/6. All remain within
their own derivative execution allowance; the largest ratio is 0.0005759913.
Eight selftests cover moment parity through degree twelve, exact y-power
reconstruction, independent derivatives, values between nodes, rational cell
coverage at both ends, post-sum norms, artifact scope and source hashes.

An unexecuted draft containing placeholder prices and unchecked derivative
code was replaced before any result was generated. It licenses no numerical
conclusion or no-go. The committed method has no zero-price placeholder.

The next obligation is a continuous kernel/annihilator weight bound on the
same cells, retaining all 41136 prime powers and signed cancellations before
bounding variation. Once the weight is bounded, cell width times the product
of the cell weight bound and the existing perturbation majorant can be summed
with directed arithmetic. Sampled weights or agreement of midpoint grids
cannot supply that missing bound. Infinite tails, actual selected-owner
readback and hgap remain open; no RH claim is made.
