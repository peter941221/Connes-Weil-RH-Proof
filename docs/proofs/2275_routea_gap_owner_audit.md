# 2275 - Same-owner gap audit and refinement-inference obstruction

Date: 2026-09-30

Result: hgap remains OPEN. Record 2255's measurements do not supply an
analytic upper bound of 10000000. This round captures the original 2249
coefficient vectors with matching byte hashes, gives an exact counterexample
to refinement-only inference, and proves why a finite quadrature rule cannot
supply its own infinite-frequency decay. These are scoped inference
obstructions, not a lower bound on the actual ideal-to-discrete error.
No producer GO, no RH claim, and no new Lean theorem are asserted.

## 1. The coefficient owner

An owner is the particular test function to which an estimate applies.
Changing its coefficients changes that function, like weighing a different
sample on the same scale.

In 2255's run_instrumented, changing m resets the GL node cache, builds a
new matrix, and solves base and corr again. GL (Gauss-Legendre quadrature)
is a finite weighted sum used to approximate an integral. Thus the quad
row changes both the evaluation rule and the coefficient owner; it is not
an isolated same-owner quadrature error. This statement concerns the
construction path; it does not assert a measured amount of coefficient drift.

The new capture reconstructs only the 2249 matrix and its two solves at
m = 6400. It does not rerun the 4001-point functional. Both byte hashes
match the original artifact:

```text
vector   original and reconstructed MD5
base     d461872e14212dcba8efe1874de6f652
corr     c37e16a9dfeb4383c7bab1d23aa59566
```

The artifact stores binary64 values as hexadecimal strings, which preserve
each floating-point input exactly, together with family parameters, target
nodes, right-hand sides and GL table hashes. The tests decode the vectors
and verify their byte hashes again; corrupted coefficients are rejected.
Local Python import dependencies are hashed and bound to the replay.
This is construction provenance, not a proof that these tests equal the
Lean selected detector or that ideal interpolation hits the prescribed nodes.
It does not borrow 2267's coefficients or transfer its envelope to this owner.

## 2. Exact obstruction to refinement-only bounds

Let A > 0 and, on [0,1], set

  f(x) = A*x*(1-x)*(x-1/2)^2.

The function is nonnegative and infinitely differentiable. Its values at
0, 1/2 and 1 are zero. Hence the endpoint trapezoid and its doubled-grid
refinement both give exactly zero, without any floating-point error.
Expanding gives

  f(x)/A = -x^4 + 2*x^3 - (5/4)*x^2 + (1/4)*x,
  integral f = A*(-1/5 + 1/2 - 5/12 + 1/8) = A/120.

For A = 2400000000, the true integral is 20000000, larger than the entire
registered gap budget, while the refinement difference is zero. Scaling A
makes the true error arbitrarily large without changing either grid reading.

This exact rational witness refutes a general implication from
|delta| + E_old + E_new to an integral error bound. It is not an example
from the actual detector family, nor a claim that that family's error is
large. Extra analytic information about that family could still prove hgap.
For any fixed finite pair of grids, a squared polynomial vanishing at their
union gives the same obstruction: its integral is positive and freely scalable.

## 3. Finite-rule recurrence, with the pi convention kept explicit

The exact-chain family in laplace_rows has the form

  V(x) = a * sum_p f_p * exp(a*X_p/2)
                    * exp(i*a*(theta - 2*pi_stored*x)*X_p).

Here a and X_p are stored binary64 inputs, f_p are fixed quadrature terms,
theta is the family modulation, and pi_stored is the stored math.pi input.
For the exact shadow target, f_p is the exact phi value at the stored node
times its stored weight; the computed phi_terms value has its own error
allowance. Recurrence depends only on the frequencies and holds for either
choice. Treating computed intermediate terms as exact must not silently
replace the exact shadow target in a gap certificate.
This is a finite exponential sum, not the Fourier transform of the smooth
compact bump. Every finite binary64 input is a dyadic rational (an integer
divided by a power of two). The exact products a*X_p therefore have a
common power-of-two denominator, say 2^B. With pi denoting mathematical pi,

  T = (pi / pi_stored) * 2^B

makes every phase increment an integer multiple of 2*pi. Consequently
V(x + T) = V(x) exactly in the stored-operands-as-real convention.
This is not a claim that floating-point evaluation at an enormous x is
accurate or bitwise recurrent.

For the captured tables B = 106. A universal sufficient exponent for
products of arbitrary finite binary64 inputs is 2148, attained by the
square of the smallest positive subnormal. Both claims use exact rational
arithmetic, not a float phase evaluation. Each captured family has
nonnegative f_p with at least one positive term. At
x = theta/(2*pi_stored), all phases vanish and V(x) > 0. Periodicity then
prevents that family's V from tending to zero at infinity.

Thus no bound C/(1+|x|)^r with finite C and r > 0 holds for this nonzero
finite-rule family on the full line. An identically zero linear combination
is an explicit exception. No sign or divergence claim about the full
kernel-weighted base/corr product follows from the family statement alone.
The obstruction freezes only extrapolation of finite-rule ring readings
into a true infinite tail; the ideal smooth functions may have valid decay.

## 4. Analytic supplier contract

An analytic bound is an inequality valid between sample points and outside
the sampled window, rather than agreement between two sampled answers.
To bind hgap to an object, first define:

  S = exact stored weighted sum of 2249, including its stored coordinates;
  Gd = exact finite-rule integrand with the captured base/corr;
  Gi = ideal smooth-bump integrand with those same coefficients;
  Tu = exact trapezoid of Gd on the uniform rational grid x_j = -40+j/50;
  Qi = integral over the full line of Gi.

Gi must specify its exact bump transform, a-scaling, pi convention and
kernel, including the visible-prime list. Extending that prime list or
changing the selected Lean test is a separate owner change, not a silent
part of this bridge. Stored coefficients alone do not establish ideal
interpolation or selected-detector readback.

For example, the smooth integral replacing the displayed finite rule is

  F_j(x) = a_j * integral from -a_j to a_j of
           phi_j(y) * exp(a_j*(1/2+i*theta_j-2*pi*i*x)*y) dy,
  phi_j(y) = exp(-30/(1-(y/a_j)^2)) inside that support, zero outside.

Its effective Fourier coordinate is a_j*y, not y. This is the scaling
actually present in 1980 family_values and 2249 laplace_rows. Pricing must
keep it; the stored-pi versus mathematical-pi discrepancy also needs a
charge when those conventions differ.

Once these definitions and integrability are established, the triangle
inequality gives the required four-part bridge:

```text
|Qi - S|
  <= integral outside [-40,40] of |Gi|          ideal tail only
   + integral inside  [-40,40] of |Gi - Gd|     fixed coefficients
   + |integral inside Gd - Tu|                 analytic grid remainder
   + |Tu - S|                                 stored coordinate transfer
```

Arithmetic evaluation errors are separate: 2249's E_total concerns its
floating sum versus S. It must not be counted again inside the gap if the
chosen q enclosure already pays it. The arbitrary Real gap argument in the
existing Lean consumer is not yet bound to |Qi-S| by a definition or theorem.

For a C2 function on a cell [l,l+h], integration by parts twice gives

  T_cell - integral_cell Gd
    = (1/2) * integral_cell (x-l)*(l+h-x)*Gd''(x) dx.

If M2 bounds |Gd''| on the window, the cell error is at most M2*h^3/12.
Summing the 4000 exact cells with h = 1/50 gives

  |integral inside Gd - Tu| <= M2/375.

Using the whole 10000000 budget on this term alone would require the
sufficient derivative cap M2 <= 3750000000. No such cap is proved here.
A large or failed global cap would reject this method, not the actual gap;
a panel-local bound or a corrected trapezoid can be much sharper.

The stored arange grid is not the uniform rational grid. The exact maximum
coordinate displacement is 55/4398046511104, approximately
1.2505552149377763e-11. If M1 bounds |Gd'| along the coordinate-transfer
segments, positivity of the weights and their total 80 give

  |Tu-S| <= 80 * (55/4398046511104) * M1.

Local derivative bounds can replace the global M1. Coordinate transfer
must be priced rather than dismissed because the decimal step looks uniform.

## 5. Reproduction and acceptance

From the repository root in the Linux verification environment:

  python3 scripts/routea_gap_owner_audit_2275.py --capture-owner
  python3 scripts/routea_gap_owner_selftest_2275.py
  python3 scripts/routea_gap_owner_audit_2275.py

The first command regenerates the matrix-level capture and aborts on either
original coefficient-hash mismatch. The second runs exact witnesses,
corruption controls and artifact replay checks. The third replays without
re-solving, rejects changed source dependencies, and preserves the captured
vectors. None performs an unbounded search or a full-grid experiment.

Acceptance: 10 new tests and all 22 existing Linux strip integration controls
pass; source control and both coefficient anchors pass. The frozen capture
replay is byte-identical to the committed candidate artifact.
The artifact's status is REFINEMENT-INFERENCE-NO-GO, with hgap_closed false.
No bound source or Lean interface changed, so no strip manifest refresh or
Lean build is required for this record. Existing 2255 numeric artifacts are
preserved as historical measurements; its window-exact/resolved wording is
withdrawn in its report and superseded by this record.

## Next steps

1. Bind the ideal integrand and its captured coefficients to the selected
   detector. Completion requires explicit transform/scaling/kernel definitions
   and owner readback, not a renamed arbitrary gap variable.
2. Price the fixed-owner finite-window bridge with directed bounds, meaning
   arithmetic rounded outward so the true value remains inside the result.
   Keep both coefficient vectors frozen; accept only a proved residual price
   plus construction, phase and rounding charges.
3. Bound the ideal full-line tail and the analytic grid/coordinate terms.
   Completion requires their combined bound to fit 10000000, or a named
   method-level failure with the actual owner and hypotheses stated. Only
   then can a Lean supplier remove hgap from the consumer.
