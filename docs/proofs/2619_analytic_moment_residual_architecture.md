2619: first-order residual architecture for actual analytic entry (0,0)

Result and scope

The polynomial-residual architecture fits the unchanged 2597 real interval
in an independently assembled model enclosure. The owner phase, the
integrating-factor error theorem, the phase-variation bound, and the
two-sided edge integral bound are Lean-verified. The numerical polynomial
tables, scalar exponential tables, and partition assembly are not yet
Lean-certified. No actual entry containment, coefficient membership,
producer GO, or RH conclusion follows yet.

This is a pricing decision for the first real-coordinate certificate, not
another Arb numerical-integration replay. The probe calls no integration
backend. It evaluates exact rational polynomial integrals and scalar
exponential balls; its capture, radius, witness, and source are fingerprinted.

1. The actual object

Record 2618 proves that the captured diagonal entry is a real integral. Let
r be storedWidth(0)^2, z the captured node, and beta = z.re*r. For the
normalized coordinate u, the actual integrand inside its support is

  F(u) = exp(-30/(1-u^2) + beta*u), for |u| < 1,

extended by zero at and outside +/-1. The matrix entry is r times the
integral of F. The probe checks its exact r against the 2351 witness radius.

The integration window is cut at +/-9/10 and subdivided into 180 panels.
Each panel has center c and half-width h = 1/200. The local coordinate is
t = u-c. Define the local phase H(t), denominator D(t), and numerator N(t):

  H(t) = -30/(1-(c+t)^2) + beta*(c+t)
  D(t) = (1-(c+t)^2)^2
  N(t) = beta*D(t) - 60*(c+t)

Then H'(t) = N(t)/D(t). Lean proves this identity, including the nonzero
denominator guard. It also proves that the original normalized function
equals exp(H(t)) on every interior panel.

2. Why only a first derivative is needed

Instead of computing and bounding dozens of derivatives of F, build a
rational polynomial S(t) with S(0) = 1. The approximation is exp(H(0))*S(t).
The exact differential-equation residual is the polynomial

  Q(t) = D(t)*S'(t) - N(t)*S(t).

If S has degree n, its rational coefficients are chosen recursively so
that the coefficients of Q at degrees 0 through n-1 vanish exactly.
Because D and N have degree four, only five residual slots remain:
degrees n through n+4. This is checked by exact rational arithmetic in the
probe, not by sampling Q.

```text
Original non-polynomial integral
                |
                | exact first-order equation
                v
Rational polynomial S, with S(0) = 1
                |
                | exact coefficient recurrence
                v
Five remaining residual coefficients
                |
                | integrating-factor error bound (Lean proved)
                v
Exact polynomial integral + explicit error allowance
```

Let w = |c| + h < 1 and d = (1-w^2)^2. If M bounds |Q(t)| on [-h,h],
then R = M/d bounds |S'(t)-H'(t)*S(t)|. The probe obtains M by summing
absolute residual coefficients times h to the corresponding power. Let

  L = |beta| + 60*w/d
  V = L*h.

Lean proves |H(t)-H(0)| <= V. The integrating factor is exp(H(0)-H(t));
it converts the approximation error to a derivative controlled by R.
The mean-value bound then gives

  |exp(H(t)) - exp(H(0))*S(t)|
    <= exp(H(0))*exp(2V)*R*|t|.

Using |t| <= h over an interval of length 2h gives the certified panel
integral error

  E_panel = exp(H(0))*exp(2V)*R*(2h^2).

The final Lean consumer
momentPhase_integral_error_of_polynomialResidual2619 derives this bound
from panel geometry, the polynomial derivative identity, S(0) = 1,
and a bound on Q. It has no assumed actual integral bound or h_interval.

3. The edges are bounded, not sampled

For cut = 9/10 and cut <= |u| < 1,

  F(u) <= exp(-30/(1-cut^2) + |beta|).

Lean proves this pointwise bound, nonnegativity of F, and a bound for
the sum of both edge integrals. After multiplying by r, the charge is

  E_edge = 2*r*(1-cut)*exp(-30/(1-cut^2) + |beta|).

Both signs are included. The numerical scalar price of this formula is
1.53851678784551e-68. The theorem is proved; this particular exponential
price still needs attachment to a Lean scalar certificate.

4. Pricing evidence

Command: .venv-flint/bin/python scripts/analytic_moment_residual_probe_2619.py

The Python interpreter is the Linux environment with python-flint. The
script defaults to degrees 32, 48, 64; 180 panels; cut 9/10; and 384-bit
scalar ball arithmetic. The degree selects the number of exact recurrence
steps; the panel count selects the geometric partition. Neither parameter
changes the owner or the target interval. The script writes
results/2619_analytic_moment_residual_probe.json.

The existing real interval has width 1.1935800200480374e-64. The charges
include the physical multiplier r. Values below are model prices, not
new Lean-certified numeric constants.

```text
+--------+--------+------------------+-------------------+
| Degree | Panels | Interior charge  | Fits original box |
+--------+--------+------------------+-------------------+
| 32     | 180    | 6.8366866290e-71  | Yes, model only   |
| 48     | 180    | 2.7476019670e-93  | Yes, model only   |
| 64     | 180    | 1.9151872685e-114 | Yes, model only   |
+--------+--------+------------------+-------------------+
```

Degree 32 leaves lower and upper margins approximately 5.8728457904e-65
and 6.0614022200e-65 respectively. Degree eight is a negative control:
its 1.2426850e-28 interior charge fails the unchanged box. Raising the
degree past 32 reduces a term already smaller than the edge charge;
certification of the degree-32 architecture is the next useful action.

5. Validation and reproduction

Command: .venv-flint/bin/python scripts/analytic_moment_residual_selftest_2619.py

The eleven tests check analytic low-order coefficients, parity, the five-slot
residual, an independent Fraction evaluation of the differential equation,
invalid geometry, insufficient degree, and repeated pricing at 384/512 bits.
The exact coefficient/residual digest is unchanged across those precisions.

The first precision control incorrectly demanded overlap of two directed
upper prices. Such prices are distinct exact scalars, not two balls enclosing
the same object. The corrected control checks overlap of the core integral
balls and verifies that the higher-precision upper charge does not increase.
The original failing test licenses no verdict; the corrected full run passes.

Command: LEAN_PATH="$WORKSPACE/.lake/build/lib/lean:$LIBRARY_ROOTS" python3 scripts/validate_moment_residual_stability_2619.py --workspace "$WORKSPACE" --logs "$LOGS" --lean "$LEAN_BINARY"

WORKSPACE names a Linux workspace with a complete project namespace;
LIBRARY_ROOTS contains matching Mathlib/package libraries. LOGS stores the
compiler logs, and LEAN_BINARY selects the repository toolchain executable.
The validator rebuilds three new modules under the resource runner, verifies
source/object fingerprints and successful exits, and checks all fourteen
audit leaves against exactly propext, Classical.choice, and Quot.sound.
It also checks capture, witness, and probe-source freshness. Upstream project
and Mathlib objects are reused, not freshly rebuilt.

The machine-readable audit is
results/2619_moment_residual_stability_validation.json. The two artifacts
separate theorem verification from model pricing; neither asserts complete
actual-entry containment.

The final warm-cache build takes 6.17 seconds of total compiler wall time,
with peak single-process RSS 3.879 GiB. This excludes upstream construction
and failed development runs. All eleven new tests and seven existing 2618
tests pass. No 2271 bound-input source or manifest changes in this record.

6. Remaining work

First certify the degree-32 rational polynomials and scalar exponential
enclosures in Lean for one actual panel. This establishes that the priced
architecture has an executable numeric certificate, not only an analytic
error theorem. Then extend to the 180 panels and combine their integrals with
the certified edge charge. Completion is the original entry-(0,0) real
membership in the unchanged 2597 rectangle. The 2618 imaginary proof can then
produce the first complete entry membership.

The route has not switched to an alternative RH producer. The full analytic
matrix, actual coefficient membership, and selected-detector signed budget
remain necessary downstream obligations.
