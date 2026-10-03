Record 2541: signed nonzero production-node certificate
Date: 2026-10-04

Lean proves the signed order-zero node upper 13.7900014901 at index 5121
of the existing 10240-cell grid, with sigma=1/2. The point is
65536001/51200000000. Unlike the center-node certificate, this evaluation
retains the nonzero signed modulation of every family.

The certificate uses the same 30 stored squared widths, signed modulation
from the 2275 capture, and exact 2338 coefficient-box midpoints imported in
2540. The 10^-30 coefficient radius from 2540 remains in the final bound.
Membership of the exact interpolation coefficients in those boxes is still
an explicit premise when applying the result to the actual function.

Complex exponential evaluation

For one family, let r be its squared stored width, theta its signed
modulation, x the node, and sigma=1/2. Its weighted unit-coefficient value
inside the support is exp(w), where

```text
w = sigma*x - 30/(1-(x/r)^2) + i*theta*x
z = w/64.
```

The theorem nodeUnit_eq2541 checks the equality with weightedUnitJet2539
for all 30 families. The generator reads each binary64 hex width and
modulation as its exact rational value. Lean checks the radius and exponent
identities against storedWidth, rather than trusting the capture's labels.

The Horner scheme evaluates a polynomial through nested multiply-and-add
steps. Here it evaluates the first 20 exponential-series terms. Starting
from H_0=1, its exact recurrence is

```text
H_(n+1) = 1 + z/(19-n)*H_n,  n=0,...,18.
H_19 = sum_(k=0..19) z^k/k!.
```

All 30 scaled arguments satisfy |z|<=1. Mathlib's Complex.exp_bound gives
a Taylor remainder no larger than 10^-18. The generator rounds both
coordinates after each Horner step to the 2^-100 grid. The sum of the two
coordinate rounding errors is at most delta=2^-99. Lean checks each such
rational inequality; the accumulated Horner radius is at most 19*delta.

Six rounded squarings recover exp(w). If v is the true value, p the current
complex approximation, e its certified error, M an upper on |p|, and q the
next rounded square, the proof uses

```text
|v-p| <= e,  |p| <= M,  |p^2-q| <= delta
     => |v^2-q| <= e*(2*M+e) + delta.
```

The witness supplies M=|Re(p)|+|Im(p)| at that step and rounds the new
error radius upward on the 2^-140 grid. This retains the decay of the
intermediate values. Replacing those magnitudes by a uniform unit bound
would lose the exp(-30)-scale damping needed when multiplying by large
coefficients. The bound also includes the e^2 term, including when p is
small or vanishes.

Signed assembly

Let m_j be the exact coefficient midpoint, p_j the final rounded exponential,
e_j its error, and S=sum_j m_j*p_j. Lean proves the exact complex value of S
by rational arithmetic. It then checks a squared norm bound on
Re(S)^2+Im(S)^2; it does not sum the norms of the 30 family contributions.

The evaluation charge is bounded by

```text
sum_j (|Re(m_j)|+|Im(m_j)|)*e_j <= 10^-12.
```

Independent exact arithmetic reads this sum as approximately
9.97382719048755e-15. The proof uses the larger 10^-12 allowance.
The final family radii are about 1.1154e-29 to 1.2126e-29. Coefficient
uncertainty adds at most 30*10^-30 because each unit-family value has norm
at most one at this node. The final rational upper is

```text
signedJetUpper2539 0 (1/2) centers errors modulations x
    <= 137900014901/10000000000.
```

The theorem weightedPhysical_nonzero_le2541 applies this result to any
coefficient vector in the imported rectangles. It introduces no numerical
inequality premise.

Validation

The acceptance checker independently parses the generated rational
expressions. It checks the 30 inputs against the capture, 570 Horner
rounding steps, 180 square steps, scalar-radius propagation, signed final
sum, coefficient charge and final margin. Changed-center and zeroed-radius
negative controls are rejected. Regeneration checks cover the emitted proof
files as well as their data.

The audit covers 36 declarations, including all 30 exponential certificates
and the final signed-node theorem. Final audit/root build: 4536 jobs;
36 standard-axiom leaves; 725 byte-identical project sources; zero errors
and no warnings in the new modules. Evidence is recorded in
results/2541_nonzero_node_validation.json.

Scope and next steps

This certifies one positive nonzero node at sigma=1/2. It does not establish
the other endpoint sign, other nodes, derivative evaluations, full-grid
integral, exact interpolation membership, correction channels or complete
selected-detector positivity. The route ruling is unchanged.

The 30 generated family witness files contain 618641 bytes of UTF-8 source
with LF newlines. Before full-grid expansion, the certificate representation
needs a size/cost check and reuse of the verified arithmetic steps; copying
this pilot's source layout to every node would be expensive.

Next targets are a stronger-phase production node and a support-edge case,
then derivative certificates and segmented grid sums. Each extension must
check its own scaled-argument condition and error budget. Success at this
small positive node is not evidence that a fixed six-square schedule works
throughout the support.

Evidence:
ConnesWeilRH/Dev/C1RouteAComplexExpBall2541.lean
ConnesWeilRH/Dev/C1RouteAExpNode2541P000.lean through C1RouteAExpNode2541P029.lean
ConnesWeilRH/Dev/C1RouteANonzeroNode2541.lean
ConnesWeilRH/Dev/C1RouteANonzeroNode2541Audit.lean
scripts/generate_complex_exp_node_2541.py
scripts/generate_nonzero_node_2541.py
scripts/validate_nonzero_node_2541.py
results/2541_nonzero_node_validation.json
