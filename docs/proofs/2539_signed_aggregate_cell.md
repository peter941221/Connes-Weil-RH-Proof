Record 2539: signed aggregate curvature and full-strip inequality
Date: 2026-10-03

The 30-family external physical function now has an analytic bound from
signed midpoint evaluations to the full-strip integral on the 10240-cell
grid. The theorem retains coefficient uncertainty as an explicit hypothesis.
Numerical evaluation of the bound and membership of the exact interpolation
coefficients in the 2338 boxes remain open.

Definitions and signed cancellation

Let c_i be the actual complex coefficient, m_i its chosen center, and e_i
an error radius satisfying |c_i-m_i|<=e_i. Let phi_i be the unit-coefficient
family with the existing squared stored width and signed modulation. For
real sigma, set F(x)=exp(sigma*x)*sum_i c_i*phi_i(x). The notation J_k(x)
below denotes the following bound on its k-th derivative:

```text
J_k(x) = |sum_i m_i*(exp(sigma*x)*phi_i(x))^(k)|
           + sum_i e_i*|(exp(sigma*x)*phi_i(x))^(k)|.
```

The first norm surrounds the complex sum. For example, contributions 10
and -9 cost 1 there, whereas separate norms would cost 19. Only coefficient
uncertainty uses separate scalar charges. The coefficient-linear derivative
identity and the triangle inequality prove the bound for every order k.

Whole-cell curvature and integration

For a cell [a,b], put h=b-a and t=(a+b)/2. Let T_i(a,b) be the explicit
unit-family third-derivative upper proved in 2538. Define

```text
L(a,b) = sum_i (|m_i|+e_i)*T_i(a,b)
M(a,b) = J_2(t) + h*L(a,b)/2.

|F''(x)| <= M(a,b), x in [a,b]
integral_a^b |F(x)| dx <= h*(J_0(a)+J_0(b))/2 + h^3*M(a,b)/12.
```

The first inequality controls movement away from the midpoint using the
third derivative. The second uses the proved complex-function chord bound
from 2347. It does not differentiate the norm at a zero of F.

Summing adjacent cell integrals proves the composite inequality. The
stored family radii lie below R=65536001/10000000, and each family vanishes
at and beyond its support boundary. Thus the full real-line weighted norm
equals the integral over [-R,R]. The final theorem uses left=-R,
step=2*R/10240 and 10240 cells.

Exact remaining interface

The theorem externalPhysical2344_strip_le_signed_10240_2539 requires
only the coefficient-error hypothesis for arbitrary coefficients, centers,
errors, signed modulations and real sigma. Its right-hand side is the
analytic expression signedCompositeUpper2539. No concrete upper value,
2338 coefficient membership, base pin, correction-channel bound or selected
detector positivity follows without further proof.

The external 2535 rational table therefore retains its existing evidence
level. The known equality between externalPhysical2344 and correctedPhysical
does not establish that the exact interpolation coefficients belong to the
chosen boxes. Both the numeric certificate and that membership proof are
needed before applying the bound to the intended interpolation owner.

Validation

The audit lists eight declarations, including the full-strip theorem. The
checker requires the three standard axioms on each declaration, a successful
audit/root build with zero error lines, and byte identity of the project
source import cones and toolchain/configuration with the build environment.
The acceptance record is results/2539_signed_aggregate_validation.json.
Acceptance passed: 4393 build jobs, eight standard-axiom leaves, zero error
lines, no new-module warnings, and 617 byte-identical project sources.

Next steps

1. Certify representative signed node and curvature evaluations in Lean,
   including cancellation and support-edge cases. A completed pilot must
   prove concrete inequalities without assuming the numerical answers.
2. Prove membership of the exact interpolation coefficients in the boxes
   used by those evaluations, retaining the same widths and modulations.
3. Extend the numerical certificates to the grid with segmented rational
   sums, then discharge the other endpoint channels and the complete
   selected-owner signed budget. The route ruling remains unchanged.

Evidence:
ConnesWeilRH/Dev/C1RouteASignedAggregateCell2539.lean
ConnesWeilRH/Dev/C1RouteASignedAggregateCell2539Audit.lean
scripts/validate_signed_aggregate_2539.py
results/2539_signed_aggregate_validation.json
