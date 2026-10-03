Record 2538: explicit whole-cell weighted-family third bound
Date: 2026-10-03

Lean now derives the fourth-derivative bound and the third-derivative
Lipschitz estimate for the existing weighted external family. The final
theorem requires only a positive support radius and an ordered cell [a,b].
It has no sampled-supremum or assumed fourth-derivative-bound premise.

Cell geometry

Let N be zero if [a,b] contains zero, and min(|a|,|b|) otherwise.
Let M=min(max(|a|,|b|),r), where r>0 is the support radius.
For interior points |x|<r, the proof establishes

```text
N/r <= |x/r| <= M/r.
```

If N>=r, the entire cell lies outside the open support. The theorem
weightedExternalFamily_iteratedDeriv_zero_outside2538 proves that the
derivatives vanish, including the boundary |x|=r. If N<r, the local
2536 bound applies with near=N/r and far=M/r.

The upper ratio is restricted to interior points. A cell that crosses the
support edge contains points with |x/r|>1, while M/r<=1. Requiring the
interior ratio inequality on the entire cell would reject valid boundary
cells. The proof handles exterior points with the zero-derivative theorem.

Derived bound

Write F for weightedFunction2348 sigma (externalFamilyValue2344 c theta r),
lambda=sigma+i*theta and E=exp(max(sigma*a,sigma*b)). The fourth bound is

```text
L = |c| * E * (B4 + 4*|lambda|*B3 + 6*|lambda|^2*B2
                   + 4*|lambda|^3*B1 + |lambda|^4*B0),
Bk = localCoupledBumpUpper2536 k r (N/r) (M/r).
```

weightedFamilyCellUpper_four2538 proves this five-term expansion from the
binomial sum. It matches the terms in the 2535 fourth-envelope evaluator.
The third derivative is differentiable across the support edge because the
underlying bump has a smooth zero extension. The mean-value inequality gives
|F'''(x)-F'''(y)|<=L*|x-y|. Applying 2534 yields

```text
|F'''(x)| <= max(|F'''(a)|, |F'''(b)|) + L*(b-a)/2,  x in [a,b].
```

The final weightedExternalFamily_third_le_cell2538 theorem computes the
cell geometry itself and selects zero for the exterior branch. It supplies
the analytic whole-cell bound used by the external 2535 calculation.

Coefficient uncertainty

For a coefficient c with center m and error radius rho, assume |c-m|<=rho.
The theorem weightedExternalFamily_third_le_coefficient_ball2538 proves
the bound (|m|+rho) times the unit-coefficient whole-cell bound. It uses the
exact coefficient-linear derivative formula, so the coefficient uncertainty
survives even when the midpoint coefficient cancels or vanishes. Importing
the 2338 coefficient enclosures into Lean remains open.

Validation and remaining work

The paired 2537/2538 audits cover nine declarations. The acceptance checker
parses multiline axiom reports, requires exactly the standard three axioms
on each leaf, checks the successful build footer and zero error lines, and
compares the audit/root import cones byte for byte with the build mirror.
Final acceptance: 4393 build jobs, zero error lines, nine standard-axiom
leaves and 617 byte-identical project source files. The accepted record is
results/2538_weighted_cell_validation.json.

The 2535 rational table has not been imported as a Lean numerical certificate.
The next obligation is the signed aggregate's midpoint-second bound using
these familywise third bounds, followed by certified node evaluations and
segmented rational sums. Exact interpolation-owner transfer and the complete
selected-owner signed margin remain open. This result does not assert
Producer GO, SourceRH or RH.

Evidence:
ConnesWeilRH/Dev/C1RouteAWeightedFamilyCell2538.lean
ConnesWeilRH/Dev/C1RouteAWeightedFamilyCell2538Audit.lean
scripts/validate_weighted_cell_2538.py
results/2538_weighted_cell_validation.json
