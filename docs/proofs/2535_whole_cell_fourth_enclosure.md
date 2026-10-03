Record 2535: whole-cell fourth-derivative enclosure
Date: 2026-10-03

The 10240-cell base-channel budget passes with an analytic whole-cell
third-derivative bound. Both endpoint totals stay below 2.7790943782.
This is an external Arb enclosure of the function defined by the 2338
coefficient boxes. Lean numerical import and the exact-owner bridge remain open.

Owner and scope

The evaluator retains all 30 families, the signed modulation, squared-width
support radii, and the ideal base-coefficient rectangles from record 2338.
The outer integration radius is the exact rational 65536001/10000000.
The program uses the 2275 capture only for family geometry, never for the
rejected captured coefficient vectors. It checks the 2338 capture hash and
the ordering and count of the coefficient rows.

For family i, r_i is its support radius, theta_i its signed modulation, and
c_i its exact coefficient inside the supplied rectangle. Write c_i=m_i+e_i,
where m_i is the exact rectangle midpoint and |e_i|<=rho_i; rho_i is the
Euclidean radius of that rectangle. The weighted family without coefficient is

```text
phi_i(x) = exp(-30 / (1-(x/r_i)^2) + (sigma + i*theta_i)*x), |x|<r_i
phi_i(x) = 0,                                           |x|>=r_i
F(x)     = sum_i c_i * phi_i(x)
sigma    = -1/2 or +1/2
```

Here i in the exponential denotes the imaginary unit. At each node the
evaluator first sums the complex midpoint terms, then takes their norm and
adds sum_i rho_i*|phi_i|. It uses the same order for F'' at each cell midpoint.
Arb also encloses transcendental evaluation and arithmetic error in these sums.

Whole-cell derivation

Let q=1-u^2, b(u)=exp(-30/q), and P_k be the polynomial satisfying
b^(k)(u)=exp(-30/q)*P_k(u)/q^(2k). Differentiation gives

```text
P_0(u)     = 1
P_(k+1)(u)= (1-u^2)^2 * P_k'(u)
             + (-60*u + 4*k*u*(1-u^2)) * P_k(u)
```

The generated coefficients agree with the existing order-0..4 formulas in
C1RouteABumpDerivativeLadder.lean. The independent selftest differentiates the
original exponential with mpmath rather than reusing this recurrence.

For a cell [a,b], let near=min(|x|) over the cell and
far=min(max(|a|,|b|),r_i). A cell crossing zero has near=0. If near>=r_i,
the family and its derivatives vanish throughout the cell. Otherwise set
t0=1/(1-(near/r_i)^2). For interior points, t=1/q>=t0>=1.
For k<=4, differentiation of t^(2k)*exp(-30*t) gives a factor 2k-30*t<0.
Consequently,

```text
t^(2k)*exp(-30*t) <= t0^(2k)*exp(-30*t0)
|P_k(u)|          <= sum_p |coefficient_(k,p)|*(far/r_i)^p
```

Multiplying these two bounds and dividing by r_i^k bounds the scaled bump
derivative. This couples decay and inverse powers even when the cell reaches
the support boundary. The smooth zero extension supplies the boundary value.
Record 2536 proves this scaled-bump inequality in Lean.

Set lambda_i=sigma+i*theta_i. The fourth family derivative obeys the product
rule bound

```text
sup_cell |phi_i''''| <= max_cell exp(sigma*x)
  * sum_(k=0..4) choose(4,k)*|lambda_i|^(4-k)*bump_bound_(i,k).
```

No sample supplies this supremum. Let L_i be this fourth bound, h=b-a,
and M3_i=max(|phi_i'''(a)|,|phi_i'''(b)|). The nearest-endpoint argument gives
sup_cell |phi_i'''|<=M3_i+h*L_i/2. Thus a valid bound for |F''| is

```text
M2 = |sum_i m_i*phi_i''(mid)| + sum_i rho_i*|phi_i''(mid)|
       + h/2 * sum_i (|m_i|+rho_i)*(M3_i+h*L_i/2).
```

For the complex function F, the linear chord interpolation error integrates
to at most h^3*M2/12. Integrating the norm of the chord costs at most the
trapezoid of its endpoint norms. This argument bounds the vector function
before taking its norm; it requires no derivative of |F| at a zero of F.

Results

WSL2, python-flint 0.9.0, Arb precision 192 bits, 10240 exact rational cells.
The command is python scripts/routea_owner_whole_cell_2535.py --cells 10240 --rows
in an environment providing python-flint. Project runs use the resource runner.

```text
+--------+-------------------+-------------------+-------------------+
| sigma  | node upper        | remainder upper   | total upper       |
+--------+-------------------+-------------------+-------------------+
| -1/2   | 2.686700019845782 | 0.001698928979351 | 2.688398948825133 |
| +1/2   | 2.675007889593529 | 0.001682237795349 | 2.676690127388878 |
+--------+-------------------+-------------------+-------------------+
```

The exact rational artifact leaves margins about 0.0906954294 and
0.1024042508. The fourth-derivative inflation costs 0.000020475533 per sign.
Displayed decimals are summaries; the exact rational fields govern comparisons.

Validation and export

- Independent derivatives: 150 comparisons, worst relative discrepancy
  4.14e-55; 792 sampled controls of the analytic envelope cover interior,
  exterior, zero-crossing and support-crossing cells. These controls detect
  implementation mistakes; the derivation above supplies whole-cell validity.
- The exact-payload checker checks 20480 cell coordinates, positive upper
  bounds, the h^3/12 charge, rational sums, margins and source hashes. Its
  negative test rejects a changed coordinate. It does not certify analysis.
- Full same-precision replay reproduces the endpoint objects and all cell
  rows exactly. A full 256-bit replay passes both pins; differences from the
  192-bit totals stay below 1e-35. The node sums agree with the independent
  2533 diagnostic within 1e-35, with matching coefficient and capture hashes.

The first export attempted to print an extremely small boundary value as a
rational with over 33000 denominator digits. The final exporter rounds positive
values below 2^-128 up to that explicit floor. It never drops them to zero.
It sums the exported rational charges and uses the larger of that sum and the
Arb accumulated upper bound, so the headline includes export inflation.

Remaining proof work

Lean still needs the weighted complex family derivative composition, its
connection to the 2534 Lipschitz theorem, certified numerical evaluations and
the segmented sum import. The midpoint-plus-error decomposition must also
connect to the exact 2338 interpolation owner in the consumer. The correction
channel and the complete selected-owner signed C3-prime budget are outside
this base-strip enclosure. Producer GO, SourceRH and RH remain open.

Evidence:
scripts/routea_owner_whole_cell_2535.py
scripts/routea_owner_whole_cell_selftest_2535.py
scripts/routea_owner_whole_cell_check_2535.py
scripts/validate_whole_cell_2535.py
results/2535_whole_cell_enclosure.json
results/2535_whole_cell_validation.json
