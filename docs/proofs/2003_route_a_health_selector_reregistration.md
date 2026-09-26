# Record 2003 - A-H health-constrained selector: instrument audit and re-registration

Date: 2026-09-26.

Status: supersedes the registered instrument of record 2002. Committed before
any registered run of the revised instrument. No theorem, no Lean brick, and
no RH claim.

## 1. Defect 1 - the record-2002 family destroys the gate instrument

Record 2002 registered an overcomplete owner family with three width copies
per node, `0.8a / 1.0a / 1.2a`. The `1.2a` copy raises the support radius
that the gate instrument uses, `support_radius = max(a) * (n + 2)`, and the
prime-power set grows with it. For the first registered case (G5-H, scale
0.92):

```text
family                 max width   support radius   prime powers   route Ap
committed base          4.9680        9.9360           2393          present
record-2002 three-copy  5.9616       11.9232          14033          dropped
```

`gate_entries` computes the exact-transform route `Ap` only while
`n_primes <= 4000`. With 14033 prime powers the route set collapses to
`{A, B}`, and `route_spread` - which measures the spread across the certified
routes `("Ap", "B")` - then has a single certified route and returns exactly
`0.0`. The registered certification test `spread_D < 1/3` is therefore
satisfied by a degenerate floor that carries no information (project law F52).
Every row of the record-2002 instrument is instrument-limited and its decision
rule is vacuous. The uncommitted smoke output of that instrument showed the
signature directly: route set `["A", "B"]`, `spread_D = 0.0`,
`certified = True`.

## 2. Defect 2 - the record-2002 verdict rule fires on the committed endpoint

Record 2002 required only "a certified healthy point". But `t = 1.0` is the
embedded committed selector, and the committed selector is certified healthy
in all four registered cases (section 5). A rule phrased that way fires on the
endpoint alone, and its NO-GO clause ("no registered case has a certified
healthy point") is unreachable. The informative statistic is interior health.

## 3. Defect 3 - the min-H1 selector endpoint is not numerically well-defined

`support_radius` can be preserved by keeping every copy no wider than the
committed width, which fixes defect 1. That repair was implemented first as a
two-copy family (`0.75a`, `1.0a`) with the correction endpoint `c_min` taken
as the minimum-H1-energy interpolant, solved through a clipped pseudo-inverse
of the H1 Gram. The smoke run of that repair exposed defect 3.

The H1 Gram of the overcomplete family is numerically rank deficient. Relative
eigenvalue spectra and the resulting interpolation accuracy for G5-H at scale
0.92, 34 basis functions, 17 interpolation nodes:

```text
family                       min rel eig   rank @1e-12   pin residual   |c|max
width copies 0.75a + a         1.4e-14      31 of 34       4.19e-06      2.3e+16
frequency offsets +0.5         2.9e-15      31 of 34       8.95e-07      6.2e+15
frequency offsets +1.0         1.3e-14      31 of 34       2.18e-07      1.9e+15
frequency offsets +2.0         2.8e-14      30 of 34       2.69e-05      1.8e+15
frequency offsets +4.0         1.2e-15      32 of 34       1.40e-05      1.5e+15
```

The deficiency is intrinsic to these smooth modulated-bump families and is
not a property of the width-copy construction. Consequences for the
registered object:

1. Clipped pseudo-inverses do not reach the registered pin gate. At cutoff
   `1e-12` the pin residual is `4.19e-06 > 1e-06`; lowering the cutoff to
   `1e-14` makes it worse (`4.19e-05`), because dividing by eigenvalues at
   roundoff level amplifies noise. Coefficients of size `2.3e+16` are
   meaningless.
2. The exact-constrained minimizer (KKT least squares) does reach the pins
   (`1.79e-13`) but with `|c|max = 7.4e+14`. Evaluating the density from
   coefficients of that size loses roughly `14` decimal digits to
   cancellation, so the density - and every gate entry built from it - is
   dominated by roundoff.
3. Therefore "the minimum-H1-energy interpolant in the overcomplete family"
   has no numerically defined value at this basis size in `float64`, and the
   registered segment `c(t) = (1 - t) c_min + t c_ref` of record 2002 (and of
   the first draft of this record) cannot be evaluated.

This is a property of the functional, not of the owner: the committed owner
itself is unaffected, and the committed single-copy interpolation stays
well conditioned (`cond = 1.9e+04` for this case).

## 4. Revised instrument - a well-posed feasible-fiber ray scan

The registered replacement drops the ill-posed energy minimisation and keeps
the well-posed part of the question, namely how the health functional `C`
responds to moving inside the feasible fiber. Two ingredients make the
replacement well posed:

1. Support preservation. Each node keeps exactly two basis functions, widths
   `0.75a` and `a`, so the widest copy is the committed width. The support
   radius, the prime-power set, and the gate instrument are then identical to
   the committed ones at every parameter value, and route `Ap` stays
   available.
2. Exact feasible directions. The pins are the equations `M c = y` with
   `M` the `(nodes x basis)` family-value matrix. Directions in the nullspace
   of `M` preserve the pins exactly to machine precision, without any
   inversion of the singular Gram. The scan moves along canonical unit-H1
   directions,

```text
Z      = null(M)                       obtained from the SVD of M
G_Z    = Z* G Z                        H1 metric restricted to the fiber
d_j    = Z v_j / sqrt(real(v_j* G_Z v_j))   v_j the j-th top eigenvector of G_Z

corr(sigma, j) = c_ref + sigma * E_ref * d_j
E_ref  = sqrt(real(c_ref* G c_ref))    H1 norm of the committed correction
```

so `sigma` is the perturbation's H1 norm measured in units of the committed
correction's H1 norm. Every row of the scan is an exact interpolant by
construction, and the scan samples the two most energetic directions in the
fiber.

The corrected correction endpoint is the committed one, so `sigma = 0`
reproduces the committed selector exactly. That reproduction is the registered
instrument check.

## 5. Registered cases, grid, and committed references

Cases and gate settings are unchanged from record 2002:

```text
case    delta   gamma        scale
G5-H    0.10    30.424876    0.92
G5-W    0.10    30.424876    0.90
G7-H    0.10    37.586178    0.92
G8-H    0.10    40.918719    0.88

sigma in {0.00, 0.02, 0.05, 0.10, 0.20, 0.40, 0.80}
directions j = 1, 2 (top two eigenvectors of G_Z)
k = 30;  n = 0;  xi_max = 40;  dxi = 0.004;  H1 Gram: 2400-point Gauss-Legendre
```

Committed EXT-convention reference rows (records 1994b and 1996, `dxi =
0.004`), all four certified healthy:

```text
case    file                              np     cond      C
G5-H    1994b_ext_convention_control.json 2393   18577.2   +1.494812433412335
G5-W    1996_gamma78_full_sweep.json      1985   25384.8   +0.2559098884994455
G7-H    1996_gamma78_full_sweep.json      2393   16116.4   +173.2980278055402
G8-H    1996_gamma78_full_sweep.json      1647   19406.7   +664.3518622617412

case    B01                      D                          det
G5-H    +115028.51993638277      -6307380989581.586         -9441583085893.906
G5-W    +1212552.3928831816      -225135731196973.47        -59084743173345.34
G7-H    -82862403431.9729        -2.0359193769218664e+20    -4.21482591816874e+22
G8-H    -53525649223.33458       -1.111261609813454e+20     -7.669186711873433e+22

case    spread_D
G5-H    3.2147501433824275e-05
G5-W    2.3717706773839426e-05
G7-H    2.280198243460176e-05
G8-H    1.3079889150016728e-05
```

## 6. Decision rules

```text
certified(row):
  density finite, cond <= 1e8, pin errors <= 1e-6, at least two certified
  routes among ("Ap", "B"), spread_D < 1/3.

healthy(row):
  certified and C > 0 and D < 0 and det < 0.

INSTRUMENT-FAIL:
  some case has no committed reference row, or its sigma = 0 row is not
  certified, or that row deviates from the committed reference by more than
  1e-6 relative on C, B01, or D.

A-H-CONE-NONEMPTY:
  no instrument failure, and at least 3 of 4 cases have a certified healthy
  row with sigma >= 0.05 in some registered direction.

A-H-CONE-EMPTY:
  no instrument failure, and no case has a certified healthy row with
  sigma >= 0.05.

A-H-CONE-MIXED:
  no instrument failure, and exactly 1 or 2 cases have such a row.
```

The registered health radius of a case is the largest `sigma` with a
certified healthy row; it is reported per case and per direction.

## 7. Scope

A-H-CONE-NONEMPTY authorizes a health-cone and dual-certificate desk; it is
not a producer theorem. A-H-CONE-EMPTY is scoped to these two canonical
directions, this two-copy family, these four owners, and this physical
energy normalisation; it does not exclude a healthy region reached along
other directions, and it does not touch the COVER layer or the committed
owner. Nothing in this record changes the binding Route A obligation
(`D < 0` on the selected healthy owner).
