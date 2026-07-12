# Pole-Free Constraint Survivor

Date: 2026-07-12

Status: superseded and rejected as an executable lower route by
`064_polefree_antimax_rejection.md`. The finite evidence below remains valid,
but the zero-energy scalar is an RH-closing pole-neutral Weil sign. The checked
Dirichlet/Perron properties do not imply it, and the Krein-string and abstract
anti-maximum theorems do not supply the missing implication. RH is unproved.

## 1. Source Object

On `L2(-a,a)`, let `A_a` be the localized Weil operator and

```text
R = W_(0,2) = 2|C><C| - 2|S><S|,
C(x)=cosh(x/2), S(x)=sinh(x/2).
```

The pole-free operator is

```text
A_tilde = A_a-R = -W_R-sum_p W_p.
```

The source proves on the common form domain

```text
<A_tilde v,v>
 = (1/2) integral integral J(x-y)|v(x)-v(y)|^2
   + sum_(n<=exp(2a)) Lambda(n)/sqrt(n)
       integral |v(x+log n)-v(x)|^2
   + integral kappa_a(x)|v(x)|^2,

J(t)=exp(-|t|/2)/(1-exp(-2|t|))>0.
```

It also proves that `A_tilde` is self-adjoint, lower semibounded with compact
resolvent, and has a simple strictly positive even ground state. These are
unconditional source theorems. The source only observes, numerically, that the
even restriction has exactly one negative eigenvalue; it does not prove that
Morse-index statement or the required resolvent sign.

Source:

```text
https://zenodo.org/records/20682834
Proposition "Form identity for the pole-free part"
Theorem "Unconditional Perron structure for the pole-free part"
```

## 2. Same-Object Vanishing Rows

In the even finite dictionary, the two independent square-root constraints
behind CC20 vanishing at `s=0,1/2,1` are

```text
mean-zero:     v_0=0,
pole-neutral:  <C,v>=0.
```

The pole-neutral row is fixed by the exact identity

```text
Q_pole = 2|C><C| = C_c beta^2 r r^T.
```

The new probe applies the rows separately to the same pole-free matrix
`Gamma+prime`; it does not infer them from the already positive full matrix.

## 3. Constraint Inertia

Arb gives the same pattern in every tested case:

```text
+-----+----+----------------+----------------+----------------+------------+
| c   | N  | full           | mean-zero only | C-neutral only | both rows  |
+-----+----+----------------+----------------+----------------+------------+
| 13  | 4  | (4+,1-)        | (3+,1-)        | (4+,0-)        | (3+,0-)    |
| 13  | 8  | (8+,1-)        | (7+,1-)        | (8+,0-)        | (7+,0-)    |
| 13  | 16 | (16+,1-)       | (15+,1-)       | (16+,0-)       | (15+,0-)   |
| 29  | 8  | (8+,1-)        | (7+,1-)        | (8+,0-)        | (7+,0-)    |
+-----+----+----------------+----------------+----------------+------------+
```

Thus:

```text
zero mean is not the sign mechanism;
pole neutrality is the active codimension-one condition;
the central CC20 row is redundant for this tested pole-free sign.
```

## 4. Scalar Resolvent Target

Assuming zero is not in the spectrum, the index-one Schur law gives

```text
A_tilde restricted to C-perp is nonnegative
  iff G(0)=<C,A_tilde^-1 C> <= 0.
```

The finite normalization is source-exact. Arb solves the indefinite system
directly and gives

```text
+-----+----+------------------------------+------------------------------+
| c   | N  | G(0)                         | 1+2G(0)                      |
+-----+----+------------------------------+------------------------------+
| 13  | 4  | -0.5000000000000021947...   | -4.3893e-15                  |
| 13  | 8  | -0.5000000000000000000...   | -4.2330e-23                  |
| 13  | 16 | -0.5000000000000000000...   | -5.3254e-35                  |
| 29  | 8  | -0.5000000000000000000...   | -1.3615e-27                  |
+-----+----+------------------------------+------------------------------+
```

This separates two gates:

```text
coarse survivor: G(0)<0, margin approximately 1/2;
full rank-one update: 1+2G(0)<=0, arithmetically tiny margin.
```

Together with the still-unproved continuum Morse-index-one statement, proving
only `G(0)<0` would establish pole-free positivity on the larger `C-perp`
class and therefore cover the triple-vanishing tests. It is stronger than the
final required test-class sign, but its scalar margin is not the tiny full Weil
margin seen in the second column.

## 5. Rejected Soft Poincare Bound

For mean-zero functions, monotonicity of `J` gives

```text
(1/2) integral integral J|v(x)-v(y)|^2
  >= 2a J(2a)||v||^2.
```

At `x=0`, the bounded remainder has the closed form

```text
m_1(0)
 = log(4/a)+pi/2
   -log((1+exp(-a/2))/(1-exp(-a/2)))
   -2 atan(exp(-a/2)).
```

Arb certifies that the sufficient margin `2aJ(2a)+kappa_a(0)` is negative:

```text
+-----+-----------------------+
| c   | soft margin           |
+-----+-----------------------+
| 5   | -2.80689362347...     |
| 13  | -4.76495279058...     |
| 29  | -7.39183029704...     |
| 53  | -9.19095487586...     |
| 100 | -10.7191709340...     |
+-----+-----------------------+
```

This rejects only the minimum-kernel plus pointwise-potential proof. A sharper
weighted inequality using the full jump geometry is still logically possible.

## 6. Remaining Analytic Gate

Let

```text
u_0 = A_tilde^-1 C.
```

A sufficient lower theorem is

```text
u_0(x)<0 almost everywhere,
```

because `C>0` then gives `G(0)=<C,u_0><0`.

The ordinary maximum principle applies below the ground eigenvalue, not at
zero between the negative ground and the first positive spectral level.
Perron positivity alone is insufficient: a two-dimensional symmetric
Z-matrix can have a positive ground vector while its restriction to the
orthogonal complement of another positive vector remains negative.

The source's stronger missing nodal identity controls
`(A_tilde-lambda)^-1 C` across the entire first gap. This route asks first for
the single energy `lambda=0`. A valid proof may use a nonlocal anti-maximum
principle or the screw/Krein-string realization, but it must verify all of that
theorem's hypotheses for this exact operator. It may not assume one negative
eigenvalue, the sign of `G(0)`, or positivity of the full Weil update.

## 7. Reproduction

```text
python3 -B docs/proofs/061_polefree_poincare_probe.py --prec 768

python3 -B docs/proofs/062_polefree_constraint_resolvent_probe.py \
  --upstream anc/arb_ldlt_certify.py \
  --component-probe docs/proofs/043_cutoff_free_weil_spectrum_probe.py \
  --triple-probe docs/proofs/053_triple_vanishing_weil_probe.py \
  --c 13 --N 8 --prec 3072
```

## 8. Route Judgment

```text
source pole-free form identity: accepted
source positivity-improving ground state: accepted
soft mean-zero Poincare bound: rejected
finite pole-neutral compression: Arb-positive in tested cases
finite G(0)<0: Arb-certified with stable sign margin
continuum Morse index one: unproved
continuum zero-energy anti-maximum sign: unproved
route status: rejected as an executable lower producer; see 064
new Lean owner: none
unconditional RH: unproved
```
