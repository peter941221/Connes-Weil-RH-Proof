# Pole-Free Anti-Maximum Rejection

Date: 2026-07-12

Status: the pole-free constraint candidate is rejected as an executable lower
RH route. Its finite scalar `G(0)<0` is robust and useful diagnostic evidence,
but the corresponding continuum statement is the positivity of the
pole-neutral Weil form. The checked source properties do not imply it, the
inverse-Neumann/Krein reformulation does not localize the operator, and the
available anti-maximum principles apply only near a principal spectral pole.
No independent lower producer or Lean owner remains.

## 1. Candidate Being Audited

The candidate from `063_polefree_constraint_survivor.md` was

```text
A_tilde = A_a-W_(0,2),
C(x)=cosh(x/2),
G(0)=<C,A_tilde^-1 C>,

MorseIndex(A_tilde|even)=1 and G(0)<0
  -> A_tilde>=0 on C-perp
  -> triple-vanishing Weil positivity
  -> RH.
```

Arb finite sections support the two premises. That does not make either one a
source theorem.

## 2. Exact Finite-Dimensional Countermodel To The Soft Logic

Consider

```text
A = [[-4,-1],[-1,1]],
C = [1,1]^T.
```

This matrix has all of the abstract properties available from the checked
pole-free source:

```text
off-diagonal entry is strictly negative;
A = [[1,-1],[-1,1]] + diag(-5,0),
so it is an irreducible graph Dirichlet form plus bounded potential;
eigenvalues are (-3-sqrt(29))/2 < 0 < (-3+sqrt(29))/2;
the negative eigenvalue is simple and its eigenvector is strictly positive;
C is strictly positive.
```

Nevertheless,

```text
A^-1 C = [-2/5,3/5]^T,
<C,A^-1 C> = 1/5 > 0.
```

For the generator of `C-perp`, take `v=(1,-1)`. Then

```text
<C,v>=0,
v^T A v=-1<0.
```

Therefore even the additional Morse-index-one premise, combined with the
Dirichlet/Perron structure and `C>0`, does not imply pole-neutral positivity or
the zero-energy anti-maximum sign. A new arithmetic/operator identity is
essential.

## 3. Why The Krein-String Reformulation Does Not Supply It

Suzuki Section 8 introduces

```text
K_a=(-Delta_N)^-1,
S_a=G_a-lambda K_a,
```

and rewrites the spectral problem as

```text
G_a u=lambda K_a u,
u in L2_0(-a,a).
```

This is a generalized eigenvalue problem for two compact integral operators.
The inverse Neumann kernel is explicit, but `G_a` remains the full screw
convolution kernel. Applying `-Delta_N` does not turn the truncated convolution
and its boundary terms into a local Sturm--Liouville equation.

Most decisively, the source's zero-energy specialization states:

```text
Assume RH. Then G_a>0, so one may take lambda=0.
```

Source: arXiv:2606.09096, `screwzelf_7.tex`, Section 8, subsection
"The Hilbert Space H(S_a)". Importing that `lambda=0` Hilbert-space picture as
an unconditional sign proof would assume the desired conclusion.

## 4. Why Abstract Anti-Maximum Theory Does Not Apply

Individual anti-maximum principles for positive/eventually positive
resolvents control `R(lambda,A)f` in a one-sided neighbourhood of a principal
spectral pole. Their hypotheses require a strongly positive spectral
projection at that pole, together with domain/order assumptions.

For `A_tilde`, zero lies between the negative Perron eigenvalue and the first
positive level. It is not a neighbourhood point on the required side of the
negative principal pole. Using the first positive pole instead does not help:
its eigenprojection is not strongly positive. Extending an anti-maximum sign
from the principal pole all the way to zero is precisely the missing no-node
statement for `(A_tilde-lambda)^-1 C`.

Primary comparison:

```text
Arora--Gluck, Criteria for eventual domination of operator semigroups and
resolvents, arXiv:2204.00146, Section 2.
```

## 5. Logical Level Of The Remaining Scalar

On the index-one/invertible domain,

```text
G(0)<=0
  <-> A_tilde is nonnegative on C-perp.
```

The CC20 triple-vanishing square roots lie in `C-perp`. Yoshida detectors show
that positivity on that test class excludes every off-critical zeta zero.
Thus a uniform continuum proof of the scalar sign, without a genuinely lower
identity, is an RH-closing sign theorem rather than a lower producer.

The numerical distinction

```text
G(0) approximately -1/2,
1+2G(0) extremely close to zero
```

is valuable for choosing estimates, but it does not change this logical
dependency.

## 6. Verdict

```text
finite pole-free index pattern: retained as diagnostic evidence
finite G(0)<0: retained as diagnostic evidence
Dirichlet/Perron/index-one abstract implication: false by exact countermodel
inverse-Neumann localization: rejected; G_a remains nonlocal
zero-energy use of Suzuki H(S_a): conditional on RH
abstract anti-maximum theorem at lambda=0: hypotheses fail
continuum G(0)<0 as root: RH-level / not a lower producer
new Lean owner: none
unconditional RH: unproved
```

Sources:

```text
https://arxiv.org/abs/2606.09096
https://zenodo.org/records/20682834
https://arxiv.org/abs/2204.00146
docs/proofs/063_polefree_constraint_survivor.md
```
