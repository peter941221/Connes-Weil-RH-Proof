# Proof 331: relative principal-function localization audit

Date: 2026-07-17

Status: corrected analytic route audit after Proof 330. The audit does not
close Gate 3U. It identifies a valid distributional derivative transfer and
rejects a proposed almost-periodic principal-function owner: principal-function
theory controls the antisymmetric commutator, whereas Gate 3U is the symmetric
semicommutator response. No stored route premise or finite-section surrogate is
introduced.

## 1. Result

```text
+--------------------------------------------------+---------------------------+
| layer                                            | judgment                  |
+--------------------------------------------------+---------------------------+
| Proof 330 moving three-branch pullback           | exact operator identity   |
| Q transfer from source distribution to root      | valid distributionally    |
| compact support after Q transfer                 | preserved                 |
| static CC20 half-power tail                      | reusable                  |
| static tail controls compressed Toeplitz term    | false / already guarded   |
| Hardy almost-periodic principal function         | wrong symmetry for Gate 3U|
| relative Sonin E/R semicommutator distribution   | not constructed           |
| uniform total variation independent of S         | not proved                |
| Gate 3U                                          | open                      |
+--------------------------------------------------+---------------------------+
```

The corrected candidate ownership chain is

```text
actual moving E/R/K_prol response
  -> relative detector-first Toeplitz cocycle
  -> relative symmetric semicommutator distribution
  -> apply compact support to that signed distribution
  -> only then expose the almost-periodic Euler frequencies
  -> uniform-in-S scalar bound.                         (BO.1)
```

Only the first arrow has an operator-level owner in the repository. The second
arrow is the new missing theorem. A Helton--Howe principal function cannot
supply it because it sees the opposite symmetry.

## 2. A valid residue-first derivative transfer

Let

```text
Q=-partial_z^2+1/4
```

be the logarithmic root differential used by the CC20 source. If `d` is the
pre-Q source distribution and `F_z` is a translated compact cross-correlation,
distributional self-adjointness gives

```text
<Q d,F_z>=<d,Q F_z>.                                  (BO.2)
```

This is the correct way to use Proof 302's split

```text
Q d=-2 Dirac_0+q_reg.                                 (BO.3)
```

It does not delete the Dirac residue. The residue is retained automatically in
the left side of `(BO.2)`. On the right side, differentiation does not enlarge
the support of `F_z`. Therefore the already source-backed pre-Q estimate

```text
|d(exp z)|<=C (1+z) exp(-z/2)                         (BO.4)
```

can control the static translated pairing by Sobolev norms of the compact
root. This avoids the false pointwise estimate for `q_reg` rejected by Proof
302.

Equation `(BO.2)` is useful but insufficient for Gate 3U. Proof 277 decomposes
the Sonin Toeplitz covariance as

```text
Tr(T_(w h)^R)-Tr(T_w^R T_h^R).                        (BO.5)
```

The CC20 static coefficient controls the first trace only. The compressed
product in the second trace is independent data; the positive three-point
guard in Proof 277 proves that a zero first trace can coexist with a nonzero
covariance. Thus `(BO.2)` cannot be substituted for the complete moving
five-branch scalar.

## 3. Principal-function symmetry obstruction

Let `P` be an orthogonal projection and let `W,H` be commuting self-adjoint
multipliers. Set

```text
C=P W(I-P)H P.                                       (BO.5a)
```

The Toeplitz commutator and the completed orthogonal-flow crossing are

```text
[T_W,T_H]=C^dagger-C,                                (BO.5b)
D_P(W,H)=C+C^dagger.                                 (BO.5c)
```

Thus Helton--Howe/Carey--Pincus principal functions control the
antisymmetric, imaginary part `C^dagger-C`. Gate 3U uses the symmetric, real
part `C+C^dagger`. In particular, a principal-function measure can vanish
while the Gate 3U scalar remains nonzero. The proposed principal-function
ownership arrow in the original audit was therefore invalid.

## 4. What the almost-periodic literature still says

Carey and Pincus construct, in a type-II-infinity von Neumann algebra, a
Toeplitz operator associated to an analytic almost-periodic function and relate
its principal function to the Jensen function and mean motion of the
corresponding Dirichlet series:

```text
R. W. Carey and J. D. Pincus,
Mean motion, principal functions, and the zeros of Dirichlet series,
Integral Equations and Operator Theory 2 (1979), 484--502.
https://doi.org/10.1007/BF01691074
```

This remains relevant background because the normalized finite Euler product
is an analytic almost-periodic symbol with frequencies `m log p`, but the
principal-function trace formula retains only the antisymmetric commutator
response. It does not own the symmetric Gate 3U scalar.

Sugahara gives a recent explicit Helton--Howe measure for almost-normal Hardy
Toeplitz operators in terms of signed multiplicity of the harmonic extension:

```text
Y. Sugahara,
The Helton--Howe measure of almost normal Toeplitz operators,
arXiv:2602.07504v1.
https://arxiv.org/abs/2602.07504
```

These results do not close the route for two independent reasons. Their owner
is one Hardy Toeplitz projection, while Gate 3U uses the relative determinant
line of the nested source pair `R<=E`, with

```text
R=E Q E-K_prol,                                      (BO.6)
```

and with the Gram-corrected projection moving with the Euler product. More
fundamentally, their trace formula has the antisymmetric sign `(BO.5b)`, not
the symmetric sign `(BO.5c)`. No cited theorem constructs the required
relative symmetric semicommutator distribution or bounds it independently of
`S`.

## 5. The exact missing theorem

The required producer is not a principal function or a generic trace-norm
estimate. It must construct a signed distribution `nu_(S,E/R)` for the actual
symmetric semicommutator such that

```text
movingFiveBranchScalar(S,eta,xi)
  =<F_(eta,xi),nu_(S,E/R)>,                           (BO.7)

supp(F_(eta,xi)) subset [-2 B_root,2 B_root],         (BO.8)

localized norm of nu_(S,E/R) on [-2 B_root,2 B_root]
  <=C (1+B_root)^d,                                   (BO.9)
```

where `C,d` are independent of the visible finite set `S`. The construction
must identify `(BO.7)` with the actual Gram-corrected moving projection, not a
static Euler-product cocycle.

After `(BO.7)--(BO.9)`, the uniform signed bound follows immediately:

```text
|movingFiveBranchScalar(S,eta,xi)|
  <=C (1+B_root)^d
    norm(eta)_(H^r) norm(xi)_(H^r).                  (BO.10)
```

The standard Helton--Howe total-variation estimate

```text
2 norm(mu_T)<=norm([T*,T])_1                         (BO.11)
```

does not prove `(BO.9)`: its measure represents `(BO.5b)`, not `(BO.5c)`.
Even as an unrelated majorant, applying it before the relative `E/R`
cancellation gives the same `S`-dependent trace-norm bound rejected by Proofs
260, 273, 288, and 289.

## 6. Relation to Proof 330

Proof 330 proves

```text
actual moving crossing
  =bounded moving dressings
     * fixed-source three-branch generator ledger.   (BO.12)
```

This closes the operator ownership needed before `(BO.7)`, but bounded
dressings do not preserve compact root support in a form that permits a
branchwise estimate. The semicommutator distribution must therefore be
relative and detector-first, as in Proof 280, rather than a bounded-sandwich
trace-norm argument.

## 7. Reproduction

The existing same-object diagnostics were rerun in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/301_support_first_two_point_cocycle_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/289_complete_prime_markov_telescope_probe.py
```

They report respectively

```text
combined_kernel_strip_estimate=OPEN,
static_product_substitution_gap=8.901014675657e-01,

global_renewal_boundary_bound=OPEN,
global_defect_operator_norm=9.999940664447e-01.
```

The exact algebra errors remain below `6.1e-16`. These diagnostics support the
ownership guards; they are not continuous estimates.

## 8. Route judgment

The derivative-transfer idea repairs an invalid post-Q pointwise argument but
does not control the compressed Sonin Toeplitz product. The principal-function
route is rejected because it controls `C^dagger-C`, whereas Gate 3U requires
`C+C^dagger`. The viable successor must instead derive a relative symmetric
semicommutator distribution directly from the actual compressed-metric kernels
or from the relative Fredholm cocycle's mixed second variation.

Do not add `(BO.9)` as a premise, do not replace `R` by the Hardy projection,
and do not use `(BO.11)` before the outer/Sonin/prolate cancellation. Gate 3U,
the finite-S sign, negative-owner integration, Burnol's identity, and RH remain
open.
