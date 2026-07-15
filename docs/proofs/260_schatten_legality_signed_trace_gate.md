# Proof 260: Schatten legality versus signed trace cancellation

Date: 2026-07-15

Status: rejects a uniformly bounded two-Hilbert--Schmidt factorization as the
estimator for Proof 257's complete three-branch flow.  A completed finite
half-line crossing does have a canonical factorization through its crossing
interval, and both root-dressed factors are Hilbert--Schmidt.  That
factorization proves ordinary trace legality.  Its optimal factor-norm product,
however, is the trace norm of the smoothed crossing.  This remains
`|I| norm(g)_2^2` even when compact root support makes the scalar trace exactly
zero.

Therefore a positive Hilbert-space norm cannot retain the support and sign
cancellation required by the route.  A branch direct sum is legal for finite
truncations but replaces all three cancellations by total variation.  Current
Proofs 228--234 prove only operator-norm compactness for part of the full Euler
boundary series, so they do not establish a common two-Hilbert--Schmidt
factorization of the complete fixed-`S` flow either.

Gate 3 must be split.  Proof 261 now proves ordinary trace-class legality of
the fully recombined, root-sandwiched fixed-`S` operator.  The active Gate 3U
must estimate its signed scalar trace through Proof 253's `D_E-D_R` formula or
Proof 257's complete three-branch formula, using compact support before any
absolute value.  No Lean owner or route rewire is authorized, and RH remains
unproved.

## 1. Result first

```text
+------------------------------------------------+------------------------------+
| object                                         | judgment                     |
+------------------------------------------------+------------------------------+
| one completed finite crossing                  | canonical S2 x S2 factor     |
| ordinary trace of that crossing                | legal                        |
| factor-norm product                            | exact nuclear mass           |
| compact-support scalar cancellation            | invisible to nuclear mass    |
| finite branch direct sum                       | legal, loses cancellation    |
| full fixed-S synchronized flow in S1           | closed by Proof 261          |
| uniform estimate by S2 Holder                  | rejected                     |
| signed D_E-D_R / three-branch scalar estimate  | active quantitative bottom   |
| same-object finite-S trace identity            | open                         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

The corrected ownership diagram is

```text
completed boundary crossing
        |
        +-- S2 x S2 factorization -> ordinary trace legality
        |
        X  factor norms do not see trace cancellation
        |
        v
fully recombined signed scalar trace
        |
        +-- root support first
        +-- D_E-D_R or complete three-branch difference
        +-- absolute value last.                                  (W.1)
```

## 2. Exact factorization of one crossing

Work on `H=L2(R)`.  Fix the conventions

```text
(U_b f)(x)=f(x+b),
(C_g f)(x)=integral_R g(x-y)f(y)dy,
E_I=M_(1_I),                                          (W.2)
```

where `I` is a finite interval and
`g in C_c^infinity(R)` is nonzero.  The convolution and translation commute.
Put

```text
Y_(I,b)=U_b E_I,
K_(I,b,g)=C_g Y_(I,b) C_g*
          =U_b C_g E_I C_g*.                         (W.3)
```

Let `i_I:L2(I)->L2(R)` be zero extension and
`r_I=i_I*` restriction.  Then

```text
Y_(I,b)=(U_b i_I) r_I.                               (W.4)
```

After the roots are attached, `(W.4)` becomes

```text
K_(I,b,g)
 =(C_g U_b i_I)(r_I C_g*).                           (W.5)
```

Both factors are Hilbert--Schmidt.  Their kernels give the exact equalities

```text
norm(C_g U_b i_I)_2^2=|I| norm(g)_2^2,
norm(r_I C_g*)_2^2  =|I| norm(g)_2^2.                (W.6)
```

For the actual half-line commutator, `|I|=|b|`; translating the interval only
changes the location of the boundary.  Equation `(W.5)` is the continuous
version of the finite-interval factors used in Proofs 196 and 201.

Thus the answer to the first part of Proof 259's contract is positive for one
completed crossing: it has two legal Hilbert--Schmidt factors.  The issue is
what their norms measure.

## 3. Trace zero, optimal factor cost positive

Define the autocorrelation

```text
F_g(b)=integral_R g(x+b) conjugate(g(x)) dx.          (W.7)
```

The diagonal kernel in `(W.3)` gives

```text
Tr(K_(I,b,g))=|I| F_g(b).                             (W.8)
```

There is simultaneously an exact trace-norm formula.  Set

```text
S_I=C_g E_I,
A_I=S_I S_I*=C_g E_I C_g*.                           (W.9)
```

The operator `A_I` is positive trace class, and left multiplication by the
unitary `U_b` preserves singular values.  Therefore

```text
norm(K_(I,b,g))_1
 =norm(A_I)_1
 =Tr(A_I)
 =norm(S_I)_2^2
 =|I| norm(g)_2^2.                                  (W.10)
```

If `supp(g) subset [-B,B]` and `|b|>2B`, then

```text
F_g(b)=0,
Tr(K_(I,b,g))=0,
norm(K_(I,b,g))_1=|I| norm(g)_2^2>0.                 (W.11)
```

For every factorization `K_(I,b,g)=A B` with `A,B in S2`, Schatten Holder
implies

```text
norm(A)_2 norm(B)_2
 >=norm(K_(I,b,g))_1
 =|I| norm(g)_2^2.                                  (W.12)
```

The canonical factors in `(W.5)` attain equality in `(W.12)`.  Hence this is
not a poor choice of crossing space.  It is the best possible positive
Hilbert-factor cost, and it is still strictly positive when the route scalar
is exactly zero.

This is the decisive obstruction.  Root support cancels the diagonal pairing,
not the singular values of the operator.

## 4. Why a branch direct sum cannot repair it

Suppose a finite crossing ledger is

```text
Y=sum_j c_j L_j R_j.                                 (W.13)
```

The standard common crossing space is

```text
mathcalK=directSum_j mathcalK_j.                      (W.14)
```

Splitting `|c_j|` equally between the row and column factors gives

```text
norm(C_g mathcalL)_2^2
 =sum_j |c_j| norm(C_g L_j)_2^2,

norm(mathcalR C_g*)_2^2
 =sum_j |c_j| norm(R_j C_g*)_2^2.                    (W.15)
```

Every sign and phase in `c_j` disappears from `(W.15)`.  For translated
half-line crossings, the right side charges

```text
sum_j |c_j| |I_j| norm(g)_2^2.                       (W.16)
```

This proves legality whenever `(W.16)` is finite.  It cannot see that
`F_g(b_j)=0`, that Proof 258's two leakage branches cancel, or that Proof 253's
`D_E-D_R` difference is small.

A nonorthogonal factorization could encode operator-level cancellation before
the norm.  It still cannot beat `(W.12)` for the resulting root-sandwiched
operator.  To gain a small Hilbert-factor product, one must prove cancellation
of the full trace norm, not only of the scalar trace.  None of Proofs 253 or
257--259 proves such a nuclear cancellation.

A Krein or signed direct sum retains the algebraic signs, but its associated
positive Hilbert majorant is again `(W.15)`.  Renaming the signature does not
produce an ordinary trace-class estimate.

## 5. Compactness plus zero diagonal still does not give trace class

The gap is not merely logical.  The same compact-root crossing geometry gives
an exact family with every scalar trace zero and a compact operator-norm sum
which is not trace class.

Choose `g in C_c^infinity([-B,B])`, `g!=0`, and

```text
b_n=2^n b_0,
b_0>2B.                                               (W.17)
```

Choose intervals `I_n` of length `b_n`, placed far enough apart that the
root-enlarged input supports and their `b_n`-translated output supports are
pairwise disjoint.  Define

```text
K_n=b_n^(-1) U_(b_n) C_g E_(I_n) C_g*.               (W.18)
```

Equations `(W.8)--(W.10)` give

```text
Tr(K_n)=0,
norm(K_n)_1=norm(g)_2^2,
norm(K_n)<=b_n^(-1) norm(C_g)^2 ->0.                 (W.19)
```

The separated supports make the initial spaces mutually orthogonal and the
final spaces mutually orthogonal.  The series

```text
K=sum_n K_n                                             (W.20)
```

converges in operator norm to a compact operator.  Its singular values are the
union of the singular values of the blocks, so

```text
norm(K)_1=sum_n norm(K_n)_1=infinity.                 (W.21)
```

Every block has zero trace, and its diagonal kernel is identically zero, yet
the sum has no ordinary trace.  Consequently

```text
compact + modewise trace cancellation
  does not imply S1
  does not imply an S2 x S2 factorization.             (W.22)
```

This is a guard against an abstract inference.  It does not prove that the
actual synchronized Euler operator is not trace class; its branches could
have additional operator-level cancellation.  Such cancellation now has to
be proved, not inferred from compactness or the scalar support rule.

## 6. Existing project results stop below the new legality gate

Proofs 228--229 establish for the critical positive-frequency boundary

```text
termwise Hilbert--Schmidt norms:  nondecaying,
termwise operator norms:          summable after chirp gain.               (W.23)
```

Proof 234 consequently claims compactness of the complete metric correction,
not a global Hilbert--Schmidt or trace-class result.  Its nonlinear
two-crossing part is Hilbert--Schmidt, while the linear boundary series is only
operator-norm summable.

These facts are enough for compactness and insufficient for Proof 259's
proposed common factorization.  In particular,

```text
operator-norm convergence of compact boundary terms
  != trace-norm convergence
  != one common pair of Hilbert--Schmidt factors.       (W.24)
```

The static endpoint product `B W R L` in Proof 257 remains trace legal for
each fixed finite `S` because `B W R` is already trace class and `L` is
bounded.  That result does not establish trace-class legality of the complete
synchronized flow `C_eta B_t' C_xi*`.

## 7. Hankel and Besov source audit

Peller's current survey states the sharp standard criterion for the relevant
Hardy commutators:

```text
V. V. Peller, Besov spaces in operator theory
https://arxiv.org/abs/2402.09853

Sections 5.2--5.3:
  [M_phi,P_+] belongs to S_p
  if and only if phi belongs to B_p^(1/p).

At p=1:
  trace class requires the B_1^1 symbol condition.      (W.25)
```

This can certify fixed-symbol legality after the fully reduced source symbol
has actually been shown to lie in `B_1^1`.  It does not provide that source
reduction, and its positive Besov norm is not a signed trace estimate.
Frequency modulation is charged by the Besov norm even when `(W.8)` vanishes
by compact support.

CC20's Appendix D theorem is consistent with `(W.25)`: a Schwartz multiplier
has an infinitely smoothing half-line commutator.  It does not state an
`S`-uniform trace-class theorem for the full CCM24 Euler generator, the moving
Sonin metric, and the prolate correction after they are recombined.

No Kato, restricted-Grassmannian, Hankel, or Besov theorem found in the source
audit converts scalar trace cancellation into a small trace norm.

## 8. Corrected Gate 3 contract

Proof 259 combined two different obligations.  They must now remain separate.

### Gate 3L: ordinary trace legality

For every fixed finite `S`, path time `t`, and selected roots `eta,xi`, prove

```text
C_eta (Y_(S,t)+Y_(S,t)*) C_xi* in S1,                (W.26)
```

for the actual same-object flow

```text
Y_(S,t)
 =(I-E_(S,t))X_(S,t)B_(S,t)
   -R_(S,t)X_(S,t)*Q B_(S,t).                        (W.27)
```

The proof may use a source-owned nuclear kernel, a convergent trace-norm
expansion after exact recombination, or a verified `B_1^1` Hankel symbol.  It
must include the outer boundary, second boundary, and base prolate branch.
No uniform factor-norm estimate is required at this gate.

Proof 261 closes `(W.26)` by passing CC20's trace-class root commutator through
the compressed metric inverse and pulling the current crossing back to the
base half-line/Sonin crossing.  Gate 3L is no longer active.

### Gate 3U: uniform signed scalar bound

After `(W.26)` makes cyclicity and the ordinary trace legitimate, identify the
same trace with either

```text
D_(E_(S,t))(w,h_(S,t))-D_(R_(S,t))(w,h_(S,t))        (W.28)
```

from Proof 253 or Proof 257's complete physical-boundary expression.  Prove

```text
abs(integral_0^1 signedCompleteTrace_(S,t) dt)
 <=C (1+B)^d norm(g)_(H^r)^2,                        (W.29)
```

with `C,d,r` independent of the visible finite set.  Compact root support must
be used before the prime, Markov, Sonin, or prolate pieces are put under an
absolute value.

Do not use

```text
norm(C_eta L_(S,t))_2 norm(R_(S,t) C_xi*)_2          (W.30)
```

as the estimator for `(W.29)`.  Equation `(W.11)` proves that even the optimal
value of `(W.30)` can stay positive and grow linearly while the target scalar
is exactly zero.

## 9. Reproducible certificate

Run from the Windows source snapshot in WSL2:

```text
OPENBLAS_NUM_THREADS=4 python3 -B \
  docs/proofs/260_schatten_legality_signed_trace_gate_probe.py
```

The single-crossing certificate reports

```text
+--------------------------------------+---------------+
| check                                | value         |
+--------------------------------------+---------------+
| factorization error                  | 0             |
| root autocorrelation                 | 0             |
| scalar trace                         | 0             |
| trace norm                           | 40            |
| product of canonical S2 norms        | 40            |
+--------------------------------------+---------------+
```

The four-block ledger has widths `16,32,64,128` and coefficients `1/width`.
Every scalar trace is zero, every trace norm is one, and the operator norms
decrease from `0.539` to `0.0807`.  The cumulative trace norm is four.  The
maximum checked algebra error is `2.31e-15`.

The finite model verifies the factor and norm identities.  Equations
`(W.17)--(W.21)` are the continuous compact-not-trace-class construction.

## 10. Route judgment

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| finite crossing interval factorization         | exact S2 x S2                |
| fixed finite crossing trace legality           | exact                        |
| root-support trace cutoff                      | exact                        |
| nuclear mass under the same cutoff             | remains positive             |
| direct-sum three-branch factorization          | legal, total variation       |
| compact => trace class inference               | rejected by exact guard      |
| full fixed-S synchronized flow in S1           | closed by Proof 261          |
| uniform two-HS factor-norm estimator           | rejected                     |
| uniform signed scalar estimate                 | open, Gate 3U                |
| negative-owner integrated smallness            | open                         |
| same-object finite-S trace identity            | open                         |
| Burnol all-zero identity                       | open                         |
| Lean owner or route rewire                     | none                         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

Proof 259 was correct to reject the Kato leakage and the infinite-frame
factorization.  Its proposed successor was still too strong: one common
positive Hilbert factor norm cannot be both the legality certificate and the
cancellation-sensitive uniform estimate.  Proof 260 retains two-Hilbert--
Schmidt factors as a legality tool and removes them as the quantitative route
owner.
