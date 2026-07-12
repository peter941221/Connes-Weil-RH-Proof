# Plan 020 M4 First Mathematical Verdict

Date: 2026-07-11

Verdict: **rejected as an executable RH route; M4 itself is not disproved.** The
explicit `mu(k)/k` direction survives finite tests, but every structural attack
leaves the inverse of the growing optimal Gram matrix. The final CUDA rejection
run reaches `N=4096` and shows large dyadic oscillation with descending low
subscales. No unconditional lower producer for the required coupled ratio was
found, while the source-grade matching Mobius asymptotic assumes RH and an
additional zero-derivative moment bound.

## 1. Exact Inner Products

For

```text
gamma(n)   = 1,
gamma_k(n) = {n/k},
<a,b>      = sum_(n>=1) a(n)b(n)/(n(n+1)),
```

direct summation gives

```text
<gamma,gamma_k> = log(k)/k.                              (M4.2)
```

For `L=lcm(j,k)`, group the sequence by `n=qL+r`, `1<=r<=L`. The residue
product is constant in each class, and

```text
sum_(q>=0) 1/((qL+r)(qL+r+1))
  = (psi((r+1)/L)-psi(r/L))/L.
```

Therefore

```text
<gamma_j,gamma_k>
  = (1/L) sum_(r=1)^L {r/j}{r/k}
      * (psi((r+1)/L)-psi(r/L)).                         (M4.3)
```

This is a finite formula. `scratch_nyman_block.py --exact` implements it with
a positive-real digamma recurrence and asymptotic expansion. Through `N=32`,
the normalized certificate from (M4.3) differs from the two-million-term
calculation by approximately `1e-5` or less:

```text
+------+----------------------+----------------------+
| N    | exact mu/k * log(N)  | cutoff 2e6 result    |
+------+----------------------+----------------------+
| 8    | 0.3484               | 0.3484               |
| 16   | 0.4263               | 0.4263               |
| 32   | 0.5779               | 0.5779               |
+------+----------------------+----------------------+
```

Thus the original tail truncation is not the observed positive margin's
mechanism.

## 2. Correlation And Projected Energy

Let `r_N=gamma-P_N gamma`, `b_N=sum_(N<k<=2N) mu(k)gamma_k/k`, and
`w_N=(I-P_N)b_N`. Since `r_N` is orthogonal to `V_N`,

```text
<r_N,w_N> = <r_N,b_N>.                                  (M4.4)
```

This removes the Schur complement from the numerator, but not the old optimal
projection. In finite coordinates, with old Gram matrix `G_N`, old target
vector `t_N`, cross block `C_N`, and block coefficient vector `a_N`,

```text
<r_N,b_N>
  = a_N^T (t_block - C_N^T G_N^-1 t_N),                 (M4.5)

||w_N||^2
  = a_N^T (B_N - C_N^T G_N^-1 C_N) a_N.                (M4.6)
```

The finite Mobius identity can simplify entries of `a_N`-weighted sums, but it
does not remove `G_N^-1`. A proof of the uniform lower bound must control the
orientation of the explicit block vector against the current optimal residual,
not merely estimate an unprojected Mobius sum.

The decomposed experiment has the same negative sign for the correlation at
every tested scale `N=8,...,128`. Both its magnitude and projected energy
decrease, leaving a stable normalized quotient. No sign flip or near-zero
correlation was found.

## 3. Larger-Scale Rejection Test

WSL2, cutoff `250000`, scalar omitted weight mass `4e-6`:

```text
+------+----------------------+----------------------+
| N    | best block * log(N)  | mu/k cert * log(N)   |
+------+----------------------+----------------------+
| 64   | 0.6287               | 0.5544               |
| 128  | 0.7170               | 0.6166               |
| 256  | 0.5725               | 0.4140               |
| 512  | 0.7285               | 0.5802               |
+------+----------------------+----------------------+
```

The dip at `N=256` does not continue at `N=512`. There is no numerical evidence
through this range that the normalized certificate tends to zero. This is only
a rejection test; ill-conditioning and finite cutoff prohibit extrapolating a
uniform positive infimum.

## 4. Known Natural-Mobius Divergence Does Not Decide This Block Route

Báez-Duarte proves that several direct natural Mobius approximations diverge
in `L2`, including the partial sums `S_n` and `V_n`. The lower barriers contain
`sqrt(n)|g(n)|` and `|M(n)+2|/sqrt(n)`. He also proves that no fixed coefficient
series of the stated natural form converges to the target in `L2`.

Source:

```text
Luis Baez-Duarte, Arithmetical Aspects of Beurling's Real Variable
Reformulation of the Riemann Hypothesis, arXiv:math/0011254,
Propositions 4.4--4.7.
https://arxiv.org/abs/math/0011254
```

Plan 020 is not one of those series. At every scale it first removes the old
span by `(I-P_N)` and uses the new block only to improve the current optimal
residual. Its coefficients therefore change implicitly through `P_N`. The
published divergence theorem is a mandatory warning against dropping the
projection, but it is not a counterexample to (M4.1).

## 5. Gate Decision

```text
+--------------------------------------+------------------------------+
| M4 first check                       | result                       |
+--------------------------------------+------------------------------+
| exact target inner product           | passed: (M4.2)               |
| exact finite Gram formula            | passed: (M4.3)               |
| truncation-artifact rejection        | passed through N=32          |
| normalized capture collapse          | not observed through N=512   |
| known natural-series divergence      | does not apply after P_N     |
| uniform c/log(N) lower bound         | unproved                     |
| lower arithmetic producer            | absent; G_N^-1 remains       |
+--------------------------------------+------------------------------+
```

First-round decision, superseded by Section 11:

```text
Plan 020 status at N <= 512: active but unresolved.
M4 status at N <= 512: partial, not passed and not rejected.
RH status: still conditional; no Lean root was removed or lowered.
```

The next attack was structural rather than larger floating-point
experiments: find a basis or biorthogonal system that makes `G_N^-1` explicit
enough to sign (M4.5), or prove that the normalized correlations have zero
infimum. Without one of those results, the route has no guaranteed closure.

## 6. Vasyunin Biorthogonal Audit

Vasyunin gives an explicit biorthogonal family for the same discrete functions.
In the weighted sequence model define `phi_k` by its two nonzero coordinates

```text
phi_k(k-1) = -k(k-1),
phi_k(k)   =  k(k+1),
```

and set

```text
f_n = sum_(k|n) mu(n/k) phi_k.
```

Then

```text
<h,phi_k> = h(k)-h(k-1),
<gamma_m,f_n> = delta_(m,n).                             (M4.7)
```

This is Vasyunin's Theorem 7. Its direct verification is just the divisor
identity for `mu`. The implementation checks (M4.7) for `2<=m,n<=20` with
maximum floating error `2.8e-16`.

Source:

```text
V. I. Vasyunin, On a biorthogonal system associated with the Riemann
hypothesis, St. Petersburg Math. J. 7 (1996), 405--419, Theorem 7.
Russian original, pp. 131--132:
https://www.mathnet.ru/php/getFT.phtml?jrnid=aa&paperid=557&what=fullt&option_lang=eng

English restatement and proof:
Bellemare--Langlois--Ransford, arXiv:2011.02847, Theorem 13.
https://arxiv.org/abs/2011.02847
```

This does **not** give an explicit finite Gram inverse. The finite canonical
dual to `gamma_n` inside `V_N` is `P_N f_n`, and its coordinates in the
`gamma_2,...,gamma_N` basis are exactly a row of `G_N^-1`. The component
`f_n-P_N f_n` is generally substantial. In the exact `N=64` calculation:

```text
+------+------------------------+
| n    | ||P_64 f_n||^2/||f_n||^2 |
+------+------------------------+
| 10   | 0.5981                 |
| 20   | 0.4751                 |
| 40   | 0.2565                 |
| 64   | 0.1478                 |
+------+------------------------+
```

Thus replacing `P_N f_n` by the explicit `f_n` discards most of the relevant
finite dual at the high end. This rejects the Vasyunin-direct-inversion subroute.

The adjacent Cholesky positivity approach also does not close M4. The published
positivity conjecture concerns entries `L_kj=<gamma_k,e_j>` after Gram--Schmidt
and remains unproved. More importantly, the target coordinates
`E_j=<gamma,e_j>` already have mixed signs: exact `N=128` computation gives 65
positive and 62 negative coordinates. Therefore even a proof `L_kj>0` leaves
the correlation as an uncontrolled signed sum.

Source for the conjecture and its status:

```text
Bellemare--Langlois--Ransford, arXiv:2011.02847,
Conjecture 9 and discussion after it.
```

## 7. Tail Localization Identity

Let

```text
S_N = sum_(N<k<=2N) mu(k)/k^2.
```

For every `m<N`, `gamma_k(m)=m/k` for `N<k<=2N`, and
`gamma_N(m)=m/N`. Hence

```text
b_N - N*S_N*gamma_N
```

vanishes identically in the first `N-1` sequence coordinates. Since
`gamma_N` belongs to the old space,

```text
w_N = (I-P_N)(b_N-N*S_N*gamma_N).                       (M4.8)
```

At every coordinate the localized vector is the explicit short-sum tail

```text
(b_N-N*S_N*gamma_N)(m)
  = -sum_(N<k<=2N) mu(k)/k * floor(m/k)
      + N*S_N*floor(m/N).                                (M4.9)
```

This is an unconditional identity. It localizes the denominator to short
weighted Mobius sums beyond the old coordinate range. It does not yet bound the
numerator, and the further projection in (M4.8) still matters: at
`N=8,16,32,64,128`, the ratio of projected to raw localized squared energy is
approximately `0.828, 0.805, 0.682, 0.646, 0.577`. Thus (M4.8) is a useful
denominator entrypoint, not a proof that old projection may be dropped.

## 8. Existing Mobius Cancellation Has The Wrong Inequality Direction

Maier--Rassias prove a power-saving estimate for a family of short
Mobius--Vasyunin sums. Their Theorem 1.1 has the form

```text
sum_(Bk<=h<(1+eta)Bk) mu(h) g(h/k)
  = O((eta*B*k)^(1-beta)).
```

This confirms that unconditional cancellation technology is available for
some kernels occurring in Nyman--Beurling Gram entries.

Source:

```text
Helmut Maier and Michael Th. Rassias,
Estimates of sums related to the Nyman-Beurling criterion for the Riemann
Hypothesis, arXiv:1705.09921, Theorem 1.1.
https://arxiv.org/abs/1705.09921
```

It does not produce M4. Such estimates upper-bound an oscillatory sum and may
help upper-bound the localized energy in (M4.9). M4 requires a uniform positive
lower bound for the magnitude of (M4.5). A cancellation theorem cannot exclude
that this signed correlation is exceptionally small, and the theorem does not
contain the finite projection `G_N^-1`.

The resulting route boundary is now precise:

```text
denominator:
  explicit tail localization exists; unconditional upper estimates may be
  possible through short-sum technology

numerator:
  requires inverse-Gram Mobius non-cancellation with a fixed positive margin;
  no producer was found
```

Therefore Plan 020 as a whole is not mathematically disproved, but the two
proposed structural shortcuts for removing `G_N^-1` are rejected:

```text
Vasyunin infinite biorthogonal -> finite inverse: rejected
Cholesky entry positivity -> signed M4 correlation: rejected
```

Any continuation must attack the new numerator theorem directly or find a
different explicit direction whose correlation has a source-defined sign.

## 9. Fixed-Sign And Smoothed-Direction Rejection

The Vasyunin dual gives one exact relation between the target's formal Mobius
coordinates and the finite optimum. Let

```text
p_N = sum_(2<=k<=N) x_k^(N) gamma_k,
r_N = gamma-p_N,
```

and let `g_n` be the biorthogonal vector for the positive `gamma_n` convention.
Then

```text
<gamma,g_n> = -mu(n),
x_n^(N)+mu(n) = -<r_N,g_n>.                             (M4.10)
```

For each fixed `n`, RH and `d_N->0` would force `x_n^(N)->-mu(n)`. This does not
give uniform control when `n` grows with `N`, because `||g_n||` grows rapidly.

The first numerical data suggested the stronger sign rule

```text
sign(<gamma,e_n>) = sign(-mu(n))
```

for squarefree `n`, where `e_n` is the normalized Gram--Schmidt direction.
That rule is false. The first counterexample is `n=31`:

```text
mu(31) = -1,
<gamma,e_31> = -0.00076384...,
-mu(31)*<gamma,e_31> < 0.
```

The exact periodic Gram computation gives `-0.0007638378`; an independent
two-million-term computation gives `-0.0007639262`. Through `n=256`, 24
squarefree counterexamples occur, beginning

```text
31, 65, 79, 94, 95, 110, 114, 139, 161, 166, ...
```

Thus the Mobius block correlation cannot be converted into a positive-term sum
by a pointwise sign theorem. Only block-level dominance remains possible.

The success of `mu(k)/k` is also not a finely tuned exponent effect. For
`a_k=mu(k)/k^alpha`, the normalized captures are:

```text
+------+---------+---------+---------+---------+---------+
| N    | alpha=-1| alpha=0 | alpha=.5| alpha=1 | alpha=2 |
+------+---------+---------+---------+---------+---------+
| 64   | 0.5363  | 0.5644  | 0.5647  | 0.5544  | 0.5046  |
| 128  | 0.5775  | 0.6119  | 0.6190  | 0.6166  | 0.5803  |
| 256  | 0.3936  | 0.4168  | 0.4189  | 0.4140  | 0.3872  |
| 512  | 0.5327  | 0.5861  | 0.5887  | 0.5802  | 0.5452  |
+------+---------+---------+---------+---------+---------+
```

A broad exponent range survives. The signal comes primarily from the Mobius
sign pattern, not the exact power weight.

Bettin--Conrey--Farmer use the smoothed coefficients

```text
mu(k) * (1-log(k)/log(X))
```

to obtain the expected Nyman--Beurling asymptotic under RH plus a moment bound
for `1/zeta'(rho)`. On the dyadic block, its shape is proportional to
`mu(k)log(2N/k)`. It does not improve this experiment: at `N=512`, the
normalized captures are approximately

```text
mu(k):                    0.5861
mu(k)/k:                  0.5802
mu(k)*sqrt(log(2N/k)):    0.5227
mu(k)*log(2N/k):          0.4887
```

Source:

```text
S. Bettin, J. B. Conrey, D. W. Farmer,
An optimal choice of Dirichlet polynomials for the Nyman-Beurling criterion,
arXiv:1211.5191, Theorem 1.
https://arxiv.org/abs/1211.5191
```

That theorem is conditional on RH and a zero-derivative moment estimate, so it
cannot produce M4 in any event. The smoothed direction is not selected for Plan
020.

The remaining M4 statement is now strictly block-level:

```text
the net Mobius correlation, after all good/bad cancellation, must remain large
relative to the same direction's projected Schur energy and d_N.
```

No pointwise positivity theorem or known smoothed Dirichlet polynomial result
supplies this comparison.

## 10. Good/Bad Block Mass Does Not Have A Fixed Visible Margin

For `c_k=<r_N,gamma_k>` split the signed numerator terms

```text
-mu(k)c_k/k^alpha
```

into their positive mass `good_N` and absolute negative mass `bad_N`. For the
selected `alpha=1` direction:

```text
+------+------------+------------+
| N    | bad/good   | net/good   |
+------+------------+------------+
| 32   | 0.0509     | 0.9491     |
| 64   | 0.1684     | 0.8316     |
| 128  | 0.2313     | 0.7687     |
| 256  | 0.4402     | 0.5598     |
| 512  | 0.5089     | 0.4911     |
+------+------------+------------+
```

The same trend occurs for `alpha=0` and `alpha=0.5`. By `N=512`, bad-sign
terms cancel about half of the good-sign mass. This does not reject M4 because
the projected Schur energy shrinks at the same time and the normalized capture
remains near `0.58`. It does reject the stronger proposed proof strategy

```text
bad_N <= (1-epsilon) good_N
```

as a numerically unsupported uniform intermediate theorem.

The M4 numerator and denominator cannot safely be bounded independently by
coarse estimates. The surviving obligation is the coupled inequality (M4.1),
or an identity that explains why numerator cancellation and Schur-energy decay
track each other.

## 11. Final Large-Scale Rejection Run

The matrix-free CUDA mode in `scratch_nyman_block.py` avoids constructing the
full `2N` Gram matrix. It forms the old basis through cutoff `M`, constructs the
selected block vector directly, and solves the two normal equations for the
target and block projections with diagonally preconditioned conjugate gradient.

Command shape:

```text
python scratch_nyman_block.py --gpu-n 4096 --cutoff 250000
```

The relative normal-equation residuals were below `1e-11`. The resulting
normalized captures are:

```text
+------+---------+---------------------------+
| N    | cutoff  | mu/k certificate * log(N) |
+------+---------+---------------------------+
| 1024 | 100000  | 0.2965                    |
| 1024 | 250000  | 0.2948                    |
| 2048 | 250000  | 0.5869                    |
| 4096 | 100000  | 0.2834                    |
| 4096 | 250000  | 0.2664                    |
+------+---------+---------------------------+
```

This weakens the earlier positive numerical evidence. The dyadic values do not
settle near one visible constant, and the low subsequence drops below the
previous `N=256` low. It is not a theorem that the normalized infimum is zero:
at `N=4096` the projected energy is about `8.13e-10`, whereas the crude omitted
scalar weight mass is about `4.00e-6`. Cutoff stability is useful rejection
evidence but not an interval certificate.

The decisive issue is structural. After the Vasyunin, Cholesky-sign,
pointwise-sign, fixed good/bad margin, power-weight, and BCF-taper attacks, the
only surviving statement is still

```text
abs(a_N^T (t_block-C_N^T G_N^-1 t_N))^2
  >= (c/log N) * d_N^2
       * a_N^T(B_N-C_N^T G_N^-1 C_N)a_N.
```

That statement implies RH through the already-checked dyadic closure. No
independent finite arithmetic theorem has replaced its inverse-Gram term.
Burnol supplies the unconditional lower obstruction on `d_N^2 log N`; it does
not supply this capture lower bound. Bettin--Conrey--Farmer obtain the expected
matching Mobius approximation only under RH plus a moment bound on
`1/zeta'(rho)` (arXiv:1211.5191, Theorem 1).

Final route judgment:

```text
Plan 020 status: rejected as an executable RH route.
M4 status: unresolved, not mathematically refuted.
RH status: still conditional; no Lean root was removed or lowered.
Reusable evidence: exact finite formulas and rejection guards only.
```
