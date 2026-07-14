# Proof 234: Sonin alternating-profile closure

Date: 2026-07-14

Status: closes the remaining metric compactness branch at the mathematical
proof level.  CC20's exact angle decomposition replaces every Sonin
projection in the one-crossing linear channel by two scattering-conjugate
half-line projections plus a trace-class prolate correction.  Euler
translations and archimedean scattering commute with the logarithmic
`Q` differential.  Consequently the no-prolate words only add linearly many
half-line cut points; two derivative transfers create at most polynomially
many boundary chirps.  Proof 233's path estimate and the uniform Neumann ratio
`eta<1` make the complete word sum compact.  Together with Proof 232's
two-crossing Hilbert--Schmidt remainder, the full nested metric correction is
compact on every finite root window.  This does not prove its sign on the
three-Mellin-row subspace, does not authorize a Lean route owner, and does not
prove RH.

## 1. Exact Sonin replacement

Use the two Hardy half-line projections `P` and `P_hat` in CC20's scattering
coordinate.  CC20 proves

```text
P P_hat P=r+K_prol,                                   (S.1)
```

where `r` is the Sonin projection and `K_prol` is positive trace class.  The
source locations are

```text
CC20, https://arxiv.org/abs/2006.13771
  original TeX lines 542--548: scattering conjugacy
  original TeX lines 960--984: rapid singular-value decay
  original TeX lines 1072--1103: identity (S.1) and trace-class sum
```

If `mathcal S` denotes the archimedean scattering multiplier, then, up to the
fixed orientation convention,

```text
P_hat=mathcal S* (I-P) mathcal S.                     (S.2)
```

Both `mathcal S` and every Euler translation `U^n` are multipliers in the
Mellin variable.  Therefore

```text
[mathcal S,U^n]=0,
[Q,mathcal S]=0,
[Q,U^n]=0.                                            (S.3)
```

These are exact commutation relations on the common smooth core.  No
derivative is lost when a scattering or Euler factor is moved through the
post-`Q` calculation.

## 2. The source commutator has three half-line branches

Let `E=P` be the crossed half-line orientation and put `b=E-r`.  From `(S.1)`

```text
b=P(I-P_hat)P+K_prol.                                 (S.4)
```

Set `Q_hat=I-P_hat`.  The Leibniz rule gives the exact finite decomposition

```text
[P Q_hat P,U]
 =P Q_hat[P,U]
  +P[Q_hat,U]P
  +[P,U]Q_hat P.                                      (S.5)
```

By `(S.2)--(S.3)`,

```text
[Q_hat,U]=mathcal S*[P,U]mathcal S                    (S.6)
```

with the orientation adjusted by replacing `P` by `I-P` if necessary.  Hence

```text
[b,U]
 =three boundedly dressed copies of [P,U]
  +[K_prol,U].                                        (S.7)
```

The last term is trace class.  Formula `(S.7)` proves that the single source
crossing in Proof 232's `Lambda_alpha` is not a new Sonin kernel: modulo a
trace-class term, it is a finite sum of the same half-line crossings treated
in Proofs 228--229 and 233.

## 3. Prolate insertions do not proliferate

The remaining corner inverse is

```text
A^(-1)
 =(1/(1+alpha^2))
   sum_(k>=0) beta^k [r(U+U*)r]^k,

beta=alpha/(1+alpha^2).                               (S.8)
```

Write

```text
r_0=P P_hat P,
r=r_0-K_prol.                                         (S.9)
```

For bounded operators `X,Y`, the exact telescope

```text
X^k-Y^k
 =sum_(j=0)^(k-1) X^j(X-Y)Y^(k-1-j)                 (S.10)
```

shows that replacing every `r` in a word by `r_0` creates only `O(k)` terms
containing `K_prol`; it does not create an exponential expansion.  Each such
term is trace class, with a polynomial word-length bound, because
`K_prol` is trace class and all other factors are contractions or uniformly
bounded metric inverses.

The coefficient sum of all prolate terms is bounded by

```text
sum_(k>=0) (1+k)^d eta^k<infinity,
eta=2alpha/(1+alpha^2)<1,                             (S.11)
```

for a fixed graph order `d`.

## 4. No-prolate alternating words

Replace `r` by `r_0` in the remaining words and use `(S.2)`.  A length-`k`
word now consists only of

```text
Euler translations U or U*,
half-line cutoffs P or I-P,
scattering multipliers mathcal S or mathcal S*.        (S.12)
```

Move all Euler translations through the scattering factors using `(S.3)`.
The word has `O(k)` half-line cut points.  Applying the second-order root
operator `Q` and transferring derivatives cellwise has three outputs:

```text
cell interiors;
first boundary values at the half-line cut points;
first-derivative jumps at those cut points.            (S.13)
```

There are at most `C(1+k)^2` terms in `(S.13)`.  Scattering factors are
unitary and commute with `Q`; half-line cutoffs are contractions.  Thus they
do not increase the operator norm of a boundary chirp after the derivative
transfer.

For each Euler path, Proof 233 identifies the relevant endpoint by its path
maximum `M`.  The archimedean endpoint contributes `p^(M/2)`, while Proof
228 gives chirp norm `p^(-M/2)`.  Their product is one.  Therefore the whole
length-`k` no-prolate family is bounded by

```text
C (1+k)^2 eta^k                                       (S.14)
```

in the sharp profile norm:

```text
HS norm for the cell interiors;
operator norm for the logarithmic-chirp boundaries.   (S.15)
```

The series in `(S.14)` converges.  This proves that `A^(-1)` preserves the
same post-`Q` profile class as `M^(-1)` and `D^(-1)` in Proof 233.

## 5. Full metric compactness theorem

Proof 232 gives

```text
b_alpha-b=Lambda_alpha+R_alpha,                       (S.16)
```

where `R_alpha` has at least two source crossings and induces a
Hilbert--Schmidt root operator.  The linear term `Lambda_alpha` contains one
source crossing dressed by `M^(-1)`, `D^(-1)`, and `A^(-1)`.

Proof 233 proves profile stability for `M^(-1)` and `D^(-1)`.  Sections 1--4
prove it for `A^(-1)`.  Proof 229 proves compactness of the underlying complete
single-crossing Euler profile.  Hence, for every bounded root interval `I`,

```text
the post-Q finite-window operator induced by b_alpha-b is compact.         (S.17)
```

The compact operator in `(S.17)` need not be Hilbert--Schmidt.  Its nonlinear
two-crossing part is Hilbert--Schmidt; the positive-frequency linear boundary
series is only operator-norm summable, exactly as in Proof 228.

Integrating in `alpha` over

```text
0<=alpha<=p^(-1/2)                                    (S.18)
```

preserves compactness because all profile majorants above are uniform on this
closed interval.  A finite set of primes is then a finite sum on the same
whole-line owner.  Thus the metric compactness gate left by Proof 224 is
closed at the mathematical level.

## 6. What compactness does not prove

The complete semilocal post-`Q` owner now has the form

```text
-2 Id + K_(S,I),
K_(S,I) compact and self-adjoint,                     (S.19)
```

on the same finite root space, with the single-crossing prime ledger already
identified by Proofs 222 and 229.  Compactness alone does not imply

```text
K_(S,I)<2 Id                                          (S.20)
```

on the common kernel of the three Mellin evaluation rows.  A compact operator
may have finitely many eigenvalues at least `2`, and three prescribed rows do
not automatically annihilate their eigenspace.

The next gate is therefore an integrated, same-domain sign theorem for this
named compact correction.  Proof 227 already rules out pointwise
monotonicity of the projection flow; the sign must use the complete
archimedean plus finite-prime form and the three route rows together.

## 7. Reproduction

Run in WSL:

```text
python3 -B docs/proofs/234_sonin_alternating_profile_closure.py
python3 -B docs/proofs/234_sonin_alternating_profile_closure.py --prime 3
```

The finite-matrix certificate checks the commutator decomposition
`(S.5)--(S.7)`, the exact telescope `(S.10)`, the `Q` commutation relations,
and the polynomially weighted majorant `(S.14)`.  Finite matrices do not prove
the infinite-dimensional trace ideals; those use the named CC20 source
theorems and the analytic profile estimates in Proofs 228--233.

## 8. Route judgment

```text
Sonin source commutator reduction:              exact, three half-line terms
prolate insertions:                             trace class and summable
no-prolate alternating words:                  profile-stable
A^(-1) Sonin profile stability:                proved
nonlinear metric root correction:              Hilbert--Schmidt
complete metric post-Q correction:             compact
complete metric Hilbert--Schmidt claim:         not required / not claimed
integrated three-row sign:                     open, now the active gate
Lean owner or route rewire:                    none
RH:                                             unproved
```

The next proof must attack the sign of the named compact correction on the
three-row subspace; further compactness refinements no longer move the route.
