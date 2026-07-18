# Proof 339: operator-valued Hankel--Besov Gate

Date: 2026-07-17

Status: valid local trace-ideal lemmas, but rejected as a same-object Gate 3U
interface by Proof 340.  Proof 294's emission/emission corner is an
`S_1`-valued Hankel matrix and Proof 271's complete missing row does induce a
contractive completely positive map.  What is not proved is that the complete
weighted Gate response -- including the canonical term, all-even sector,
path-boundary strip, and infinite trace anomaly -- is the Hankel operator of
the proposed symbol.

Consequently a `B^1_1(S_1)` bound for the symbol below would control only the
emission Hankel corner.  It would not close Gate 3U.  See Proof 340 before
using any conclusion in Sections 6--9.

## 1. Result

```text
+------------------------------------------------+--------------------------+
| layer                                          | judgment                 |
+------------------------------------------------+--------------------------+
| right-path emission corner                     | exact block Hankel       |
| trace-class criterion                          | B^1_1(S_1)              |
| Hardy multiplicity                             | included in criterion    |
| complete missing row                           | contraction              |
| induced CP map on S_1                          | contraction              |
| induced map on B^1_1(S_1)                     | contraction              |
| primewise / branchwise trace-norm sum          | not used                 |
| reciprocal survival gap                        | absent                   |
| full Gate scalar = proposed Hankel operator    | false / unproved         |
| source emission-symbol Besov bound             | open                     |
| Gate 3U / RH                                   | open / unproved          |
+------------------------------------------------+--------------------------+
```

The proposed reduction was

```text
complete Q-root outer-minus-Sonin coefficients
  -> one S_1-valued analytic symbol Phi_W
  -> Peller B^1_1(S_1) norm
  -> complete missing CP channel (contractive)
  -> de Branges--Rovnyak compression (contractive)
  -> ordinary trace bound.                         (BW.1)
```

Proof 340 rejects the first arrow for the complete weighted owner.  Equation
`(BW.1)` is retained only as a candidate local estimate for the unweighted
emission corner.

## 2. The exact Hankel corner

Use Proof 337's normalized output

```text
C=K(I+Delta)^(1/2),
C*C=I-Delta^2.                                      (BW.2)
```

At infinite horizon, Proof 294's emission corner is

```text
P_(j,k)=C Delta^(j+k) C*,  j,k>=0.                  (BW.3)
```

It is a block Hankel matrix: the block depends only on `j+k`.  For the
coefficient-wise detector `mathcalW`, its commutator has blocks

```text
[mathcalW,P]_(j,k)
 =W_E C Delta^(j+k)C*
  -C Delta^(j+k)C* W_E.                             (BW.4)
```

Proofs 291--295 generate the emission blocks and local reflected identities.
They do **not** assemble the mandatory path-boundary corrections inside the
actual `Z_n* [O_n,P_n]R_n` weights.  Proof 296 performs that assembly and
shows that the weights depend separately on the row and column indices.
Therefore there is currently no well-defined complete block
`A_m(S,W)` depending only on `m=j+k`.

The analytic operator-valued symbol is

```text
Phi_(S,W)(z)=sum_(m>=0) A_m(S,W) z^m.                (BW.5)
```

The emission-corner operator, not the full hard path owner, is the Hankel
matrix

```text
Gamma_(Phi_(S,W))
 =(A_(j+k)(S,W))_(j,k>=0).                           (BW.6)
```

## 3. Peller's trace-class criterion in the required coefficient space

Let `H_src` be the physical source carrier and take the coefficient operator
space

```text
E=S_1(H_src).                                        (BW.7)
```

The operator-valued Peller theorem gives

```text
Gamma_Phi in S_1(l2(N) tensor H_src)
  iff
Phi in B^1_1(S_1(H_src))_+,                         (BW.8)
```

with equivalent norms.  In dyadic form a sufficient and necessary norm is

```text
norm(Phi)_(B^1_1(S_1))
 =sum_(n>=0) 2^n
   norm(W_n*Phi)_(L1(T;S_1)).                       (BW.9)
```

Primary source:

```text
Mikael de la Salle,
Operator space valued Hankel matrices,
Theorem 0.1 with p=1 and E=S_1(H_src),
arXiv:0909.5151.
https://arxiv.org/abs/0909.5151
```

The paper proves the estimate uniformly for every operator space `E`; this is
the required infinite-dimensional coefficient version, not merely the scalar
Peller theorem.  The scalar precursor is Peller's trace-class criterion
`H_phi in S_1 iff P_-phi in B^1_1`, recalled as Theorem 5.1 in:

```text
V. V. Peller,
The behavior of functions of operators under perturbations,
arXiv:0904.1761.
https://arxiv.org/abs/0904.1761
```

Equation `(BW.8)` is exactly what a spatial-only Sobolev estimate misses: it
controls both the source trace multiplicity and the infinite Hardy path
index.  Therefore it survives Proof 270's direct-sum guard.

## 4. Complete missing channel as one contraction

Proof 271 constructs the outer missing map `M_C` and the complete random
missing row `M_rand`.  Put

```text
mathcalM x=(M_rand x,M_C x).                         (BW.10)
```

Its exact Gram identity is

```text
mathcalM* mathcalM
 =M_rand* M_rand+M_C* M_C
 =Delta<=I.                                          (BW.11)
```

Hence

```text
norm(mathcalM)<=1.                                   (BW.12)
```

For a trace-class operator `X`, define the block output

```text
Psi_S(X)
 =Diag(M_rand X M_rand*, M_C X M_C*).                (BW.13)
```

Equivalently, form `mathcalM X mathcalM*` and apply the diagonal conditional
expectation.  Both maps are completely positive, and the diagonal expectation
is trace preserving.  From `(BW.12)` and the trace-ideal property,

```text
norm(Psi_S(X))_1
 <=norm(mathcalM X mathcalM*)_1
 <=norm(X)_1.                                        (BW.14)
```

This packages all missing branches before a norm.  Expanding `(BW.13)` into a
sum of individual factor norms would return the forbidden total-variation
route.

## 5. Besov contraction

Apply `Psi_S` coefficientwise to an `S_1`-valued analytic symbol.  Since
`Psi_S` is fixed with respect to the circle variable, it commutes with every
dyadic convolution `W_n`.  Equations `(BW.9)` and `(BW.14)` give

```text
norm(Psi_S Phi)_(B^1_1(S_1))

 =sum_n 2^n norm(Psi_S(W_n*Phi))_(L1(S_1))

 <=sum_n 2^n norm(W_n*Phi)_(L1(S_1))

 =norm(Phi)_(B^1_1(S_1)).                           (BW.15)
```

Thus the abstract missing-channel map does not enlarge the Besov norm of a
symbol on which it genuinely acts coefficientwise.  Proof 340 notes that the
actual weighted path coefficients contain horizon- and index-dependent
future factors, so `(BW.15)` has not been identified with Proof 289's complete
scalar telescope.  No Gate estimate follows from this contraction alone.

This use of `(BW.11)` is not the forbidden circular step
`(AZ.26a)--(AZ.26c)`: the random and outer channels remain separate diagonal
outputs through the support calculation.  They are combined only by the norm
of one CP map after the complete physical symbol has been formed.

## 6. How compact-root regularity enters

For an `S_1`-valued analytic symbol, a concrete sufficient estimate for
`(BW.9)` is any `q>1` derivative bound of the form

```text
sup_(finite S)
 norm(partial_theta^q Phi_(S,W))_(L1(T;S_1))

 <=C_q(1+B_root)^d
   norm(eta)_(H^r) norm(xi)_(H^r).                  (BW.16)
```

Indeed a dyadic block at frequency `2^n` gains `2^(-nq)` from `q`
derivatives, while `(BW.9)` costs `2^n`; the sum

```text
sum_n 2^n 2^(-nq)
```

converges exactly when `q>1`.

The derivative in `(BW.16)` must be taken after:

```text
the Q-root completion;
the outer-minus-Sonin recombination;
the path-boundary correction;
the -2 residue cancellation from Proof 335.          (BW.17)
```

Taking it on an individual prime, physical branch, or uncompressed residue is
forbidden.

Proof 336 supplies the far-displacement part after the half-density residue is
removed.  The remaining source theorem is the near-displacement estimate
`(BW.16)` for the complete symbol.

## 7. Finite guard

The companion probe constructs `(BW.2)--(BW.4)` from Proof 270's
source-shaped finite model.  It compares a finite block-Hankel trace norm with
the dyadic `B^1_1(S_1)` surrogate while the survival gap collapses:

```text
+----------+------------+-------------+-------------+
| diagonal | norm Delta | Hankel S1   | Besov B11   |
+----------+------------+-------------+-------------+
|     0.55 | 0.732239   | 0.637266    | 1.256406    |
|     0.35 | 0.903462   | 0.636026    | 1.668855    |
|     0.20 | 0.971312   | 0.575917    | 1.831857    |
|     0.10 | 0.991062   | 0.425009    | 1.548778    |
|     0.05 | 0.995780   | 0.340506    | 1.256833    |
+----------+------------+-------------+-------------+
```

Run without a Lean build:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/339_operator_valued_hankel_besov_probe.py
```

The absence of reciprocal-gap growth supports the coordinate.  It is not
evidence for the continuous source estimate `(BW.16)`.

## 8. Rejected completion claim

The following statement was proposed as the near Gate 3U bottom:

```text
sup_(finite S)
 norm(Phi_(S,W))_(B^1_1(S_1))

 <=C(1+B_root)^d
   norm(eta)_(H^r) norm(xi)_(H^r),                  (BW.18)
```

Proof 340 shows that no complete anti-diagonal owner has been constructed:
the actual weighted contributions are not Hankel and the boundary strip is
order one.  Hence `(BW.18)` is not currently a theorem about the Gate scalar.

Even if `(BW.18)` holds for the emission symbol, the following implication is
unproved:

```text
Peller/de la Salle        -> full-Hardy trace-class bound;
de Branges domination     -> no larger model-space bound;
complete CP contraction   -> no prime/outer missing-channel cost;
Proof 336                 -> far-displacement bound;
one final absolute value  -> Gate 3U.               (BW.19)
```

The corrected active owner is Proof 298's ordered relative heat cocycle, or
equivalently Proof 282's complete moving-band integral.  A future Hankel/BOGC
factorization is usable only if its derivative is proved equal to that entire
owner, including the canonical and boundary-anomaly terms.

## 9. Route judgment

```text
emission Hankel/Peller interface:           closed locally;
abstract missing-channel contraction:       closed locally;
complete Gate owner is that Hankel symbol:  rejected by Proof 340;
primewise p^(-1/2) summation:               not eliminated;
ordered heat / moving-band uniform bound:   open;
Gate 3U:                                   open;
finite-S sign / Burnol identity / RH:      open.       (BW.20)
```
