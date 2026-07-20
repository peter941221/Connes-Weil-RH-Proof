# Proof 413: Relative-displacement scalar owner and stopping no-go

Date: 2026-07-19

Status: analytic correction of Proof 412.  Compact root support does not stop
absolute Euler paths, and no positive path square function can encode the
resulting scalar cancellation.  The legal Gate 3U owner is a signed functional
of the relative displacement after common history, the complete prime
telescope, and the outer-minus-Sonin boundary have been combined.

This proof closes the proposed pathwise stopping kill test negatively.  It
does not prove the resulting uniform functional bound, Gate 3U, the finite-S
sign, Burnol's identity, or RH.

## 1. Result

```text
+---------------------------------------------------+--------------------------+
| layer                                             | judgment                 |
+---------------------------------------------------+--------------------------+
| fixed-S causal Gram response                      | exact                    |
| dependence on compact roots                       | through cross-correlation|
| simultaneous translation of two path histories   | cancels exactly          |
| stopping by absolute path position                | impossible               |
| stopping by relative displacement                 | legal only after trace   |
| positive H1 / nuclear stopped column              | impossible               |
| complete-prime Markov telescope                   | retained                 |
| signed relative-displacement functional bound     | open, exact Gate bottom  |
| Gate 3U / RH                                      | open / unproved          |
+---------------------------------------------------+--------------------------+
```

The correction is

```text
absolute Euler paths
  -X-> no compact stopping theorem;

completed signed scalar
  -> quotient simultaneous translation history
  -> retain relative displacement
  -> apply compact cross-correlation support
  -> prove one uniform distribution bound.             (SD.1)
```

## 2. Exact fixed-S scalar owner

Retain Proofs 264--266.  For a finite prime set `S`, put

```text
A_S=product_(p in S)
  (1-p^(-1/2))(I-p^(-1/2)U_(log p))^(-1),

K_S=E A_S iota_B,
Gamma_S=K_S* K_S,
W=C_xi* C_eta.                                        (SD.2)
```

The ordered response is

```text
Q_S(eta,xi)
 =Tr_B(K_S* W K_S Gamma_S^(-1)-W_B)
 =Tr_B(N_W Gamma_S^(-1)).                             (SD.3)
```

The order of `Gamma_S^(-1)` is mandatory.  Proof 264's unilateral-shift
guard forbids cycling `(SD.3)` to a polar projection trace before the
root-completed trace-class product has been formed.

Proof 263 proves that `(SD.3)` depends on the roots only through

```text
F=xi^star*eta,
supp(F) subset [-2B_root,2B_root].                    (SD.4)
```

For fixed `S`, Proof 261 supplies continuity in the compact test-function
topology after the complete physical boundary has been assembled.  Denote the
resulting scalar functional by

```text
Lambda_S(F)=Q_S(eta,xi).                              (SD.5)
```

Equation `(SD.5)` is not the forbidden raw point trace
`Tr(U_z(B_S-B))`.  It is defined only after pairing with the compact smooth
cross-correlation.

## 3. Absolute path stopping is impossible

The contradiction already occurs in the actual half-line geometry used by
the outer Gate channel.  On `L2(R)`, let

```text
E=P_[0,infinity),
W=C_F,
supp(F) subset [-L,L].                               (SD.6)
```

For two positive shifts, Proof 268 uses the centered path atom

```text
D_(x,y)
 =E U_x* E W E U_y E
  -E W E E U_x* E U_y E.                            (SD.7)
```

If `x>y>=L`, common history cancels and

```text
D_(x,y)=E W(I-E)U_(y-x)E.                            (SD.8)
```

Consequently, once no artificial far boundary is present,

```text
D_(x+k,y+k)=D_(x,y),  k>=0.                          (SD.9)
```

Choose `d=x-y` with `0<d<L` and `F(d)!=0`.  For example, a nonzero compact
autocorrelation is positive for all sufficiently small `d`.  The completed
half-line trace in `(SD.8)` is the crossing-length multiple of `F(d)`, so it
is nonzero.  Equation `(SD.9)` keeps that same nonzero scalar for arbitrarily
large `k`.

Now suppose an absolute stopping rule deleted every path whose individual
translations missed a fixed compact boundary neighborhood.  For sufficiently
large `k`, it would delete `(x+k,y+k)`.  It would therefore assign zero to the
left side of `(SD.9)`, while `(SD.8)--(SD.9)` give the same nonzero completed
trace.  This is a contradiction.

Thus

```text
compact support cannot stop x and y separately;
compact support can restrict d=x-y only after common history cancels. (SD.10)
```

In particular, large comparable primes with

```text
abs(log p-log q)<=2B_root                             (SD.11)
```

remain visible.  Their absolute logarithmic shifts are large, but their
relative displacement lies in the detector window.

## 4. A positive stopped square function is also impossible

Proof 273 gives the same obstruction at the operator-ideal level.  For a
nonzero compact root `g`, a finite interval `I`, and `abs(b)>2B_root`, put

```text
K_(I,b,g)=C_g U_b E_I C_g*.
```

Then

```text
Tr(K_(I,b,g))=0,
norm(K_(I,b,g))_1=abs(I) norm(g)_2^2>0.              (SD.12)
```

A one-column noncommutative `H1` norm is exactly the trace norm.  Hence no
positive `H1`, Hilbert--Schmidt square, or nuclear column can inherit the
zero-support event in `(SD.12)`.  Compact support cancels the signed scalar,
not the positive operator mass.

This rules out Proof 412's proposed order

```text
absolute path stopping
  -> positive prime martingale square function
  -> signed physical response.                       (SD.13)
```

The failure is analytic and source-level; it is not a finite-section or
quadrature artifact.

## 5. The correct test-function space

For `r>=0` and `B>=0`, let `R_B^r` be the finite sums

```text
F=sum_j xi_j^star*eta_j,
supp(eta_j),supp(xi_j) subset [-B,B],
eta_j,xi_j in H^r(R).                                (SD.14)
```

Equip this space with the projective root norm

```text
norm(F)_(R_B^r)
 =inf sum_j norm(eta_j)_(H^r) norm(xi_j)_(H^r),      (SD.15)
```

where the infimum runs over all representations in `(SD.14)`.  Proof 263's
correlation factorization makes `Lambda_S` well-defined on this quotient.

The exact Gate 3U theorem is

```text
sup_(finite S) norm(Lambda_S)_(R_B^r)*
 <=C(1+B)^d.                                         (SD.16)
```

For one pair of roots, `(SD.16)` is the requested bilinear Gate bound.
Conversely, the bilinear bound and the triangle inequality give `(SD.16)`.
Thus `(SD.16)` is an equivalent functional formulation, not a stronger
stored premise.

Dixmier--Malliavin factorization gives a qualitative representation of
compact smooth tests by convolution products.  It does not provide the
polynomial comparison between `(SD.15)` and a standard Sobolev norm which
Gate 3U requires.  Therefore `Lambda_S` may be described qualitatively as a
compact-test distribution, but a uniform `H^(-r)` bound must not be asserted
without that quantitative factorization.

## 6. Where the complete-prime telescope belongs

Proof 289 remains exact.  For every common completed renewal reward `X`,

```text
sum_(p in S)G_fut(p)(I-G_p)=I-G_S,                  (SD.17)

sum_(p in S)Tr(G_fut(p)(I-G_p)X)
 =Tr((I-G_S)X).                                      (SD.18)
```

Equations `(SD.17)--(SD.18)` must be used inside `Lambda_S(F)`, before an
absolute value.  They do not make a positive stopped path column.  Moreover,
merging the global random defect with the outer escape channel immediately
reconstructs `Delta` and the original `Gamma_S^(-1)` renewal; Proof 289
`(AZ.26b)--(AZ.26c)` shows that this is a circular identity, not an estimate.

The latest scalar cocycle owner is equivalently Proof 400's legal prefix
collapse:

```text
Lambda_S(F)
 =sum_(j=1)^n rho_j^(-1)Tr(f_j(F))
 =sum_(j=1)^n Tr(W(P_j-P_(j-1))).                    (SD.19)
```

Every term in `(SD.19)` is trace legal only after root completion.  The sum
is signed and must remain complete.  Proof 405 identifies its source first
jet with the inseparable reflected-second-support/prolate corner

```text
P Q_f W_E R
 +P(I-Q_f)[W_E,Q_f]R.                               (SD.20)
```

No theorem currently bounds the complete finite-prefix sum `(SD.19)` in the
norm `(SD.16)`.

## 7. Why almost-periodic Szego does not fill the gap

The closest additional source checked after Proof 412 is

```text
T. Ehrhardt, S. Roch, and B. Silbermann,
A Strong Szego--Widom Limit Theorem for operators with almost periodic
diagonal, Journal of Functional Analysis 260 (2011), 30--75.
https://www.mathematik.tu-darmstadt.de/media/mathematik/forschung/preprint/preprints/2564.pdf
```

That theorem concerns finite sections on `ell2(Z)` of band-dominated
operators whose diagonals are almost-periodic sequences.  Its contract uses
weighted Wiener-type Banach algebras and distinguished subsequences.  The
paper also records that the determinant error can be unbounded without the
required Fourier-spectrum condition.

The Gate owner instead has all of the following features:

```text
Burnol's fixed singular-inner / nearly invariant carrier;
the nonconstant weight h=abs(g_0)^2;
continuous prime-log translations;
trace class only after compact root completion;
an exact finite-S bound, not a distinguished finite-section asymptotic. (SD.21)
```

Therefore the almost-periodic diagonal theorem does not imply `(SD.16)`.
The same contract mismatch remains for the ordinary Wiener--Hopf and finite
Blaschke BOGC theorems audited in Proof 412.

## 8. Route judgment

The proposed Proof 412 kill test has a decisive answer:

```text
pathwise physical stopping:              false;
positive stopped martingale estimator:   false;
complete signed scalar disintegration:   mandatory;
uniform projective root bound (SD.16):    open;
Gate 3U:                                  open;
direct RH bypass:                         no shorter proved theorem. (SD.22)
```

This does not force a pivot to Suzuki's all-window nondegeneracy theorem.
That target is already RH-equivalent and discards the repository's closed
carrier and fixed-S trace-legality layers.  The shortest remaining route is
still Gate 3U, but only through `(SD.16)` or the equivalent complete weighted
relative-determinant cocycle `(SD.19)`.  No absolute-path stop, positive
square function, primewise absolute sum, or raw almost-periodic Szego import
can prove it.
