# Proof 254: Shorted Markov boundary gate

Date: 2026-07-15

Status: exact uniform bound for the ambient Markov boundary response, and an
exact obstruction to promoting that bound through compressed metric inverses
by abstract operator order alone.  The normalized inverse Euler transport is
a probability average of one-sided prime-log translations.  After one legal
half-line crossing is paired with a compact convolution root, every shift
outside the root difference support vanishes and the entire probability
average is bounded by the support diameter.

The compressed inverse is not that probability operator.  It is an exact
shorted operator: the ambient Markov compression minus a positive conditional
defect.  A two-mode cyclic-translation example has all of Proof 253's abstract
normalizations, including a Markov inverse and a detector vanishing at the
Markov fixed mode, while its complete nested projection response tends to
`-1`.  Thus a Markov-only proof of the detector estimate is false.  The next
theorem must carry CC20's concrete half-line/scattering/prolate geometry
through the shorting defect while preserving the full `D_E-D_R` difference.

This is not a continuous Sonin bound, a finite-S sign, or an RH proof.  No
Lean owner or route rewire is authorized.

## 1. Result first

Proof 253 left the suggestion

```text
normalized inverse metric
  -> probability average of prime-log translations
  -> compact root boundary crossing
  -> uniform finite-S response.                         (M.1)
```

Proof 254 separates the part of `(M.1)` which is correct from the part which
is not automatic:

```text
+--------------------------------------+-------------------------------+
| layer                                | verdict                       |
+--------------------------------------+-------------------------------+
| inverse complete transport           | one-sided probability average |
| inverse complete metric              | two-sided probability average |
| one smoothed half-line crossing      | uniformly clipped by support  |
| inverse compressed metric            | Markov compression minus      |
|                                      | a positive shorting defect     |
| abstract Markov-to-projection lift   | false by exact two-mode model |
| concrete shorted Sonin response      | open, new active theorem      |
+--------------------------------------+-------------------------------+
```

The important change is that the open object is no longer an unspecified
"averaged boundary response."  It is the response of one named shorting
defect after the three CC20 half-line branches and the prolate correction are
recombined.

## 2. One-sided Markov inverse

Use Proof 253's normalized finite-S transport.  Put

```text
r_p=t p^(-1/2),
U_p=translation by log(p),

Ttilde_(S,t)
 =product_(p in S) (I-r_p U_p)/(1-r_p).                (M.2)
```

Every local inverse has the norm-convergent expansion

```text
(1-r_p)(I-r_p U_p)^(-1)
 =sum_(n>=0)(1-r_p)r_p^n U_p^n.                        (M.3)
```

The coefficients in `(M.3)` are a probability law.  Since all translations
commute, multiplying the local series gives the exact complete identity

```text
Ttilde_(S,t)^(-1)
 =E[U_(Z_(S,t))],

Z_(S,t)=sum_(p in S) N_p log(p),
P(N_p=n)=(1-r_p)r_p^n,  n>=0.                          (M.4)
```

This is stronger than the two-sided formula recorded in Proof 253: the inverse
transport itself, not only its squared metric, is a Markov convolution.

Taking the product with its adjoint gives

```text
Htilde_(S,t)^(-1)
 =Ttilde^(-1) Ttilde^(-*)
 =E[U_(Z-Z')],                                        (M.5)
```

where `Z'` is an independent copy of `Z`.  For one prime,

```text
P(N_p-N'_p=k)
 =(1-r_p)/(1+r_p) r_p^|k|,  k in Z.                   (M.6)
```

Equations `(M.4)--(M.6)` are exact probability identities.  There is no sum
of primewise operator norms.

## 3. Compact-root crossing clip

Let `P` be a half-line projection and let

```text
(U_z f)(x)=f(x-z).                                    (M.7)
```

Let `g` be a smooth root supported in `[-B,B]`, and write its autocorrelation

```text
F(z)=integral_R conjugate(g(x))g(x+z) dx.              (M.8)
```

Then

```text
F(z)=0                    for |z|>2B,
|F(z)|<=||g||_2^2         for every z.                 (M.9)
```

For the legally smoothed half-line crossing, direct kernel integration gives,
up to the fixed translation convention,

```text
Tr(C_F [P,U_z])=z F(-z).                               (M.10)
```

The trace in `(M.10)` only sees the interval on which the translated half-line
indicators disagree.  Its length is `|z|`; the convolution diagonal on that
crossing is the constant `F(-z)`.

Now let `mu` be any probability measure on translations.  Apply compact
support before expanding the average:

```text
|integral z F(-z) dmu(z)|
 <=integral_(|z|<=2B) |z| |F(-z)| dmu(z)
 <=2B ||g||_2^2.                                      (M.11)
```

The constant in `(M.11)` is independent of the number of primes, their
locations, and every moment of `Z`.  In particular, the rapidly growing
quantity

```text
E|Z| approximately sum_p log(p)/sqrt(p)                (M.12)
```

is irrelevant after the support clip.  This is the exact uniform estimate
which a primewise absolute expansion loses.

Proofs 228--234 reduce the source commutator modulo the prolate term to three
boundedly dressed half-line crossings.  Therefore `(M.11)` closes the ambient
Markov part of those branches.  It does not yet close the compressed inverse.

## 4. Compression is a shorted operator

Let `J` be any orthogonal projection, `K=I-J`, and put

```text
H=Htilde_(S,t)>=I,
M=H^(-1).                                             (M.13)
```

For finite `S`, every compression below is boundedly invertible.  Block
inversion of `H=M^(-1)` gives the exact identity

```text
(J H J)^(-1)
 =J M J
  -J M K (K M K)^(-1) K M J.                         (M.14)
```

The second term is positive.  Thus `(M.14)` also proves the Jensen/shorting
bound

```text
0<=(J H J)^(-1)<=J M J.                               (M.15)
```

The order bound `(M.15)` is useful, but it is not an identity with the Markov
compression.

The exact nested version is even more relevant.  Decompose

```text
I=R+B+C,
B=E-R,
C=I-E.                                                (M.16)
```

Let `Sigma` be the Schur complement of `EHE` from `R` onto `B`, as in Proof
253.  The `B-B` block of `(EHE)^(-1)` is `Sigma^(-1)`.  Apply `(M.14)` first to
the split `E direct-sum C`, then compress to `B`:

```text
Sigma^(-1)
 =B M B
  -B M C (C M C)^(-1) C M B.                         (M.17)
```

Hence

```text
0<=Sigma^(-1)<=B M B.                                 (M.18)
```

Formula `(M.17)` names the exact missing object:

```text
shorting defect
 =B M C (C M C)^(-1) C M B.                          (M.19)
```

Although `M` is a probability convolution, `(C M C)^(-1)` is not another
probability average.  Expanding it before the CC20 boundary cancellation can
recreate large signed coefficients.  Positivity of `(M.19)` does not control
the signed trace after the noncommuting root and boundary factors are inserted.

## 5. Exact two-mode obstruction

The failure of the abstract lift can be seen without an asymptotic matrix
experiment.

Work on `C^2` in the Fourier basis of the two-cycle translation

```text
U=diag(1,-1).                                         (M.20)
```

For `0<r<1`, the normalized local transport is

```text
T_r=(I-rU)/(1-r)=diag(1,kappa),
kappa=(1+r)/(1-r).                                    (M.21)
```

It satisfies `H_r=T_r* T_r>=I`.  Its inverse metric is

```text
M_r=diag(1,kappa^(-2)).                               (M.22)
```

In the physical two-cycle basis, `(M.22)` is exactly

```text
M_r
 =[(1+kappa^(-2))/2] I
  +[(1-kappa^(-2))/2] U_swap.                         (M.23)
```

Both coefficients are nonnegative and sum to one.  Thus `(M.23)` is a genuine
Markov average, not merely a positive contraction.

Let

```text
E=I,
R=|v_epsilon><v_epsilon|,
v_epsilon=(sqrt(1-epsilon^2),epsilon),
B=E-R,                                                (M.24)

W=diag(0,1).                                          (M.25)
```

The detector `W` is nonnegative and vanishes on the fixed mode of `(M.23)`.
The transported inner projection is the projection onto

```text
(sqrt(1-epsilon^2),kappa epsilon).                    (M.26)
```

Since `E` is fixed, the complete nested-band response is exactly

```text
Tr(W(B_r-B))
 =epsilon^2
  -kappa^2 epsilon^2
    /(1-epsilon^2+kappa^2 epsilon^2).                 (M.27)
```

For the fixed value `epsilon=0.1`, `(M.27)` tends to `-0.99`.  More sharply,
choose

```text
epsilon=kappa^(-1/2).                                 (M.28)
```

Then

```text
norm([W,R])=epsilon sqrt(1-epsilon^2)->0,

Tr(W(B_r-B))->-1.                                     (M.29)
```

Large `kappa` does not require one illegal Euler parameter near one.  Repeating
normalized factors with any fixed local `r<=1/sqrt(2)` multiplies their odd
eigenvalue ratios, so their complete product realizes arbitrarily large
`kappa` while every local factor stays inside the route interval.

Equations `(M.20)--(M.29)` prove:

```text
H>=I
+ H^(-1) Markov
+ nested projections
+ detector zero at the Markov fixed mode

does not imply a small transported nested response.   (M.30)
```

This does not reject the real Sonin route.  It proves that the missing estimate
must use its concrete half-line/scattering geometry; no abstract operator-order
argument can replace that work.

## 6. Reproducible certificate

The companion script checks four independent layers.

Default WSL run:

```text
python3 -B docs/proofs/254_shorted_markov_boundary_gate_probe.py
```

The exact identity errors are:

```text
+--------------------------------------+---------------+
| check                                | error         |
+--------------------------------------+---------------+
| one-sided characteristic             | 6.88e-15      |
| two-sided characteristic             | 1.45e-14      |
| smoothed crossing trace              | 4.97e-16      |
| inverse product                      | 3.27e-15      |
| inverse metric / Markov square       | 7.86e-14      |
| compressed shorting identity         | 1.44e-15      |
| nested shorting identity             | 8.34e-16      |
| two-mode closed response              | 3.33e-16      |
+--------------------------------------+---------------+
```

The finite cyclic shorting defects are genuinely positive:

```text
minimum ordinary defect eigenvalue     2.81e-5
minimum nested defect eigenvalue       1.49e-4
minimum shorted inverse eigenvalue      4.01e-4
Jensen violation                        0
```

For the compact root of radius `9`, the direct crossing vanishes identically
outside radius `18`.  The one-sided probability average has magnitude
`0.6985`, against the source-free upper bound `18`; the ratio is about
`0.0388`.

At effective ratio `r=0.999`, the two-mode responses are

```text
fixed epsilon=0.1:             -0.9899752258452
epsilon=kappa^(-1/2):          -0.9989999998750
```

The script aborts unless all algebraic identities, positivity checks, support
clipping, and obstruction margins pass.

## 7. Large-S finite-section warning

The optional command

```text
OPENBLAS_NUM_THREADS=4 python3 -B \
  docs/proofs/254_shorted_markov_boundary_gate_probe.py \
  --finite-section
```

uses an `O(size * prime_count)` Fourier product instead of storing one dense
translation matrix per prime.  At `p<=100000` it reports:

```text
+------+----------+-----------+------------+-----------+-----------+
| size | half-box | freq step | Sonin rank | root norm | witness   |
+------+----------+-----------+------------+-----------+-----------+
|  384 |    15.36 | 0.204531  |          9 |   4.0409  | -0.7931   |
|  512 |    20.48 | 0.153398  |          9 |  17.1640  | +3.6440   |
|  640 |    25.60 | 0.122718  |          9 |   7.5157  | -0.0751   |
|  768 |    30.72 | 0.102265  |          9 |  10.7080  | -2.2297   |
+------+----------+-----------+------------+-----------+-----------+
```

The multiplier log condition is between about `105` and `123`.  The root norm
and the fixed witness both oscillate strongly with the box, while the selected
finite Sonin rank remains `9`.  This is bad evidence for accepting fixed-box
boundedness and equally bad evidence for claiming a continuous divergence.
The finite section is not resolving the full continuous Sonin space in this
regime.  It is a diagnostic guard only.

## 8. New analytic bottom

Let

```text
M_(S,t)=Htilde_(S,t)^(-1),
C=I-E,
B=E-R.                                                (M.31)
```

The new lowest unresolved metric factor is

```text
Short_(B,C)(M_(S,t))
 :=B M B-B M C(C M C)^(-1)C M B.                     (M.32)
```

It is exactly the nested Schur inverse, not a proposed approximation.  A
successful successor must prove a shorted Sonin boundary-response theorem:

```text
after inserting

  B=P(I-P_hat)P+K_prol,
  P_hat=Scattering* (I-P) Scattering,
  g=L_+ xi supported in [-B_root,B_root],

the complete root trace containing (M.32), together with its band/coherence
partner, obeys

  absolute value
    <=C (1+B_root)^d ||g||_(H^r)^2,                  (M.33)

with C,d,r independent of the finite prime set.
```

The proof order is forced:

```text
1. insert the exact shorted difference (M.32);
2. expand B through all three CC20 half-line branches plus K_prol;
3. keep the band/coherence difference paired;
4. apply compact support to every completed crossing;
5. only then expand the Markov probability law;
6. sum probability mass, not primewise absolute coefficients.             (M.34)
```

Step 4 closes the ambient term by `(M.11)`.  The open work is to show that the
conditioned defect in `(M.32)` admits the same completed-crossing structure.
If it does, Proof 249's resonant contraction can consume `(M.33)`.  If a
conditioned return coefficient with super-polynomial `B_root` growth remains,
the detector-specific route is rejected.

## 9. Source boundary

The source-owned identities used here remain:

```text
CC20, Weil Positivity and Trace Formula, the Archimedean Place
https://arxiv.org/abs/2006.13771
  original TeX lines 542--548: scattering conjugacy
  original TeX lines 960--984: rapid prolate decay
  original TeX lines 1072--1103: P P_hat P=R+K_prol
  original TeX lines 2087--2120: legal smoothed boundary commutators

CCM24, Zeta Zeros and Prolate Wave Operators
https://arxiv.org/html/2310.18423v2
  original TeX lines 946--981: finite Euler multiplier
  original TeX lines 983--1029: Sonin transport
  original TeX lines 1033--1073: common carrier with changed norm
```

The Markov and shorting identities `(M.4)--(M.6)` and `(M.14)--(M.17)` are
elementary project derivations.  A research-stack search also checked
`An approximation theory for Markov chain compression`
<https://arxiv.org/abs/2506.22918>.  Its finite-state compression estimates
depend on a separate Nystrom approximation error, and Section 1 explicitly
defers continuous state spaces.  It does not supply `(M.33)` or a Sonin
shorting theorem.

## 10. Route judgment

```text
+------------------------------------------------+--------------------------+
| layer                                          | judgment                 |
+------------------------------------------------+--------------------------+
| normalized inverse transport                   | exact Markov average     |
| normalized inverse metric                      | exact Markov average     |
| compact-root single-crossing average            | uniformly O(B)||g||^2   |
| compressed inverse shorting formula             | exact                   |
| nested Schur shorting formula                   | exact                   |
| shorting defect                                | positive and nontrivial |
| Markov/order/row-zero abstract shortcut         | rejected exactly        |
| large-S finite Fourier sections                 | nonconverged diagnostic |
| concrete shorted Sonin response (M.33)          | open, active bottom     |
| detector-specific integrated smallness          | open                     |
| same-object finite-S trace identity             | open                     |
| Burnol all-zero identity                        | open                     |
| Lean owner or route rewire                      | none                     |
| RH                                             | unproved                 |
+------------------------------------------------+--------------------------+
```

Proof 254 earns a uniform estimate exactly where the inverse is a probability
average, and proves why that estimate cannot simply be pushed through a
compression symbol.  The remaining hard bone is now `(M.32)--(M.34)`, not
another finite box and not another scalar metric bound.
