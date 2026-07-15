# Proof 266: Three-branch causal determinant and innovation target

Date: 2026-07-15

Status: exact refinement of Proof 265.  The centered causal Gram numerator is
one sum of the outer boundary, second-support boundary, and prolate leakage.
Every term in the signed renewal carries this same three-branch numerator.
Omitting the prolate branch, even as a preliminary falsification model, is
invalid by Proof 258.

For every fixed finite `S`, the ordered endpoint response is also the logarithmic
derivative of a genuine relative Fredholm determinant near the detector origin.
This closes the determinant-domain premise left formal in Proof 264; it does not
bound that determinant uniformly in `S`.

The proposed Gate 3U successor is a stopped causal innovation theorem.  The
Markov-normalized Euler inverse has an exact random-unitary dilation whose four
orthogonal output channels are the prime innovation, outer complement, Sonin
space, and source band.  The missing theorem must insert the complete
three-branch detector reward into that conservative dilation, stop it at the
physical compact-support boundary, and use prime martingale orthogonality before
one absolute value.

No finite-`S` sign, same-object arithmetic identity, Burnol identity, Lean
owner, route rewire, or RH proof is claimed.

## 1. Result first

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| Gate 3L fixed-S trace legality                 | closed by Proof 261          |
| centered causal Gram numerator                 | exact by Proof 265           |
| outer/second-support/prolate common split      | exact                        |
| same split before every renewal power          | exact                        |
| no-prolate preliminary model                   | rejected by Proof 258        |
| fixed-S relative determinant domain            | closed near detector origin  |
| causal random-unitary channel dilation         | exact                        |
| stopped innovation factorization               | open, active successor       |
| uniform polynomial-support bound               | open, Gate 3U                |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

The exact common numerator is

```text
N_W=O_W+S_W+P_W,                                      (AC.1)

O_W=-B A* C[W,E]E A B,                                (AC.2)

S_W=B(I-Q)[W,Q]R A*E A B,                             (AC.3)

P_W=B Q W R A*E A B.                                  (AC.4)
```

Here `Q` is the second support projection.  The covariance remains named
`Gamma`; these two objects must not share notation.

For

```text
Gamma=B A*E A B,
Delta=B-Gamma,
```

Proof 265's endpoint is

```text
Q_S(eta,xi)
 =sum_(k>=0) Tr_B((O_W+S_W+P_W)Delta^k).               (AC.5)
```

The parentheses in `(AC.5)` are part of the target theorem.  No branch is
estimated before the common renewal is summed.

## 2. Source projections and prolate geometry

Use the source projections

```text
R<=E,
R<=Q,
B=E-R,
C=I-E.                                                 (AC.6)
```

CC20 supplies

```text
E Q E=R+K_prol,
(B Q)(B Q)*=K_prol on Ran(B).                          (AC.7)
```

Thus `BQ` is the source-owned prolate square root.  Its singular values are the
CC20 values `|lambda(n)|`, with the explicit factorial bound recorded in Proof
257.  Equation `(AC.7)` proves trace legality of `(AC.4)` for fixed `S`; it does
not license a separate trace-norm estimate of `(AC.4)`.

## 3. Exact three-branch numerator

Proof 265 gives

```text
N_W
 =-B A* C[W,E]E A B
   +B[W,R]R A*E A B.                                  (AC.8)
```

Since `BR=0`,

```text
B[W,R]R=B W R.                                        (AC.9)
```

Insert `I=Q+(I-Q)` on the left of `W R`.  The source identity `QR=R` gives

```text
B W R
 =B Q W R+B(I-Q)W R

 =B Q W R+B(I-Q)[W,Q]R.                              (AC.10)
```

Substitution of `(AC.10)` into `(AC.8)` proves `(AC.1)--(AC.4)`.

The three terms have different legal factorizations:

```text
+----------------------+-----------------------------------------------+
| branch               | source factor                                 |
+----------------------+-----------------------------------------------+
| outer boundary       | C[W,E]E with compact displacement support     |
| second support       | (I-Q)[W,Q]R with the same support ledger       |
| prolate leakage      | BQ, whose singular values are |lambda(n)|      |
+----------------------+-----------------------------------------------+
```

They do not have independent quantitative meanings.  Proof 258 constructs an
exact `Q`-preserving model in which the second-support and prolate-like pieces
are `+kappa e_1` and `-kappa e_1`, while their sum is zero, for arbitrary
`kappa`.  Therefore deleting `P_W`, or applying a triangle inequality to
`S_W+P_W`, loses an unbounded cancellation before the renewal even starts.

## 4. The common renewal is mandatory

For fixed finite `S`, Proof 265 proves

```text
0<Gamma<=B,
Delta=B-Gamma,
Gamma^(-1)=sum_(k>=0)Delta^k.                          (AC.11)
```

Combining `(AC.1)` and `(AC.11)` gives `(AC.5)` in trace norm.  In particular,
for every `k`,

```text
Tr_B(N_W Delta^k)
 =Tr_B((O_W+S_W+P_W)Delta^k).                          (AC.12)
```

The allowed and forbidden orders are now:

```text
allowed:
  complete three-branch reward
    -> physical support stopping
    -> common causal renewal or determinant
    -> one absolute value;

forbidden:
  delete K_prol or split branches
    -> trace norms
    -> geometric inverse majorant.                    (AC.13)
```

Proof 265's former suggestion to test the two boundary branches with `K_prol`
omitted has been removed.  It contradicted the exact Proof 258 guard.

## 5. The fixed-S relative determinant is genuine

Proof 264 introduced the formal detector deformation

```text
Gamma_s=K* exp(sW)K,
Gamma_0=Gamma,
B_s=B exp(sW)B,
K=E A B.                                               (AC.14)
```

For real `s` and self-adjoint `W`, `B_s` is positive and invertible.  For a
bounded cross detector, it is invertible in a complex neighborhood of zero.
Define there

```text
mathcalR_s=Gamma_s Gamma^(-1) B_s^(-1).                (AC.15)
```

Equation `(AC.15)` defines a fixed-`S` operator on the source band.  Put

```text
F_s=Gamma_s Gamma^(-1)-B_s.                            (AC.16)
```

Then `F_0=0` and

```text
F_s'
 =[K*D_sK-BD_sB Gamma]Gamma^(-1),

D_s=W exp(sW).                                         (AC.17)
```

The operator `D_s` commutes with the Euler convolution.  Duhamel's formula
gives, for each source projection `J in {E,R,B,Q}` whose detector commutator is
trace class,

```text
[exp(sW),J]
 =integral_0^s exp(tW)[W,J]exp((s-t)W) dt in S1.       (AC.18)
```

Hence the numerator in `(AC.17)` has the same fixed-`S` three-branch trace
factorization as `(AC.1)`.  Proof 261's inverse-closed root-smooth algebra and
the bounded fixed-`S` operator `Gamma^(-1)` make `(AC.17)` trace-norm
continuous.  Integrating from zero gives

```text
F_s in S1,

mathcalR_s-B=F_s B_s^(-1) in S1.                       (AC.19)
```

Therefore

```text
tau_S(s)=det_B(mathcalR_s)                             (AC.20)
```

is a genuine Fredholm determinant near zero, and

```text
partial_s log tau_S(s) at s=0
 =Tr_B(K* W K Gamma^(-1)-B W B)
 =Q_S(eta,xi).                                         (AC.21)
```

Equation `(AC.21)` closes only the fixed-`S` determinant domain.  Bounding
`log tau_S` by `norm(mathcalR_s-B)_1` would repeat the forbidden conditioned
trace-norm estimate.

## 6. Exact causal innovation dilation

After Proof 253's scalar normalization, the causal inverse is the probability
average

```text
A_S=E_omega[U_(X_S(omega))],

X_S=sum_(p in S) N_p log(p),
P(N_p=n)=(1-p^(-1/2))p^(-n/2).                        (AC.22)
```

Let

```text
mathcalH_S=L2(Omega_S;H),
(V_S f)(omega)=U_(X_S(omega))f,
(J f)(omega)=f,
P_0=J J*.                                              (AC.23)
```

Every translation is unitary, so

```text
V_S*V_S=I,
A_S=J*V_S,
I-A_S*A_S=V_S*(I-P_0)V_S.                              (AC.24)
```

Define four channel maps with common input `Ran(B)`:

```text
I_rand=(I-P_0)V_S B,
I_C   =C A_S B,
I_R   =R A_S B,
I_B   =B A_S B.                                        (AC.25)
```

Equations `(AC.24)--(AC.25)` give the exact conservative identity

```text
I_rand*I_rand+I_C*I_C+I_R*I_R+I_B*I_B=B.              (AC.26)
```

Moreover,

```text
Gamma=I_R*I_R+I_B*I_B,
Delta=I_rand*I_rand+I_C*I_C.                           (AC.27)
```

The renewal defect is the Gram operator of two missing channels in one
source-owned conservative system: random Euler innovation and escape across
the outer boundary.

Order the primes and let `P_j` be conditional expectation onto the first `j`
prime coordinates.  Then

```text
I-P_0=sum_j (P_j-P_(j-1))                              (AC.28)
```

is an orthogonal sum of prime martingale differences.  This is the first exact
structure capable of turning mixed-prime cancellation into a square function
without expanding the physical operator into absolute prime words.

Equation `(AC.28)` is not yet the Gate 3U estimate.  A raw variance bound still
sees the half-power probability of a single prime jump.  The complete reward
`O_W+S_W+P_W` must first be shown to kill excursions which do not meet the
compact physical boundary.

## 7. The stopped innovation theorem to prove

The recommended next theorem has three parts.

```text
1. determinant-to-dilation identity:
   rewrite partial_s log tau_S(0) as one pairing between the complete
   three-branch reward and the conservative channels (AC.25);

2. causal stopping identity:
   before an absolute value, cancel every path whose one-sided displacement
   misses the 2 B_root boundary window, including large comparable mixed
   primes;

3. prime square function:
   apply the orthogonal martingale decomposition (AC.28) only to the stopped
   reward, so surviving prime weights are squared or enter a controlled Euler
   product.                                                   (AC.29)
```

The desired conclusion remains

```text
abs partial_s log tau_S(s) at s=0

 <=C(1+B_root)^d
      norm(eta)_(H^r) norm(xi)_(H^r),                 (AC.30)
```

with constants independent of finite `S`.

The stopping clause is essential.  Orthogonality alone does not control pairs
of arbitrarily large comparable primes whose net logarithmic displacement is
small.  The one-sided source geometry must cancel such out-and-back paths before
the prime square function is invoked.

## 8. Why the determinant direction is plausible but not imported

A new primary source has the right algebraic shape:

```text
Leonid Petrov,
A Borodin--Okounkov--Geronimo--Case identity for tilted Toeplitz minors,
arXiv:2605.24976v1 (2026-05-24)
https://arxiv.org/abs/2605.24976
```

Its Theorem 2.4 proves a Jacobi complementary-minor identity for arbitrary
closed oblique splittings.  The paper's main formula puts the tilt into an
oblique projection multiplying one trace-class BOGC kernel, while the ambient
Toeplitz operator remains unchanged.  That is the correct architecture for
keeping the second-support and prolate branches inside one determinant.

Petrov's theorem covers a different determinant.  It assumes an ambient
operator

```text
A=I-K,
K in S1,                                               (AC.31)
```

whereas the route's almost-periodic Euler convolution is not an identity plus
trace-class operator on the whole line.  Section 5.3 of that paper also labels
the finite-dimensional resolvent closure as Conjecture 5.12.  Therefore no
BOGC, IIKS, or Riemann--Hilbert formula may be imported without proving a
source-specific relative version.

The useful lesson is narrower: apply the oblique Jacobi mechanism to the
already legal relative object `mathcalR_s-B in S1`, not to the ambient Euler
operator.  The resulting factorization must reproduce `(AC.1)` when
differentiated; otherwise it has separated the forbidden branches.

## 9. Death conditions

Reject a successor immediately if it produces any of the following:

```text
norm(Gamma^(-1));
norm(N_W)_1/(1-norm(Delta));
norm(O_W)_1+norm(S_W)_1+norm(P_W)_1;
a model with P_W or K_prol deleted;
sum_p p^(-1/2);
sum_(p,q) (p q)^(-1/2) after absolute values;
an almost-periodic Toeplitz determinant without a proved relative S1 domain;
a periodic or finite-section trace cycle which erases the physical anomaly.
                                                               (AC.32)
```

A successful proof must expose one of these source mechanisms before its first
positive majorant:

```text
pathwise compact-support stopping;
orthogonal prime innovation after stopping;
or an equivalent oblique relative-determinant factorization.   (AC.33)
```

## 10. Reproducible certificate

Run from the Windows source snapshot in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/266_three_branch_causal_determinant_probe.py
```

The default certificate reports

```text
+--------------------------------------+----------------+
| check                                | value          |
+--------------------------------------+----------------+
| maximum source/algebra error         | 1.07e-15       |
| relative determinant derivative error| 2.23e-10       |
| renewal final operator error         | 1.78e-15       |
| Gamma lower bound                    | 5.79e-1        |
| norm(Delta)                          | 4.21e-1        |
+--------------------------------------+----------------+
```

The model enforces `(AC.6)--(AC.7)`, causal orientation, and commutation of the
detector with `A` and `A*`.  It verifies `(AC.1)`, `(AC.10)`, every selected
common renewal power, and the finite-dimensional derivative of `(AC.20)`.

The model deliberately proves no continuous estimate.  Its finite causal
operator is nonnormal, while the source whole-line convolution is normal; only
the displayed algebraic relations are being certified.

## 11. Route judgment

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| Proof 265 no-prolate test                      | corrected and rejected       |
| exact three-branch common numerator            | closed                       |
| common fixed-S renewal                         | closed                       |
| fixed-S relative Fredholm determinant          | closed near zero             |
| conservative causal innovation dilation        | exact                        |
| stopped determinant/dilation identity          | open                         |
| uniform prime square-function estimate         | open, Gate 3U                |
| negative-owner integrated smallness            | open                         |
| same-object finite-S trace identity            | open                         |
| Burnol all-zero identity                       | open                         |
| Lean owner or route rewire                     | none                         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

Proof 266 replaces the positive inverse estimate with a conservative
boundary-scattering problem.  The next proof must factor the relative
determinant derivative through a stopped source process, keep all three
physical branches in one reward, and use the product-geometric Euler law
through orthogonal innovations.
