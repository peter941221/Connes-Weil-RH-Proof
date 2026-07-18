# Proof 350: Julia graph prime-square gain

Date: 2026-07-18

Status: exact condition-number-free one-factor orthogonalization for every
current closed subspace and every unitary translation.  After applying one
Euler inverse factor, the new range is a graph whose squared angle is bounded
by `1/(p-1)`.  The proof is the defect identity of a unitary Julia colligation;
it resums every power of the prime before taking a norm and is independent of
all other primes and of prime-log spacing.

This supplies the missing half-power at the level of the orthogonalized range
angle.  It does not yet prove that the complete compact-root
outer-minus-Sonin-prolate scalar is a Bessel pairing of these angles.  Linear
off-diagonal detector terms remain possible until that same-object innovation
identity is constructed.  Gate 3U, the finite-`S` sign, Burnol's identity, and
RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| one inverse Euler factor                      | complete graph formula    |
| internal compressed inverse                   | absent from graph bound  |
| Julia transfer defect                         | exact                     |
| squared Grassmann angle                       | <=1/(p-1)                |
| dependence on earlier primes/subspace         | none                      |
| dependence on prime-log separation            | none                      |
| near cumulative angle ledger                  | <=L(1+L)                 |
| complete detector Bessel pairing              | open, next theorem       |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

The corrected square-gain order is

```text
current orthogonal subspace P
  -> apply the complete factor (I-aU)^(-1)
  -> solve its exact graph Riccati equation
  -> use the Julia defect identity
  -> normalize the graph to an isometry
  -> obtain the a^2/(1-a^2) angle budget
  -> only then pair the completed detector innovations.          (JG.1)
```

Proof 268 used the Markov covariance defect `I-A_a* A_a`, whose norm is
`O(a)`.  The object below is different: it is the squared angle between the
old range and the Gram-corrected new range.  Its scale is `O(a^2)`.

## 2. One-factor graph

Let `P` be an orthogonal projection on a Hilbert space `H`, put `Q=I-P`, and
let `U` be unitary.  Relative to

```text
H=Ran(P) orthogonal-direct-sum Ran(Q),
```

write

```text
U=[[U_00,U_01],
   [U_10,U_11]].                                      (JG.2)
```

Fix `0<a<1` and set

```text
T_a=I-aU.                                             (JG.3)
```

The scalar Euler normalization `1-a` is omitted because it does not change a
range.  Since `norm(aU)<1`, `T_a` is boundedly invertible.

The transported subspace is exactly the graph

```text
T_a^(-1)Ran(P)=Graph(X_a),

X_a=a(I-aU_11)^(-1)U_10.                             (JG.4)
```

Indeed a vector `y=(x,Xx)` lies in the left side exactly when the `Q` component
of `T_a y` vanishes.  That condition is

```text
Xx-a(U_10x+U_11Xx)=0,                                (JG.5)
```

whose unique solution is `(JG.4)`.  This is a range identity; no norm of
`(I-aU_11)^(-1)` is taken.

## 3. Julia transfer defect

Define the transfer contraction

```text
Phi_a
 =U_00+a U_01(I-aU_11)^(-1)U_10.                    (JG.6)
```

For `x in Ran(P)`, put

```text
v=(I-aU_11)^(-1)U_10x.                               (JG.7)
```

Equations `(JG.6)--(JG.7)` are equivalent to the exact colligation relation

```text
U(x,a v)=(Phi_a x,v).                                (JG.8)
```

Unitarity of `U` now gives

```text
norm(x)^2+a^2 norm(v)^2
 =norm(Phi_a x)^2+norm(v)^2.                         (JG.9)
```

Therefore

```text
I-Phi_a*Phi_a

 =(1-a^2)U_10*(I-aU_11*)^(-1)
             (I-aU_11)^(-1)U_10,                    (JG.10)
```

and, using `(JG.4)`,

```text
X_a*X_a
 =a^2/(1-a^2) [I-Phi_a*Phi_a]
 <=a^2/(1-a^2) P.                                    (JG.11)
```

Equation `(JG.11)` is the square gain.  A potentially large resolvent has
disappeared into the defect of a contraction.

The colligation calculation is elementary and self-contained.  It is the
standard transfer-function defect identity used in unitary realization theory;
the de Branges--Rovnyak kernel version is discussed in:

```text
Ball--Bolotnikov, de Branges--Rovnyak spaces: basics and theory,
unitary colligations and observability kernels, arXiv:1405.2980:
https://arxiv.org/abs/1405.2980
```

## 4. Gram-normalized angle

Put

```text
C_a=(I+X_a*X_a)^(-1/2),
S_a=X_a(I+X_a*X_a)^(-1/2),
V_a=[C_a;S_a].                                       (JG.12)
```

Then

```text
V_a*V_a=P,
Ran(V_a)=T_a^(-1)Ran(P),
P_a=V_aV_a*.                                         (JG.13)
```

Thus `P_a` is the actual Gram-corrected transported projection.  Since the
function `t/(1+t)` is bounded above by `t` on positive operators,

```text
S_a*S_a
 =X_a*X_a(I+X_a*X_a)^(-1)
 <=X_a*X_a
 <=a^2/(1-a^2)P.                                     (JG.14)
```

For an Euler prime, `a=p^(-1/2)`, so

```text
S_p*S_p<=1/(p-1) P.                                  (JG.15)
```

No lower bound for the transported Gram and no Euler condition number occurs.

## 5. Sequential complete product

Order the finite prime set arbitrarily.  Start from any closed subspace
`K_0`, and recursively define

```text
K_j=(I-p_j^(-1/2)U_(log p_j))^(-1)K_(j-1),
P_j=projection onto K_j.                             (JG.16)
```

Apply Sections 2--4 with `P=P_(j-1)`.  The unitary is still the genuine
translation `U_(log p_j)`, while every earlier Euler factor is already inside
the current subspace.  Hence `(JG.15)` holds at every step, independently of:

```text
the shape of K_(j-1);
the number and condition of earlier factors;
whether log(p_j) is close to another prime log;
the order of the commuting Euler factors.            (JG.17)
```

This sequential statement is stronger than applying `(JG.11)` only to the
source half-line.  It is a complete-product reorthogonalization rule.

## 6. Polynomial near ledger

For a displacement cutoff `L`, define the Julia angle budget

```text
mathcalJ_S(L)
 =sum_(p in S,log(p)<=L) log(p)/(p-1).                (JG.18)
```

The resolvent in `(JG.4)` has already resummed all repetitions of the prime:

```text
1/(p-1)=sum_(m>=1)p^(-m).                            (JG.19)
```

Every prime in `(JG.18)` satisfies `p<=exp(L)`.  Enlarge primes to integers,
put `N=floor(exp(L))`, and use the harmonic bound:

```text
mathcalJ_S(L)
 <=sum_(2<=n<=N)log(n)/(n-1)
 <=L sum_(1<=k<N)1/k
 <=L(1+L).                                           (JG.20)
```

This is the same polynomial support cost as Proof 344, with the harmless
larger geometric ledger `(JG.19)` replacing the exact logarithmic weight
`p^(-m)/m`.

For the short prime clusters of Proof 348, `(JG.18)` remains asymptotic to
`log(1+epsilon)`, while the prematurely root-smoothed linear crossing Gram is
of order `X/log(X)`.

## 7. Why the angle budget is not yet Gate 3U

The projection `P_a=V_aV_a*` has off-diagonal blocks linear in `S_a`.  For a
bounded detector `W`, the difference

```text
Tr[W(P_a-P)]                                         (JG.21)
```

can therefore have a first-order `O(a)` term.  Equation `(JG.15)` alone does
not turn every signed detector response into `O(a^2)`.  Claiming otherwise
would contradict the one-factor first variation already visible in Proofs 224
and 253.

The gain becomes usable only if the complete endpoint scalar is first written
as one Bessel pairing of orthogonal Julia innovation slots.  Schematically,
the required identity has the form

```text
Q_S(eta,xi)
 =sum_(p in S)
   <detector_innovation_(p,eta,xi), range_sine_p>,    (JG.22)
```

where the cascade dilation makes the prime slots orthogonal and proves

```text
sum_p [log(p)]^(-1)
  norm(detector_innovation_p)^2

 <=C(1+B_root)^d
   norm(eta)_(H^r)^2 norm(xi)_(H^r)^2.               (JG.23)
```

Together, `(JG.15)`, `(JG.18)`, and `(JG.23)` would permit one final
Cauchy--Schwarz inequality with polynomial cost.

The phrase `detector_innovation` in `(JG.22)--(JG.23)` is not a stored object.
It must be constructed from the literal Proof 343 quotient owner and must keep
the following bracket whole:

```text
outer boundary
  -Sonin boundary
  +prolate correction
  +Proof 335 half-density cancellation.              (JG.24)
```

Proof 340's ownership guard also requires the canonical and boundary-anomaly
terms to be present in `(JG.22)`.  A direct sum of branch trace norms is not the
required Bessel pairing.

## 8. Relation to the previous Markov obstruction

Proof 268 computes, for the probability-normalized scalar multiplier

```text
A_a(theta)=(1-a)/(1-a exp(i theta)),
```

that

```text
norm(I-A_a*A_a)=4a/(1+a)^2=O(a).                     (JG.25)
```

There is no contradiction with `(JG.11)`:

```text
I-A_a*A_a:
  ambient Markov covariance loss before range orthogonalization;

X_a*X_a:
  squared graph angle after the complete inverse factor and
  canonical Gram correction.                         (JG.26)
```

Proof 268 correctly rejects using `(JG.25)` as a square gain.  Proof 350
supplies that gain on a different, projection-owned object.

## 9. Reproducible certificate

The companion WSL2 script checks:

```text
the exact graph range against the direct frame projection;
the Julia colligation relation;
the transfer defect identity `(JG.10)`;
the graph square identity `(JG.11)`;
the bound `(JG.14)` for several prime coefficients;
the Proof 348 cluster Gram against `(JG.18)`.          (JG.27)
```

Run without a Lean build:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/350_julia_graph_prime_square_gain_probe.py
```

The cluster table is an arithmetic/linear-algebra certificate.  It does not
construct the continuous detector innovations in `(JG.22)`.

## 10. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| one-factor graph Riccati identity             | exact                     |
| Julia transfer defect                         | exact                     |
| post-Gram prime square gain                    | exact                     |
| uniform near angle budget                     | polynomial                |
| raw Markov O(p^-1/2) guard                    | respected                 |
| source detector innovation identity            | open `(JG.22)`            |
| detector Bessel bound                          | open `(JG.23)`            |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
