# Proof 269: Stopped-chirp square function and coordinate-influence guard

Date: 2026-07-15

Status: exact local Euler defect decomposition and coefficient-accounting
correction.  The normalized inverse Euler product has an orthogonal prime
innovation realization.  A former cubic ledger counted the same geometric
coefficient once as event probability and again inside Proof 228's already
weighted chirp operator.  That ledger is not route-owned.

A direct matrix Efron-Stein estimate on the complete endpoint does not reach
this scale.  Leave-one-prime-out screens on three periodic Sonin sections give
root-operator slopes between `-0.50` and `-0.66`, close to the raw
`p^(-1/2)` influence and far from `p^(-1)`.  Periodic sections carry boundary
pollution, so these values form a death screen rather than a continuous lower
bound.

The correct coefficient-weighted chirp square has first-mode scale `p^(-1)`.
Its prime sum diverges.  Gate 3U still needs a compact-support stopping factor
or an equivalent signed concentration estimate after the outer,
second-support, and prolate terms have recombined.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| normalized local inverse as geometric law     | exact                        |
| local defect Fourier series                    | exact                        |
| finite-product defect telescope               | exact                        |
| prime martingale channel decomposition         | exact                        |
| raw endpoint coordinate p^(-1) influence       | rejected in periodic screen |
| coefficient-weighted chirp square p^(-m)       | exact, first mode divergent |
| cubic p^(-3m/2) ledger                         | rejected double count        |
| positive square-energy concentration sum        | exact in Proof 272           |
| signed scalar local coefficient                 | p^(-m/2), exact              |
| complete signed extra half-power                | open, Proof 274 (AK.12)      |
| complete E/R/Q/K_prol channelization           | open, active Gate 3U        |
| finite-S sign and RH                           | unproved                     |
+------------------------------------------------+------------------------------+
```

The active estimate has two stages:

```text
ordered relative Jacobi first jet
  -> complete physical three-branch innovation channel
  -> Proof 228 logarithmic-chirp gain
  -> compact-support stopping
  -> orthogonal prime square function
  -> one absolute value.                                  (AF.1)
```

The order in `(AF.1)` keeps the determinant ordering from Proof 268 and the
three-branch cancellation from Proof 266.

## 2. Normalized local Euler inverse

For one prime set

```text
a_p=p^(-1/2),
L_p=log(p),

b_p(theta)=(1-a_p)/(1-a_p exp(i theta)).                (AF.2)
```

The geometric expansion gives

```text
b_p(theta)
 =sum_(m>=0) nu_p(m) exp(i m theta),

nu_p(m)=(1-a_p)a_p^m.                                  (AF.3)
```

Thus `b_p` is the characteristic function of a geometric random variable on
the nonnegative integers.  It satisfies

```text
|b_p(theta)|<=1,
b_p(0)=1.                                               (AF.4)
```

The scalar normalization in `(AF.2)` leaves transported ranges unchanged.
It removes the Euler condition number from the inverse metric, as proved in
Proof 253.

The local defect has the exact form

```text
d_p(theta):=1-|b_p(theta)|^2

 =2a_p(1-cos(theta))
    /(1-2a_p cos(theta)+a_p^2)                          (AF.5)

 =2a_p/(1+a_p)
   -2(1-a_p)/(1+a_p)
      sum_(m>=1)a_p^m cos(m theta).                     (AF.6)
```

Equation `(AF.6)` separates the scalar fixed mode from the translation modes.
The fixed mode cancels only if the later source factorization retains the
scalar-gauge cancellation proved in Proofs 253 and 257.  Dropping one physical
branch can restore that mode.

## 3. Product defect and prime innovations

Order a finite set as `S={p_1,...,p_n}` and put

```text
A_j(theta)=product_(i<=j)b_(p_i)(L_(p_i) theta),
A_0(theta)=1.                                           (AF.7)
```

Scalar multiplication gives the defect telescope

```text
1-|A_n(theta)|^2

 =sum_(j=1)^n |A_(j-1)(theta)|^2
    [1-|b_(p_j)(L_(p_j)theta)|^2].                     (AF.8)
```

All prefix factors in `(AF.8)` have modulus at most one.  No Euler condition
number occurs.

Proof 266 supplies the operator realization.  On the product probability
space let

```text
(V_S f)(omega)=U_(X_S(omega))f,
X_S=sum_(p in S)N_p log(p),
A_S=J*V_S,
P_0=J J*.                                               (AF.9)
```

Then

```text
I-A_S* A_S=V_S*(I-P_0)V_S.                             (AF.10)
```

Let `P_j` denote conditional expectation onto the first `j` prime variables.
The orthogonal decomposition

```text
I-P_0=sum_j(P_j-P_(j-1))                               (AF.11)
```

turns `(AF.10)` into prime innovation channels.  Equations `(AF.8)` and
`(AF.11)` describe the same loss of the constant-probability covariance in
spectral and probability coordinates.

## 4. Raw endpoint Efron-Stein fails its entry test

Paulin, Mackey, and Tropp prove matrix Efron-Stein inequalities for a centered
matrix-valued function of independent variables.  Their variance proxy is

```text
V_ES=(1/2)sum_j E[(X-X^(j))^2 | Z].                    (AF.12)
```

Theorem 4.2 bounds moments of `X-E[X]` by moments of `(AF.12)`.  It does not
bound the deterministic mean or the ordered relative determinant derivative.
The route needs an identity that places the Gate 3U scalar inside the centered
innovation channels before using that theorem.

The complete finite-S endpoint also fails the stronger coordinate estimate

```text
norm(Response(S)-Response(S without p))
  <=C p^(-1).                                           (AF.13)
```

The companion screen uses the full transported half-line minus Sonin
projection, applies the same compact pre-root read-off as Proof 252, and deletes
one prime from the complete product.  It reports:

```text
+------+----------+-------------+----------------+------------------+
| size | step     | half-box    | root slope     | row residual     |
+------+----------+-------------+----------------+------------------+
|  256 | 0.080000 | 10.240      | -0.583         | 1.26e-2          |
|  512 | 0.080000 | 20.480      | -0.505         | 1.26e-2          |
|  640 | 0.040000 | 12.800      | -0.655         | 2.19e-3          |
+------+----------+-------------+----------------+------------------+
```

The fit uses primes from `29` through `997`.  Box enlargement and grid
refinement retain a half-power-scale influence.  The fixed four-mode witness
also lacks stable `p^(-1)` decay.

Proof 257 explains the limitation: periodic sections do not preserve the
source second half-line under transport.  The table rejects a proof based on
raw endpoint coordinate replacement.  A source proof may still gain the
second half-power after it inserts the real-line crossing formula and keeps the
prolate branch.

## 5. Correct coefficient accounting for Proof 228

Let `I` be the compact pre-root interval.  Proof 228 studies the endpoint after
the Euler coefficient `a_p^m` has already been inserted.  Denote the unweighted
physical endpoint by `Ktilde_(p,m)` and the coefficient-weighted operator by

```text
K_(p,m)=a_p^m Ktilde_(p,m).                             (AF.14)
```

The logarithmic-chirp conjugation gives

```text
norm(K_(p,m))<=C a_p^m=C p^(-m/2).                     (AF.15)
```

Equivalently, the unweighted physical map has an order-one operator-norm bound.
The local geometric law from `(AF.3)` has the same coefficient

```text
nu_p(m)=(1-a_p)a_p^m.                                  (AF.16)
```

The probability dilation represents the coefficient `nu_p(m)` by two
Stinespring legs of size `sqrt(nu_p(m))`.  Equation `(AF.15)` represents the
deterministic term after the coefficient has been multiplied into the physical
kernel.  A square-function proof may use either representation of the
coefficient.  It may not use both.

The route-owned coefficient-weighted square therefore has the scale

```text
norm(K_(p,m))^2
 <=C^2 a_p^(2m)
 =C^2 p^(-m).                                          (AF.17)
```

For `m=1`,

```text
sum_p p^(-1)=infinity.                                  (AF.18)
```

Proof 228 improves the topology from a nondecaying termwise Hilbert-Schmidt
ledger to the harmonic operator square `(AF.17)`.  It does not make the prime
square function summable.

## 6. Rejected cubic surrogate

The former calculation multiplied the event probability in `(AF.16)` by the
square of the already weighted operator in `(AF.15)`:

```text
nu_p(m) norm(K_(p,m))^2
 <=C^2(1-a_p)a_p^(3m).                                 (AF.19)
```

The series in `(AF.19)` converges, including fixed polynomial weights in
`m log(p)`.  Its convergence is a correct scalar fact and an incorrect route
ledger.  It counts `a_p^m` inside `K_(p,m)` and again as `nu_p(m)`.

The companion script keeps `(AF.19)` as a regression guard.  Its output labels
the cubic column `DOUBLE_COUNTED_NOT_ROUTE_OWNED`.  Any successor that recovers
`p^(-3m/2)` must identify a second independent source factor rather than reuse
the local geometric coefficient.

## 7. Positive concentration ledger and signed gap

Proofs 270 and 271 now provide the exact determinant-line channelization.  The
complete reward and first-missing prime rows contain no standalone
`Gamma^(-1)`.  Their local chirp square still has the harmonic scale
`(AF.17)`.

For the positive square energy, compact-root stopping provides a probability
factor.  Its sufficient ledger has the form

```text
sum_p sum_(m>=1)
 (1+m log(p))^(2d) p^(-m) Q_(p,m)(B_root),             (AF.20)
```

where `Q_(S,p,k)(B_root)` bounds the concentration of the residual relative
displacement after the renewal and predictable factors have been retained.
For the first mode, the pointwise estimate

```text
Q_(p,1)(B_root)
 <=C(1+B_root)^c p^(-epsilon)                          (AF.21)
```

with any fixed `epsilon>0` makes the large-prime tail summable.  Small primes
must contribute only a polynomial support cost.  This pointwise estimate is
sufficient and stronger than necessary.

Proof 272 defines the Levy concentration function

```text
Q_h(mu)=sup_x mu((x,x+h])
```

and proves a uniform aggregate bound for this positive square-energy ledger
over the ordered future relative Euler cloud.  The Doob filtration runs from
large primes to small primes, so its
future factor contains the smaller independent prime variables.
Kolmogorov--Rogozin supplies the missing small-interval
probability, and a large/small-prime split proves `(AF.20)` with polynomial
support cost without requiring `(AF.21)` prime by prime.

Proof 273 shows why this positive estimate is not itself a scalar route
estimate.  The source must first pair
the complete outer/second-support/prolate left row with the survivor row and
take the scalar trace.  A positive `H1` norm of the left row cannot see compact
support.  Proof 271's intervening `D^k B A_>p*` must remain inside that signed
pairing.  A raw
leave-one-prime endpoint estimate, matrix Efron-Stein, or the local chirp bound
alone leaves `(AF.18)` unchanged.

Proof 274 audits the surviving scalar coefficient.  Before the complete
physical cancellation it is `a_p^m=p^(-m/2)`, not the square `p^(-m)`.
Thus the `p^(-m)` envelope required by the sufficient signed contract is
precisely the missing extra-half-power theorem `(AK.12)`.

## 8. Literature boundary

Primary references used in this step:

```text
Paulin, Mackey, Tropp,
Efron-Stein Inequalities for Random Matrices,
arXiv:1408.3470, Theorem 4.2.
https://arxiv.org/abs/1408.3470

Petrov,
A Borodin-Okounkov-Geronimo-Case identity for tilted Toeplitz minors,
arXiv:2605.24976v1, Theorem 2.4.
https://arxiv.org/abs/2605.24976
```

Paulin, Mackey, and Tropp control fluctuations around a mean.  Their theorem
does not supply the compact-support concentration factor in `(AF.20)`.

Petrov proves a complementary-minor identity for an ambient operator of the
form `I-K` with `K` trace class.  The whole-line Euler multiplier does not have
that form.  Proof 267 supplies the legal source-specific relative Jacobi
identity; a BOGC or IIKS analysis must start from that relative determinant and
reproduce all three Proof 266 physical branches when differentiated.

The project derives `(AF.2)--(AF.19)` directly.  Proofs 270 and 271 provide the
relative channelization.  No cited source proves `(AF.20)` for the CC20
first-missing row.

## 9. Reproduction

Run in WSL2 from the Windows source snapshot:

```text
python3 -B docs/proofs/269_stopped_chirp_square_function_probe.py

python3 -B docs/proofs/269_stopped_chirp_square_function_probe.py \
  --periodic-size 512 --periodic-step 0.08

python3 -B docs/proofs/269_stopped_chirp_square_function_probe.py \
  --periodic-size 640 --periodic-step 0.04
```

The exact layer checks `(AF.3)`, `(AF.6)`, and `(AF.8)`.  It prints the
coefficient-weighted chirp square beside the convergent cubic double-count
ledger.  The verdict labels the latter as unowned.

The periodic layer imports the Proof 251 and Proof 252 source sections.  It
recomputes the complete product, removes selected primes one at a time, and
fits the root-operator influence.  The script rejects the naive coordinate
route if the periodic fit changes to `p^(-1)` or faster, because such a change
would require a new audit of the finite-section mechanism.

## 10. Route judgment

Proof 269 retains the exact local defect algebra and rejects two shortcuts.  A
raw endpoint Efron-Stein estimate keeps the half-power influence.  Multiplying
the local event probability by Proof 228's coefficient-weighted chirp counts
the same Euler coefficient twice.

The active Gate 3U task is Proof 274 `(AK.12)`: construct the signed scalar
disintegration in Proof 273 `(AJ.14)` and obtain an additional
`p^(-m/2)` from the complete same-object cancellation, or prove a sharper
location-aware stopping theorem for the exact scalar ledger.  Proof 272
controls only the positive square-energy ledger.  The
negative-owner integration, same-object finite-S arithmetic trace identity,
Burnol all-zero identity, and RH remain open.
