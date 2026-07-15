# Proof 267: Relative Jacobi cocycle and lifted shorted covariance

Date: 2026-07-15

Status: exact fixed-`S` determinant refinement of Proof 266.  For each source
projection `J`, the transported metric response is the logarithmic derivative
of a genuine relative determinant `tau_J`.  For the nested pair `R<=E`, the
Gate 3U response is the derivative of the quotient `tau_E/tau_R`.

A source-specific relative Jacobi identity moves `tau_J` to the complementary
inverse-metric covariance without assuming that the ambient Euler operator is
an identity plus trace class.  The nested quotient then has one determinant-line
Schur representation on `B=E-R`.  Its first jet is the ratio of the Markov
shorted covariance and the identity shorted covariance.

The Markov random-unitary dilation identifies those two covariances as the
constant-probability channel and the full probability channel before shorting.
This gives the precise object on which compact-support stopping must act.  A
pure polar or subspace determinant remains invalid because it deletes Proof
264's nonzero Toeplitz central cocycle.

This proof does not establish the stopped compact-support estimate, the
finite-`S` sign, the same-object arithmetic trace identity, Burnol's identity,
a Lean owner, a route rewire, or RH.

## 1. Result first

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| Gate 3L fixed-S trace legality                 | closed by Proof 261          |
| single-J relative determinant                 | exact                        |
| nested determinant quotient tau_E/tau_R       | exact                        |
| source-specific relative Jacobi complement    | exact                        |
| B-shorted covariance first jet                | exact                        |
| full finite-dimensional Schur determinant     | exact certificate            |
| ordinary infinite det_B Schur operator domain | open, unnecessary for first  |
| random-unitary lifted covariance pair         | exact                        |
| pure polar/dilation determinant               | rejected by central cocycle  |
| stopped relative-Jacobi bound                 | open, active Gate 3U         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

The new fixed-`S` owner is

```text
tau_(E/R,S)(s)=tau_(E,S)(s)/tau_(R,S)(s),             (AD.1)

Q_S(eta,xi)
 =partial_s log tau_(E/R,S)(s) at s=0.                (AD.2)
```

The quotient in `(AD.1)` keeps the outer Toeplitz cocycle and the Sonin
correction in one scalar determinant line.  Estimating its two factors
separately remains forbidden.

## 2. One source projection

Let `J` be an orthogonal projection and put

```text
H=T* T,
M=H^(-1)=A* A,
A=T^(-1).                                              (AD.3)
```

The normalized whole-line Euler convolution is normal, and the compact-root
detector `W` commutes with `T`, `H`, `A`, and `M`.  Define the transported
projection

```text
D_J=(J H J+(I-J))^(-1),
J_T=T J D_J J T*.                                      (AD.4)
```

For a detector parameter `s`, put

```text
H_(J,s)=J exp(sW)H J+(I-J),
G_(J,s)=J exp(sW)J+(I-J),

Theta_(J,s)=H_(J,s) D_J G_(J,s)^(-1).                 (AD.5)
```

At `s=0`, `Theta_(J,0)=I`.

## 3. Fixed-S determinant domain

Let

```text
D_s=W exp(sW).                                         (AD.6)
```

The difference before the last inverse in `(AD.5)` satisfies

```text
partial_s[H_(J,s)D_J-G_(J,s)]

 =J D_s H J D_J-J D_s J

 =J D_s(I-J)H J D_J

 =[J,D_s](I-J)H J D_J.                                (AD.7)
```

Proof 261 gives `[W,J] in S1` for `J in {E,R}`.  Duhamel's formula gives

```text
[exp(sW),J]
 =integral_0^s exp(tW)[W,J]exp((s-t)W) dt in S1,

[D_s,J] in S1.                                        (AD.8)
```

Equations `(AD.7)--(AD.8)` make the path trace-norm continuous.  Therefore

```text
Theta_(J,s)-I in S1                                   (AD.9)
```

near zero, and

```text
tau_(J,S)(s)=det(Theta_(J,s))                          (AD.10)
```

is a genuine Fredholm determinant.

The logarithmic derivative is

```text
partial_s log tau_(J,S)(s) at s=0

 =Tr(J W H J D_J-J W J)

 =Tr(W(J_T-J)).                                       (AD.11)
```

The last equality is Proof 262's endpoint identity with fixed-`S` trace
legality from Proof 261.

## 4. The nested determinant quotient

Use

```text
R<=E,
B=E-R.                                                 (AD.12)
```

The transported ranges remain nested, so

```text
B_T=E_T-R_T.                                           (AD.13)
```

Equations `(AD.11)--(AD.13)` give

```text
Tr(W(B_T-B))
 =partial_s log tau_(E,S)(s) at s=0
  -partial_s log tau_(R,S)(s) at s=0

 =partial_s log tau_(E/R,S)(s) at s=0.                (AD.14)
```

This proves `(AD.1)--(AD.2)`.  The quotient is one determinant-line object;
its factors serve as algebraic coordinates, not as two positive estimates.

For `R=0`, `(AD.14)` reduces to the outer-half-line response.  Proof 222 gives

```text
-log(p) sum_(m>=1)p^(-m/2)
  [F(m log(p))+F(-m log(p))].                          (AD.15)
```

Thus `tau_E` contains the genuine finite-prime Toeplitz cocycle.  Any
factorization that replaces it with the determinant of an orthogonal polar
subspace loses `(AD.15)`.

## 5. Relative Jacobi complement without an ambient determinant

Put

```text
Jc=I-J,
M_s=M exp(-sW),
G_s=exp(-sW).                                          (AD.16)
```

Define the complementary relative operator

```text
Mhat_(J,s)=Jc M_s Jc+J,
Mhat_(J,0)=Jc M Jc+J,
Ghat_(J,s)=Jc G_s Jc+J,

Thetahat_(J,s)
 =Mhat_(J,s) Mhat_(J,0)^(-1) Ghat_(J,s)^(-1).          (AD.17)
```

The same commutator calculation as `(AD.7)` proves

```text
Thetahat_(J,s)-I in S1.                               (AD.18)
```

The route does not need an ambient determinant of `exp(sW)H`.  Let

```text
X_s=exp(sW)H,
Y_s=X_s^(-1)=M exp(-sW).                               (AD.19)
```

The block inverse identity for `J direct-sum Jc` is

```text
(Jc Y_s Jc)^(-1) Jc Y_s J
 =-Jc X_s J (J X_s J)^(-1).                           (AD.20)
```

The off-diagonal block `J W Jc` is trace class.  Apply `(AD.20)`, cycle only
that trace-class factor, and subtract the same identity for
`X_s=exp(sW)`.  The logarithmic derivatives of `(AD.5)` and `(AD.17)` agree.
Both determinants equal one at `s=0`, hence

```text
det(Theta_(J,s))=det(Thetahat_(J,s))                   (AD.21)
```

near zero.

Equation `(AD.21)` is the source-specific relative Jacobi complementary-minor
identity.  It uses relative `S1` paths on the two source corners and never
asserts that `H-I` or the Euler convolution is trace class.

## 6. Nesting produces one shorted covariance ratio

The two complements in `(AD.21)` are

```text
E^perp=C,
R^perp=C direct-sum B.                                 (AD.22)
```

For an invertible operator `X`, define its Schur shorting from `C direct-sum B`
to `B` by

```text
Short_B|C(X)

 =B X B
  -B X C(C X C)^(-1)C X B.                            (AD.23)
```

In finite dimensions, block determinant factorization applied to `(AD.21)`
gives

```text
tau_(E/R,S)(s)

 =det_B(
    Short_B|C(M)
    Short_B|C(M_s)^(-1)
    Short_B|C(G_s)
   ).                                                  (AD.24)
```

For the infinite source, `(AD.24)` is an exact determinant-line identity:
the left side defines the relative determinant, and the block calculation
identifies its first jet on `B`.  An ordinary claim that the displayed
operator differs from `B` by `S1` for nonzero `s` would require one further
relative-Schur domain theorem.  Gate 3U only needs the first derivative at
zero, already licensed by `(AD.14)`.

The causal orientation from Proof 264 gives

```text
Short_B|C(M)
 =B A*E A B
 =Gamma.                                               (AD.25)
```

Thus `(AD.24)` is the shorted-covariance form of Proof 266's ordered Gram
response.  It retains the reference shorting `Short_B|C(G_s)`; deleting that
factor would restore the polar-cycle error.

## 7. Lift the two covariances to the Euler probability space

Proof 253 writes the normalized inverse as

```text
A=E_omega[U_(X(omega))].                               (AD.26)
```

On

```text
mathcalH_S=L2(Omega_S;H),
```

define

```text
(Vf)(omega)=U_(X(omega))f,
(J_0f)(omega)=f,
P_0=J_0 J_0*.                                          (AD.27)
```

Then

```text
V*V=I,
A=J_0*V,
M=A*A=V*P_0V.                                         (AD.28)
```

Let

```text
mathcalW_s=I_(Omega_S) tensor exp(-sW).                (AD.29)
```

Every Euler translation commutes with `W`, and `P_0` acts only on the
probability coordinate.  Hence

```text
G_s=V* mathcalW_s V,
M_s=V* P_0 mathcalW_s V.                              (AD.30)
```

Equations `(AD.23)--(AD.30)` identify the active determinant-line ratio as

```text
full lifted covariance, shorted over C
          versus
constant-probability covariance, shorted over C.       (AD.31)
```

This is the determinant-to-dilation identity sought after Proof 266.  The
shorting operation must remain outside the difference; it is nonlinear and
contains the outer, second-support, and prolate cancellation.

## 8. Conservative channel decomposition

Define

```text
I_rand=(I-P_0)V B,
I_C=C A B,
I_R=R A B,
I_B=B A B.                                             (AD.32)
```

Direct multiplication gives

```text
I_rand*I_rand+I_C*I_C+I_R*I_R+I_B*I_B=B,

Gamma=I_R*I_R+I_B*I_B,
Delta=I_rand*I_rand+I_C*I_C.                           (AD.33)
```

The four channels are an exact conservative dilation.  They do not authorize
the polar replacement

```text
K(K*K)^(-1/2).                                         (AD.34)
```

Proof 264's unilateral-shift guard has a positive detector and

```text
Tr(exp(tX)W_0exp(-tX)-W_0)=-i t/2.                    (AD.35)
```

The value in `(AD.35)` is the central Toeplitz cocycle.  Finite sections place
the opposite value at their artificial far boundary.  The lifted covariance
ratio `(AD.31)` must retain this cocycle together with the Sonin shorting.

## 9. Correct stopped-innovation target

Order the primes and let `P_j` denote conditional expectation onto the first
`j` prime variables.  On the lifted space,

```text
I-P_0=sum_j (P_j-P_(j-1))                              (AD.36)
```

is an orthogonal martingale decomposition.

The next theorem must work with the nonlinear shorted ratio in `(AD.31)`:

```text
1. cancel common translation history in the centered relative first jet;

2. apply the 2 B_root support clip to the resulting relative displacement;

3. keep the complete C/R/B/Q response on large comparable-prime residuals,
   then apply (AD.36) and take one absolute value.
                                                               (AD.37)
```

Applying `(AD.36)` to `M` or `I-M` before shorting is invalid.  A raw variance
sees one-prime mass at `p^(-1/2)`, and large comparable prime pairs can have
small net logarithmic displacement.  Compact support clips the reduced
displacement, not each absolute path.  Proof 268 records the exact
common-history guard and the remaining comparable-prime obstruction.

The quantitative target remains

```text
abs partial_s log tau_(E/R,S)(s) at s=0

 <=C(1+B_root)^d
      norm(eta)_(H^r) norm(xi)_(H^r),                 (AD.38)
```

uniformly in finite `S`.

## 10. Literature boundary

The following primary sources support the determinant architecture:

```text
Petrov, A Borodin--Okounkov--Geronimo--Case identity for tilted
Toeplitz minors, arXiv:2605.24976v1
https://arxiv.org/abs/2605.24976

  Theorem 2.4 proves a Jacobi identity for closed oblique splittings under an
  ambient identity-plus-trace-class hypothesis.

Cafasso--Gavrylenko--Lisovyy, Tau functions as Widom constants,
arXiv:1712.08546
https://arxiv.org/abs/1712.08546

  The paper identifies a Fredholm tau function with a Widom constant for
  analytic Riemann--Hilbert jump data on smooth closed curves.
```

Neither source proves `(AD.21)` for the route's almost-periodic whole-line
Euler convolution or supplies the uniform compact-support estimate `(AD.38)`.
Equation `(AD.20)` supplies the missing fixed-`S` relative proof without an
ambient determinant.  The stopping theorem remains a source obligation.

## 11. Death conditions

Reject a successor if it uses any of these steps:

```text
replace tau_E by a polar-subspace determinant;
estimate log tau_E and log tau_R separately;
expand I-P_0 before the physical shorting/stopping identity;
drop Short_B|C(G_s), the reference covariance;
bound Gamma^(-1) or a complete Euler condition number;
invoke an ambient Toeplitz determinant for H-I;
use a periodic finite section to erase the central cocycle.     (AD.39)
```

## 12. Reproducible certificate

Run from the Windows source snapshot in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/267_relative_jacobi_cocycle_probe.py
```

The default certificate reports

```text
+--------------------------------------+----------------+
| check                                | value          |
+--------------------------------------+----------------+
| relative Jacobi determinant error    | 1.54e-15       |
| nested complement quotient error     | 1.80e-15       |
| shorted determinant error            | 2.24e-15       |
| determinant derivative error         | 1.09e-10       |
| causal Short(M)=Gamma error           | 1.34e-16       |
| lifted covariance error              | 6.88e-16       |
| central anomaly boundary error        | 3.80e-14       |
+--------------------------------------+----------------+
```

The probe checks the full finite-dimensional Jacobi and Schur determinant
identities, an independent derivative against the transported nested
projection, the causal shorted-covariance identity, the random-unitary lift,
and the unilateral-shift boundary anomaly.

Finite matrices do not establish the infinite ordinary `det_B` domain in
`(AD.24)` or the uniform estimate `(AD.38)`.  The fixed-`S` determinant owner
and relative Jacobi identity come from `(AD.7)--(AD.21)`.

## 13. Route judgment

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| Proof 266 determinant-to-dilation target      | refined exactly              |
| tau_E/tau_R Gate response                     | closed                       |
| relative Jacobi complement                    | closed for fixed S           |
| causal shorted covariance Gamma               | exact                        |
| lifted full/constant covariance pair          | exact                        |
| pure polar determinant                        | rejected                     |
| compact-support stopping of relative shorting | open, active Gate 3U         |
| prime martingale square function              | waits on stopping            |
| negative-owner integrated smallness           | open                         |
| same-object finite-S trace identity            | open                         |
| Burnol all-zero identity                       | open                         |
| Lean owner or route rewire                     | none                         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

Proof 267 identifies the exact nonlinear object which must receive compact
support: the first jet of a relative Schur shorting between the full lifted
Euler covariance and its constant-probability channel.  Prime orthogonality
enters after that shorting.  The central Toeplitz cocycle remains inside the
same determinant quotient.
