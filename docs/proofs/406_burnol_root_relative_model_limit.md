# Proof 406: Burnol root-relative model-limit carrier guard

Date: 2026-07-18

Status: the originally claimed route bridge is withdrawn.  The trace-norm
limit for standard Hardy model projections is valid, but Burnol Theorem 8
identifies the Sonin space only as an abstract de Branges/model space.  It does
not identify the compressed Euler and detector forms on the route's fixed
quotient carrier with the standard truncated-Toeplitz forms used by the finite
BOGC theorem.

Consequently this document does not close the continuous first-jet passage,
Gate 3U, the finite-`S` sign, Burnol's identity, or RH.  The companion probe is
only a certificate for the abstract model-projection lemma.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| standard model-projection S1 limit             | valid                    |
| Burnol Sonin space -> de Branges space         | source theorem           |
| de Branges space -> standard model space       | source-space isometry    |
| route multiplier-form intertwinement           | not proved               |
| fixed quotient -> standard model projection    | not proved               |
| finite BOGC jet -> actual Proof 405 jet         | withdrawn                |
| Basor--Chen raw atomic Euler application        | outside stated contract |
| continuous root-relative determinant estimate  | open                    |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

The missing arrow is not strong convergence.  It is the same-carrier identity

```text
actual compressed multiplier forms on R or E-R
  = standard truncated-Toeplitz multiplier forms on K_Theta.       (RL.1)
```

Without `(RL.1)`, convergence of a different model-space semicommutator cannot
be substituted into the Gate response.

## 2. What Burnol actually identifies

Let `H` be the source Hilbert space, let `E` be the outer support projection,
and let `R<=E` be the source Sonin projection.  The fixed quotient band used by
Proofs 343 and 405 is

```text
P=E-R,
E H=Ran(R) orthogonal-direct-sum Ran(P).              (RL.2)
```

Burnol Theorem 8 identifies the completed Mellin image of `Ran(R)` with the de
Branges space `B(mathscrE_lambda)`.  Division by its Hermite--Biehler structure
function gives the standard source-space isometry

```text
U_R:Ran(R) ->K_Theta,
Theta=mathscrE_lambda^#/mathscrE_lambda.              (RL.3)
```

This is a theorem about `Ran(R)`.  It is not an isometry

```text
E H ->H^2                                             (RL.4)
```

which sends the orthogonal decomposition `(RL.2)` to

```text
H^2=K_Theta orthogonal-direct-sum Theta H^2.          (RL.5)
```

An isometry on one closed subspace does not determine the image of its ambient
orthogonal complement.  Thus `(RL.3)` alone does not represent Proof 405's
quotient projection `P` by either standard projection in `(RL.5)`.

Primary source:

```text
Jean-Francois Burnol,
Sur les espaces de Sonine associes par de Branges a la transformation
de Fourier, Theorem 8,
https://arxiv.org/abs/math/0208121
```

## 3. Why working on the Sonin carrier still needs a theorem

Because the outer carrier is fixed, the endpoint band difference can also be
written as the negative Sonin projection difference:

```text
(E-R_S)-(E-R)=-(R_S-R).                              (RL.6)
```

This avoids extending `(RL.3)` to the quotient only if the isometry also
intertwines every compressed multiplier form needed by the Gram projection.
For the Euler multiplier `tau` and detector `w`, one needs, at minimum,

```text
U_R (R M_a R)|Ran(R) U_R*
 =P_Theta M_(a_model) P_Theta|K_Theta,                (RL.7)

a in {abs(tau)^2, w, w abs(tau)^2}.                  (RL.8)
```

Burnol's isometric norm identity proves `(RL.7)` for `a=1`.  Polarization also
proves it when both multiplied vectors remain in the de Branges space.  It
does not prove `(RL.7)` for a general boundary multiplier: `M_a F` need not
remain in `B(mathscrE_lambda)`.

The issue is visible in CCM24 Section 4.8.  The same set of entire functions
inherits its semilocal norm from

```text
L2(R, ds/abs(E_S(s))^2),                              (RL.9)
```

and the paper explicitly says that the finite set `S` fixes the inner product.
It does not identify the displayed local Euler factor `E_S` with the
Hermite--Biehler structure function of that norm.  Equality of two norms on the
Sonin subspace is therefore not a pointwise equality of their ambient weights
and does not imply `(RL.7)`.

Source:

```text
Connes--Consani--Moscovici,
Zeta zeros and prolate wave operators,
Sections 4.7--4.8, especially Theorem 4.6 and the paragraph following
Proposition 4.14,
https://arxiv.org/html/2310.18423v2#S4.SS8
```

## 4. The valid abstract model-space limit

The following statement from the original draft remains valid.  Let
`Theta_n,Theta` be inner functions whose boundary multiplication operators
converge strong-star:

```text
M_(Theta_n)->M_Theta,
M_(Theta_n)*->M_Theta* strongly.                      (RL.10)
```

On boundary `L2`, define

```text
P_n=P_+-M_(Theta_n)P_+M_(Theta_n)*,
P=P_+-M_Theta P_+M_Theta*.                           (RL.11)
```

If `W` is a boundary multiplier with

```text
H_W=[W,P_+] in S1,                                   (RL.12)
```

then commutativity of boundary multipliers gives

```text
[W,P_n]
 =H_W-M_(Theta_n)H_WM_(Theta_n)*.                    (RL.13)
```

Strong-star multiplication is continuous on a fixed trace-class operator, so

```text
norm([W,P_n]-[W,P])_1 ->0.                            (RL.14)
```

For a bounded `X`, put

```text
C_n=P_n W(I-P_n)X P_n,
C=P W(I-P)X P.                                       (RL.15)
```

The projection identity

```text
P W(I-P)=-P[W,P](I-P)                                (RL.16)
```

and `(RL.10)--(RL.14)` imply

```text
norm(C_n-C)_1 ->0,
Tr(C_n)->Tr(C).                                       (RL.17)
```

This proves a useful topology lemma for a semicommutator already known to live
on the standard model carrier.  It does not prove `(RL.1)` or `(RL.7)` for the
Burnol route.  The companion numerical probe checks only `(RL.11)--(RL.17)`.

Peller's trace-class Hankel theory can supply `(RL.12)` for a sufficiently
smooth compact detector, but it does not supply the missing carrier identity:

```text
V. V. Peller,
The behavior of functions of operators under perturbations,
https://arxiv.org/abs/0904.1761
```

## 5. Why the continuous BOGC sources do not close the gap

Bottcher's model-space BOGC theorem applies to a finite Blaschke model carrier
`K_u` and standard truncated-Toeplitz compressions `P_u M_a P_u`.  Without
`(RL.7)`, its determinant derivative is not the actual Gram derivative on the
route carrier.

```text
Albrecht Bottcher,
Borodin--Okounkov and Szego for Toeplitz operators on model spaces,
Theorem 1.1,
https://arxiv.org/abs/1307.0329
```

Basor--Chen's continuous Wiener--Hopf identity assumes, in its own statement,

```text
F in L1(R) intersect Linfinity(R),
K in L1(R),
integral_R abs(x) abs(K(x)) dx < infinity,
1-F bounded away from zero with index zero.           (RL.18)
```

The finite Euler symbol has translation atoms at `m log(p)`.  Its inverse
Fourier kernel is a discrete measure, not an `L1` function with the first
moment in `(RL.18)`.  Hence that theorem cannot be applied before proving a new
detector-first relative extension and an atomic limiting theorem.

```text
Estelle Basor and Yang Chen,
A Note on Wiener-Hopf Determinants and the Borodin-Okounkov Identity,
formulas (1.3)--(1.6) and the assumptions immediately following them,
https://arxiv.org/abs/math/0202062
```

Bufetov's later continuous BOGC formula weakens the smooth compact-support
assumptions to an `H^(1/2)` contract, but the raw atomic Euler background is
still outside that contract.  It does not state a theorem in which only the
detector direction is trace class:

```text
Alexander Bufetov,
The Expectation of a Multiplicative Functional under the Sine-Process,
Theorem 1,
https://arxiv.org/abs/2412.20902
```

## 6. Exact remaining Gate theorem

The route must stay on the already identified source owner.  For compact roots
`eta,xi` supported in `[-B_root,B_root]`, it still asks for

```text
sup_(finite S)
abs Tr(C_eta(B_S-B)C_xi*)

 <=C(1+B_root)^d
   norm(eta)_(H^r) norm(xi)_(H^r),                   (RL.19)
```

where `B_S` is the actual Gram-corrected finite-`S` band projection.  A valid
determinant proof must first establish one of the following same-object
statements:

```text
actual Burnol compressed forms satisfy `(RL.7)`;

or

the Proof 342 causal quotient Gram has a detector-first relative
Wiener--Hopf/Hankel factorization whose derivative is `(RL.19)`.             (RL.20)
```

The second option must keep the reflected second-support commutator and the
prolate-root leg together.  Applying a trace norm to either branch separately
recreates the rejected half-power sum.

## 7. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| abstract strong-star -> S1 model limit         | valid                    |
| model limit is the actual Burnol Gate owner    | not established          |
| finite BOGC uniform gradient                   | wrong carrier until RL.7 |
| Basor--Chen direct atomic application          | outside source contract  |
| detector-first relative atomic extension       | open                    |
| uniform Gate estimate `(RL.19)`                 | open                    |
| decisive continuous counterexample             | not obtained            |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

Proof 406 is therefore a guard against counting a standard-model topology
lemma as Gate progress.  It supplies neither closure nor a continuous no-go.
