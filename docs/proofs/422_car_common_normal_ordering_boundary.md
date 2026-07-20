# Proof 422: CAR common-normal-ordering boundary

Date: 2026-07-20

Status: exact source-audited rejection of the standard CAR/quasi-free lift of
Proof 421.  A compact-root detector has a centered implementer in each fixed
band representation, but those separately centered observables do not retain
the relative first cumulant owned by Gate 3U.  A translated-half-line model
meets the root-completed trace contract, has identical centered detector laws
at both endpoints, and nevertheless has a strictly positive relative trace
anomaly.

This does not reject every cutoff-before-limit Fisher argument.  It proves that
such an argument must carry one common finite-cutoff normal ordering and prove
the anomaly and Fisher limits together.  Standard Shale--Stinespring
implementability, per-state CAR centering, and the Avron--Bachmann--Graf--Klich
regularized determinant do not supply that theorem under the route's present
hypotheses.

Gate 3U, the finite-`S` sign, the same-object arithmetic identity, Burnol's
identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------------+---------------------------+
| layer                                                | judgment                  |
+------------------------------------------------------+---------------------------+
| fixed-band compact-root detector                    | CAR implementable         |
| centered detector generator                         | unique in each GNS space  |
| additive normal-ordering constant                   | independent at each band  |
| common pure quasi-free representation               | needs `B_t-B_0 in S2`     |
| Avron et al. pure-state transport determinant       | needs raw `S1` change     |
| route's current endpoint contract                   | root-sandwiched `S1` only |
| translated-half-line endpoint states                | disjoint                  |
| centered endpoint detector laws                     | identical                 |
| root-completed relative first moment                | strictly positive         |
| standard CAR/Fisher lift of Proof 421               | rejected                  |
| common-cutoff relative Fisher theorem               | possible, but open        |
| Gate 3U / finite-S sign / Burnol / RH                | open / open / open / open |
+------------------------------------------------------+---------------------------+
```

The obstruction is a first-cumulant obstruction:

```text
fixed-state CAR variance
  -> sees the off-diagonal detector commutator;

relative Gate response
  -> also needs the common normal-ordering phase;

separate vacuum centering
  -> deletes exactly that phase.                         (CN.1)
```

## 2. What fixed-state CAR implementability gives

Let `P` be an orthogonal projection on a separable one-particle Hilbert space
`H`.  It defines a pure gauge-invariant quasi-free state `omega_P` of the CAR
algebra and a GNS triple

```text
(H_P,pi_P,Omega_P).                                    (CN.2)
```

Let `W` be bounded and self-adjoint.  Avron, Bachmann, Graf, and Klich,
Propositions 5--6, state that the one-parameter Bogoliubov group

```text
V_s=exp(i s W)                                         (CN.3)
```

is implementable in `pi_P` precisely under the restricted-unitary condition

```text
P W(I-P) in S2,

equivalently [P,W] in S2.                              (CN.4)
```

There is then a self-adjoint generator `W_hat_P` implementing `(CN.3)`.  It is
defined only up to an additive scalar.  Proposition 6 fixes that scalar by

```text
<Omega_P,W_hat_P^0 Omega_P>=0,                         (CN.5)
```

and the centered generator `W_hat_P^0` is unique.

For any real `c_P`, however,

```text
W_hat_P^(c)=W_hat_P^0+c_P I                            (CN.6)
```

implements exactly the same one-particle automorphism.  Its characteristic
function and first moment are

```text
chi_P^(c)(s)
 =<Omega_P,exp(i s W_hat_P^(c))Omega_P>
 =exp(i s c_P) chi_P^0(s),

-i partial_s chi_P^(c)(0)=c_P.                        (CN.7)
```

Thus `(CN.4)` canonically fixes all centered fluctuation data, but not the
relative first moment between two independently represented seas.

For the route detector

```text
W_(eta,xi)=C_xi* C_eta,                                (CN.8)
```

Proof 261 gives the stronger fixed-band commutator statement

```text
[W_(eta,xi),B_t] in S1 subset S2.                      (CN.9)
```

Therefore fixed-state detector implementability is not the missing theorem.
It already follows from the route's owned root regularity.

## 3. What is needed to compare two pure seas

Let `P,Q` be projections and let `omega_P,omega_Q` be their pure quasi-free
states.  Matsui--Yamagami Theorem 2.1 gives

```text
omega_P and omega_Q are quasi-equivalent
 <-> sqrt(P)-sqrt(Q) in S2
 <-> P-Q in S2.                                       (CN.10)
```

Their Theorem 3.3 gives the accompanying dichotomy: otherwise the
representations are disjoint.

Equivalently, if `Q=U P U*`, Shale--Stinespring implementability of `U` in the
`P` representation requires

```text
[P,U] in S2.                                          (CN.11)
```

The full-counting-statistics theorem of Avron et al. uses a stronger raw
transport condition.  In the pure case its hypothesis `(15)` reduces to

```text
P-U P U* in S1.                                       (CN.12)
```

Under `(CN.12)`, the transport implementer and the detector implementer live in
one representation, and their additive ambiguities cancel inside

```text
U_hat* exp(i s W_hat) U_hat exp(-i s W_hat).           (CN.13)
```

The paper's equations `(6)--(9)` explicitly explain that its determinant
regularization changes only the first cumulant.  That is precisely the
cumulant which is open in the present route.

Proof 261 establishes only

```text
C_eta(B_1-B_0)C_xi* in S1.                            (CN.14)
```

Neither `(CN.10)` nor `(CN.12)` follows from `(CN.14)`.

## 4. Exact translated-half-line guard

The gap between `(CN.14)` and raw quasi-equivalence is already exact in the
physical half-line geometry used by the route.  Work on

```text
H=L2(R),
E=M_(1_[0,infinity)),
(U_b f)(x)=f(x-b),
E_b=U_b E U_b*=M_(1_[b,infinity)),
b>0.                                                   (CN.15)
```

Then

```text
D_b=E-E_b=M_(1_[0,b)).                                (CN.16)
```

The operator `D_b` is an infinite-rank projection.  It is not compact and
hence belongs to neither `S2` nor `S1`.  In particular,

```text
omega_E and omega_(E_b) are disjoint,                 (CN.17)
```

and `U_b` is not implementable in the `E`-sea representation.  Concretely,
the crossing block `E U_b(I-E)` is an isometry between two copies of `L2` of a
nonempty interval, so it cannot be Hilbert--Schmidt.

Now take a nonzero root

```text
g in C_c^infinity(R),
(C_g f)(x)=integral_R g(x-y)f(y)dy.                    (CN.18)
```

The operator `C_g D_b` has kernel

```text
g(x-y)1_[0,b)(y).                                     (CN.19)
```

Fubini gives the exact Hilbert--Schmidt norm

```text
norm(C_g D_b)_2^2
 =integral_(0<=y<b) integral_R abs(g(x-y))^2 dx dy
 =b norm(g)_2^2.                                      (CN.20)
```

Consequently the root-completed relative response is positive trace class:

```text
C_g(E-E_b)C_g*
 =(C_g D_b)(C_g D_b)* in S1,

Tr(C_g(E-E_b)C_g*)=b norm(g)_2^2>0.                  (CN.21)
```

This is the same completed-crossing mechanism as Proofs 260--263.  It proves
directly that a legal nonzero root response does not imply raw `S2` equivalence
of the two sea projections.

## 5. The centered CAR laws are blind to `(CN.21)`

Put

```text
W=C_g* C_g.                                           (CN.22)
```

It is a bounded self-adjoint convolution operator.  Its kernel is

```text
F(x-y),
F=g^star*g in C_c^infinity(R).                        (CN.23)
```

The half-line commutator has kernel

```text
F(x-y)(1_[0,infinity)(y)-1_[0,infinity)(x)).          (CN.24)
```

Therefore

```text
norm([W,E])_2^2
 =integral_R abs(z) abs(F(z))^2 dz<infinity.           (CN.25)
```

The translated projection satisfies the same estimate.  Hence `W` has the
unique centered implementers

```text
W_hat_E^0,
W_hat_(E_b)^0.                                        (CN.26)
```

But `W` commutes with every translation.  Simultaneous conjugation of the
quasi-free state and detector therefore preserves the centered spectral law:

```text
law_(omega_E)(W_hat_E^0)
 =law_(omega_(E_b))(W_hat_(E_b)^0).                   (CN.27)
```

All centered cumulants, every centered relative entropy, and every Fisher
distance built only from the two laws in `(CN.27)` vanish.  On the other hand,
ordinary trace cyclicity is legal in `(CN.21)` and gives

```text
Tr(W(E-E_b))_(root-relative)
 :=Tr(C_g(E-E_b)C_g*)
 =b norm(g)_2^2>0.                                    (CN.28)
```

To force the second centered law to have relative mean `(CN.28)`, one must
replace its implementer by

```text
W_hat_(E_b)^0+b norm(g)_2^2 I.                        (CN.29)
```

Equation `(CN.29)` inserts the desired anomaly as the otherwise arbitrary
constant from `(CN.6)`.  It does not derive or bound it.

The exact mechanism is

```text
translation covariance
  -> identical centered detector laws
  -> zero centered Fisher cost;

root completion
  -> finite nonzero first-cumulant anomaly;

common normal ordering
  -> must choose that anomaly as an extra phase.       (CN.30)
```

## 6. Consequence for Proof 421

Proof 421's finite projection DPP lives on one common finite ground set.  That
ground set fixes the particle-number origin, so its score automatically sees
the first cumulant.  Passing to separately centered infinite CAR
representations changes the object:

```text
finite common DPP score
 != collection of independently centered CAR scores.  (CN.31)
```

The finite inequality

```text
abs(endpoint response)^2
 <=[integrated detector variance]
   [detector-pushforward Fisher action]                (CN.32)
```

remains exact.  What fails is the proposed standard infinite owner of the
second factor.  If its normal-ordering constants are chosen independently,
the half-line guard makes the right Fisher action zero while the left response
is positive.  If the constants are chosen to reproduce the response, that
response has already been inserted into the Fisher action.

Thus a CAR construction can close Gate 3U only if it proves substantially more
than fixed-state implementability: it must construct one root-relative
determinant-line phase and estimate that phase by canonical Euler energy.  This
is another formulation of the open first-cumulant theorem, not a shortcut to
it.

## 7. The surviving cutoff-before-limit contract

The guard does not reject a common finite-cutoff argument.  Let `L` denote a
finite-rank or finite-volume regularization which is applied to every `B_t` in
the same one-particle carrier before forming its DPP.  A valid limit theorem
must prove all three lines together:

```text
1. common-normal-ordering convergence:

   lim_(L->infinity)
     [E_(mu_(1,L))X_(w,L)-E_(mu_(0,L))X_(w,L)]
   =Tr(C_g(B_1-B_0)C_g*);

2. cutoff-independent detector variance:

   limsup_(L->infinity)
     integral_0^1 Var_(mu_(t,L))(X_(w,L))dt
   <=C_root;

3. canonical Fisher-energy estimate:

   limsup_(L->infinity) mathfrakI_(w,L)(B_bullet)
   <=C_lambda (1+B_F)^d E(S_F).                       (CN.33)
```

Trace-class convergence from Proof 261 makes the first line plausible for a
cutoff built directly on the root-completed operator.  It does not construct a
finite projection-DPP approximation whose score satisfies the other two lines.
The translated-half-line guard requires the same cutoff to retain its physical
boundary; translation-covariant centering would erase `(CN.21)`.

Until `(CN.33)` is proved, the active nonprobabilistic target remains Proof
415's completed boundary form, equivalently Proof 416's canonical-family
energy estimate `(EN.7)`.  A proof may use finite Fisher inequalities as a
tool, but it must not cite an independently centered infinite CAR law as their
limit.

## 8. Primary-source boundary

The exact external contracts used here are:

```text
J. E. Avron, S. Bachmann, G. M. Graf, and I. Klich,
Fredholm determinants and the statistics of charge transport,
Theorem 1, Corollary 2, Propositions 5--7, and equations (6)--(9),
https://arxiv.org/abs/0705.0099

T. Matsui and S. Yamagami,
Kakutani dichotomy on free states,
Theorems 2.1 and 3.3,
https://arxiv.org/abs/1203.3581
```

Avron et al. prove fixed-representation implementability under an `S2`
off-diagonal condition and their positive transport determinant under the
stated raw trace-ideal hypotheses.  They do not state a theorem replacing
`P-U P U* in S1` by the externally sandwiched condition `(CN.14)`.

Matsui--Yamagami prove the quasi-equivalence criterion and disjointness
dichotomy.  For projection covariances, their square-root criterion is exactly
`P-Q in S2`; root-sandwiched trace class is not among its alternatives.

## 9. Decision

```text
fixed-band CAR detector implementation:              closed by Proof 261;
per-state centered generator:                        exact, source-backed;
common representation from current route premises:  unavailable;
standard Avron transport determinant:                hypotheses fail;
root-completed response with disjoint seas:           exact `(CN.21)`;
centered-law blindness to the response:               exact `(CN.27)--(CN.30)`;
standard infinite CAR Fisher owner:                   rejected;
common-cutoff relative Fisher contract `(CN.33)`:     open;
direct canonical energy estimate `(EN.7)`:            open;
Gate 3U / finite-S sign / Burnol / RH:                open / open / open / unproved.
```
