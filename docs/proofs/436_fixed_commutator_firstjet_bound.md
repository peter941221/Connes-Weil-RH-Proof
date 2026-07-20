# Proof 436: fixed-commutator first-jet bound

Date: 2026-07-20

Status: exact Lean reduction of the normalized finite-Euler fixed-quotient
first jet to a bounded sandwich of one fixed source commutator, together with
a mathematical trace-class estimate which is polynomial in the compact-root
support and uniform in every finite visible-prime family.

This closes Proof 435 `(RN.17)` at the mathematical route-evidence level.  It
does not identify the first jet with the nonlinear Burnol endpoint, bound the
endpoint remainder, close Gate 3U, prove the finite-`S` sign, prove Burnol's
identity, or prove RH.

## 1. Verdict

```text
+------------------------------------------------------+----------------------+
| statement                                            | judgment             |
+------------------------------------------------------+----------------------+
| centered root pair = fixed commutator sandwich       | Lean proved          |
| visible-family dependence occurs only through `A_S`  | exact                |
| `norm(A_S) <= 1`                                     | existing Lean theorem|
| nearly-invariant root commutator belongs to `S_1`    | proved mathematically|
| compact-root `S_1` norm has a polynomial bound       | proved mathematically|
| Proof 435 family-uniform estimate `(RN.17)`           | closed mathematically|
| first jet = complete Burnol endpoint                 | false in general     |
| nonlinear endpoint remainder bound                   | open                 |
| Gate 3U / finite-S sign / Burnol / RH                | open                 |
+------------------------------------------------------+----------------------+
```

The reduction is

```text
three physical root branches
  -> one centered root pair                       Proof 435
  -> one fixed source commutator                  Proof 436
  -> one `S_1` norm independent of `S`
  -> polynomial compact-root bound.                         (FC.1)
```

## 2. Exact same-object algebra

On the common logarithmic Hilbert carrier put

```text
P   =sourceSoninProjection,
E   =radialSupportProjection,
B   =E-P,
C   =rootConvolution,
W   =C^* C,
A_S =normalizedFiniteEulerInverse.                         (FC.2)
```

The projection geometry is

```text
P^2=P,       PB=0,       BP=0,                             (FC.3)
```

and Proof 435 gives the literal fixed-quotient first jet

```text
J_S=(CB)^* C P(A_S-I)B.                                   (FC.4)
```

No trace cycle is needed.  Expand only the adjoint and use `(FC.3)`:

```text
J_S
 =B W P(A_S-I)B
 =B W P A_S B
 =B(WP-PW)P A_S B
 =B[W,P]P A_S B.                                         (FC.5)
```

The second equality deletes `P I B=PB=0`.  The fourth uses both `P^2=P` and
`BP=0`.  Equation `(FC.5)` is an operator equality before any trace is taken.
It preserves the complete outer, reflected-second-support, and prolate
cancellation already assembled inside the fixed commutator `[W,P]`.

Lean owns `(FC.5)` through

```lean
centeredDetectorPair_eq_fixedCommutatorSandwich
detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution
sourceBandProjection_comp_sourceSoninProjection_eq_zero
sourceRootCompletedFiniteEulerCorner_eq_fixedCommutatorSandwich
```

in

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSRootCompletedFirstJet.lean.                    (FC.6)
```

## 3. Trace-class upgrade for nearly invariant projections

Proof 376 used the Hitt--Sarason representation of a scalar nearly invariant
Hardy subspace

```text
M=h K_Theta                                             (FC.7)
```

to prove a Hilbert--Schmidt commutator estimate.  The same rank telescope has
a stronger trace-class endpoint.

Let `P_M` be the orthogonal projection onto `M`.  The rank-two Cayley defect
and the power telescope give, for every nonzero integer `n`,

```text
rank([M_(z^n),P_M]) <=2 |n|,
norm([M_(z^n),P_M]) <=1.                              (FC.8)
```

For a finite-rank operator `T`,

```text
norm(T)_1 <=rank(T) norm(T).                          (FC.9)
```

Consequently

```text
norm([M_(z^n),P_M])_1 <=2 |n|.                       (FC.10)
```

If

```text
c(zeta)=sum_(n in Z) c_n zeta^n,
L_1(c)=sum_(n !=0)|n| |c_n|<infinity,                (FC.11)
```

then the trigonometric truncations are Cauchy in `S_1`, converge in operator
norm to the multiplier commutator, and prove

```text
[M_c,P_M] in S_1,
norm([M_c,P_M])_1 <=2 L_1(c).                        (FC.12)
```

This argument is self-contained once `(FC.8)` is available.  It agrees with
Peller's general `B_1^1` characterization of trace-class Hankel operators,
but it does not require importing that characterization as a black box.

## 4. Compact-root Sobolev budget

Let `g` be supported in `[-B_root,B_root]`, let `c` be its Fourier multiplier,
and transfer `c` to the circle by the Cayley boundary coordinate used in
Proof 377.  Cauchy--Schwarz gives

```text
L_1(c)
 <=[
    sum_n (1+n^2)^2 |c_n|^2
   ]^(1/2)
   [
    sum_(n !=0) n^2/(1+n^2)^2
   ]^(1/2).                                           (FC.13)
```

The second factor is universal and finite.  The first is the circle `H^2`
norm already estimated in Proof 377.  Its Cayley derivative calculation and
Fourier Plancherel therefore give

```text
L_1(c)
 <=C (1+B_root)^2 norm(g)_(H^3(R)).                  (FC.14)
```

The selected positive detector is `W=C^*C`.  The Leibniz identity is

```text
[W,P]=C^*[C,P]+[C^*,P]C.                             (FC.15)
```

The adjoint multiplier has the same coefficient functional.  Equations
`(FC.12)--(FC.15)` yield

```text
norm([W,P])_1
 <=4 norm(C) L_1(c)
 <=C_0 (1+B_root)^3 norm(g)_(H^3(R))^2.              (FC.16)
```

The last inequality uses the Fourier multiplier bound

```text
norm(C)<=norm(g)_1
       <=sqrt(2 B_root) norm(g)_2
       <=C(1+B_root) norm(g)_(H^3).                  (FC.17)
```

The exponents are deliberately not optimized.  The route needs a fixed
polynomial, not the sharp Besov embedding constant.

## 5. Uniform first-jet estimate

Lean already proves

```text
norm(A_S)<=1.                                        (FC.18)
```

All other factors in `(FC.5)` are orthogonal projections.  The trace ideal
property and `(FC.16)--(FC.18)` give

```text
norm(J_S)_1
 <=norm([W,P])_1
 <=C_0 (1+B_root)^3 norm(g)_(H^3(R))^2.              (FC.19)
```

Hence the ordinary trace satisfies

```text
abs Tr(J_S)
 <=C_0 (1+B_root)^3 norm(g)_(H^3(R))^2,              (FC.20)
```

with no dependence on `S`.  This is stronger than the support-coupled
canonical-family quantifier requested by Proof 435 `(RN.17)`.

Equation `(FC.20)` does not take a nuclear norm of any renewal atom.  It takes
the trace norm of the one fixed, already recombined commutator `[W,P]` and
only then applies the complete Markov contraction.  Proof 260's signed-trace
guard is therefore respected.

## 6. Why this is not yet Gate 3U

The first jet is the derivative of the fixed-quotient Gram projection at the
identity in the complete direction `A_S-I`.  The completed Burnol endpoint is
a nonlinear Gram-normalized response.  In general,

```text
endpoint response != first jet.                      (FC.21)
```

Proof 416's Bernstein--Szego family is the decisive guard: the fixed detector
commutator has uniformly bounded finite defect while the nonlinear endpoint
response is `2 M r` and grows with `M`.  Thus `(FC.20)` cannot be promoted to
an endpoint estimate by wording or by an unproved trace cycle.

The remaining one-hammer decomposition is

```text
completed Burnol endpoint
  =fixed-commutator first jet
   +root-completed nonlinear remainder.               (FC.22)
```

The first term is now polynomially controlled.  The next theorem must
construct `(FC.22)` on the actual weighted Burnol form and prove

```text
abs(nonlinear remainder)
 <=C_lambda (1+B_root)^d
      P(E(S_F)) norm(g)_(H^r)^2,                     (FC.23)

E(S_F)=sum_(p in S_F)sum_(m>=1) log(p)/(m p^m).
```

Proof 416 already bounds `E(S_F)` polynomially.  Separating the linear term
before invoking the positive quadratic energy also passes Proof 418's exact
half-power guard: no local `O(p^(-1/2))` response is being bounded by an
`O(p^(-1))` charge.

Equation `(FC.23)` is the remaining theorem contract, not a proved estimate.

## 7. Source evidence

```text
Hartmann--Ross, nearly invariant subspaces and truncated Toeplitz operators:
https://arxiv.org/abs/1101.3771

Peller, Besov spaces and Schatten-class Hankel operators:
https://arxiv.org/abs/2402.09853

Connes--Consani, the archimedean Sonin/prolate trace geometry:
https://arxiv.org/abs/2006.13771

Burnol, the de Branges/Sonin carrier:
https://arxiv.org/abs/math/0208121                              (FC.24)
```

The source papers support the carrier and trace-ideal ingredients.  The
same-object reduction `(FC.5)` and its application to the repository's
normalized Euler inverse are project theorems.

## 8. Remaining route

```text
fixed-S trace legality                              CLOSED
root-homogeneous first-jet owner                    CLOSED
centered signed root-pair normal form               CLOSED
fixed-commutator first-jet estimate                 CLOSED mathematically
endpoint = first jet + nonlinear remainder          OPEN
canonical-energy bound for nonlinear remainder      OPEN
Gate 3U / finite-S sign                             OPEN
Burnol identity                                     OPEN
_root_.RiemannHypothesis                            OPEN
```

## 9. Verification

The new Lean declarations are covered by

```text
ConnesWeilRH/Dev/
  CCM24FiniteSRootCompletedFirstJetAudit.lean.        (FC.25)
```

The isolated Ubuntu 24.04 ext4 acceptance batch passes:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| root-completed first-jet focused axiom audit         |  3259 | PASS   |
| CCM25Concrete aggregate                              |  3709 | PASS   |
| full repository                                      |  3790 | PASS   |
+------------------------------------------------------+-------+--------+
```

The focused audit contains `68` `#check` commands and `62` matching
`#print axioms` commands.  The generic centered-commutator identity uses
exactly

```text
[propext].                                             (FC.26)
```

The concrete detector-square, projection-orthogonality, and finite-Euler
commutator-sandwich declarations use exactly

```text
[propext, Classical.choice, Quot.sound].               (FC.27)
```

The new source and audit contain no `sorry`, `admit`, or `sorryAx`, and add no
line longer than 100 characters.  The aggregate and full builds replay only
pre-existing warnings from other modules.
