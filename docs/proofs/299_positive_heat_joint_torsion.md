# Proof 299: Positive heat and diagonal joint-torsion cancellation

Date: 2026-07-16

Status: exact fixed-`S` factorization of Proof 298's ordered relative Gram
determinant into a positive symmetric covariance factor and one determinant-
invariant anomaly factor.  The anomaly is generally nontrivial in infinite
dimension, but its first logarithmic derivative vanishes on the route's
diagonal Hermitian response.  Consequently the diagonal Gate 3U endpoint has
an exact positive symmetric determinant owner.  Cross roots are recovered
after the diagonal estimate by complex polarization.

This does not prove the uniform positive symmetric determinant bound, the
finite-`S` sign, the arithmetic same-object identity, negative-owner
integration, Burnol's all-zero identity, or RH.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| ordered relative Gram determinant             | exact / Proof 266           |
| positive symmetric covariance factor          | exact                        |
| central anomaly factor                        | exact I+S1                   |
| anomaly as inverse determinant invariant      | exact                        |
| generic infinite anomaly                      | can be nonzero               |
| finite-section anomaly determinant            | boundary polluted           |
| diagonal source anomaly first jet             | zero by Hermitian reality   |
| diagonal positive determinant owner           | exact                        |
| nonlinear or cross-root anomaly deletion      | forbidden                    |
| uniform positive determinant estimate         | open                         |
| Gate 3U and RH                                | open / unproved              |
+------------------------------------------------+------------------------------+
```

The ownership change is

```text
ordered endpoint determinant
  -> positive symmetric determinant
     times determinant-invariant anomaly
  -> use Hermitian source reality at the first jet
  -> anomaly first jet vanishes on the diagonal
  -> estimate one positive symmetric endpoint owner
  -> recover cross roots by polarization.                    (BJ.1)
```

This is not a finite trace cycle.  The vanishing uses the route's original
self-adjoint endpoint response and fixed-`S` trace-class theorem.

## 2. Three covariance paths

Retain Proof 298's fixed-`S` objects on `Ran(B)`:

```text
Gamma=K* K,
G_s=K* exp(sW) K,
C_s=B exp(sW) B.                                      (BJ.2)
```

For real `s` and `W=W*`, all three displayed covariance factors are positive
and invertible.  Put

```text
A_s=C_s^(1/2),
Gamma_sym(s)=A_s Gamma A_s.                          (BJ.3)
```

The ordered, positive symmetric, and anomaly relative operators are

```text
R_ord(s)=G_s Gamma^(-1) C_s^(-1),

R_sym(s)=G_s Gamma_sym(s)^(-1),

J(s)=Gamma_sym(s) Gamma^(-1) C_s^(-1).               (BJ.4)
```

Direct multiplication gives

```text
R_ord(s)=R_sym(s) J(s).                               (BJ.5)
```

Proof 266 gives `R_ord(s)-B in S1`.  It also gives

```text
G_s-C_s Gamma in S1.                                 (BJ.6)
```

Taking the adjoint of `(BJ.6)` gives `G_s-Gamma C_s in S1`; hence

```text
[C_s,Gamma] in S1.                                   (BJ.7)
```

Functional calculus for the positive invertible `C_s` gives

```text
[A_s,Gamma] in S1.                                   (BJ.8)
```

Since

```text
Gamma_sym(s)-C_s Gamma
 =A_s[Gamma,A_s] in S1,                              (BJ.9)
```

both `J(s)-B` and `R_sym(s)-B` lie in `S1`.  Therefore every determinant in

```text
tau_ord(s)=tau_sym(s) j(s),

tau_ord=det_B(R_ord),
tau_sym=det_B(R_sym),
j=det_B(J)                                            (BJ.10)
```

is a genuine fixed-`S` Fredholm determinant near zero.  Equation `(BJ.10)`
uses multiplicativity only after all three factors are `I+S1`.

## 3. The anomaly is an inverse determinant invariant

Use `C_s=A_s^2`.  The anomaly factor has the exact factorization

```text
J(s)
 =A_s Gamma A_s Gamma^(-1) A_s^(-2)

 =[A_s,Gamma]_mult [Gamma,A_s^2]_mult,               (BJ.11)
```

where

```text
[X,Y]_mult=X Y X^(-1)Y^(-1).                         (BJ.12)
```

Equation `(BJ.8)` makes both multiplicative commutators identity plus trace
class.  Let

```text
d(A_s,Gamma)
 =det_B([A_s,Gamma]_mult).                            (BJ.13)
```

The determinant invariant is antisymmetric and multiplicative in each
variable.  Thus

```text
det([Gamma,A_s^2]_mult)
 =d(Gamma,A_s)^2
 =d(A_s,Gamma)^(-2).                                 (BJ.14)
```

Equations `(BJ.11)--(BJ.14)` prove

```text
j(s)=d(A_s,Gamma)^(-1).                              (BJ.15)
```

Finite matrices force every multiplicative commutator determinant to one.
Equation `(BJ.15)` is not a license to make the same claim in infinite
dimension.  Proof 264's unilateral-shift guard and the determinant-invariant
literature show that an `I+S1` multiplicative commutator may have nonunit
Fredholm determinant.

Primary-source boundary:

```text
Elgart--Fraas, On Kitaev's determinant formula:
https://arxiv.org/abs/2110.00599

Migler, Joint torsion equals the determinant invariant:
https://arxiv.org/abs/1403.4882

Migler, Functional calculus and joint torsion of pairs of almost
commuting operators:
https://arxiv.org/abs/1409.6289
```

Elgart--Fraas give sufficient hypotheses for a multiplicative commutator
determinant to equal one; the route has not proved those hypotheses.  Migler
supplies the determinant-invariant, joint-torsion, functional-calculus, and
variation architecture.  Equations `(BJ.5)` and `(BJ.11)` are direct project
algebra and do not assume a source torsion formula.

## 4. First-jet split

At `s=0`,

```text
C_0=A_0=B,
C_0'=W_B,
A_0'=W_B/2,
G_0'=K* W K.                                         (BJ.16)
```

Define

```text
N_ord=K* W K-W_B Gamma,

N_sym
 =K* W K-(W_B Gamma+Gamma W_B)/2,

N_anom
 =(Gamma W_B-W_B Gamma)/2.                           (BJ.17)
```

Then

```text
N_ord=N_sym+N_anom.                                  (BJ.18)
```

Differentiating `(BJ.4)` gives

```text
R_ord'(0)=N_ord Gamma^(-1),

R_sym'(0)=N_sym Gamma^(-1),

J'(0)
 =N_anom Gamma^(-1)
 =[Gamma,W_B]Gamma^(-1)/2.                           (BJ.19)
```

The determinant invariant in `(BJ.13)` has the opposite first jet:

```text
partial_s [A_s,Gamma]_mult|_(s=0)=-J'(0).            (BJ.20)
```

For every finite heat cutoff `T`, Proof 298's function `phi_T` also gives the
operator identity

```text
N_ord phi_T(Gamma)
 =N_sym phi_T(Gamma)+N_anom phi_T(Gamma).             (BJ.21)
```

The anomaly in `(BJ.21)` need not vanish.  The diagonal cancellation below is
an endpoint statement at `T=infinity`.

## 5. Source Hermitian reality kills the diagonal first jet

Take the route's diagonal detector

```text
W_g=C_g* C_g=W_g*.                                   (BJ.22)
```

Proof 263 gives the original endpoint owner

```text
Q_S(g,g)=Tr(C_g(B_S-B)C_g*) in Real.                 (BJ.23)
```

Proof 265 gives `N_ord in S1` for fixed finite `S`.  Therefore `N_sym` and
`N_anom` in `(BJ.17)` are also trace class.  Since `N_sym=N_sym*` and
`Gamma^(-1)=Gamma^(-1)*`, ordinary `S1` cyclicity gives

```text
Tr(N_sym Gamma^(-1)) in Real.                        (BJ.24)
```

Since `N_anom*=-N_anom`, the same legal cyclicity gives

```text
Tr(N_anom Gamma^(-1)) in i Real.                     (BJ.25)
```

Proofs 264--265 identify `(BJ.23)` with

```text
Q_S(g,g)
 =Tr(N_ord Gamma^(-1))
 =Tr(N_sym Gamma^(-1))
  +Tr(N_anom Gamma^(-1)).                            (BJ.26)
```

The left side and the first term on the right are real, while the last term
is purely imaginary.  Hence

```text
Tr(N_anom Gamma^(-1))=0,                             (BJ.27)

Q_S(g,g)
 =Tr(N_sym Gamma^(-1))
 =partial_s log tau_sym(s)|_(s=0).                   (BJ.28)
```

Equation `(BJ.27)` is the source-specific anomaly cancellation which Proof
264's abstract guard did not have.  It does not assert

```text
j(s)=1,
J(s)=B,
or a zero anomaly for cross roots.                   (BJ.29)
```

Once `(BJ.28)` is bounded uniformly for every compact root `g`, Proof 263's
complex polarization recovers the cross-root Gate 3U bound without support
growth.

## 6. Physical positive heat owner

For diagonal `W`, Proof 293 gives `g_W^left=g_W*` and

```text
N_ord=g_W* K,
N_ord*=K* g_W.                                       (BJ.30)
```

Therefore

```text
N_sym=(g_W* K+K* g_W)/2.                             (BJ.31)
```

Proof 298's heat representation and `(BJ.28)` give the exact real scalar

```text
Q_S(g,g)
 =integral_0^infinity
    Re Tr_B(g_W* K exp(-t Gamma))dt.                 (BJ.32)
```

The physical generator remains

```text
g_W
 =-E W C A iota_B
  -E A R[W,R]iota_B.                                 (BJ.33)
```

The two terms in `(BJ.33)`, and the outer/second-support/prolate expansion of
the Sonin commutator, remain inside the single real part in `(BJ.32)`.  Source
reality does not authorize a branchwise absolute value.

The active endpoint theorem is now

```text
sup_(finite S)
 |partial_s log tau_(sym,S,g)(s)|_(s=0)|

 <=C(1+B_root)^d norm(g)_(H^r)^2,                    (BJ.34)
```

equivalently the same bound for `(BJ.32)`.  This is exactly the diagonal Gate
3U endpoint, not Proof 298's stronger uniform-in-`T` sufficient condition.

## 7. Infinite anomaly guard and scope

Proof 264's shift model has a positive covariance `Gamma`, a positive
detector `W_0`, and

```text
Tr(Gamma W_0 Gamma^(-1)-W_0)=-i t/2.                 (BJ.35)
```

Choose an abstract actual covariance path equal to the symmetric reference.
Then `tau_sym=1`, while the ordered first jet is the pure central anomaly
`-it/4`.  Finite shift sections add `+it/4` at the artificial far boundary
and report zero.

This guard proves that `(BJ.27)` does not follow from positivity, similarity,
or finite determinant calculations.  It follows from the additional route
fact `(BJ.23)`: the same diagonal endpoint response is Hermitian and real.

The guard also forbids extending `(BJ.27)` to nonzero `s`.  Joint torsion may
remain nontrivial even though its first derivative vanishes at the detector
origin.

## 8. Finite certificate

`299_positive_heat_joint_torsion_probe.py` verifies:

```text
the factorization R_ord=R_sym J;
the two-multiplicative-commutator formula for J;
the determinant product and inverse-invariant identities;
the ordered/symmetric/anomaly numerator and endpoint splits;
the finite-T heat split;
the first derivatives of J and the determinant invariant;
diagonal ordered/symmetric trace agreement;
Proof 264's nonzero infinite-boundary anomaly guard.
```

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/299_positive_heat_joint_torsion_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/299_positive_heat_joint_torsion_probe.py \
  --multiplicity 12 --seed 2299 --parameter 0.09 \
  --heat-time 2.4 --anomaly-time 0.9
```

The two cohorts report:

```text
+--------------------------------------------+-------------+-------------+
| diagnostic                                 | default     | alternate   |
+--------------------------------------------+-------------+-------------+
| maximum exact error                        | 2.38e-10    | 1.69e-10    |
| ordered factorization error                | 2.38e-16    | 1.87e-16    |
| anomaly two-commutator error               | 1.98e-15    | 2.00e-15    |
| endpoint jet split error                   | 2.81e-16    | 3.00e-16    |
| ordered/symmetric trace error              | 7.07e-19    | 3.85e-19    |
| finite anomaly trace                       | 4.44e-16    | 4.44e-16    |
| generic physical central anomaly           | 1.75e-1     | 2.25e-1     |
| finite total generic anomaly               | 2.33e-14    | 3.03e-14    |
+--------------------------------------------+-------------+-------------+
```

The finite source-shaped certificate checks algebra and diagonal reality.  It
does not prove the uniform estimate `(BJ.34)`.  The shift guard supplies the
independent infinite-dimensional rejection evidence.

## 9. Route judgment

Proof 299 replaces Proof 298's stronger truncated-time target by the exact
diagonal endpoint owner `(BJ.28)--(BJ.34)`.  It also identifies precisely why
this does not repeat the forbidden polar cycle:

```text
generic ordered determinant:
  positive factor times joint-torsion anomaly;

route diagonal first jet:
  original Hermitian response is real
  -> anomaly jet is simultaneously real and purely imaginary
  -> anomaly jet is zero;

nonlinear or cross-root determinant:
  anomaly factor remains and must not be deleted.                  (BJ.36)
```

The next analytic attack is the positive symmetric determinant derivative
`(BJ.34)`, with the complete generator `(BJ.33)` inserted before compact
support and before one absolute value.  Gate 3U, the finite-`S` sign,
arithmetic same-object identity, negative-owner integration, Burnol identity,
and RH remain open.  No Lean owner or route rewire is authorized.

## 10. Successor: Proof 300

Proof 300 normalizes the killed Gram frame by

```text
V=K Gamma^(-1/2),
P_S=V V*.
```

It reads `(BJ.34)` back as the original projection response

```text
partial_s log det(R_sym(s))|_(s=0)
 =Tr(W_g(P_S-B)).
```

This equality follows through the already legal source scalar, not by cycling
two non-trace-class polar terms.  An exact two-dimensional commuting guard has

```text
Tr(W_-(P_a-B))=-a/(1+a^2),
Tr(W_+(P_a-B))=+a/(1+a^2),
a=p^(-1/2),
```

with both `W_+` and `W_-` strictly positive.  Therefore positivity supplies
neither a sign nor the missing `p^(-1)` gain.  The active analytic work returns
to Proof 277's complete Sonin Toeplitz covariance `(AN.13)` inside Proof 283's
signed moving-band owner `(AT.18)`.  See
`docs/proofs/300_positive_polar_no_gain_guard.md`.
