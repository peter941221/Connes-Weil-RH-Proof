# Proof 425: central extension and boundary-completion guard

Date: 2026-07-20

Status: exact finite boundary-completion algebra in Lean, together with an
infinite-dimensional strong-limit counterexample for the actual compact-root
convolution detector.  A finite multiplicative commutator has determinant
one, while equal-rank cutoff responses can converge to different values under
the same strong endpoint limits.  The missing scalar is therefore a chosen
normal-ordering boundary datum, not a consequence of finite determinant
algebra or strong convergence.

This closes the proposed central-extension shortcut as an independent route
to Proof 416 `(EN.7)`.  It does not reject the already fixed physical
outer-minus-Sonin relative trace, and it does not prove the estimate for that
trace, Gate 3U, the finite-`S` sign, Burnol's identity, or RH.

## 1. Result

```text
+--------------------------------------------------+---------------------------+
| layer                                            | judgment                  |
+--------------------------------------------------+---------------------------+
| finite removed-versus-padding trace ledger       | exact, Lean-owned         |
| equal-rank response                              | rank times charge mismatch|
| finite multiplicative-commutator determinant     | exactly one, Lean-owned   |
| strong-limit continuity of root-relative trace   | false                     |
| translation-covariant padding                    | erases physical anomaly   |
| high-frequency escaping padding                  | retains physical anomaly  |
| cutoff-independent normal-ordering scalar        | not selected by topology  |
| central extension as bookkeeping                 | valid after datum chosen  |
| central extension as Proof 416 estimate          | rejected                  |
| Proof 416 `(EN.7)` / Gate 3U                     | open / open               |
| finite-`S` sign / Burnol / RH                    | open / open / unproved    |
+--------------------------------------------------+---------------------------+
```

The logical distinction is

```text
physical polarization + completed root trace
  -> one already defined relative anomaly;

finite equal-rank cutoffs + strong convergence
  -X-> a canonical value for that anomaly;

central extension
  -> packages the chosen anomaly
  -X-> bounds it by the canonical Euler energy.       (NC.1)
```

Proof 425 concerns the second and third lines.  The route must keep using the
first line, namely Proof 415's completed boundary semicommutator.

## 2. Exact finite boundary replacement

Let `X` be a finite orthonormal coordinate set and let `P_A` denote the
coordinate projection onto `A subset X`.  Split a source cutoff into retained
and removed modes, then replace the removed modes by padding modes:

```text
source = retained union removed,
target = retained union padding.                       (NC.2)
```

Assume the displayed unions are disjoint.  For an arbitrary detector matrix
`W`, direct diagonal readback gives

```text
Tr[W(P_source-P_target)]
 =sum_(x in removed) W_(x,x)
  -sum_(x in padding) W_(x,x).                         (NC.3)
```

The common retained block cancels before any estimate.  If

```text
card(removed)=card(padding)=b,
W_(x,x)=kappa on removed,
W_(x,x)=lambda on padding,                              (NC.4)
```

then

```text
Tr[W(P_source-P_target)]=b(kappa-lambda).               (NC.5)
```

Thus equal rank alone has no preferred response:

```text
lambda=kappa  -> response=0;
lambda=0      -> response=b kappa;
general lambda -> an arbitrary boundary counterterm.    (NC.6)
```

For two padding choices `padding_1,padding_2`, the new Lean theorem also
proves the exact difference

```text
response(padding_1)-response(padding_2)
 =charge(padding_2)-charge(padding_1).                  (NC.7)
```

Equation `(NC.7)` is the finite normal-ordering ambiguity.  It is not an
approximation and does not use positivity, translation covariance, or a
determinant.

## 3. Why finite central extensions cannot repair it

Let `A,B` be invertible finite matrices.  Multiplicativity of the ordinary
determinant gives

```text
det(A B A^(-1) B^(-1))=1.                              (NC.8)
```

This is formalized by

```text
det_multiplicativeCommutator_eq_one.
```

A nontrivial Toeplitz determinant invariant is possible in infinite
dimension precisely because the four individual factors need not be
determinant class while their multiplicative commutator is `I+S_1`.  A finite
section adds an artificial far boundary, and `(NC.8)` forces its anomaly to
cancel the physical anomaly.

Consequently, finite determinant algebra cannot choose between the values in
`(NC.6)`.  The missing value has to enter through a polarization, a boundary
condition, or an explicitly proved renormalized limit.

## 4. Strong convergence still does not choose the value

The ambiguity survives the infinite-dimensional limit.  Let `H` be a
separable Hilbert space, let `W>=0` be bounded, and choose a unit vector `u`
with

```text
kappa=<u,Wu>>0.                                        (NC.9)
```

For any unit sequence `v_n` converging weakly to zero, the rank-one
projections

```text
P=|u><u|,
Q_n=|v_n><v_n|                                         (NC.10)
```

satisfy

```text
Q_n ->0 strongly,
rank(P)=rank(Q_n)=1,
Tr[W(P-Q_n)]=kappa-<v_n,Wv_n>.                         (NC.11)
```

The first statement follows because

```text
norm(Q_n x)=abs(<v_n,x>) ->0                           (NC.12)
```

for every fixed `x`.  Hence two weakly escaping sequences with different
limiting `W`-charges give the same strong projection endpoints `(P,0)` but
different relative trace limits.

This is not a pathology of an unrelated detector.  It occurs for the route's
root convolution.

## 5. The actual compact-root detector has both completions

Take nonzero `g in C_c^infinity(R)` and put

```text
C_g f=g*f,
W_g=C_g* C_g>=0.                                      (NC.13)
```

Choose a compactly supported unit vector `u` with

```text
kappa=<u,W_g u>=norm(C_g u)_2^2>0.                    (NC.14)
```

Write `T_a` for physical translation and `M_xi` for frequency modulation.
The convolution detector commutes with translation, so for `a_n ->infinity`,

```text
v_n^cov=T_(a_n)u,
<v_n^cov,W_g v_n^cov>=kappa.                          (NC.15)
```

Choose `a_n` so the translated supports escape the support of `u`.  Then
`v_n^cov` converges weakly to zero and is orthogonal to `u` for all large
`n`.  Equations `(NC.11)` and `(NC.15)` give

```text
Tr[W_g(P-Q_n^cov)]=0.                                 (NC.16)
```

This is the translation-covariant far-boundary cancellation from Proof 424.

For a detector-invisible completion, also choose `abs(xi_n)->infinity` and set

```text
v_n^inv=T_(a_n)M_(xi_n)u.                             (NC.17)
```

Fourier diagonalization gives, up to the fixed Fourier normalization,

```text
<v_n^inv,W_g v_n^inv>
 =integral_R abs(g_hat(zeta))^2
      abs(u_hat(zeta-xi_n))^2 dzeta.                  (NC.18)
```

Because `g` is compactly supported and smooth, `g_hat` is bounded and tends
to zero at infinity.  Dominated convergence after the change of variable
`eta=zeta-xi_n` yields

```text
<v_n^inv,W_g v_n^inv> ->0.                            (NC.19)
```

The spatial translations again make `v_n^inv` weakly escaping and disjoint
from the physical mode.  Therefore

```text
Q_n^cov ->0 strongly,
Q_n^inv ->0 strongly,

lim_n Tr[W_g(P-Q_n^cov)]=0,
lim_n Tr[W_g(P-Q_n^inv)]=kappa.                       (NC.20)
```

Both cutoff paths have rank one at every `n` and the same strong endpoints.
The only difference is the detector charge carried by the escaping padding.
This proves

```text
strong convergence + equal rank
  -X-> cutoff-independent root-relative trace.        (NC.21)
```

The operator-theoretic reason is that a nonzero translation-invariant
convolution on `L2(R)` is not compact.  Strong convergence tests fixed
vectors; the trace in `(NC.20)` also sees mass escaping through a noncompact
detector.

## 6. Literature boundary

The determinant-invariant literature supplies an architecture, not the
missing cutoff selection or Gate estimate.

```text
Joseph Migler,
Joint torsion equals the determinant invariant,
https://arxiv.org/abs/1403.4882

  determinant invariants and joint torsion are defined for almost
  commuting Fredholm operators under their stated ideal hypotheses;

Joseph Migler,
Functional calculus and joint torsion of pairs of almost commuting operators,
https://arxiv.org/abs/1409.6289

  the abstract variation and functional-calculus results start from
  trace-class commutators;

Alexander Elgart and Martin Fraas,
On Kitaev's determinant formula,
https://arxiv.org/abs/2110.00599

  gives sufficient hypotheses for a multiplicative-commutator
  determinant to equal one;

Leonid Petrov,
A Borodin-Okounkov-Geronimo-Case identity for tilted Toeplitz minors,
https://arxiv.org/abs/2605.24976

  assumes A=I-K with K trace class and keeps the tilt in an oblique
  projection multiplying that trace-class kernel;

Alexander I. Bufetov,
The Expectation of a Multiplicative Functional under the Sine-Process,
https://arxiv.org/abs/2412.20902

  treats the ordinary sine projection under a real-line H^(1/2)
  symbol contract and a continuous Hankel-product determinant.             (NC.22)
```

The route has a different ideal contract:

```text
C_eta(B_S-B)C_xi* in S_1,                             (NC.23)
```

after the root and the outer-minus-Sonin subtraction are assembled.  It does
not have a raw Euler background `I+S_1`, a raw half-line Hilbert--Schmidt
crossing, or a real-line `H^(1/2)` norm for the almost-periodic Euler
logarithm.  None of the cited theorems upgrades `(NC.23)` to those stronger
premises.

## 7. Relation to the existing determinant lane

Proofs 299--300 already identify what a central extension can do at the
diagonal source first jet:

```text
ordered relative determinant
 =positive symmetric determinant
   times central anomaly;

Hermitian diagonal response
 -> central-anomaly first jet is both real and purely imaginary
 -> central-anomaly first jet is zero;

positive symmetric first jet
 =the original completed projection response.         (NC.24)
```

Proof 417 then gives an exact rank-one guard: positivity of the symmetric
determinant does not bound its gradient without paying a compression entropy,
and the raw continuous Euler entropy is not Fredholm-legal.  Proofs 420--424
do not change that conclusion; they test determinant-line, DPP, CAR, and
common-cutoff attempts to construct the missing localized entropy.

Thus introducing a central extension after Proof 424 returns the route to an
already known scalar:

```text
central phase first jet=0,
Quillen/positive first jet=Lambda_(S_F)(F).            (NC.25)
```

It supplies no inequality for `Lambda`.

## 8. Exact successor

The direct active target remains Proof 416:

```text
abs Lambda_(S_F)(F)
 <=C_lambda (1+B_F)^d P(E(S_F))
      norm(F)_(R_(B_F)^r),                            (NC.26)

Lambda_(S_F)(F)
 =Tr[
   G_(S_F)^(-1) mathcalB_(h_(S_F))(w_F)
   -G_0^(-1) mathcalB_(h_0)(w_F)].                    (NC.27)
```

A determinant formulation is useful only if it proves all four additional
facts, rather than naming them:

```text
1. construct a relative Fredholm object directly from the completed
   root-sandwiched E/R difference;

2. prove independence from admissible cutoffs after the physical Hardy
   polarization, not from strong convergence alone;

3. differentiate it and recover every outer, reflected-second-support,
   and prolate term in `(NC.27)`;

4. prove a positive Hessian or mixed-gradient bound by the canonical
   Euler energy, uniformly in S_F.                    (NC.28)
```

Without line 4, a central extension is only bookkeeping.  Without lines 1--3,
it changes the route scalar by an unproved normal-ordering counterterm.

## 9. Lean owner and verification

The new source module is

```text
ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCentralAnomalyGuard.
```

It exports

```text
boundaryCompletion_response_eq_removed_sub_padding;
equalCard_boundaryCompletion_response_eq_card_mul_sub;
boundaryCompletion_response_sub_eq_paddingDifference;
det_multiplicativeCommutator_eq_one.                  (NC.29)
```

The batched WSL2 checks pass as follows:

```text
+------------------------------------------+-------+--------+
| target                                   | jobs  | result |
+------------------------------------------+-------+--------+
| CCM24FiniteSCentralAnomalyGuardAudit     | 1406  | pass   |
| CCM25Concrete aggregate                  | 3701  | pass   |
| full repository                          | 3782  | pass   |
+------------------------------------------+-------+--------+
```

Each declaration uses exactly

```text
[propext, Classical.choice, Quot.sound].               (NC.30)
```

The infinite strong-limit counterexample is the analytic calculation
`(NC.9)--(NC.20)`; no floating-point experiment is needed.  No `sorry`,
`admit`, `sorryAx`, new project axiom, or new linter warning was introduced.

## 10. Route judgment

```text
finite determinant central extension:
  trivial on multiplicative commutators;

infinite determinant invariant:
  can retain a chosen physical boundary anomaly under stronger ideal data;

equal-rank cutoff plus strong convergence:
  leaves that anomaly noncanonical by `(NC.20)`;

actual route:
  already fixes the physical relative trace in `(NC.27)`;

remaining mathematics:
  estimate the same signed semicommutator by `(NC.26)`, with no branchwise
  trace norm and no new normal-ordering constant.       (NC.31)
```

Proof 425 therefore closes central extension as a shortcut, not as notation.
The next valid lane must attack the localized continuous BOGC / Burnol
mixed-gradient estimate on the actual completed owner, or find a genuinely
different unconditional RH producer.
