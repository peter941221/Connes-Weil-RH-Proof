# Proof 298: Relative Gram heat boundary layer

Date: 2026-07-16

Status: exact fixed-`S` ordered heat-semigroup owner for Proof 266's relative
Gram response, together with an exact scaling limit from Proof 290's finite
renewal path.  The limit exposes a nonuniform survival boundary layer: every
Proof 296 reflection sector has a generally nonzero hyperbolic profile when
the horizon grows at the reciprocal spectral-gap scale.  Fixed-horizon
double/triple zeros therefore cannot provide the uniform Gate 3U estimate.

This proof replaces the growing path grid by one ordered relative heat
cocycle.  It
does not prove the required uniform source heat bound, Gate 3U, the finite-`S`
sign, the arithmetic same-object identity, negative-owner integration,
Burnol's all-zero identity, or RH.

## 1. Result

```text
+-----------------------------------------------+------------------------------+
| layer                                         | judgment                     |
+-----------------------------------------------+------------------------------+
| ordered Gram numerator                        | unchanged / exact            |
| finite renewal with step T/N                  | exact path owner             |
| N -> infinity boundary-layer limit            | relative Gram heat integral |
| ordered relative heat first jet               | exact                        |
| relative Fredholm determinant readback        | exact for fixed S           |
| positive-reference symmetrization             | forbidden by trace anomaly |
| fixed-horizon reflected zero ledger           | correct but nonuniform      |
| hyperbolic boundary profiles of four sectors  | generally nonzero           |
| blockwise reflected DOI norm route            | rejected                    |
| complete outer/Sonin heat estimate            | open                         |
| Gate 3U and RH                                | open / unproved              |
+-----------------------------------------------+------------------------------+
```

The ownership change is

```text
canonical + all-even + path boundary + soft sectors
  -> keep the complete finite response
  -> take its reciprocal-gap scaling limit
  -> one relative Gram heat integral
  -> insert the complete outer-minus-Sonin numerator
  -> compact support
  -> one absolute value.                                  (BI.1)
```

The reflected path is still useful as an exact finite certificate.  Its local
zero orders are not a uniform estimator.

## 2. Ordered Gram owner

Retain Proofs 264--266 on the source band `B=E-R`:

```text
K=E A iota_B,
Gamma=K* K,
Delta=B-Gamma,
0<Gamma<=B.                                           (BI.2)
```

For a Hermitian compact-root detector `W`, put

```text
W_B=iota_B* W iota_B,
N_W=K* W K-W_B Gamma.                                (BI.3)
```

The factor order in `(BI.3)` is mandatory.  The endpoint response is

```text
Q_S(W)=Tr_B(N_W Gamma^(-1)).                         (BI.4)
```

Proof 266 makes `(BI.4)` a genuine fixed-`S` relative Fredholm determinant
jet.  Proof 261 supplies the trace-class legality after the compact root has
been inserted.  Neither theorem gives a bound uniform in the visible prime
set.

## 3. Heat regularization without a path inverse

For `T>=0`, define the bounded scalar function

```text
phi_T(lambda)
 =(1-exp(-T lambda))/lambda
 =integral_0^T exp(-t lambda) dt.                    (BI.5)
```

Since `Gamma>0` for fixed finite `S`, functional calculus gives

```text
Q_(S,T)(W)
 =Tr_B(N_W phi_T(Gamma))
 =integral_0^T Tr_B(N_W exp(-t Gamma)) dt.            (BI.6)
```

The integral in `(BI.6)` is one signed scalar.  The absolute value stays
outside the time integral.  For fixed `S`,

```text
lim_(T->infinity) Q_(S,T)(W)=Q_S(W).                 (BI.7)
```

Equation `(BI.6)` does not estimate `Gamma^(-1)`.  It replaces it by the
killed semigroup `exp(-t Gamma)` while retaining the complete numerator.

## 4. Ordered relative heat cocycle

Use the detector deformations from Proof 266:

```text
Gamma_W(s)=K* exp(sW) K,
C_B(s)=iota_B* exp(sW) iota_B.                       (BI.8)
```

For real `s`, both `Gamma_W(s)` and `C_B(s)` are positive.  The route-owned
reference, however, is the ordered product

```text
Gamma_ord(s)=C_B(s) Gamma.                           (BI.9)
```

At the origin,

```text
Gamma_W(0)=Gamma_ord(0)=Gamma,

Gamma_W'(0)=K* W K,
Gamma_ord'(0)=W_B Gamma.                             (BI.10)
```

`Gamma_ord(s)` need not be self-adjoint.  It is similar to the positive
operator

```text
C_B(s)^(1/2) Gamma C_B(s)^(1/2),                     (BI.10a)
```

so its spectrum is positive and its bounded heat semigroup is well defined.
Its order must not be changed.

Duhamel differentiation gives, for `t>0`,

```text
partial_s Tr_B(
  exp(-t Gamma_W(s))-exp(-t Gamma_ord(s)))|_(s=0)

 =-t Tr_B(N_W exp(-t Gamma)).                        (BI.11)
```

No symmetrization and no cycle of `Gamma^(-1)` occurs in `(BI.11)`.  The
ordered reference derivative is already the second term of `(BI.3)`.

Proof 266 defines

```text
F_s=Gamma_W(s) Gamma^(-1)-C_B(s) in S1.
```

Therefore, exactly in the required order,

```text
Gamma_W(s)-Gamma_ord(s)=F_s Gamma in S1.             (BI.12)
```

Duhamel's formula makes the ordered heat difference in `(BI.11)` trace
class.  The relative operator Frullani identity yields

```text
log det_B(Gamma_W(s) Gamma_ord(s)^(-1))
 =integral_0^infinity
    Tr_B(
      exp(-t Gamma_ord(s))-exp(-t Gamma_W(s))) dt/t. (BI.13)
```

The determinant in `(BI.13)` is exactly Proof 266's relative determinant,
because

```text
Gamma_W(s) Gamma_ord(s)^(-1)
 =Gamma_W(s) Gamma^(-1) C_B(s)^(-1).                 (BI.14)
```

Its logarithmic first jet is `(BI.4)`.  Differentiating `(BI.13)` and using
`(BI.11)` recovers `(BI.6)--(BI.7)`.

This is a new coordinate, not a new assumption: the fixed-`S` determinant
was already legal.  Its value is that the horizon has disappeared.

### 4.1 The positive-reference trap

The tempting replacement

```text
Gamma_ord(s)
 -X-> C_B(s)^(1/2) Gamma C_B(s)^(1/2)                (BI.14a)
```

is forbidden in the infinite source trace.  The two operators are similar,
so finite matrices give the same determinant and heat trace.  That is not a
valid infinite-dimensional trace cycle when only the completed difference is
trace class.

Proof 264 constructs a positive detector whose similarity difference has
nonzero source trace while every finite shift section adds the opposite far
boundary and reports zero.  Proof 297 gives the same mechanism for a weighted
emission commutator.  Thus `(BI.14a)` can erase the ordered arithmetic
anomaly.  The probe retains the ordered product and reruns Proof 264's
physical/far-boundary guard.

## 5. Exact finite-path boundary layer

Introduce only a scalar gauge parameter `epsilon>0`:

```text
K_epsilon=sqrt(epsilon) K,
Gamma_epsilon=epsilon Gamma,
Delta_epsilon=B-epsilon Gamma,
N_(W,epsilon)=epsilon N_W.                           (BI.15)
```

Multiplying the causal inverse `A` by a scalar preserves its commutation with
`W` and every `C/E/R/Q` projection relation.  The endpoint is gauge
invariant:

```text
N_(W,epsilon) Gamma_epsilon^(-1)
 =N_W Gamma^(-1).                                    (BI.16)
```

Use `N` renewal steps and set `epsilon=T/N`.  Proof 290's exact path response
becomes

```text
Q_(N,T)
 =Tr_B[
    (T/N) N_W
    sum_(k=0)^(N-1)(B-(T/N)Gamma)^k].                (BI.17)
```

The Euler product formula for the exponential and a Riemann sum give the
operator-norm limit

```text
lim_(N->infinity)
 (T/N)sum_(k=0)^(N-1)(B-(T/N)Gamma)^k

 =integral_0^T exp(-t Gamma)dt.                      (BI.18)
```

Thus

```text
lim_(N->infinity)Q_(N,T)=Q_(S,T)(W).                 (BI.19)
```

The finite path is an Euler discretization of the relative heat owner.  This
explains why increasing the horizon while keeping only local fixed-mode
Taylor coefficients is unsafe.

For fixed `N`, the first gauge jet is

```text
partial_epsilon Q_(N,epsilon)|_(epsilon=0)
 =N Tr_B(N_W).                                       (BI.20)
```

The coefficient grows with the horizon.  Equation `(BI.18)`, not a local
zero count, performs its correct resummation.

## 6. Reflection zeros are nonuniform

Proof 296 uses, for path length `N`,

```text
h_N(t)=(1+t)/(1+t^(2N+1)),
f_(N,r)(t)=t^r h_N(t).                               (BI.21)
```

Take the reciprocal-gap scaling

```text
t_N=exp(-x/N),
a_N/N->alpha,
b_N/N->beta,
0<alpha,beta<1.                                      (BI.22)
```

Then the six parity filters have the exact limits

```text
a_plus
 ->1-[exp((1-alpha)x)+exp(alpha x)]/[2 cosh(x)],

a_minus
 ->[exp(alpha x)-exp((1-alpha)x)]/[2 cosh(x)],

b_plus
 ->[exp(-beta x)+exp(-(1-beta)x)]/2,

b_minus
 ->[exp(-beta x)-exp(-(1-beta)x)]/2,

c_plus
 ->cosh((1-alpha-beta)x)/cosh(x),

c_minus
 ->sinh((1-alpha-beta)x)/cosh(x).                    (BI.23)
```

All six values, and therefore all four sector products

```text
a_plus c_plus b_plus,
a_plus c_minus b_minus,
a_minus c_plus b_minus,
a_minus c_minus b_plus,                              (BI.24)
```

are generally nonzero.  This does not contradict Proof 296's fixed-`N`
ledger.  The two limits do not commute:

```text
fixed N, t->1:
  double/triple zeros are real;

N->infinity, N(1-t)->x:
  their Taylor coefficients grow and produce (BI.23).               (BI.25)
```

At fixed `N`, the physical scaling `K_epsilon=sqrt(epsilon)K` makes the
interior sector orders

```text
+++ : O(epsilon^3),
+-- : O(epsilon^5),
-+- : O(epsilon^4),
--+ : O(epsilon^4).                                  (BI.26)
```

There are `O(N^2)` cells and their divided-difference coefficients depend on
`N`.  In the boundary layer `epsilon=O(1/N)`, `(BI.26)` cannot be summed by
fixed-`N` constants.  The nonzero profiles `(BI.23)--(BI.24)` are an exact
guard against that step.

Consequently the following route is rejected:

```text
count fixed-mode zeros in each reflected block
  -> take positive block norms
  -> sum over the path grid
  -> claim a horizon-uniform bound.                  (BI.27)
```

Proof 297's trace-anomaly guard remains active as well: finite sector traces
cannot replace the signed resummation.

## 7. Physical readback and next theorem

Proof 293 identifies the complete observable generator:

```text
g_W
 =-E W C A iota_B
  -E A R[W,R]iota_B.                                 (BI.28)
```

Its left companion satisfies

```text
g_W^left K=N_W.                                      (BI.29)
```

Therefore the new active scalar is

```text
Q_(S,T)(W)
 =integral_0^T
   Tr_B(g_W^left K exp(-t Gamma))dt.                 (BI.30)
```

The two terms in `(BI.28)` remain one outer-return minus Sonin numerator.
Expanding `[W,R]` still requires all outer, second-support, and prolate
branches.  Neither the time integral nor its two physical terms receives a
separate absolute value.

The successor theorem is now

```text
sup_(finite S,T>=0)
 |integral_0^T
   Tr_B(g_(W,S)^left K_S exp(-t Gamma_S))dt|

 <=C(1+B_root)^d
   norm(eta)_(H^r)norm(xi)_(H^r).                    (BI.31)
```

The legal order is

```text
relative heat first jet
  -> complete outer/Sonin numerator
  -> real-line compact displacement support
  -> signed time integration
  -> one absolute value
  -> T -> infinity.                                  (BI.32)
```

Equation `(BI.31)` is a sufficient uniform strengthening of the required
endpoint bound; the endpoint bound alone need not control every truncated
time integral.  Proof 298 proves neither statement.  It removes the
artificial path horizon and rejects a nonuniform local-sector estimator.

## 8. Finite certificate

`298_relative_gram_heat_boundary_layer_probe.py` verifies:

```text
Proof 290's scaled finite path response;
the canonical/off-range split at the same ordering;
the fixed-horizon first gauge jet (BI.20);
the discrete-to-heat limit (BI.18)--(BI.19);
the ordered relative heat first jet (BI.11);
the relative log-determinant first jet;
the ordered Frullani determinant formula (BI.13);
Proof 264's nonzero similarity-anomaly boundary guard;
the six hyperbolic limits (BI.23);
nonvanishing of all four generic sector profiles (BI.24).
```

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/298_relative_gram_heat_boundary_layer_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/298_relative_gram_heat_boundary_layer_probe.py \
  --multiplicity 12 --seed 2298 --steps 31 --time 2.3 \
  --profile-length 193 --profile-x 0.9 --alpha 0.27 --beta 0.61
```

The two cohorts report:

```text
+----------------------------------------+-------------+-------------+
| diagnostic                             | default     | alternate   |
+----------------------------------------+-------------+-------------+
| maximum exact error                    | 4.91e-10    | 9.86e-10    |
| ordered heat first-jet error           | 6.41e-11    | 1.38e-10    |
| ordered Frullani determinant error     | 1.47e-16    | 3.79e-16    |
| boundary error at N                    | 8.32e-5     | 7.18e-5     |
| boundary error at 4N                   | 2.05e-5     | 1.77e-5     |
| N-to-4N refinement ratio               | 4.05        | 4.04        |
| minimum nonzero sector profile         | 8.58e-5     | 5.65e-4     |
| physical similarity anomaly            | 2.50e-1     | 2.50e-1     |
| finite total similarity trace          | 6.15e-14    | 6.15e-14    |
+----------------------------------------+-------------+-------------+
```

The certificate is finite-dimensional algebra and functional-calculus
diagnostics.  The continuous source estimate `(BI.31)` remains open.

## 9. Evidence and route judgment

Project evidence:

```text
Proof 266, genuine fixed-S relative Gram determinant:
docs/proofs/266_three_branch_causal_determinant.md

Proof 290, exact finite renewal path:
docs/proofs/290_biorthogonal_finite_horizon_renewal.md

Proof 293, complete physical generator:
docs/proofs/293_observable_two_boundary_path.md

Proofs 296--297, weighted parity and trace-anomaly guards:
docs/proofs/296_weighted_reflection_parity.md
docs/proofs/297_emission_trace_anomaly_guard.md
```

The heat derivative uses Duhamel's formula and the relative Frullani
identity; both are derived in `(BI.10)--(BI.14)`.  The divided-difference
background remains:

```text
Vladimir Peller,
Multiple operator integrals in perturbation theory,
https://arxiv.org/abs/1509.02803

Alexei Aleksandrov and Vladimir Peller,
Operator Lipschitz functions,
https://arxiv.org/abs/1611.01593
```

Those papers support the functional-calculus language.  They do not supply
the source-specific estimate `(BI.31)`.

The route now reads

```text
finite reflected path
  -> reciprocal-gap boundary layer (Proof 298)
  -> ordered relative Gram heat cocycle
  -> complete outer/Sonin heat first jet
  -> compact-support signed heat estimate (open)
  -> Gate 3U / finite-S sign / RH (open).             (BI.33)
```

No Lean theorem, route consumer, commit, or push is authorized by this proof.

## 10. Successor: Proof 299

Proof 299 factors the ordered determinant into

```text
tau_ord(s)=tau_sym(s) j(s),
```

where `tau_sym` compares two positive covariances and `j` is the inverse
determinant invariant of `(C_B(s)^(1/2),Gamma)`.  The generic anomaly factor
must not be deleted.  On the route's diagonal Hermitian response, however,
its first logarithmic derivative is both real and purely imaginary, hence
zero.  Therefore

```text
Q_S(g,g)=partial_s log tau_sym(s)|_(s=0).
```

This replaces the stronger sufficient target `(BI.31)` by the exact endpoint
target `(BJ.34)`.  It does not assert `j(s)=1`, and it does not delete the
cross-root or nonlinear anomaly.  See
`docs/proofs/299_positive_heat_joint_torsion.md`.
