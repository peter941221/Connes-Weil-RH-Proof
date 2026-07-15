# Proof 257: Two-boundary Q-preserving flow

Date: 2026-07-15

Status: exact replacement of Proof 256's endpoint Sonin graph as the analytic
organization by a Q-preserving synchronized projection flow.  The static hard
factor has an exact decomposition into the square root of CC20's prolate
remainder and a smoothed second-half-line commutator.  Along the actual source
flow, the complete nested band derivative factors through the outer half-line
crossing and the current second-support leakage, with every scalar Euler
generator component deleted before an estimate.

The endpoint graph formula remains useful for trace legality and algebraic
cross-checking, but `L_t` and the expanding primal frame are no longer proposed
as norm targets.  The remaining theorem is a uniform polynomial-support bound
for the recombined three-branch flow.  That bound, the same-object finite-S
trace identity, the Burnol all-zero identity, and RH are not proved here.  No
Lean owner or route rewire is authorized.

## 1. Result first

```text
+---------------------------------------------+------------------------------+
| layer                                       | verdict                      |
+---------------------------------------------+------------------------------+
| CC20 base prolate owner                     | source theorem               |
| BQ square-root factorization                | exact                        |
| second-boundary commutator rewrite          | exact                        |
| endpoint hard-channel trace legality        | exact for each finite S      |
| synchronized graph derivative               | exact                        |
| Q-preserving complete band-flow factor      | exact, stronger owner        |
| scalar Euler bulk in the complete flow      | deleted exactly              |
| periodic transported-Q diagnostics          | rejected: boundary polluted  |
| complete three-branch polynomial bound      | open, active Gate 3          |
| RH                                          | unproved                     |
+---------------------------------------------+------------------------------+
```

The route move is

```text
endpoint conditioned inverse
        |
        X  Proof 256
        |
endpoint graph coordinate L
        |
        X  do not estimate separately
        |
Q-preserving orthogonal band flow
        |
        +-- crossed outer half-line
        +-- crossed second half-line
        +-- base CC20 prolate leakage
        |
        v
one recombined compact-root trace estimate.                         (T.1)
```

## 2. Primary-source audit

The CC20 source was read from the arXiv source package, not inferred from a
project theorem name:

```text
Connes--Consani, Weil positivity and Trace formula,
the archimedean place
https://arxiv.org/abs/2006.13771

weil-compo.tex:1072--1076
  P P_hat P
    =sum_n lambda(n)^2 |zeta_n><zeta_n|+R,
  where R is the Sonin projection;

weil-compo.tex:982--984
  |lambda(n)| has the explicit rapid-decay bound (T.5) below;

weil-compo.tex:2105--2116
  the commutator of a half-line projection with a Schwartz multiplier is
  an infinitesimal of infinite order, hence trace class.
```

CCM24 supplies the finite Euler transport and preservation of the second
support orientation:

```text
Connes--Consani--Moscovici,
Zeta zeros and prolate wave operators: Semilocal adelic operators, v2
https://arxiv.org/html/2310.18423v2

mainc2m24fine.tex:946--981    finite Euler multiplier
mainc2m24fine.tex:983--1029   Sonin transport
mainc2m24fine.tex:1031--1073  common carrier with S-dependent norm.
```

Proof 224 records the source-orientation consequence explicitly: one support
half-line is crossed by the Euler multiplier and the other is preserved.  All
factorizations below after the source facts are project derivations.

## 3. Static two-boundary factorization

Let `E` and `Q` be the two support projections and let their intersection be
the Sonin projection `R`.  Put

```text
R<=E,
R<=Q,
B=E-R.                                                   (T.2)
```

CC20's spectral decomposition has the operator form

```text
E Q E=R+K_prol,
K_prol=sum_n lambda(n)^2 |zeta_n><zeta_n|.              (T.3)
```

Since `BR=RB=0`, compression of `(T.3)` to `Ran(B)` gives

```text
(B Q)(B Q)*=B Q B=K_prol on Ran(B).                    (T.4)
```

Thus the singular values of `B Q` are `|lambda(n)|`.  CC20 gives

```text
|lambda(n)|
 <=2^(2n) pi^(2n+1/2) ((2n)!)^2
    /[(4n)! Gamma(2n+3/2)]

 ~ (4n+1)^(-2n-1/2) (e*pi)^(2n+1/2).                  (T.5)
```

In particular `B Q` is an infinitesimal of infinite order and is trace class.

Let `W` be the route's legally smoothed convolution detector.  Since `QR=R`,

```text
B W R
 =B Q W R+B(I-Q)W R

 =B Q W R+B(I-Q)[W,Q]R.                              (T.6)
```

The first term starts with the trace-class prolate square root `BQ`.  The
second starts with the trace-class smoothed boundary commutator from CC20
Appendix D, after conjugating the half-line by the source scattering unitary.
Therefore

```text
B W R is trace class.                                  (T.7)
```

For every fixed finite `S`, Proof 256's graph map

```text
L=(R H R)^(-1)R H B                                   (T.8)
```

is bounded.  Equations `(T.6)--(T.8)` prove that the endpoint hard channel

```text
-Tr_B(B W R L)                                        (T.9)
```

is trace legal.  This closes legality only.  Multiplying a trace norm from
`(T.6)` by a raw norm of `L` is not an `S`-uniform estimate.

## 4. Graph-flow identity

For the synchronized path `T_t`, put

```text
H_t=T_t* T_t,
A_t=R H_t R,
L_t=A_t^(-1)R H_t B,
Z_t=B-RL_t.                                           (T.10)
```

Differentiating `A_tL_t=R H_tB` gives

```text
L_t'=A_t^(-1)R H_t'Z_t.                              (T.11)
```

If `T_t'=X_tT_t`, define

```text
K_t=X_t*+X_t,
V_(R,t)=T_t R A_t^(-1/2),
G_t=T_t Z_t.                                          (T.12)
```

Then `V_(R,t)` is an isometry, `V_(R,t)*G_t=0`, and

```text
L_t'
 =A_t^(-1/2)V_(R,t)*K_tG_t.                          (T.13)
```

The orthogonality in `(T.13)` deletes every scalar part of `K_t`.  This is an
exact condition-number-free identity, but a separate norm of `G_t` can still
recreate the rejected Euler amplification.  Equation `(T.13)` is retained as
an independent certificate, not as the final estimate.

## 5. Stronger Q-preserving band flow

The source transfer preserves `Ran(Q)`.  For the synchronized path this means

```text
T_t Ran(Q)=Ran(Q),
X_t Ran(Q) subset Ran(Q).                             (T.14)
```

Transport the nested pair:

```text
E_t=projection onto T_t Ran(E),
R_t=projection onto T_t Ran(R),
B_t=E_t-R_t.                                          (T.15)
```

Invertibility of `T_t` and `(T.14)` give

```text
Ran(R_t)=Ran(E_t) intersection Ran(Q),
R_t<=Q.                                               (T.16)
```

Proof 252's exact derivative is

```text
B_t'=Y_t+Y_t*,

Y_t=(I-E_t)X_tB_t-R_tX_t*B_t.                        (T.17)
```

Invariance in `(T.14)` implies

```text
(I-Q)X_tQ=0,
QX_t*(I-Q)=0,
R_tX_t*=R_tX_t*Q.                                    (T.18)
```

Substitution into `(T.17)` gives the stronger owner

```text
Y_t
 =(I-E_t)X_tB_t-R_tX_t*Q B_t.                        (T.19)
```

This is the decisive algebraic move.  It contains only orthogonal projections
and the complete logarithmic generator.  No endpoint graph, shorted inverse,
or expanding frame is present.

Replacing `X_t` by `X_t+c_t I` changes neither term of `(T.19)`:

```text
(I-E_t)B_t=0,
R_t Q B_t=R_tB_t=0.                                  (T.20)
```

Thus scalar gauge cancellation holds branch by branch, before a trace or
absolute value.

For the root detector, the instantaneous complete response is

```text
q_(S,t)(W)
 =2 Re Tr[W(I-E_t)X_tB_t]
  -2 Re Tr[W R_tX_t*Q B_t].                          (T.21)
```

Equation `(T.21)` is the physical-boundary version of Proof 253's Berezin
double-difference formula.

## 6. Complete the three branches

The factor `Q B_t` in `(T.19)` must not be called compact without another
argument.  Transporting a half-line can add a noncompact boundary channel.

Let

```text
G_t=(I-R_t)T_tB,
Sigma_t=G_t*G_t,
U_t=G_t Sigma_t^(-1/2).                               (T.22)
```

Then `U_t` is an isometry from the base band onto `Ran(B_t)`.  From `R_t<=Q`,

```text
Q U_t
 =(Q-R_t)T_tB Sigma_t^(-1/2).                        (T.23)
```

Invariance of `Q` gives

```text
Q T_tB=T_tQ B+[Q,T_t]B.                              (T.24)
```

Combining `(T.23)--(T.24)` yields

```text
Q U_t
 =(Q-R_t)
   [T_tQ B+[Q,T_t]B]
   Sigma_t^(-1/2).                                    (T.25)
```

The three source-owned branches are now explicit:

```text
+----------------------+-----------------------------------------------+
| branch               | exact owner                                   |
+----------------------+-----------------------------------------------+
| outer boundary       | (I-E_t)X_tB_t                                 |
| second boundary      | [Q,T_t]B                                      |
| base prolate         | Q B, with singular values |lambda(n)|         |
+----------------------+-----------------------------------------------+
```

`Sigma_t^(-1/2)` is contractive because the scalar-normalized metric is at
least the identity.  Also `Q U_t` is a contraction directly.  Neither fact by
itself proves a trace-norm bound: trace ideals arise only after the compact
root and the completed crossings remain paired.

## 7. Quantitative successor

The active theorem is one estimate for `(T.21)` after `(T.25)` is inserted:

```text
integral_0^1 |complete recombined three-branch trace| dt
 <=C (1+B)^d ||g||_(H^s)^2                           (T.26)
```

for a root `g` supported in `[-B,B]`, uniformly in its visible finite set.
An equivalent prime-power proof must achieve `poly(m)p^(-m)` after all
dressings, not a separate `p^(-m/2)` majorant.

The explicit prolate bound `(T.5)` gives a new quantitative option.  Its
logarithm is

```text
log |lambda(n)|=-2n log n+O(n).                       (T.27)
```

Therefore a cutoff of the prospective size

```text
N(B)=ceil(kappa B/log(2+B))                            (T.28)
```

makes the high prolate tail exponentially small in `B`, with an adjustable
rate through `kappa`.  This can absorb an exponential envelope if the exact
factorial bound in `(T.5)` is carried through with explicit constants.

This does not close `(T.26)`.  It separates its remaining work into:

```text
high prolate modes:
  explicit super-exponential tail from CC20;

low prolate modes n<=N(B):
  complete paired boundary estimate, with no raw T_t or X_t norm;

two boundary branches:
  compact support first, Markov/prime expansion second.              (T.29)
```

Do not introduce `N(B)` control rows until a quantitative construction proves
that their interpolation/support cost is sublinear enough to preserve the
resonant contraction.  Proof 248 is the guard against assuming this.

## 8. Exact certificate

The companion script has three independent exact layers:

```text
docs/proofs/257_two_boundary_graph_flow_probe.py
```

Default WSL2 command:

```text
OPENBLAS_NUM_THREADS=4 python3 -B \
  docs/proofs/257_two_boundary_graph_flow_probe.py
```

The exact errors are:

```text
+--------------------------------------+-----------+
| check                                | error     |
+--------------------------------------+-----------+
| generic two-projection identities    | 9.81e-16  |
| graph flow, including finite diff    | 1.21e-10  |
| Q-preserving nonzero-time flow       | 1.70e-9   |
| strict periodic Sonin flow algebra   | 3.14e-14  |
+--------------------------------------+-----------+
```

Inside the Q-preserving nonzero-time layer:

```text
+--------------------------------------+-----------+
| check                                | error     |
+--------------------------------------+-----------+
| (I-Q)X_tQ                            | 1.16e-16  |
| R_t<=Q                               | 4.56e-18  |
| inner prolate factor                 | 1.62e-16  |
| complete nested flow                 | 4.22e-16  |
| scalar gauge cancellation            | 2.91e-14  |
| independent finite difference        | 1.70e-9   |
+--------------------------------------+-----------+
```

The finite difference dominates the reported maximum.  The operator
identities themselves are at roundoff scale.

## 9. Death diagnostics

At fixed root width, three physically larger periodic sections through
`p<=997` report:

```text
+------+-------+---------------+------------+----------+----------+
| size | step  | abs hard flow | graph norm | complete | verdict  |
+------+-------+---------------+------------+----------+----------+
|  208 | 0.080 | 0.909         | 2.46       | -1.427   | survives |
|  288 | 0.060 | 1.148         | 3.19       | -1.350   | survives |
|  320 | 0.050 | 1.222         | 2.98       | -1.158   | survives |
+------+-------+---------------+------------+----------+----------+
```

The old separated phase is `5.6e10--8.0e10` on the same configurations.
The new paired values remain order one.  This rejects the condition-number
organization again, but it is not a convergence theorem.

A second diagnostic grows the root width and the visible prime cutoff
together:

```text
+------------+------------+---------------+------------+
| root width | largest p  | abs hard flow | graph norm |
+------------+------------+---------------+------------+
| 0.48       | 2          | 0.086         | 0.85       |
| 0.72       | 3          | 0.349         | 1.16       |
| 0.96       | 5          | 1.203         | 1.47       |
| 1.20       | 11         | 1.322         | 1.61       |
| 1.44       | 17         | 0.189         | 1.68       |
| 1.92       | 47         | 0.028         | 2.15       |
+------------+------------+---------------+------------+
```

There is no observed exponential support growth.  The detector changes with
the width, the values oscillate, and this is not the actual resonant Yoshida
sequence, so no polynomial bound is inferred.

The periodic model must not test `(T.14)`: by `p<=997` its transported
`R_t<=Q` residual is about `0.4`.  The circle has destroyed the one-sided
invariant half-line.  Transported-prolate trace norms from that model are
therefore explicitly rejected as continuous evidence.  The exact
Q-preserving model, not the periodic diagnostic, certifies `(T.18)--(T.21)`.

## 10. Route judgment

```text
+------------------------------------------------+--------------------------+
| layer                                          | judgment                 |
+------------------------------------------------+--------------------------+
| CC20 base prolate spectral owner               | source theorem           |
| static BQ / second-boundary split               | exact                    |
| endpoint hard trace legality                    | closed                   |
| raw endpoint L norm route                       | retired                  |
| synchronized graph derivative                  | exact cross-check        |
| Q-preserving orthogonal band flow               | exact active owner       |
| scalar generator cancellation                  | exact branchwise         |
| three-branch completion                        | exact algebraic target    |
| high prolate tail schedule                      | viable, constants open    |
| low-mode complete paired bound                  | open                     |
| uniform polynomial-support estimate            | open, active Gate 3      |
| negative-owner integrated smallness            | open                     |
| same-object finite-S trace identity             | open                     |
| Burnol all-zero identity                        | open                     |
| Lean owner or route rewire                      | none                     |
| RH                                              | unproved                 |
+------------------------------------------------+--------------------------+
```

Proof 257 changes the active analytic object.  The route no longer asks for a
conditioned inverse or a Sonin graph norm.  It asks for one compact-root trace
of the exact Q-preserving band flow, with the outer boundary, second boundary,
and base prolate branches completed before any absolute estimate.

Successor note: Proof 258 gives an exact `C^2` model in which the two terms
`T_tQB` and `[Q,T_t]B` in `(T.25)` have norms `kappa,kappa` and cancel to zero
after the common Gram normalization.  Thus `(T.25)` remains a source
factorization but its two bracketed terms must not be estimated separately.
Proof 259 then shows that Proof 258's covariant Kato leakage
`C_t=Q mathcalU_tB` records only the `Q`-corner and cannot carry the route
trace.  Keep it as a diagnostic.  The active owner is the full lower crossing
`Y_t`, factored through one source-owned crossing space after all three
branches have been recombined.  Proof 260 separates the uses of that
factorization: it may prove fixed-`S` ordinary trace legality, but its positive
Hilbert--Schmidt factor norms cannot prove the uniform estimate.  The latter
must be established on the recombined signed scalar trace after legality is
closed.  Proof 261 closes that fixed-`S` legality gate by pulling the moving
crossing back through the complete compressed metric inverse.  The signed
uniform estimate remains open.  Proof 262 integrates the legal flow and
replaces `(T.26)` by the endpoint pairing

```text
Tr_B(mathcalD_S*
  ((I-E)[W,E]B-[W,R]R L_S)).
```

This is the active Gate 3U owner; both detector commutators carry the fixed
compact-root boundary support.
