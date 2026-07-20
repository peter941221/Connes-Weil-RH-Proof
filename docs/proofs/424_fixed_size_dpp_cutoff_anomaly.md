# Proof 424: fixed-size DPP cutoff anomaly

Date: 2026-07-20

Status: exact rejection of the translation-covariant fixed-size
projection-DPP implementation of Proof 422 `(CN.33)`, together with an
axiom-clean finite matrix owner.  An equal-rank translated cutoff cancels the
physical half-line response against an artificial far boundary at every
finite stage.  A common far endpoint retains the response but changes rank.

Detector-adapted equal-rank padding can retain the response, so fixed size is
not rejected in complete generality.  A second exact guard shows why it still
does not supply Proof 421's estimate: conditioning the score on the exact
linear statistic can reveal the entire finite configuration.  Summable
detector weights give uniformly bounded response and variance while the
detector-conditional Fisher action grows like the cutoff dimension.

A variable-size positive-contraction DPP can also carry the rank change, but
its unlocalized Fisher cost is at least `pi^2` per removed mode.  A surviving
probability argument must therefore construct a source-specific boundary
completion and a genuinely stable localization, then prove its canonical
Euler-energy bound.  Those theorems are not supplied here.

This proof does not establish Proof 416 `(EN.7)`, Gate 3U, the finite-`S`
sign, Burnol's identity, or RH.

## 1. Result

```text
+------------------------------------------------------+----------------------+
| statement                                            | judgment             |
+------------------------------------------------------+----------------------+
| finite coordinate-window trace                       | Lean-owned           |
| equal-cardinality relative response                  | exactly zero         |
| response with a cardinality defect                   | exact rank ledger    |
| translated equal-rank windows converge strongly      | yes                  |
| their detector traces converge to the anomaly        | no                   |
| common far endpoint retains the anomaly               | yes                  |
| common far endpoint preserves rank                    | no                   |
| differentiable fixed-rank projection path             | impossible           |
| detector-invisible equal-rank padding                 | possible, noncanonical|
| exact-statistic conditional Fisher is local           | false                |
| bounded response and variance bound conditional Fisher| false                |
| variable-size Bernoulli boundary path                 | exact survivor       |
| minimum Fisher action per removed mode                | `pi^2`               |
| canonical modewise raw Fisher action                  | infinite             |
| detector-relative Fisher renormalization              | open                 |
| RH                                                   | unproved             |
+------------------------------------------------------+----------------------+
```

The corrected probability dependency is

```text
physical trace anomaly
  -> choose and prove a boundary completion
  -> rank-changing contraction or detector-invisible padding
  -> stable detector localization
  -> canonical Euler-energy estimate
  -> Gate 3U.                                          (CA.1)
```

Proof 421 starts with an arbitrary fixed-rank projection DPP and an
exact-statistic conditional score.  Proof 424 shows that neither step owns the
first or third line of `(CA.1)`.

## 2. Discrete half-line owner

Work on `ell2(Z)` with standard basis `e_j` and bilateral shift

```text
S e_j=e_(j+1).                                        (CA.2)
```

Let

```text
P_0=projection onto span{e_j:j>=0},
P_b=S^b P_0 S^(-b),
b>=1.                                                  (CA.3)
```

Then

```text
P_0-P_b=projection onto span{e_0,...,e_(b-1)}.         (CA.4)
```

Let `W` be a bounded translation-invariant detector, so `WS=SW`.  Its basis
diagonal is constant:

```text
<e_j,W e_j>=<e_0,W e_0>=kappa.                        (CA.5)
```

For a positive convolution detector `W=C_g* C_g`, Parseval gives

```text
kappa=norm(g)_2^2>=0.                                 (CA.6)
```

The physical relative trace is finite in this discrete guard and equals

```text
Tr[W(P_0-P_b)]=b kappa.                               (CA.7)
```

Equation `(CA.7)` is the discrete multiplicity-one analogue of Proof 422

```text
Tr[C_g(E-E_b)C_g*]=b norm(g)_2^2.                    (CA.8)
```

The continuous interval in `(CA.8)` has infinite Hilbert dimension; root
completion, rather than finite rank, makes its trace legal.

## 3. Equal-rank cutoff erases the anomaly

For `N>=1`, define the translated finite windows

```text
P_(0,N)=projection onto span{e_0,...,e_(N-1)},
P_(b,N)=projection onto span{e_b,...,e_(b+N-1)}.       (CA.9)
```

Both have rank `N`, and

```text
P_(0,N) -> P_0 strongly,
P_(b,N) -> P_b strongly.                              (CA.10)
```

However, constant diagonal and equal rank give

```text
Tr[W P_(0,N)]=N kappa=Tr[W P_(b,N)],

Tr[W(P_(0,N)-P_(b,N))]=0                             (CA.11)
```

for every `N`.  The exact operator decomposition is

```text
P_(0,N)-P_(b,N)
 =P_[0,b)-P_[N,N+b).                                  (CA.12)
```

Thus

```text
physical boundary       +b kappa
artificial far boundary -b kappa
                         --------
finite response                 0.                    (CA.13)
```

Strong convergence in `(CA.10)` does not imply convergence of these traces.
The products in `(CA.11)` do not converge in trace norm; their escaping far
boundary is exactly the trace anomaly.

The same cancellation in the detector-diagonal coordinate is stronger.  Let
`D_b` be the diagonal phase implementing translation, let `P_N` be any finite
rank source projection, and set

```text
Q_N=D_b P_N D_b*,
W D_b=D_b W.                                          (CA.13a)
```

Finite trace cyclicity gives

```text
Tr(W Q_N)=Tr(D_b* W D_b P_N)=Tr(W P_N).              (CA.13b)
```

Moreover, for every ground-set configuration `X`,

```text
(Q_N)_(X,X)=(D_b)_X (P_N)_(X,X) (D_b)_X*,
det((Q_N)_(X,X))=det((P_N)_(X,X)).                   (CA.13c)
```

Thus the two fixed-size projection-DPP laws are exactly identical, not merely
equal in their first detector moment.  Along the gauge path
`D_(tb)P_ND_(tb)*`, every configuration probability is constant, so its score
and detector-pushforward Fisher action are both zero.  This is the finite
counterpart of Proof 422's centered-law blindness.

## 4. A common far endpoint changes rank

To retain only the physical boundary, fix the same upper cutoff:

```text
widehat P_(0,N)=P_[0,N),
widehat P_(b,N)=P_[b,N),
N>b.                                                   (CA.14)
```

Then

```text
widehat P_(0,N)-widehat P_(b,N)=P_[0,b),

Tr[W(widehat P_(0,N)-widehat P_(b,N))]=b kappa.       (CA.15)
```

But

```text
rank(widehat P_(0,N))=N,
rank(widehat P_(b,N))=N-b.                            (CA.16)
```

A norm-continuous path of finite-dimensional orthogonal projections has
constant rank.  Indeed, projection rank equals its ordinary trace, the trace
is continuous, and an integer-valued continuous function on `[0,1]` is
constant.  Therefore no differentiable projection path connects the two
cutoffs in `(CA.14)`.

Their projection-DPP laws also live on disjoint configuration spaces:

```text
mu_(0,N) is supported on N-point sets,
mu_(b,N) is supported on (N-b)-point sets.             (CA.17)
```

The fixed-size score `(DF.21)--(DF.28)` is not defined across `(CA.17)`.  Both
directions of Kullback--Leibler divergence are infinite when the laws are
embedded in the common space of all finite configurations.

This gives the cutoff dichotomy:

```text
translation-covariant and equal rank -> erase anomaly;
common physical far endpoint          -> change rank;
equal-rank detector-adapted padding    -> new boundary datum. (CA.18)
```

The third option is not impossible.  One may add modes which escape weakly to
infinity and whose detector charge tends to zero.  Such a cutoff can preserve
rank and retain `(CA.15)`, but it breaks translation covariance and depends on
the detector.  Its anomaly convergence and Fisher cost are new theorems, not
consequences of strong convergence.

## 5. Lean finite trace owner

The new module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCutoffTraceAnomaly.lean                 (CA.19)
```

For a finite basis type `X` and `support : Finset X`, it defines the literal
diagonal coordinate projection `coordinateProjection support`.  The main
readback is

```lean
theorem trace_mul_coordinateProjection_eq_card_mul
    (detector : Matrix X X Complex)
    (support : Finset X) (diagonalValue : Complex)
    (hdiagonal : forall x, detector x x = diagonalValue) :
    Matrix.trace (detector * coordinateProjection support) =
      (support.card : Complex) * diagonalValue
```

The relative theorem is

```lean
theorem coordinateProjection_response_eq_card_sub_mul ... :
  Tr(detector * P_source)-Tr(detector * P_target)
   =(card(source)-card(target))*diagonalValue.         (CA.20)
```

Its equal-cardinality specialization proves `(CA.11)` exactly.  It does not
take a limit or assume trace continuity.

The same module proves the basis-independent finite cancellation

```lean
theorem trace_commuting_similarity_eq
    (hinverse : inverse * transport = 1)
    (hcommute : detector * transport = transport * detector) :
    Tr[detector * transport * projection * inverse]
      =Tr[detector * projection].                     (CA.20a)
```

Equation `(CA.20a)` owns `(CA.13b)` and makes explicit that a finite cyclic
trace cannot retain the infinite relative-trace anomaly.

## 6. Variable-size DPP survivor

The minimal finite repair replaces projections by positive contractions.
Keep `N-b` bulk modes occupied and let the `b` boundary modes have common
occupation probability

```text
p(t),
p(0)=1,
p(1)=0.                                               (CA.21)
```

The DPP kernel is

```text
K_t=P_[b,N)+p(t)P_[0,b).                              (CA.22)
```

For `0<p(t)<1`, this is a variable-size DPP: the bulk is deterministic and
the boundary consists of `b` independent Bernoulli variables.  Let `K` be
the number of occupied boundary modes.  The score is

```text
sigma_t
 =p'(t)[K-bp(t)]/[p(t)(1-p(t))].                     (CA.23)
```

For the particle-number detector `X=kappa K`, the statistic determines the
score whenever `kappa!=0`; detector conditioning loses nothing.  Direct
binomial variance gives

```text
I_t=E[sigma_t^2]
   =b p'(t)^2/[p(t)(1-p(t))].                         (CA.24)
```

Put

```text
theta(t)=2 arcsin(sqrt(p(t))).                        (CA.25)
```

Then

```text
theta'(t)^2=p'(t)^2/[p(t)(1-p(t))],
theta(0)=pi,
theta(1)=0.                                           (CA.26)
```

Cauchy--Schwarz on `[0,1]` gives the sharp lower bound

```text
integral_0^1 I_t dt
 =b integral_0^1 theta'(t)^2 dt
 >=b pi^2.                                            (CA.27)
```

Equality holds for

```text
theta(t)=pi(1-t),
p(t)=cos^2(pi t/2).                                   (CA.28)
```

Thus a rank-changing probability path can retain the anomaly, but it pays a
strict Fisher cost per boundary mode.  This cost is the probability owner of
the missing normal-ordering phase; it is absent from the fixed-size path.

## 7. Exact-conditioning does not localize Fisher information

There is also an equal-rank, fixed-size guard against Proof 421's proposed
localization.  On a `2M`-point ground set, use disjoint pairs

```text
{e_j,f_j},  1<=j<=M.                                 (CA.28a)
```

Let the rank-`M` projection have one orthonormal frame vector in each pair:

```text
v_j(t)=sqrt(p(t)) e_j+sqrt(1-p(t)) f_j.               (CA.28b)
```

The projection DPP chooses exactly one point from every pair.  The choices are
independent Bernoulli variables `B_j`, with

```text
Pr(B_j=1)=p(t).                                       (CA.28c)
```

Give the two sites detector weights

```text
w(e_j)=3^(-j),
w(f_j)=0,                                             (CA.28d)

X_w=sum_(j=1)^M 3^(-j) B_j.                          (CA.28e)
```

The ternary sum in `(CA.28e)` determines every bit.  If two bit strings first
differ at index `k`, their leading difference has magnitude `3^(-k)`, while
the sum of every later possible difference is less than

```text
sum_(j>k)3^(-j)=3^(-k)/2.                            (CA.28f)
```

Therefore `X_w` is injective on the finite configuration space.  Conditional
expectation on `X_w` does nothing:

```text
E[sigma_t | X_w]=sigma_t.                             (CA.28g)
```

Using the endpoint path `(CA.28)`, the exact ledgers are

```text
abs(E_1 X_w-E_0 X_w)
 =sum_(j=1)^M 3^(-j)<1/2,                             (CA.28h)

integral_0^1 Var_t(X_w)dt
 =1/8 sum_(j=1)^M 3^(-2j)<1/64,                      (CA.28i)

mathfrakI_w
 =integral_0^1 E[sigma_t^2]dt
 =M pi^2.                                             (CA.28j)
```

Thus response, detector trace mass, and integrated detector variance remain
uniformly bounded, while the detector-pushforward Fisher action diverges.
The weights are positive and summable; making a mode's detector charge tiny
does not make it information-theoretically invisible when the exact real
statistic still labels that mode.

This is not a defect of the Cauchy--Schwarz inequality `(DF.27)`.  It proves
that the proposed conditional Fisher factor is not a stable notion of root
localization.  Scaling every nonzero weight by any constant leaves the
sigma-algebra generated by `X_w` unchanged and hence leaves `(CA.28j)`
unchanged.

A robust probability successor would need a specified coarse graining,
noise channel, or a smaller linear score projection.  Projecting only onto
the span of `X_w-E X_w` is stable, but its squared norm is exactly

```text
abs(d/dt E X_w)^2/Var(X_w),                           (CA.28k)
```

so bounding it is the original signed response estimate in another notation.

## 8. Continuous implication

For the real-line half-line projections of Proof 422,

```text
E-E_b=M_(1_[0,b))                                    (CA.29)
```

has infinite rank.  The canonical modewise interpolation `(CA.22)` has

```text
raw rank-changing Fisher action=infinity.             (CA.30)
```

More precisely, restrict `L2([0,b))` to any `M`-dimensional subspace and use
the modewise path `(CA.22)`.  It costs at least `M pi^2`; letting `M` increase
proves `(CA.30)` for that canonical interpolation without assigning a formal
cardinality to the continuum.  The guard `(CA.28a)--(CA.28j)` independently
shows that exact-statistic conditioning need not remove this divergence even
when detector charges are summable.

Root completion nevertheless has finite first moment:

```text
Tr[C_g(E-E_b)C_g*]=b norm(g)_2^2.                    (CA.31)
```

The missing continuous construction must therefore do more than take a
fixed-size cutoff limit.  It must define a detector-relative boundary spectral
flow whose effective Fisher multiplicity is controlled by the trace-class
root completion, while retaining the complete outer-minus-Sonin/prolate
cancellation.

There is no canonical way to obtain that flow by replacing `E-E_b` with
`C_g(E-E_b)C_g*`: the latter is a positive trace-class response operator, not
the difference of the route's projection covariances.  Treating it as a new
DPP kernel would change the state in a detector-dependent way and assume the
root localization which the estimate is meant to prove.

## 9. Consequence for Proof 422 `(CN.33)`

The first line of `(CN.33)` required a common finite projection-DPP cutoff
whose relative mean converges to the nonzero root-completed trace.  Equations
`(CA.11)--(CA.18)` show:

```text
translation-covariant fixed-size projection cutoff
  -X-> common-normal-ordering convergence.            (CA.32)
```

Hence a translation-covariant implementation of Proof 421 is not the
continuous Gate owner.  Detector-adapted padding can repair the first line,
but `(CA.28j)` shows that the exact conditional Fisher does not then satisfy
the third line from response and variance control alone.  A probability
successor must replace `(CN.33)` by

```text
1. construct a rank-changing path or an equal-rank boundary completion;

2. prove its detector-relative first moment is the completed Gate trace;

3. define a stable localization and prove its action is bounded by
   C_lambda (1+B_F)^d E(S_F).                         (CA.33)
```

Line 2 must be proved before line 3.  Otherwise the unknown trace anomaly has
again been inserted as a normal-ordering constant.

The direct nonprobabilistic alternative remains Proof 416

```text
abs Lambda_(S_F)(F)
 <=C_lambda (1+B_F)^d P(E(S_F)) norm(F)_(R_B^r).      (CA.34)
```

Proof 424 shows that fixed size and exact-statistic conditioning do not make
`(CA.34)` easier.  Every viable extension must reconstruct the same boundary
functional and add a nontrivial localization theorem.

## 10. Evidence boundary

The finite DPP identities are derived directly from the Bernoulli product in
`(CA.21)--(CA.28)`.  The projection-DPP fixed-size contract and score formula
are Proof 421 `(DF.4)` and `(DF.21)--(DF.28)`.  The continuous trace-ideal and
disjointness contracts are proved and source-audited in Proof 422 using:

```text
J. E. Avron, S. Bachmann, G. M. Graf, and I. Klich,
Fredholm determinants and the statistics of charge transport:
https://arxiv.org/abs/0705.0099

T. Matsui and S. Yamagami,
Kakutani dichotomy on free states:
https://arxiv.org/abs/1203.3581
```

No numerical experiment is needed.  The finite cutoff cancellation is exact
matrix algebra, and the Fisher lower bound is the one-dimensional identity
`(CA.25)--(CA.27)`.

## 11. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| finite constant-diagonal trace owner           | closed in Lean            |
| translated equal-rank cutoff                   | anomaly erased exactly    |
| common far-boundary cutoff                     | correct trace, wrong rank |
| detector-invisible equal-rank padding          | possible, needs proof     |
| exact-statistic Fisher localization            | rejected by `(CA.28j)`    |
| variable-size positive-contraction DPP         | exact finite survivor     |
| Fisher cost per removed boundary mode          | at least `pi^2`           |
| canonical modewise continuous Fisher cost      | infinite                  |
| stable detector-relative probability owner     | open                      |
| Proof 416 `(EN.7)` / Gate 3U                   | open / open               |
| finite-S sign / Burnol / RH                    | open / open / unproved    |
+------------------------------------------------+---------------------------+
```

The next valid probability lane must specify both a detector-relative boundary
completion and a stable information projection on the already recombined
Burnol band.  Unless that construction produces the completed trace without a
stored phase and avoids the injectivity guard `(CA.28j)`, the probability route
must be abandoned in favor of the direct signed boundary estimate `(CA.34)`.

## 12. Lean verification

The finite trace owner was copied one way from the Windows source of truth to
the isolated Ubuntu 24.04 ext4 verification directory.  The batched checks
passed as follows:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| CCM24FiniteSCutoffTraceAnomalyAudit  | 1216  | pass   |
| CCM25Concrete aggregate              | 3700  | pass   |
| full repository                      | 3781  | pass   |
+--------------------------------------+-------+--------+
```

The audit prints exactly

```text
[propext, Classical.choice, Quot.sound]
```

for all six public trace declarations.  No `sorry`, `admit`, `sorryAx`, new
project axiom, or new linter warning was introduced.  These checks certify the
finite-dimensional cutoff identities only; they do not prove `(CA.34)`, Gate
3U, the finite-`S` sign, Burnol's identity, or RH.
