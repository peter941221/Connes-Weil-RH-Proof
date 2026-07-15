# 032 Burnol Same-Square Formula And Semilocal Gate

Date: 2026-07-12

Status: normalization passed; prime-free branch rejected by proof 113;
radial full-space escape rejected by proof 204; finite-S sign gate remains;
route Lean denied.

## Objective

Decide whether the fixed-detector route can turn one hypothetical off-critical
zero into a contradiction without importing global Weil positivity.  Keep the
same compact log square through all three layers:

```text
source zero sum
  = SelectedWeilFormulaOwner.weilValue
  = QW of the same square
  -> fixed-test CC20/M4 sign contradiction.
```

This plan does not authorize a route owner, a stored spectral equality, or a
finite-S compact remainder premise.

## Gate 1: Exact Burnol Dictionary

Let `f` be the selected additive log-coordinate convolution square and define
the multiplicative test

```text
g(u) = u^(-1/2) f(log u).
```

Burnol uses

```text
gHat(s) = integral_0^infinity g(u) u^s du/u.
```

The change of variables `u=exp(x)` gives

```text
gHat(s) = integral_R exp((s-1/2)x) f(x) dx.
```

Therefore Burnol's two pole evaluations are exactly the selected owner fields:

```text
gHat(0)+gHat(1) = laplaceAt(-1/2)+laplaceAt(1/2).
```

For `n=p^k`, the finite-place term is also exact:

```text
log(p) [g(p^k)+p^(-k)g(p^(-k))]
  = log(p) p^(-k/2)
      [f(k log p)+f(-k log p)].
```

Summing over prime powers is precisely the repository's von Mangoldt-weighted
`finitePrimeTerm`.

The archimedean expressions look different but agree.  Burnol's formula becomes

```text
(log(pi)+gamma) f(0)
  + integral_0^infinity
      [exp(y/2)(f(y)+f(-y))-2 exp(-y)f(0)]
      /(exp(y)-exp(-y)) dy.
```

The selected owner instead uses `log(4*pi)+gamma` and replaces
`-2 exp(-y)f(0)` by `-2f(0)`.  Their integral difference is

```text
-2 f(0) integral_0^infinity 1/(exp(y)+1) dy
  = -2 log(2) f(0),
```

which cancels the constant difference `log(4)=2 log(2)`.  Thus the
normalization and signs agree exactly.

Primary source:

```text
Jean-Francois Burnol, The Explicit Formula in Simple Terms,
arXiv:math/9810169v2, pp. 3-4 and the convolution-algebra theorem on pp. 10-11.
https://arxiv.org/pdf/math/9810169
```

Repository evidence:

```text
Source/CCM25Concrete/SelectedWeilSquare.lean:67-78
Source/CCM25Concrete/SelectedWeilFormula.lean:75-86
Source/CCM25Concrete/SelectedWeilFormula.lean:94-154
Source/CCM25Concrete/SelectedWeilFormula.lean:233-237
```

Verdict: pass.  `SelectedWeilFormulaOwner.weilValue` has the correct classical
shape for the same-square zero sum.

## Gate 2: Formalization Bottom

The theorem is unconditional mathematics, but the current Lean stack does not
already contain its proof.  The available ingredients include:

```text
LSeries_vonMangoldt_eq_deriv_riemannZeta_div on Re(s)>1
basic logDeriv lemmas
analytic completedRiemannXi and its functional equation
Jensen/divisor counting for completedRiemannXi
rapid vertical decay for compact Mellin tests.
```

The audit found no reusable Riemann-zeta Hadamard product, completed-Xi
logarithmic-derivative zero expansion, or general residue theorem that directly
turns the contour shift into the zero sum.  Proving the spectral identity is
therefore a substantial complex-analysis/library lane, not a wrapper theorem.

Verdict: mathematically valid but not the first route implementation target.
Do not spend that cost until Gate 3 survives.

## Gate 3: Decisive Semilocal Sign

For the archimedean CC20 remainder, M4 gives

```text
D_infinity(Q(xi*xi*)) = <xi,(-2 Id+K_I)xi>
```

and finite-dimensional bad-space orthogonality makes this strictly negative.
This controls the full selected Weil value only when no finite prime is visible.

The Xi-quotient detector is obtained by a growing physical cutoff.  Once its
square reaches `log 2`, finite-prime terms enter.  The required identity then
uses a finite-S remainder `D_S`, not `D_infinity`.  Existing source work does
not prove that the finite-place correction preserves the `-2 Id + compact`
form.  The raw finite Euler phase has noncompact partial translations, and the
metric-projection repair is rejected by the wrong second-prime-power
coefficient.

Thus the next death test is exactly:

```text
Can one keep the negative Xi detector inside a prime-free support window,
or derive a same-object finite-prime main-term subtraction whose remaining
post-Q operator is -2 Id + compact with the correct coefficient for every p^m?
```

Failure of both branches rejects Plan 028 as an executable route even after the
classical explicit formula is formalized.

The original CCM24 source audit confirms that the finite-S inequality is not
already available under another name. Its introduction calls semilocal Weil
positivity a program and defers a second semilocal prolate candidate; the
proved `theta_S`/Sonin isomorphism supplies only domain transport. See proof
112. Do not turn those transport theorems into a positive trace premise.

## Execution Order

1. Reject or prove a fixed prime-free-window Xi detector with strict negative
   zero sum and the M4 finite constraints.
2. If that fails, audit source-backed finite-S identities only; reject any
   construction that assumes compactness after leaving a prime translation in
   the remainder.
3. Require the coefficient `p^(-m/2)/m` before the crossing length
   `m log(p)` for every prime power, especially `m=2`.
4. Only after one branch passes, formalize the Burnol spectral identity on
   `SelectedWeilFormulaOwner`.
5. Then build a standalone fixed-detector contradiction before touching the
   broad route API.

The first branch is now rejected by Plan 035/proof 113. On the M4 complement,
the corrected prime-free trace identity itself gives `QW >= ||xi||^2`; no
negative detector can remain after those constraints. The only surviving
branch is a new finite-S remainder theorem.

## 2026-07-13 whole-line main-term operator assembly

Proofs 188--198 identify each selected `p^m` finite-prime atom with the
Euler-log weighted forward/adjoint whole-line crossing pair. Proof 199 first
assembled the scalar traces. Proof 200 now assembles the operators themselves
on one `SelectedWeilSquareOwner` and one whole-line Hilbert space:

```text
K_S = sum_(p,m) 1/(m sqrt(p^m)) * (T_(p,m) + T_(p,m)^dagger),
Tr(K_S) = sum_(p,m) owner.finitePrimeTerm(p^m).
```

Proof 201 upgrades the analytic status: each Hilbert--Schmidt product has an
operator-norm absolutely convergent rank-one expansion, and `K_S` is a genuine
Mathlib compact operator as well as self-adjoint and diagonal-trace legal.
This closes the finite-family arithmetic main-term operator-ideal layer. It
does not close Gate 3: compact self-adjointness is not positivity. The future positive owner
must still produce exactly `K_S` as its single-crossing component, with every
other word entering a same-domain compact self-adjoint post-`Q` remainder.

The 2025 paper *Zeta Spectral Triples* (arXiv:2511.22755) does not provide that
owner. Its abstract makes rigorous spectral convergence RH-closing, and its
Section 8 leaves two essential steps open. The 2026 finite Guinand--Weil
dictionary (arXiv:2607.02828) likewise supplies no uniform sign theorem.

## 2026-07-13 common-carrier CC20 regular operator

Proof 202 removes the Hilbert-space mismatch on the archimedean regular side.
For the actual L2 restriction `R_lambda` and indicator zero extension
`E_lambda`, Lean now proves

```text
E_lambda^dagger = R_lambda,
cc20GlobalLogWindowL2Operator = E_lambda H_lambda E_lambda^dagger.
```

The global ordinary CC20 regular-kernel operator is therefore compact and
self-adjoint on the same whole-line logarithmic L2 carrier as `K_S`.

This is not Gate 3. The module contains only the ordinary regular kernel; it
does not contain the diagonal Dirac term or the finite-S semilocal trace
read-off. The next required theorem must derive, from a genuine positive
finite-S owner, an exact same-object decomposition whose single-crossing term
is `K_S` and whose post-Q remainder includes the correct CC20 regular term.
Defining the difference of two same-domain operators would not prove that
identity.

## Verification Contract

```text
smallest source target:
  ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge

future import-facing checks:
  #check @finiteSPositiveTrace_singleCrossing_eq_namedFiniteSum
  #print finiteSPositiveTrace_singleCrossing_eq_namedFiniteSum
  #print axioms finiteSPositiveTrace_singleCrossing_eq_namedFiniteSum

rejection evidence:
  one exact coefficient mismatch, noncompact remainder block, or proof that a
  fixed prime-free window cannot retain a strict negative detector.
```

## 2026-07-13 same-object quadratic-form bridge

Proof 203 adds a complementary semantic owner on the same global L2 carrier.
`sourceRootLp owner` is the selected source test, and its inner product with a
global translation is exactly `owner.convolutionSquare.test b`. Therefore the
self-adjoint symmetric translation operator

```text
log(p) / sqrt(p^m) * (T_(m log p) + T_(-m log p))
```

has quadratic form `owner.finitePrimeTerm (p^m)` for every prime `p` and
nonzero exponent `m`; finite sums give the corresponding finite-prime sum.
This confirms the arithmetic main term on one explicit vector and one square,
but it is intentionally noncompact and supplies neither finite-S positivity
nor the post-Q remainder sign. The active Gate 3 bottom is unchanged.

## 2026-07-13 radial full-space collapse

Proof 204 rejects a carrier-only escape from the invariant semilocal model.
Let `E_K` be Haar averaging onto `L2(X_S)^K_S`. For the existing radial zeta
test `g(c)=g_0(Mod_S(c))`, its integrated scaling operator satisfies

```text
U(g) = E_K U(g) = U(g) E_K.
```

Therefore every bounded full-space sandwich obeys

```text
U(g)^* B U(g) = U(g)^* E_K B E_K U(g).
```

Nontrivial `K_S` input/output blocks are invisible to the same radial test.
In particular, lifting the direct one-prime cocycle owner from the invariant
space to full `L2(X_S)` leaves the scalar Euler channel unchanged, so proof
026's central `2^(-1) log(2)` Dirac coefficient and unbounded post-`Q`
principal part still apply.

This does not reject an explicitly new invariant block `E_K B E_K` or an
unbounded relative form. It does reject treating the larger carrier itself as
the missing cancellation mechanism. Any successor must now provide one of:

```text
1. a new invariant compression with an exact same-object finite-S trace
   identity and a common-domain remainder sign; or
2. an unbounded/relative positive form with a proved common form domain and
   the same exact arithmetic read-off.
```

A nonradial operator obtained by integrating only along a chosen section of
`C_S -> C_S/K_S` is a different test owner, not an escape for the same radial
test. It needs a new semilocal trace formula before any nontrivial `K_S`
character channel can be identified with the selected `finitePrimeTerm`.

No Lean owner is authorized. Gate 3 and the RH route roots are unchanged.

## 2026-07-13 inverse-log metric projection rejection

Proof 205 proposed a positive translation-invariant metric. For a
finite prime set `S_f`, put

```text
ell_S = sum_(p in S_f) log((I-p^(-1/2)U_p)^*(I-p^(-1/2)U_p)),
b_S = sum_(p in S_f) 2 log(1+p^(-1/2)),
H_S = ((1+b_S)I-ell_S)^(-1).
```

The scalar `b_S` is essential for `0<H_S<=I`. It does disappear from the
formal block `Q(I-H_S^(-1))R`, but proof 206 shows that it does not disappear
through the compressed inverse `(R H_S R)^(-1)`. The exact finite-place factor
is

```text
Q H_S R(R H_S R)^(-1)
  =((1+b_S)Q-Q ell_S Q)^(-1)Q ell_S R.
```

For one prime its difference from `Q ell R` contains

```text
a^2(2Q(U+U*)R+Q(U+U*)Q(U+U*)R)+O(a^3).
```

The first term is another noncompact one-step crossing; the second has even
translation degree and cannot cancel it. Therefore Plan 046 fails before the
weighted Wiener and common-domain gates.

Proof 207 also rejects prescribing the exact Euler-log regression map to an
otherwise unknown translation-invariant metric. Such a metric would make its
graph invariant under the unilateral shift, while the Euler-log Hankel graph
violates that invariance by the nonzero coefficient `d_0 d_s`.

Gate 3 is open again at the stronger boundary: a successor must use a genuine
two-cutoff Sonin identity or a common-domain unbounded relative form. It may
not reuse either inverse-log split. No Lean owner or route rewire is
authorized. See Plans 046--047 and proofs 206--207.

## 2026-07-13 endpoint collar and current-source verdict

Proof 208 rejects the immediate pole-free endpoint-wall escape. In the final
prime-indicator cell, with `x=a-d` and `c=exp(2a)`, the source potential is

```text
kappa_a(a-d)
 = -(1/2)log(d(2a-d))-log(2*pi)-EulerGamma
   -F(d)-F(2a-d)-sum_(q<c) Lambda(q)/sqrt(q).
```

Its derivative is `J(2a-d)-J(d)<0`, so the endpoint collar has one exact root
`d_c`. Partial summation gives

```text
-log(d_c)=4 sqrt(c)+o(sqrt(c)).
```

Arb certifies widths from `1.33e-4` at `c=5` down to `1.31e-175` at
`c=10000`. A root translated into one such collar has convolution-square
support below `log 2` at the certified and asymptotic cutoffs, hence sees no
finite prime. Proof 113 then makes it strictly QW-positive on the M4
complement. It cannot also be the strict negative Yoshida detector. The
two-collar class is outside this rejection, but it has neither a determining
theorem nor the required same-object finite-S trace read-off.

Proof 209 also rejects the proposed source composition. Zenodo 20710075 proves
only the prime sign on `C=cosh(x/2)` and leaves the odd prime competition open;
arXiv:2607.02828 proves total positivity only for the isolated post-band
archimedean increment. Zenodo 20737111 and 20694588 reduce the arithmetic
ordering to scalar Loewner/Herglotz inequalities but explicitly leave those
inequalities open. Zenodo 21326823 version 4, published 2026-07-12, proves
simple strictly interlacing parity determinants for the negative
Connes--Moscovici prolate spectrum; its source explicitly says the bridge to
the truncated Weil form remains open.

Therefore Gate 3 does not move to a finite Loewner, Herglotz, endpoint-collar,
or exact-CM-prolate owner. The surviving target remains the genuine two-cutoff
finite-S post-Q identity or a common-domain unbounded relative form whose
single crossings are the existing named operator sum. No Lean owner or route
rewire is authorized.

## 2026-07-13 two-cutoff central-atom verdict

Proof 210 rejects the bounded two-cutoff positive-angle branch.  In the
additive log coordinate let `P_r=1_[r,infinity)`, let `s` be the independently
chosen Fourier threshold, and for one prime write

```text
v_a=sum_m c_m T_(m log p),
c_1=-a,
c_(-j)=(1-a^2)a^j,
a=p^(-1/2).
```

The natural positive owner

```text
B_(r,s)=P_r v_a^*(1-P_s)v_a P_r
```

has the exact central coefficient

```text
b_(r,s)(a)
  =sum_m |c_m|^2 (s-r-m log p)_+ > 0
```

for every finite pair `(r,s)`.  Equal cutoffs give
`b=a^2 log(p)`, exactly the obstruction in proof 026.  At separations
`r-s=n log(p)`, the coefficient is `log(p)a^(2n+2)`: it can be made small but
never zero at finite cutoff.

A positive difference of nested Fourier cutoffs is a genuine cutoff-band
square, but its central coefficient is again strictly positive.  A difference
of nested support compressions is not positive unless the cross block between
the support shell and the retained half-line vanishes; the Euler/Fourier angle
does not have that invariance.  After `Q=-partial^2+1/4`, the surviving central
atom grows like `b t^2` on narrow modulated roots, while the archimedean
`-2 Id+compact` remainder and the mixed cocycle term are bounded/compact.

Thus no finite positive two-cutoff angle, positive cutoff-band difference, or
finite convex combination can supply the missing cancellation.  Sending the
cutoff separation to infinity collapses the positive owner and gives no
uniform sign theorem.  Gate 3 is now reduced to a genuinely common-domain
relative form that explicitly renormalizes this second-order central piece.
No Lean owner or route rewire is authorized.

## 2026-07-13 compressed Euler-log Jensen verdict

Proof 211 checks the most direct relative-log repair.  For

```text
H_a=(I-aU)^*(I-aU),
ell_a=-log(H_a)=sum_(m>=1)a^m(U^m+U*^m)/m,
A_a=R H_a R | Ran(R),
```

the direct logarithm has exactly the required Euler coefficient before the
crossing length supplies `m log(p)`.  It is not positive: its bilateral-shift
symbol takes the values `-2log(1-a)>0` and `-2log(1+a)<0`.  The scalar shift
that makes it positive is a noncompact same-range bulk and recreates the
post-Q central second-order obstruction.

The operator-convex compression gap

```text
J_a=R(-log H_a)R+log(A_a)>=0
```

is genuinely positive by Hansen--Pedersen Jensen.  However,

```text
J_a=(a^2/2)R(U+U*)Q(U+U*)R+O(a^3).
```

Its coefficient-correct first-order single crossing cancels.  The resolvent
Schur-complement formula proves that every term of `J_a` contains an
off-diagonal block and its adjoint, hence at least two Sonin-boundary
crossings.  The positive gap belongs to the multi-crossing remainder ideal and
does not carry the existing finite-prime crossing sum.  Subtracting it loses
positivity and merely restates the missing domination theorem.

Gate 3 therefore cannot use a finite-place compressed-log Jensen gap.  The
remaining relative form must couple the archimedean unbounded owner to the
Euler logarithm before positive completion, so that a first-order cross term
survives without scalar central bulk.  No Lean owner or route rewire is
authorized.

## 2026-07-13 p=2 scalar-budget lower gate

Proof 212 gives an exact obstruction inside the remaining common-domain lane.
At cutoff `c=2^8=256`, divide the source-root interval into eight cells of
length `L=log(2)` and repeat one arbitrary cell function in every cell.  The
visible `p=2` translation operator then has the constant-cell Rayleigh quotient

```text
R_8=(L/4)sum_(m=1)^7(8-m)2^(-m/2)
   =2.007741159155714... > 2.
```

The strict inequality has an exact rational certificate using
`1/sqrt(2)>707/1000` and `log(2)>693/1000`; the latter follows from four
positive terms of the `2 atanh(1/3)` series.  The three route Mellin rows become
three linear conditions on the one-cell function, leaving an
infinite-dimensional subspace with the same Rayleigh quotient.  An orthonormal
sequence in that subspace is weakly zero, so every compact correction vanishes
along it.  Therefore

```text
2 Id + compact - K_(p=2)
```

is not nonnegative on the triple-vanishing domain.

This does not reject the common-domain route.  It proves that the
archimedean positive trace in the corrected CC20 identity is quantitatively
essential: it cannot be discarded after noting only that it is nonnegative.
The next gate is an explicit lower bound for that positive trace against the
finite-prime excess on the same one-cell/Floquet fibers.  No Lean owner or
route rewire is authorized.

## 2026-07-13 strict CC20 multiplier and p=2 gate

Proof 214 certifies the unconditional archimedean theorem

```text
ell_CC20(t)=2 theta'(t)+delta_hat(t) > 1/50
```

for every real `t`.  On `[0,50]`, 1251 Arb Taylor balls use an explicit
`|ell_CC20''|<100` bound; the smallest lower endpoint is
`0.029051430687854`.  For `|t|>=50`, monotonicity of `2 theta'`, the variation
bound `integral |d'|<50` for `d(x)=delta(exp x)`, and an Arb endpoint check give
the lower endpoint `0.074129271185...`.  The `delta` integration tail and its
first derivative are charged using

```text
|delta(exp x)-exp(-x/2)| <= 2exp(-3x/2),  x>=8.
```

Plancherel therefore gives the common-domain coercive estimate

```text
PositiveTrace_infinity(Q(g*g*))
 > (1/50)(||g'||^2+(1/4)||g||^2).
```

The session initially inferred a complete visible `p=2` pass from this bound
and Proof 213.  That inference is withdrawn by the Q-root ownership correction
immediately below.  Proof 214 remains an independent multiplier theorem; it
does not by itself advance Gate 3 to the all-prime problem.

## 2026-07-13 Q-root ownership correction

Proof 217 supersedes the preceding claim that Proof 213 passes a same-object
`p=2` gate.  The exact CC20 post-Q relation uses two linked roots:

```text
g=(d/dx+1/2)xi,
g* * g=Q(xi* * xi),
D_infinity(g* * g)=<xi,(-2 Id+K_I)xi>.
```

Consequently the finite-prime form is `<g,K_c g>`, whereas the scalar and
ordinary compact terms act on `xi`.  Proof 213 instead compared

```text
PositiveTrace(Q(g* * g))+2||g||^2-<g,K_c g>,
```

which applies the Q multiplier to the positive trace without applying the
matching first-order multiplier to the finite-prime root.  That is a different
convolution square.

On the range condition, the genuine pre-root is

```text
xi(x)=exp(-x/2) integral_(-a)^x exp(t/2)g(t)dt.
```

The corrected coarse form obtained from Proof 214's minimum alone is

```text
(1/50)||g||^2+2||L^(-1)g||^2-<g,K_c g>.
```

The corrected grid screen is strongly negative: about `-2.026` for the
single `p=2` channel at `c=256`, size 1000, and about `-2.96` for all visible
prime powers at `c=10000`, size 500.  The sign is stable under the pole and
range rows.  These are death diagnostics rather than continuum certificates;
the exact ownership mismatch already withdraws the old pass.

Proof 214 remains an accepted standalone theorem:

```text
ell_CC20(t)>1/50 for every real t.
```

Proof 215's continuous PNT-main sign also remains exact in its raw model, and
Proof 216 gives an Arb-certified no-go for a constant scalar PNT-main
S-procedure at `c=10^6`.  Neither is a same-object Q-root producer.

Gate 3 is reset to the full-multiplier comparison

```text
<g,(ell_CC20(D)-K_c)g>
  +2||L^(-1)g||^2
  -<L^(-1)g,K_I L^(-1)g>.                            (G3-corrected)
```

Do not replace `ell_CC20` by its global minimum, do not put the prime operator
on the pre-root, and do not call Proofs 213--216 finite-Euler route passes.
No Lean owner or route rewire is authorized.

## 2026-07-13 archimedean relative-form collapse

Proof 218 closes the corrected archimedean algebra.  Since

```text
ell_CC20(t)=2 theta'(t)+delta_hat(t),
|g_hat(t)|^2=(t^2+1/4)|xi_hat(t)|^2,
```

the `delta_hat` part of `PositiveTrace_infinity(g)` is exactly
`D_infinity(Q(xi* * xi))=<xi,(-2 Id+K_I)xi>`.  Therefore

```text
PositiveTrace_infinity(g)-D_infinity(g* * g)
  = <g,2 theta'(D)g>,
```

and `(G3-corrected)` is simply

```text
<g,(2 theta'(D)-K_c)g>=QW(g,g)
```

after the pole rows vanish.  The strict bound `ell_CC20>1/50` supplies no
independent surplus once the same-object remainder is subtracted.

Gate 3 cannot close through a purely archimedean relative-form estimate: that
would be the restricted Weil sign itself.  The active bottom returns to a
genuine finite-S positive owner with a semilocal post-Q remainder not obtained
by merely decomposing the archimedean identity, or to a new detector-specific
property strong enough to control the exact prime form.  No such producer is
currently known, and no Lean owner is authorized.

## 2026-07-13 cutoff-event and detector-Schur rejection

Proof 219 closes two immediate continuations after the relative-form collapse.
First, the cutoff-free finite Weil path cannot be proved positive by pairing
each prime-power event with the following cutoff interval.  Using the official
Arb matrix builder from arXiv:2607.02828, the increments from `c=2` to `c=3`
are strictly negative both in the scalar `N=0` coordinate and in the exact odd
`N=1` coordinate:

```text
scalar: -0.0610540277693744...
odd:    -0.1307698745455364...
```

The same strict failure recurs on several later consecutive prime-power
intervals.  This rejects an interval-by-interval PSD telescope, including the
odd Yoshida sector; it does not reject a nonlocal multi-interval identity.

Second, the first critical-zero Xi quotient was used as a limiting-shape
screen for detector-specific positive Schur absorption.  First-prime channels
alone misleadingly approach the unit cost, but restoring every required
`q=p^m` channel with pre-crossing weight `1/(m sqrt(q))` gives costs

```text
q<=11:   1.202546270438
q<=50:   2.865228837928
q<=250:  5.698625603386.
```

These values are stable under three Fourier-grid refinements but remain
diagnostic, not an interval theorem about a hypothetical off-line zero.  They
forbid treating the canonical Xi shape or its first-prime truncation as an
already-passed Schur budget.

The rational-cancellation/PNT repair also has no missing exponential gain:
the off-line symmetry orbit creates opposite half-line rational tails, so a
tail cutoff `T` creates a root span and prime-log range of order `2T`.  The
squared `exp(-delta T)` approximation is exactly balanced by the contribution
of a supremal-displacement target zero.  Any reopening needs a signed
target-zero prime cancellation, not only subtraction of the PNT main term.

Gate 3 remains open at the same two objects: a new finite-S same-object
positive owner, or a new detector-specific identity for the complete
prime-power form.  No Lean owner or route rewire follows from Proof 219.

## 2026-07-14 metric projection and triangular principal channel

Proofs 220--221 retain the exact Q-root ownership and show that the weighted
Chebyshev target-orbit term is the original negative detector signal, not an
independent positive budget.  They do not produce the finite-S sign.

Proof 222 repairs the former factor-two rejection of the endpoint metric
projection.  On each half-line translation fiber the exact Laurent diagonal
sums of the relative projection are

```text
q_0=0,
q_k=-a^|k| for k!=0.
```

The interrupted word at order `a^2` removes one boundary cell, so every
prime-power coefficient is the required `p^(-m/2)log(p)`.  Proofs 042, 124,
and 127 no longer reject this local coefficient owner.

Proof 223 rejects transporting CC20's archimedean prolate angle as a
Q-stable trace-class correction.  Its finite-Euler central coefficient is
`a^2 log(p)`, whereas Proof 222's relative metric projection has zero central
Laurent coefficient.  The difference grows quadratically after `Q`.

Proof 224 supplies the correct same-object globalization.  For nested
projections `R<=E`, their metric images remain nested and

```text
R_a-R=(E_a-E)-[(E_a-R_a)-(E-R)].
```

The first difference is Proof 222's exact Euler series.  The bracket is a
canonical nested-complement projection with an explicit Schur-complement
owner.  This closes operator bookkeeping but leaves its post-`Q` analytic
class and sign open.

Proof 225 closes only the normalized fixed-frequency principal channel.  For
`a_q(r)=(1-cos(qr))/r^2`,

```text
Fourier(a_q)(xi)=pi(q-|xi|)_+.
```

The principal residual is therefore an archimedean chirp multiplied by a
compact triangular band.  Its inverse Fourier response is locally smooth, so
every fixed-`q` finite-window post-`Q` compression is Hilbert--Schmidt even
though its pointwise symbol need not decay.

This does not settle the actual metric kernel.  CCM24's ambient factor
`E_S=product_v L_v` defines the norm weight; it is not automatically the
Hermite--Biehler generator of the Sonin de Branges subspace.  The exact kernel
has a nonconstant isometric-multiplier amplitude.  In addition, fixed-`q`
compactness does not by itself give a summable estimate for
`q=m log(p)`.

The active Gate 3 analytic target is now exact:

```text
1. identify the Hermite--Biehler/isometric multiplier for the metric kernel;
2. prove its amplitude correction is locally H^2, uniformly in
   0<=alpha<=p^(-1/2);
3. prove compatible locally H^2 growth for q=m log(p), summable against the
   exact Euler coefficients;
4. otherwise extract a fixed-frequency atom and reject compactness;
5. only after compactness, prove the independent three-Mellin-row sign.
```

No Lean owner or route rewire is authorized.  RH remains unproved.

## 2026-07-14 exact oblique-defect amplitude owner

Proof 226 supersedes the preceding instruction to search first for an unknown
Hermite--Biehler amplitude.  CCM24 already fixes the metric on the common
Mellin carrier.  For the archimedean Sonin projection `P`, put

```text
T_alpha=I-alpha U,
H_alpha=T_alpha* T_alpha,
A_alpha=P H_alpha P | Ran(P),

P_alpha=T_alpha P A_alpha^(-1)P T_alpha*.
```

The canonical oblique projection onto the same transported range is

```text
Q_alpha=T_alpha P T_alpha^(-1).
```

With `Delta_alpha=Q_alpha-P_alpha`, common-range algebra gives the exact
identity

```text
P_alpha
 =Q_alpha Q_alpha*-Delta_alpha Delta_alpha*.
```

Thus the nonconstant amplitude is the negative of one named positive square,
not a free structure function.  In the block decomposition
`Ran(P) direct-sum Ran(I-P)`, its exact Schur owner is

```text
Delta_alpha Delta_alpha*
 =T_alpha P A^(-1) C Sigma^(-1) C* A^(-1)P T_alpha*,

C=-alpha P(U+U*)(I-P).
```

Every amplitude word therefore contains two boundary crossings and begins at
order `alpha^2`.  CC20's `quantsmooth` lemma and its scattering-conjugate
version make the amplitude trace legal for every compact smooth Q-root, and

```text
Tr(C_g* C_g P_alpha)
 =Tr(C_g* C_g Q_alpha Q_alpha*)
   -norm(C_g Delta_alpha)_HS^2.
```

The individual amplitude contribution has a fixed nonpositive sign.  The
compressed inverse has the uniformly convergent expansion

```text
A_alpha^(-1)
 =(1/(1+alpha^2))
   sum_(n>=0)(alpha/(1+alpha^2))^n[P(U+U*)P]^n,

2alpha/(1+alpha^2)<=2sqrt(2)/3<1.
```

Hence any polynomial Euler-word factor is uniformly summable throughout
`0<=alpha<=p^(-1/2)`.

This does not order the nested amplitudes.  The exact finite-dimensional
counterexample

```text
U e1=e2, U e2=e3, U e3=e1,
alpha=1/4,
R=span(e1), E=span(e1,e2)
```

has

```text
<e1,(Amp(E)-Amp(R))e1>=-256/4641,
<e2,(Amp(E)-Amp(R))e2>=2032/41769.
```

Therefore `R<=E` supplies no generic sign for the difference of defect
squares.  The next target must use the special Sonin scattering phase and the
same compact Q-root to control the complete combination

```text
[Q_R Q_R*-Q_E Q_E*]
  -[Delta_R Delta_R*-Delta_E Delta_E*],
```

after the exact half-line Euler series is removed.  Proving the phase and
amplitude pieces separately by absolute estimates can destroy their required
cancellation.  Compactness and the three-row sign of this complete nested
combination remain open.  No Lean owner or route rewire is authorized.

## 2026-07-14 complete nested metric flow

Proof 227 supersedes the separated uniform estimates requested at the end of
Proofs 225--226.  Let `R_alpha<=E_alpha` be the transported Sonin and crossed
half-line metric projections, and put

```text
B_alpha=E_alpha-R_alpha,
C_alpha=I-E_alpha,
X_alpha=-U(I-alpha U)^(-1).
```

The exact projection flow is

```text
B_alpha'
 =C_alpha X_alpha B_alpha+B_alpha X_alpha* C_alpha
  -B_alpha X_alpha R_alpha-R_alpha X_alpha* B_alpha.
```

Equivalently, with

```text
Y_alpha=C_alpha X_alpha B_alpha-R_alpha X_alpha* B_alpha,
```

one has

```text
B_alpha'=Y_alpha+Y_alpha*.
```

All diagonal phase and amplitude terms cancel before this formula is formed.
The Euler words are already summed by the uniformly bounded resolvent

```text
X_alpha=-sum_(m>=1)alpha^(m-1)U^m,
alpha<=p^(-1/2)<=1/sqrt(2).
```

Thus the two previous gates

```text
uniform principal q=m log(p) summation;
uniform separate amplitude summation
```

are removed as independent targets.  The correct remaining compactness target
is one local Hilbert--Schmidt estimate for the complete crossing difference
`Y_alpha+Y_alpha*` on the same compact `Q`-root, integrable in `alpha`.

There is no abstract monotonicity shortcut.  Since the derivative is
off-diagonal relative to `B_alpha`, it anticommutes with `2B_alpha-I` and is
indefinite whenever nonzero.  This rejects a sign proof based only on nesting
or monotonicity, but it does not decide the integrated form on the three-row
subspace.  Compactness, the integrated three-row sign, and RH remain open.  No
Lean owner or route rewire is authorized.

## 2026-07-14 Euler chirp operator-norm compactness

Proof 228 removes the apparent non-summability of the critical positive
endpoint in Proof 225.  For `L=log(p)`, `a=p^(-1/2)`, and `q_m=mL`, the exact
weighted endpoint kernel is

```text
a^m k_infinity(x-y+q_m)
 =2exp((x-y)/2)cos(2pi p^m exp(x-y)).
```

Its Hilbert--Schmidt norm on a fixed interval does not decay.  However the
complex phase kernel

```text
exp((x-y)/2)exp(2pi i lambda exp(x-y))
```

is exactly unitarily conjugate, under `u=exp(x)` and `w=exp(-y)`, to a Fourier
transform from `exp(-I)` to `lambda exp(I)`.  Plancherel gives

```text
norm(K_lambda)<=lambda^(-1/2).
```

Consequently the real endpoint operator at `lambda=p^m` has norm at most
`2p^(-m/2)`, and every fixed polynomially weighted Euler sum converges in
operator norm to a compact operator.  The negative endpoint is already
Hilbert--Schmidt summable with coefficient `p^(-m)`.

Do not require termwise Hilbert--Schmidt summability: it discards the exact
oscillatory Fourier gain.  The remaining Proof 227 bottom is now the internal,
non-endpoint profile of the complete crossing `Y_alpha+Y_alpha*`, followed by
the independent integrated three-row sign.  No Lean owner or route rewire is
authorized; RH remains unproved.

## 2026-07-14 complete principal Euler profile compactness

Proof 229 sums the full normalized triangular profile before applying post-Q.
For

```text
W_p(r)=sum_(m>=1)p^(-m/2)(m log(p)-r)_+,
```

and `r=n log(p)+t`, `0<=t<log(p)`, the exact cell formula is

```text
W_p(r)
 =p^(-(n+1)/2)
   (log(p)-(1-p^(-1/2))t)/(1-p^(-1/2))^2.
```

The envelope is continuous, and its derivative jump at `n log(p)` is exactly
`p^(-n/2)`.  In the only non-absolutely differentiable convolution tail, the
cell phase satisfies `partial_r Phi_n=partial_t Phi_n`.  Two integrations by
parts move the post-Q derivatives onto the cell amplitude.  First boundary
values cancel by continuity; the remaining derivative-jump chirps have size
`p^(-n/2)` and acquire Proof 228's additional `p^(-n/2)` operator-norm gain.
They are therefore summable as `p^(-n)`.  Cell interiors are HS-summable as
`p^(-n/2)`.

Hence the complete normalized principal Euler channel is compact on every
finite root interval.  It need not be Hilbert--Schmidt.  Proof 227's `(F.23)`
is a sufficient but unnecessarily strong contract; the sharp full-metric
target allows an HS-summable interior plus an operator-norm-summable chirp
boundary.  Only the nonconstant metric part of the complete crossing and the
integrated three-row sign remain open.  No Lean owner or route rewire is
authorized; RH remains unproved.

## 2026-07-14 metric complement ideal invariance

Proof 230 removes an independent essential-spectrum concern from the
nonconstant metric part.  In a unital C*-algebra, let `r<=e`, `b=e-r`,
`T=I-alpha u`, and let `r_alpha,e_alpha` be the exact orthogonal metric images.
For any closed two-sided ideal `J`,

```text
[b,u] in J
  => (e_alpha-r_alpha)-b in J.
```

The proof passes to the quotient by `J`.  There `b` commutes with `T* T`, the
compression to `e=r+b` becomes block diagonal, and

```text
T b(b T* T b)^(-1)b T*=b.
```

Thus the complete metric correction belongs to the ideal generated by the
single source commutator `[b,u]`.  Compressed inverses, Schur complements, and
oblique-defect squares cannot create a new quotient class.

This does not by itself prove root compactness because the smoothed trace
read-off is not a *-homomorphism on all ambient operators.  The remaining
compactness bottom is now exact: prove that Proofs 228--229's profile class
(HS-summable interiors plus operator-norm-summable logarithmic chirps) is
stable under the Euler, half-line, scattering, and prolate words surrounding
the source commutator.  The integrated three-row sign remains independent.
No Lean owner or route rewire is authorized; RH remains unproved.

## 2026-07-14 quantitative metric graph factorization

Proof 231 strengthens the ideal statement.  With `b=e-r`,
`h=T* T`, and the Schur blocks

```text
A=r h r,
C=r h b,
D=b h b,
Z=b-r A^(-1)C,
```

the nested complement is the graph projection onto `T Z`, while the bare
metric image of `b` is the graph projection onto `T b`.  If
`delta=norm([b,u])` and `alpha<1`, then

```text
norm(C)<=2alpha delta,
norm((I-b)T b)<=alpha delta,
```

and the graph-gap estimate gives the explicit bound

```text
norm(b_alpha-b)
 <=[alpha/(1-alpha)+4alpha(1+alpha)/(1-alpha)^3] delta.
```

Thus the entire metric correction is a bounded graph dressing of the single
source commutator.  The finite-window Q-root read-off is still not an ambient
*-homomorphism, so this is not yet full compactness.  It does remove any need
to estimate phase and amplitude separately; the next gate is only the
root-form stability of these two graph factors.  No Lean owner or route
rewire is authorized; RH remains unproved.

## 2026-07-14 metric graph quadratic remainder

Proof 232 gives exact graph and Schur tangents for the full metric correction.
Every term beyond the named linear channel `Lambda_alpha` contains at least
two copies of `[b,u]` or its adjoint.  CC20's smoothed one-crossing
Hilbert--Schmidt estimate factors those nonlinear terms through two
Hilbert--Schmidt blocks, so their root operator is Hilbert--Schmidt.  WSL
certificates at `p=2,3` show the nonlinear residual divided by
`norm([b,u])^2` stabilizing near `1.1634` and `0.8509`.

## 2026-07-14 half-line Toeplitz path profile

Proof 233 proves

```text
P U^(epsilon_1) P ... U^(epsilon_k) P
  =1_[M(epsilon) log(p),infinity) U^(sum epsilon_j),
```

where `M` is the maximum partial path sum.  The endpoint amplitude
`p^(M/2)` cancels Proof 228's chirp gain `p^(-M/2)` path by path.  Mixed
metric words have total coefficient `eta^k`, with
`eta=2alpha/(1+alpha^2)<=2sqrt(2)/3`, so every fixed polynomial graph-order
weight remains summable.  This closes the `M^(-1)` and `D^(-1)` half-line
branches.

## 2026-07-14 Sonin alternating-profile closure

Proof 234 uses `P P_hat P=r+K_prol`.  The source commutator becomes three
boundedly dressed half-line commutators plus the trace-class
`[K_prol,U]`.  A power telescope gives only polynomial cost for prolate
insertions.  Since scattering and Euler multipliers commute with logarithmic
`Q`, no-prolate words have only linearly many half-line cut points and are
dominated by `(1+k)^2 eta^k` in the sharp profile norm.

Consequently the complete metric post-Q correction is compact at the
mathematical route-evidence level.  It need not be Hilbert--Schmidt.  The
active bottom is now the same-domain integrated sign of the named compact
correction on the common kernel of the three Mellin rows.  No Lean owner or
route rewire is authorized; RH remains unproved.

## 2026-07-14 unscaled Yoshida fixed-threshold escape

Proof 235 removes the detector radius--convolution-count loop that invalidated
the fixed-window version of Proof 041.  The support-preserving rescaling had
changed the contraction threshold from `T` to `(n+1)T`; choosing the nearby
zero radius therefore required the still-unknown convolution count.

The new axiom-clean Lean chain keeps the base factors unscaled.  For one fixed
base and one finite correction it proves

```text
|t/(2pi)|^2 |Laplace(f^(n+1)*correction)(sigma+it)|
  <=(1/2)^(n+1) C
```

at the original fixed threshold `|t|>=T`.  The corresponding distance bound
is epsilon-small after choosing `n`, while the support is recorded as

```text
((n+1)log(a)+lower, (n+1)log(b)+upper).
```

`exists_fixedThreshold_nearbyZero_unscaled_normalized_assembly` puts the
normalization at `rho`, cancellation at every other selected finite node,
growing support, and far-tail estimate on the same convolution product.  Its
quantifier order is `exists T, forall R, exists correction C n`; hence the
nearby radius is chosen after the fixed threshold and the count is chosen only
after the correction constant.

This result makes the growing-support Yoshida detector lane executable.  The
finite-S post-Q sign and the semilocal positive owner remain open, and route
consumers remain unchanged.  The next same-object target is to feed this
detector into the existing finite-prime owner and prove the integrated sign of
the named compact remainder on the common three-row kernel.  RH remains
unproved.

## 2026-07-14 half-density centered owner repair

Proof 236's raw theorem was algebraically valid but its selected-coordinate
interpretation was wrong.  Burnol's spectral variable is `u=rho-1/2`.  For
the mandatory half-density shift `H_c(x)=exp(x/2)H(x)`, the actual identity is

```text
Laplace(H_c^star*H_c)(rho-1/2)
  =conj(Laplace(H)(1-conj(rho))) Laplace(H)(rho).
```

Therefore the raw source companion is `1-conj(rho)`, not `-conj(rho)`.
Proof 237 repairs the owner explicitly.  The new Lean definition
`halfDensityShift` preserves compact support and proves
`Laplace(H_c)(u)=Laplace(H)(u+1/2)`.  `selectedOwner` now owns `H_c`, while
`exists_fixedWindows_nearbyZero_unscaled_sourceOrbit_assembly` constructs the
same raw factor at both `rho` and `1-conj(rho)`.

The corrected no-premise existence theorem returns, for one selected owner,

```text
Laplace(owner.sourceTest)(rho-1/2)=1,
Laplace(owner.sourceTest)(-conj(rho-1/2))=1,
Laplace(owner.convolutionSquare)(rho-1/2)=1,
Laplace(owner.convolutionSquare)(z-1/2)=0
  for selected source z outside {rho,1-conj(rho)}.
```

It also multiplies the two source-factor tails into the same-square bound

```text
|z-rho|^2 |(1-conj(z))-rho|^2
  * |Laplace(owner.convolutionSquare)(z-1/2)| < epsilon^2.
```

The existing finite-family whole-line crossing sum remains attached to this
same owner.  It is self-adjoint, compact when supplied the existing per-prime
factor-basis witnesses, and its ordinary trace is the same owner's
finite-prime sum.  Those basis witnesses remain explicit theorem parameters.

The corrected construction still normalizes the two target source values to
`+1`; it therefore detects the orbit positively.  The next algebraic theorem
must interpolate the full source orbit with values

```text
H(rho)=1,
H(1-conj(rho))=-1,
H(conj(rho))=0,
H(1-rho)=0,
```

so that the centered square orbit contributes `-2`.  Even that does not close
Gate 3: it must be combined with the quartic tail, finite nearby-zero
cancellation, finite bad-space orthogonality, and the integrated same-domain
sign of the actual finite-S remainder `-2 Id+K_(S,I)`.  No route rewire is
authorized; RH remains unproved.

## 2026-07-14 negative orbit owner

Proof 238 closes the negative finite-orbit algebra on the corrected
half-density owner.  A new generic assembly keeps the repeated base equal to
one at every target and puts arbitrary values in the final correction, so the
target `-1` is independent of the convolution-count parity.

The source orbit is represented by the actual finite set

```text
{rho,1-conj(rho),conj(rho),1-rho}.
```

Its adaptive values are `1` at `rho`, `-1` at the distinct companion
`1-conj(rho)`, and zero elsewhere.  After the half-density translation, Lean
proves that the same selected square has orbit sum exactly `-2`.  The proof
handles both the four-point nonreal orbit and the two-point conjugation-fixed
orbit, so the final existence theorem needs no `Im(rho) != 0` premise.

`exists_fixedWindows_nearbyZero_negativeOrbit_selectedOwner` now puts the
negative orbit sum, finite nearby-zero cancellation, growing support,
quadratic source tail, and fourth-order selected-square tail on one owner.
This removes the positive-detection defect left by Proof 237.

Gate 3 is still open.  The theorem does not prove Burnol's all-zero spectral
identity in Lean, identify the named crossing sum with a finite-S positive
owner, or prove the integrated sign of `-2 Id+K_(S,I)`.  Proof 113 also forbids
reinterpreting compact bad-space orthogonalization as a prime-free shortcut.
The surviving next target is the complete finite-S same-domain trace/sign
identity for this owner; no route rewire is authorized and RH remains
unproved.

## 2026-07-14 constrained sign death test

Proof 239 combines the literal archimedean Q-delta kernel with Proof 224's
one-prime nested-complement finite section and imposes the two independent
Q-root Mellin rows.  Raw grids show positive constrained eigenvalues at
several resolutions, but their maximizing vectors place `60%--74%` of their
mass in the artificial boundary entries and move with the grid.  They are not
stable bad eigendirections.

Fixing the lowest smooth Dirichlet modes before refining the scattering grid
changes the verdict.  The first six `p=2` modes remain strictly negative
through `cells=28`; the first eight `p=3` modes remain strictly negative
through `cells=24`.  A ten-mode `p=2` crossing at `cells=24` disappears at
`cells=28`.  Thus the current diagnostic neither rejects nor proves the sign
gate.

Because Proof 234's proposed continuous correction is compact, a genuine bad
eigenvalue must eventually appear in a fixed Galerkin scale under an
operator-norm-consistent discretization.  A direction that continually
escapes to a shrinking boundary layer violates that consistency test.  Do not
use raw full-grid eigenvalues from the scattering proxy as route evidence.

The numerical lane must now prove a convergent Galerkin approximation of the
same post-Q owner before enlarging matrices.  The analytic lane remains the
integrated three-row sign of the named continuous compact correction.  No
route rewire is authorized and RH remains unproved.

## 2026-07-14 certified row-only archimedean counterexample

Proof 240 closes the numerical uncertainty left by Proof 239, but it changes
the target rather than closing Gate 3.  The current route convention has nodes
`s=0,1/2,1` (Proof 072), so for `g=(d/dx+1/2)xi` the two independent pre-root
rows are `M_0(xi)=M_1(xi)=0`.  On the interval

```text
I=[0,3 log(2)/2],
```

the fixed four-mode Dirichlet witness with modes `{1,2,3,5}`, coefficients
`c_1=-8/15`, `c_3=c_5=1`, and `c_2` defined by the exact `M_1` equation has

```text
<xi,(-2 Id+K_infinity)xi> > 1.3868,
Rayleigh quotient > 0.596.
```

The value is certified by an Arb one-dimensional integral after integrating
the CC20 derivative kernel by parts; no finite scattering matrix, Sonin cutoff,
or grid eigenvector is involved.  Therefore the universal row-only implication
`M_0=M_1=0 => D_infinity<=0` is false once the first prime is visible.

This does not reject the complete finite-`S` sign.  It proves that the missing
finite-dimensional bad/control space is mandatory, and that its orthogonality
must be imposed on the same finite-`S` owner.  Proof 113 still rejects the
prime-free shortcut.  The next bottom is a same-object finite-`S` conditioning
theorem coupled to the negative Yoshida owner and the Burnol all-zero identity;
no Lean owner or route rewire is authorized and RH remains unproved.

## 2026-07-14 natural Mellin completeness and fixed-window loop

Proofs 241--244 close the ordinary finite-window control-row layer.  Proof 241
extracts a finite bad/control frame from compactness, Proof 242 replaces raw
row-map density by the correct dense-algebraic-span condition, and Proof 243
identifies the actual finite-window Riesz rows with global Mellin evaluation
under the explicit same-window support premise.

Proof 244 supplies the missing completeness producer without a circle Fourier
transport.  At the natural nodes the log-window rows are

```text
r_n(t)=exp(n*t),  n=0,1,2,... .
```

They contain one, multiply by adding indices, are fixed by star, and
`r_1=exp(t)` separates points.  Complex Stone--Weierstrass makes their span
dense in the continuous window functions.  Continuous-to-`L2` density and the
two exact log/Haar isometries transport the result to the named ordinary Haar
operator.  The theorem
`exists_finite_cc20WindowHaarNaturalMellinZeros_remainder_nonpositive`
therefore selects finitely many actual natural Mellin zeros and proves the
shifted ordinary regular form nonpositive with no control-space containment
parameter.

This closes ordinary-kernel row coverage, not Gate 3.  Proof 238 can include
the shifted nodes `n+1/2` among its arbitrary finite route nodes, but its
unscaled support grows with the convolution count chosen after the nearby-zero
radius.  Proof 244 selects its finite row set only after fixing `lambda`.
Hence the remaining quantifier loop is

```text
fix lambda -> select rows(lambda) -> Yoshida support may escape lambda,
build Yoshida -> enlarge lambda -> rows(lambda) may change.
```

A valid successor must produce uniform control under window enlargement, a
coupled-radius support-preserving detector, or a post-assembly correction that
preserves the negative orbit and far tail.  It must still identify the
ordinary regular kernel with the actual finite-S post-Q remainder on the same
owner and prove Burnol's all-zero identity.  No route rewire is authorized;
RH remains unproved.

## 2026-07-14 detector-specific global contraction

Proof 249 replaces the fixed-window control-row loop by a quantitatively
different target.  The support-corrected translated-bump DFT construction is
rejected: its control rows must use the full envelope
`(n+1)*base span+correction span`, and the resulting interpolation is rank
deficient from the first tested power.

For an off-line centered point `delta+i*gamma`, the resonant pair

```text
h_ell(x)=[h(x-ell)+h(x+ell)]/[2 cosh(ell*delta)],
ell*gamma=2*pi*N,
```

keeps the transform equal to one on the complete centered orbit and makes its
global critical-line transform and `L1` mass strictly smaller than any chosen
`q in (0,1)`.  The exact translation, resonance, orbit-preservation,
half-density, and `L1` statements are now axiom-clean in
`CC20YoshidaCriticalContraction.lean`.

This permits a detector-specific version of Gate 3.  It is not necessary to
prove `E_S<=0` on the complete three-row subspace.  It is enough to prove that
the one negative Yoshida detector satisfies `|E_S|<1/2`; semilocal trace
positivity then bounds its Weil value below by `-1/2`, while the orbit sum
`-2` and a small all-other-zero tail bound it above by `-7/4` after the Burnol
identity.

The exact remaining quantitative contract is a support-uniform estimate whose
fully dressed prime-power terms are bounded by

```text
poly(m) p^(-m),
```

not the current absolute `p^(-m/2)` interior majorant.  Summing `p^(-m)` over
the prime powers visible in support `[-B,B]` costs only a polynomial in `B`, so
the `q^(2n)` graph-energy decay wins.  Summing `p^(-m/2)` costs exponentially
in `B` and rejects this route.  Proof 228 supplies the second half-power for
the endpoint chirp; the next gate is the same `TT*`/nonstationary-phase gain
for all Proof 229 interiors after the graph dressings of Proofs 230--234.

No negative-owner assembly with this base, quantitative finite-S theorem,
Burnol Lean identity, route rewire, or RH proof is claimed.

## 2026-07-15 chirp-mixture tail gain and central obstruction

Proof 250 replaces the proposed generic `TT*` step by an exact calculation.
On the Proof 229 negative cell `x=-n log(p)-t`, the two half-density factors
cancel and the fast phase separates:

```text
A_(p,n)(r,t)=exp(r/2)b_(p,n)(t),
Phi_(p,n)(r,t)=exp(+-2*pi*i*p^n*exp(r+t)).
```

The derivative transfer satisfies

```text
(partial_r-partial_t)^2[exp(r/2)b(t)]
 =exp(r/2)(partial_t-1/2)^2b(t).
```

Thus every complex interior is a Bochner integral of Proof 228 chirps at
frequency `p^n exp(t)`.  Their exact Plancherel norm gives

```text
norm(T_(p,n))<=C(1+log(p))p^(-n),  n>=1.
```

The no-prolate dressings in Proofs 230--234 preserve this tail bound: the
scattering and Euler factors commute with `Q`, half-line cutoffs are
contractions, and the polynomial word count sums against
`eta^k`, `eta<=2sqrt(2)/3`.

This does not pass Proof 249's complete gate.  The central cell `n=0` has
scale `p^(-1/2)log(p)`, not `p^(-1)`.  Stable Nyström refinements through
`p=211` agree with that scale.  The resonant pair's sparse binomial support
cannot compensate: its exact two-sided moment at the half-prime exponent is

```text
[cosh(ell/2)/cosh(ell*|delta|)]^(2N)>1
```

for every off-line `|delta|<1/2`.  Hence neither an absolute central estimate
nor a support-cluster count closes detector smallness.

The next gate is now narrower and signed.  Compute the central coefficient of
the complete same-object crossing

```text
Y_alpha+Y_alpha*,
```

before separating its phase, metric, half-line, or prolate branches.  A viable
successor must prove either exact central cancellation, or a decomposition

```text
complete remainder
 =nonnegative scalar * common central operator
  +poly(log(p))O(p^(-1)) tail
```

with a favorable sign of the common operator on the same negative Yoshida
detector.  If neither statement holds, Proof 249's detector-specific route is
rejected.  The Burnol identity and finite-S trace identity remain open; no
route rewire is authorized and RH remains unproved.

## 2026-07-15 complete central gain and mixed-prime curvature

Proof 251 tests the complete nested projection before splitting its phase and
metric amplitudes.  The one-prime first variation now has strong finite-section
evidence for the missing half-power: after multiplying by
`a=exp(-L/2)`, the long-translation norm behaves like `exp(-L)`.  This remains
a continuous-kernel obligation rather than a theorem.

The multi-place transport introduces a new earlier death gate.  For a fixed
projection `P` and commuting translations `U,V`, let `P_(a,b)` be the
orthogonal projection onto `(I-aU)(I-bV) Ran(P)`.  Proof 251 derives the exact
mixed Hessian

```text
H_P(U,V)
 =D+D*+A_U A_V*+A_V A_U*-A_U* A_V-A_V* A_U,

A_U=(I-P)UP,
A_V=(I-P)VP,
D=(I-P)UVP-(I-P)UPVP-(I-P)V P U P.
```

The formula agrees with an independent QR finite difference.  In the nested
half-line/Sonin finite section, the post-Q half-line Hessian cancels and the
Sonin Hessian survives.  At fixed separation `M-L=0.5`, its coefficient is
constant under common translation, so the dressed mixed term scales as

```text
exp(-(L+M)/2)=1/sqrt(p*q),
```

not `1/(p*q)`.  The root operator remains indefinite after the two genuine
pre-root rows.  Fixed 8-mode Dirichlet spaces retain both signs from step
`0.05` through `0.025`, and Proof 240's explicit four-mode row witness has a
positive mixed value on every refinement while its row quadrature residual
decreases.

This is not yet a continuous rejection.  The next theorem must evaluate the
continuous mixed Sonin curvature on that explicit witness and prove or reject
a nonzero common-translation limit.  A nonzero value on an open interval of
`log(q/p)` rejects termwise absolute finite-S smallness because comparable
prime pairs retain the half-power-product density.  It does not reject signed
aggregate cancellation or a detector constructed to annihilate the complete
finite-S bad space.  Those are the only active successors if the continuous
death theorem passes.  Burnol's all-zero identity, the same-object finite-S
trace identity, and RH remain open; no route rewire is authorized.

## 2026-07-15 synchronized finite-S logarithmic flow

Proof 252 attacks the signed-aggregate successor left open by Proof 251.  For
the complete finite place set, define

```text
T_S(t)=product_(p in S)(I-t p^(-1/2)U_p).
```

All `U_p` are commuting logarithmic translations.  Hence

```text
X_S(t):=T_S'(t)T_S(t)^(-1)
 =-sum_(p in S)sum_(m>=1)t^(m-1)p^(-m/2)U_p^m.
```

This is the exact Euler prime-power resolvent before any trace or norm.  Apply
the general projection derivative to the transported half-line and Sonin
ranges.  Their nested difference satisfies

```text
B_S'(t)=Y_S(t)+Y_S(t)*,

B_S(1)-B_S(0)
 =integral_0^1 (Y_S(t)+Y_S(t)*) dt.
```

The companion finite-section script verifies this endpoint identity, the
right logarithmic derivative, mixed-Hessian polarization, factor-order
independence, and an independent direct Fourier-product construction.  The
default endpoint integration error is `6.17e-10`; the algebraic checks are at
roundoff scale.

The route-level observation is that Proof 251's degree-two pair Hessian does
not approximate the complete endpoint once many local factors are present.
On the fixed four-mode witness it reaches about `+1.31` by `p<=97`, while the
complete endpoint is about `-1.12`.  Through `p<=997`, the complete tested
endpoint remains negative and bounded even though `sum p^(-1/2)` is about
`12.65`.  This is only a survivor diagnostic.  The values are box-sensitive,
not converged, and every complete constrained root operator remains
indefinite.  Finite-dimensional projection boundedness cannot be promoted to
a continuous estimate.

The active Gate 3 bottom is now the complete synchronized flow form

```text
q_(S,t)(eta,xi)
 =Tr(C_(L_+ eta)(Y_S(t)+Y_S(t)*)C_(L_+ xi)*).
```

A successor must construct its continuous finite-window kernel and prove that
its integral is small on the actual resonant negative-owner sequence,
uniformly in the visible sets `S_n`, without bounding the prime-power
resolvents separately.  CCM24's common de Branges carrier and multiplicative
metric are the intended coordinates.  CC20's prolate correction must remain
in the identity.

This does not reopen the rejected direct cocycle, compact Wiener--Hopf repair,
or Fredholm determinant routes.  The factorwise logarithmic derivative is not
`Tr log`; both nested ranges are transported before `Q`, and no compact term is
asked to cancel an unchanged essential prime symbol.  Proof 251 remains a
guard against pairwise absolute estimates, but its continuous nonzero pair
value is no longer the decisive death theorem for the complete owner.  The
negative-owner integration, Burnol identity, same-object finite-S trace
identity, and RH remain open; no route rewire is authorized.

## 2026-07-15 nested Berezin synchronized flow

Proof 253 identifies Proof 252's complete synchronized kernel on CCM24's
common Mellin carrier.  The original CCM24 TeX defines

```text
E_S(s)=product_(v in S)L_v(1/2+is)
```

as the real-axis weight in `ds/|E_S|^2`.  It does not supply a semilocal
Hermite--Biehler structure function; the relevant source paragraph is inside
an `\iffalse` block and discusses only Burnol's archimedean case.  Hence the
complete Sonin kernel cannot be replaced by a guessed Euler phase.

For `J=R,E`, the exact changed-metric projection is

```text
J_(S,t)
 =M_(tau)J(J M_(|tau|^2)J)^(-1)J M_(conj(tau)).
```

Its diagonal kernel density satisfies the synchronized Berezin identity

```text
partial_t k_J(s)
 =2 Re integral
    (x_(S,t)(s)-x_(S,t)(u))|K_J(s,u)|^2 du,

x_(S,t)=partial_t log(tau_(S,t)).
```

For the nested band `B=E-R`, this splits exactly into a band variance and a
Sonin--band coherence.  If `w=|Fourier(L_+xi)|^2` and `h=Re(x)`, the full
instantaneous root form is

```text
q_(S,t)(xi)
 =D_(E_(S,t))(w,h)-D_(R_(S,t))(w,h),

D_J(w,h)=<[M_w,J],[M_h,J]>_HS.
```

This is a double-difference formula.  Every scalar component of `h` cancels
exactly, including the endpoint bulk
`sum_p p^(-1/2)/(1-p^(-1/2))`.

Normalize the complete transport by the scalar
`product_p(1-t p^(-1/2))`.  The resulting metric is pointwise at least the
identity.  All compressed metric inverses and the nested Schur-complement
inverse therefore have norm at most one, uniformly in `S`.  Its normalized
real generator is a nonnegative sum of `1-cos(m log(p)s)` modes, and the
inverse ambient metric is a probability average of independent two-sided
geometric prime-log translations.

The finite-section certificate verifies all four independent forms of the
kernel derivative, scalar-gauge invariance, metric monotonicity, and the path
endpoint.  Through `p<=997`, a scalar bulk about `16.96` and normalized
generator maximum about `23.27` coexist with order-one exact responses:

```text
D_E=-2.378,
D_R=-1.629,
band variance=-2.763,
coherence=+2.014,
complete=-0.748.
```

The values are not a continuous convergence theorem and do not prove a sign.
Metric monotonicity does not order the projection flow, which remains
indefinite by Proof 227.

The active Gate 3 bottom is now the detector-specific estimate

```text
integral_0^1 [D_(E_(S_n,t))(w_n,h_(S_n,t))
              -D_(R_(S_n,t))(w_n,h_(S_n,t))] dt=o(1),
```

uniformly for the visible finite sets of the actual resonant negative-owner
sequence.  A sufficient proof may use the normalized inverse's probability
average together with compact root support, but it must retain the difference
`D_E-D_R`.  Separate absolute estimates can recreate the rejected
`sum p^(-1/2)` route.  Do not apply standalone Hilbert--Schmidt
Cauchy--Schwarz to the raw Euler commutator; its trace legality comes only
after the root smoothing and boundary cancellation remain together.  The
negative-owner integration, Burnol identity, same-object finite-S trace
identity, and RH remain open; no route rewire is authorized.

## 2026-07-15 shorted Markov boundary gate

Proof 254 tests the probability-average successor proposed by Proof 253.  It
first strengthens the exact normalization.  If

```text
Ttilde_(S,t)
 =product_(p in S)(I-r_p U_p)/(1-r_p),
r_p=t p^(-1/2),
```

then the inverse transport itself is a one-sided Markov convolution:

```text
Ttilde_(S,t)^(-1)
 =E[U_(sum_p N_p log(p))],
P(N_p=n)=(1-r_p)r_p^n.
```

Its metric square gives Proof 253's independent two-sided geometric law.  For
a compact root `g` supported in `[-B,B]`, the legally smoothed half-line
crossing has trace `z F(-z)`, where `F` is the autocorrelation of `g`.
Therefore `F(z)=0` for `|z|>2B` and every probability average obeys

```text
abs(E[z F(-z)])<=2B ||g||_2^2,
```

uniformly in `S`.  This closes the ambient Markov boundary response without
using a moment of the random prime-log shift.

The compression step has an exact additional owner.  With
`M=Htilde^-1`, block inversion gives

```text
(J Htilde J)^-1
 =J M J-J M(I-J)((I-J)M(I-J))^-1(I-J)M J.
```

For the nested decomposition `I=R+B+C`, the Schur inverse is

```text
Sigma^-1=B M B-B M C(C M C)^-1 C M B.
```

The second term is a positive shorting defect and is not a probability
convolution.  A closed two-mode model proves that this is a real logical gate:
`Htilde>=I`, a Markov inverse, nested projections, and a nonnegative detector
vanishing at the Markov fixed mode coexist with a complete response tending to
`-1`.  Repeating legal local factors realizes the required large total
condition while every local Euler parameter remains below `1/sqrt(2)`.

The WSL certificate verifies the one- and two-sided characteristic functions,
the compact crossing trace, both shorting formulas, positivity, and the closed
two-mode response at errors at most `7.9e-14`.  An optimized optional section
through `p<=100000` is deliberately nonconverged: at sizes `384,512,640,768`
the root norm is approximately `4.04,17.16,7.52,10.71`, the fixed witness
changes sign, and the selected finite Sonin rank remains `9`.  These values
reject fixed-box acceptance but are not a continuous divergence theorem.

The active Gate 3 theorem is now a shorted Sonin boundary estimate.  Insert

```text
B=P(I-P_hat)P+K_prol
```

into the exact shorted difference, retain all three half-line branches and the
band/coherence pairing, apply compact support to each completed crossing, and
only then expand the Markov law.  A uniform polynomial bound closes Proof
249's detector smallness; a conditioned-return coefficient with
super-polynomial support growth rejects that route.  The negative-owner
integration, Burnol identity, same-object finite-S trace identity, and RH
remain open; no Lean owner or route rewire is authorized.

## 2026-07-15 nested shorting cancellation and dual-frame gate

Proof 255 rejects the standalone positive shorting-defect target left by
Proof 254.  For the nested Schur frame

```text
A_R=R H R,
Z=B-R A_R^-1 R H B,
G=T Z,
Sigma=G*G,
```

the oblique band projection satisfies

```text
A_obl=(I-R_T)T E T^-1,

A_obl A_obl*-B_T
 =(A_obl-B_T)(A_obl-B_T)*
 =G[B M C(C M C)^-1 C M B]G*.
```

This is exact but cannot be estimated by positive domination.  In an exact
three-dimensional Markov model, the phase and defect both grow as
`kappa^2/4` while the orthogonal response remains bounded.  In the actual
finite Sonin geometry through `p<=997`, the two positive traces are about
`1.3262e11`, their difference is about `76.85`, and the oblique norm is about
`1.13e7`.

The canonical polar isometry

```text
V=G Sigma^-1/2,
V*V=B,
VV*=B_T
```

recombines the cancellation.  Its response operator obeys the exact
Sylvester equation

```text
Omega X+X Omega=V* K+K* V,

Omega=Sigma^1/2,
X=V* W V-B W B,
K=W G-G B W B.
```

Since the normalized metric has `H>=I`, one has `Sigma>=I`.  This removes any
inverse-square-root condition loss, but a raw trace norm of the expanding
`K` still grows with the outer Euler product and is rejected.

The stronger owner is the inverse-metric dual frame

```text
D=B-C(C M C)^-1 C M B,
F=T^(-*)D=G Sigma^-1.
```

It satisfies

```text
G*F=F*G=B,
G F*=F G*=B_T,
F*F=Sigma^-1<=B.
```

For the route's convolution detector `W`, `WT=TW`, so the outer Euler
transport deletes exactly:

```text
Tr(W(B_T-B))
 =Tr_B(F* W G-B W B)
 =Tr_B(D*(W Z-Z B W B)).
```

Across physically larger finite sections containing all translations through
`p<=997`, the intrinsic defect trace norm stays about `19.7--24.4` while the
separated phase remains `5.6e10--8.0e10`.  This is strong survivor evidence
for the new organization, not a continuous theorem or convergence claim.

The active Gate 3 theorem is now a trace-legal polynomial-support estimate for
the exact dual-frame pairing above, uniform in the visible finite set and the
synchronized flow parameter.  The proof must insert
`B=P(I-P_hat)P+K_prol`, retain the three half-line/scattering branches and the
prolate term, apply compact support before the Markov expansion, and keep `D`
paired with `Z`.  A polynomial support bound closes Proof 249's detector
smallness; exponential conditioned-return growth rejects it.  The
negative-owner integration, Burnol all-zero identity, same-object finite-S
trace identity, and RH remain open.  No Lean owner or route rewire is
authorized.

## 2026-07-15 one-sided shorting collapse

Proof 256 removes the conditioned inverse from Proof 255's dual coframe.  In
Proof 222's source orientation the whole-line Euler inverse `A=T^-1` is a
normal one-sided convolution, while the opposite half-line `C` is invariant
under both `A` and `T`.  With `M=(T*T)^-1=A*A`, normality permits the causal
factorization

```text
C M C=(C A C)*(C A C),
C M B=(C A C)* C A B.
```

Consequently

```text
D
 =B-C(C M C)^-1 C M B
 =T E T^-1 B.
```

Thus `(C M C)^-1` is not an independent analytic target.  It is exactly the
one-sided spectral factor hidden inside the oblique half-line lift.

For

```text
L=(R H R)^-1 R H B,
Z=B-RL,
Y=WZ-Z B W B,
K_E=D-B,
```

the intrinsic response now splits as

```text
D*Y=-B W R L+K_E*Y.
```

The second term is a completed two-crossing channel.  The first is the
remaining complete-S Sonin graph channel.  It should not be estimated by a raw
endpoint norm of `L`.

The next organization uses the second support projection `Q`:

```text
B W R=B Q W R+B(I-Q)[W,Q]R,
(B Q)(B Q)*=K_prol on B.
```

It then differentiates the graph along the synchronized flow:

```text
L_t'=A_t^-1 R H_t' Z_t
    =A_t^-1/2 V_(R,t)* K_t G_t,
V_(R,t)*G_t=0.
```

The scalar Euler bulk cancels in this formula.  A successor must pair these
detector/prolate crossings with the graph flow inside the trace, use the
contractive dual frame before any norm, and prove a polynomial support bound.
Separate norms of `G_t`, `L_t`, or prime channels can recreate the rejected
Euler condition number or the insufficient `p^(-m/2)` sum.

The WSL certificate passes with maximum triangular error `4.47e-16` and
maximum response-split error `7.13e-12`.  Its periodic and causal models are
complementary only: periodic FFT preserves normality but loses the invariant
half-line; zero-fill preserves causality but loses normality at the artificial
outer endpoint.  The causal central commutator is `5.35e-14` while its global
commutator error is `0.289`, confirming boundary localization rather than a
continuous counterexample.

The active Gate 3 theorem remains the uniform polynomial-support estimate for
the complete two-boundary pairing.  Negative-owner integration, the Burnol
all-zero identity, the same-object finite-S trace identity, and RH remain
open.  No Lean owner or route rewire is authorized.

## 2026-07-15 two-boundary Q-preserving flow

Proof 257 closes the trace legality of Proof 256's hard endpoint channel and
then retires its graph coordinate as the proposed norm target.  With `E,Q`
the two source support projections, `R` their Sonin intersection, and
`B=E-R`, CC20's exact spectral decomposition is

```text
E Q E=R+K_prol,
K_prol=sum_n lambda(n)^2 |zeta_n><zeta_n|.
```

Therefore

```text
(B Q)(B Q)*=K_prol on B,

B W R
 =B Q W R+B(I-Q)[W,Q]R.
```

CC20's explicit rapid-decay bound makes `BQ` trace class, and Appendix D
makes the smoothed commutator `[W,Q]` trace class.  Thus `BWRL` is trace legal
for every fixed finite `S`.  This supplies no uniform bound on `L`.

The stronger source owner uses preservation of the second support orientation
by the CCM24 transport.  For

```text
E_t=projection onto T_t Ran(E),
R_t=projection onto T_t Ran(R),
B_t=E_t-R_t,
X_t=T_t'T_t^-1,
```

one has `R_t<=Q` and `(I-Q)X_tQ=0`.  Proof 252's band derivative therefore
factors exactly as

```text
B_t'=Y_t+Y_t*,

Y_t
 =(I-E_t)X_tB_t-R_tX_t*Q B_t.
```

Every scalar addition to `X_t` cancels in the two displayed branches.  This
orthogonal flow, not the endpoint graph `L_t`, is now the active analytic
owner.

The current second-support leakage must be completed before estimation.  If
`U_t=(I-R_t)T_tB Sigma_t^-1/2` is the band isometry, then

```text
Q U_t
 =(Q-R_t)[T_t Q B+[Q,T_t]B]Sigma_t^-1/2.
```

This exposes exactly three branches: the crossed outer half-line, the crossed
second half-line, and the base CC20 prolate leakage.  Do not call `Q B_t`
compact by itself.  Keep all three branches with the compact root before any
absolute estimate.

CC20 gives the explicit super-exponential bound

```text
|lambda(n)|
 <=2^(2n) pi^(2n+1/2) ((2n)!)^2
   /[(4n)! Gamma(2n+3/2)]
 =exp(-2n log n+O(n)).
```

This suggests a high-mode cutoff `N(B)=O(B/log B)` capable of beating an
exponential support envelope.  The constants and the complete low-mode bound
remain open.  Do not introduce growing control rows until their interpolation
and support cost are quantitatively proved; Proof 248 remains the guard.

The exact WSL certificate reports generic two-projection error below
`9.9e-16`, graph-flow error `1.21e-10`, Q-preserving nonzero-time flow error
`1.71e-9`, and strict Sonin-flow error below `4.4e-14`.  Three physical
sections through `p<=997` keep the hard absolute flow between `0.91` and
`1.22` and the complete response between `-1.43` and `-1.16`, while the old
separated phase is `10^10--10^11`.  This is survivor evidence only.

Periodic transported-Q values are rejected as continuous evidence.  By
`p<=997` the periodic model has `R_t<=Q` residual about `0.4`, exactly because
the circle destroys the one-sided invariant half-line.  The independent
Q-preserving model is the certificate for the new identity.

The active Gate 3 theorem is now a polynomial-support bound for the complete
three-branch Q-preserving flow.  Negative-owner integration, the same-object
finite-S trace identity, the Burnol all-zero identity, and RH remain open.  No
Lean owner or route rewire is authorized.

## 2026-07-15 covariant transported-prolate cancellation

Proof 258 rejects a tempting but invalid estimate left by Proof 257.  In the
exact Q-preserving two-dimensional model

```text
Q=|e_1><e_1|,
b_kappa=(kappa e_1+e_2)/sqrt(1+kappa^2),
T_kappa=[[1,-kappa],[0,1]],
```

scale `T_kappa` so that `T_kappa*T_kappa>=I`.  The normalized transported band
is `e_2`, so its complete Q leakage is zero, while

```text
T_kappa Q b_kappa Sigma_kappa^-1/2=+kappa e_1,
[Q,T_kappa]b_kappa Sigma_kappa^-1/2=-kappa e_1.
```

Thus the two endpoint branches in Proof 257 can be arbitrarily large and
cancel exactly.  Separate high-prolate and second-boundary triangle estimates
are rejected even under Q invariance and the normalized metric lower bound.

The replacement uses the orthogonal band projection `P_t=B_t`.  Define

```text
A_t=[P_t',P_t],
mathcalU_t'=A_t mathcalU_t,
mathcalU_0=I.
```

Then `A_t` is skew-adjoint,

```text
P_t=mathcalU_t P_0 mathcalU_t*,

C_t=Q mathcalU_tP_0,
C_tC_t*=Q P_tQ,

C_t
 =Q P_0+integral_0^t Q[P_s',P_s]mathcalU_sP_0 ds.
```

The CC20 prolate leakage is now only the initial condition `C_0=QP_0`; it is
never multiplied by a raw norm of `T_t`.  The evolution is driven by Proof
257's complete scalar-free band derivative.  The active analytic target is a
root-smoothed Hilbert--Schmidt estimate for this Kato/Duhamel flow, followed by
the compatible second factor needed for the trace.

The WSL certificate verifies the branch counterexample through
`kappa=10000` with relative sum error below `8.7e-19`.  An independent
Q-preserving nested flow verifies Kato unitarity and transported projection
identities below `1.3e-15`; the independent finite-difference derivative error
is `2.70e-9`.

Do not return to `norm(T_tQB)+norm([Q,T_t]B)`, a raw transported prolate tail,
or a separate graph norm.  The uniform root-smoothed covariant estimate,
negative-owner integration, same-object finite-S trace identity, Burnol
identity, and RH remain open.  No Lean owner or route rewire is authorized.

## 2026-07-15 Kato trace-factorization gate

Proof 259 audits whether Proof 258's covariant leakage can carry the route
trace.  It cannot.  Put

```text
V_t=mathcalU_tB,
C_t=QV_t,
D_t=(I-Q)V_t.
```

Then

```text
B_t=V_tV_t*
   =C_tC_t*+C_tD_t*+D_tC_t*+D_tD_t*,
C_tC_t*=QB_tQ.
```

The convolution detector does not factor through `Q`, so `C_t` omits three
blocks of the projection response.  Differentiation only gives

```text
C_t'=Q A_tV_t,
A_t=[B_t',B_t]=Y_t-Y_t*.
```

This is one corner of the full lower crossing.  A Q-preserving nested `C^4`
model uses a diagonal nonunitary transport which commutes with the positive
detector and has normalized metric at least the identity.  It makes `C_t`
constant and nonzero while the detector sees endpoint response `1/4` and
derivative response `sqrt(3)/4`.  Thus no estimate based only on `C_t`, `C_t'`,
or `C_tC_t*` determines the route trace.

The natural Kato-frame split fails the project trace standard:

```text
C_eta B_t'C_xi*
 =(C_eta A_tV_t)(C_xiV_t)*
   +(C_etaV_t)(C_xiA_tV_t)*.
```

The factors `C_gV_t` need not be Hilbert--Schmidt.  On `L2(R)`, for any
nonzero convolution kernel `g`,

```text
norm(C_gP_+)_HS^2
 =integral_(y>=0) integral_R |g(x-y)|^2 dx dy
 =infinity.
```

By contrast, a completed translation crossing satisfies
`norm(C_g[P_+,U_b])_HS^2=|b|norm(g)_2^2`.  The boundary crossing, not the
transported infinite frame, supplies the ideal property.

The full Kato generator has the trace-compatible identity

```text
Tr(C_eta B_t'C_xi*)
 =Tr([B_t,C_xi*] C_eta A_t)
   +Tr([B_t,C_eta] A_t C_xi*).
```

This preserves `A_t=Y_t-Y_t*` before taking a norm.  It yields two legal scalar
trace products if the band/root commutators and the root-smoothed full
generator are Hilbert--Schmidt.  It does not prove that the original smoothed
route operator is trace class.  The required source-specific owner has the
stronger shape

```text
Y_t=L_tR_t,
C_etaL_t in S2,
R_tC_xi* in S2,
C_etaY_tC_xi*=(C_etaL_t)(R_tC_xi*) in S1.
```

The outer boundary, second-support boundary, and base prolate term must remain
recombined inside this factorization.  Putting them in separate direct-sum
factors replaces their cancellation by a sum of squared norms.

The research audit found no standard shortcut.  Kato transport
(`arXiv:1106.4661v2`, Section 2.1, equations (5)--(7)) transports the ranges of
a norm-differentiable projection family.  The Hilbert--Schmidt restricted
Grassmannian in `arXiv:0808.2525v1` lies inside `P+S2`, and the horizontal lift
in `arXiv:0808.2274v1`, Proposition 2.2, assumes an `S2`-valued tangent.
`arXiv:1310.1778`, Section 2.3, likewise uses Hilbert--Schmidt graph maps as the
chart definition.  These results assume the missing ideal property; they do
not produce it from bounded Kato flow.  Unitarity avoids an exponential
Gronwall factor, but the estimate still depends on the forbidden ambient
length `integral norm(B_t')_2 dt`.

The WSL certificate verifies the Kato trace identity at relative error
`1.98e-16`, its two-factor expansion at `9.88e-17`, and the leakage-blindness
model with maximum algebra error `3.45e-16`.  No continuous Schatten bound
follows from the finite model.

Proof 258's Kato identities and `C_t` remain useful diagnostics.  Its proposed
seminorm `norm(C_gC_t)_HS` is retired as the active bottom.  Gate 3 returns to
Proof 227's complete-crossing factorization, now with the two required
Hilbert--Schmidt maps named explicitly.  The uniform polynomial-support bound,
negative-owner integration, same-object finite-S trace identity, Burnol
identity, and RH remain open.  No Lean owner or route rewire is authorized.

## 2026-07-15 Schatten legality versus signed trace cancellation

Proof 260 finds that Proof 259's successor contract still combined two
different obligations.  A completed finite half-line crossing does have the
requested source-owned factorization.  On `L2(R)`, put

```text
Y_(I,b)=U_b E_I,
K_(I,b,g)=C_g Y_(I,b) C_g*.
```

Factoring through `L2(I)` gives

```text
K_(I,b,g)
 =(C_g U_b i_I)(r_I C_g*),

norm(C_g U_b i_I)_2^2
 =norm(r_I C_g*)_2^2
 =|I| norm(g)_2^2.
```

Thus both factors are legal Hilbert--Schmidt maps.  They also attain the
minimum possible positive factor cost:

```text
Tr(K_(I,b,g))=|I| F_g(b),
norm(K_(I,b,g))_1=|I| norm(g)_2^2.
```

If the root is supported in `[-B,B]` and `|b|>2B`, then `F_g(b)=0`.  The
scalar trace is exactly zero, while the nuclear norm and the optimal product
of the two Hilbert--Schmidt norms remain strictly positive.  Schatten Holder
therefore cannot retain the compact-support cancellation, even with the best
factorization.

Putting the outer boundary, second boundary, and base prolate pieces in a
Hilbert direct sum replaces their signs by sums of squared norms.  A signed or
Krein direct sum keeps the algebraic signs but its positive Hilbert majorant
has the same defect.  A fused factorization can improve the estimate only if
one first proves cancellation of the full trace norm, which is stronger than
Proof 253's scalar `D_E-D_R` identity and is not supplied by CC20 or CCM24.

An exact continuous guard uses disjoint intervals `I_n` of length
`b_n=2^n b_0`, `b_0>2B`, and

```text
K_n=b_n^(-1)U_(b_n)C_gE_(I_n)C_g*.
```

Every `K_n` has zero diagonal trace, constant trace norm `norm(g)_2^2`, and
operator norm tending to zero.  Placing their input and output supports
orthogonally makes `sum_n K_n` compact but not trace class.  Hence Proofs
228--234's operator-norm compactness cannot be upgraded to ordinary trace
legality by abstraction.  This guard does not prove that the actual Euler
operator is non-trace-class; it proves that its additional operator-level
cancellation must be constructed.

Peller's criterion (`arXiv:2402.09853`, Sections 5.2--5.3) says that the Hardy
commutator `[M_phi,P_+]` is in `S_p` exactly when `phi` is in
`B_p^(1/p)`.  At `p=1`, a verified `B_1^1` symbol can close fixed-symbol trace
legality.  The theorem does not supply the complete three-branch symbol or a
uniform signed estimate; its Besov norm charges modulation mass which the
root autocorrelation can cancel at the scalar trace.

Gate 3 is now split:

```text
Gate 3L:
  prove C_eta(Y_(S,t)+Y_(S,t)*)C_xi* is in S1
  for the fully recombined fixed-S source flow;

Gate 3U:
  identify that ordinary trace with the same-object signed
  D_E-D_R / physical three-branch expression and prove the
  polynomial-support bound uniformly in S.
```

Two-Hilbert--Schmidt factors remain an allowed Gate 3L certificate.  Their norm
product is forbidden as the Gate 3U estimator.  The WSL certificate reports
zero scalar trace, trace norm `40`, optimal factor product `40`, and maximum
algebra error `2.31e-15`; its four crossing blocks have trace norm one each
while their operator norms decrease from `0.539` to `0.0807`.

The fixed-`S` ordinary trace-class theorem, the uniform signed bound,
negative-owner integration, same-object finite-S trace identity, Burnol
identity, and RH remain open.  No Lean owner or route rewire is authorized.

## 2026-07-15 fixed-S trace-class gate

Proof 261 closes Gate 3L at the mathematical route-evidence level.  Let `G` be
one compact-root convolution.  CC20 Lemma `quantsmooth` gives `[G,P] in S1`
for the crossed half-line projection.  The scattering identity and

```text
P P_hat P=R+K_prol,
K_prol in S1,
```

give `[G,R] in S1` as well.

For `J in {E,R}`, extend the compressed metric to the ambient space:

```text
A_(J,t)=J H_t J+(I-J),
D_(J,t)=A_(J,t)^(-1).
```

The root commutes with the complete Euler metric.  Hence

```text
[G,A_(J,t)] in S1,
[G,D_(J,t)]
 =-D_(J,t)[G,A_(J,t)]D_(J,t) in S1.
```

The transported projection

```text
J_t=T_t J D_(J,t)J T_t*
```

therefore satisfies `[G,J_t] in S1`.  This keeps the complete compressed
inverse intact and generalizes Proof 226's one-prime inverse-commutator step to
the synchronized finite-`S` metric.

The current crossing pulls back to the source without a Neumann expansion:

```text
Z_(J,t)=(I-J_t)X_tJ_t
 =(I-J_t)T_t[(I-J)X_tJ]D_(J,t)J T_t*.
```

Proof 257's Q-preserving identity then gives

```text
Y_t=[Z_(E,t)-Z_(R,t)*]B_t.
```

For `E=P`, the base crossing is a sum of translation crossings through
intervals of length `m log(p)`.  For `R`, the CC20 identity
`R=P P_hat P-K_prol` expands each source crossing into three
scattering-dressed half-line crossings plus a trace-class prolate commutator.
All metric and projection dressings have trace-class commutators with the
roots.

If `[U_b,P]=L_bR_b` is the interval factorization, commuting a root through the
bounded dressings produces

```text
(C_eta A_0L_b)(R_bA_1C_xi*),
```

with both factors Hilbert--Schmidt.  The trace-norm cost is
`O(1+|b|)`.  The complete fixed-`S` generator has coefficients
`t^(m-1)p^(-m/2)`, and

```text
sum_(p in S)sum_(m>=1)
  t^(m-1)p^(-m/2)(1+m log(p))<infinity.
```

The resulting trace-norm majorant is uniform in `t in [0,1]` for each fixed
finite `S`, because

```text
s_min(T_t)>=product_(p in S)(1-p^(-1/2))>0.
```

Consequently

```text
C_eta B_t'C_xi* in S1,

C_eta(B_1-B_0)C_xi*
 =integral_0^1 C_eta B_t'C_xi* dt in S1.
```

The ordinary trace commutes with the time integral.  Proof 253's instantaneous
Dirichlet identity is now legal as an `S1`-times-bounded trace pairing:

```text
D_J(w,h)=Tr([M_w,J]*[M_h,J]).
```

The raw Euler commutator need not be Hilbert--Schmidt.

The WSL certificate checks the compressed inverse commutator, transported
projection, crossing pullback, complete lower flow, and band derivative with
maximum algebra error `1.12e-15`.  The extended Dirichlet trace identity has
relative error `1.81e-14`.  For `S={2,3,5,7,11}` and `t=0.63`, the closed
prime-power trace majorant is `10.59827533`; 80 modes recover it within
`4.44e-16`.

Gate 3L is closed.  Gate 3U remains the active analytic bottom: prove a bound
for the signed `D_E-D_R` trace which is independent of `S`.  Proof 261's
absolute trace-norm sum depends on `S` and is forbidden for that estimate.
The arithmetic same-object finite-S identity, negative-owner integration,
Burnol identity, and RH remain open.  No Lean owner or route rewire is
authorized.

## 2026-07-15 endpoint two-commutator Gate 3U

Proof 262 replaces the synchronized time integral by one endpoint pairing.
Proof 261 supplies trace legality.  For one projection `J`, with

```text
J_T=T J(J H J)^(-1)J T*,
H=T*T,
[W,T]=0,
```

ordinary cyclicity gives

```text
Tr(W(J_T-J))
 =Tr([J,W](I-J)H J(J H J)^(-1)).
```

For the nested pair `R<=E`, put

```text
B=E-R,
C_0=I-E,
L=(R H R)^(-1)R H B,
Z=B-RL,
Sigma=Z*H Z,
mathcalD=H Z Sigma^(-1).
```

The dual coframe satisfies

```text
mathcalD*Z=B,
mathcalD*R=0,
mathcalD*B=B.
```

Proof 255's intrinsic endpoint response is therefore

```text
Tr(W(B_T-B))
 =Tr_B(mathcalD*(WZ-ZBWB)).
```

Expanding `Z=B-RL` and using the three coframe identities collapses it to

```text
Tr(W(B_T-B))
 =Tr_B(mathcalD*
   (C_0[W,E]B-[W,R]R L)).
```

This is the new Gate 3U owner.  It contains no path parameter, Euler generator,
Kato unitary, or outer transport.  The two terms must remain paired.

For `W=C_g*C_g`, `supp(g) subset [-B_root,B_root]`, the kernel of `[W,E]`
vanishes unless the two variables cross the outer boundary and differ by at
most `2B_root`.  The CC20 identity

```text
R=E E_hat E-K_prol
```

decomposes `[W,R]` into the outer boundary, the scattering-conjugate second
boundary, and a prolate trace-class commutator.  Thus all detector dependence
is fixed and source-local; all `S` dependence sits in the paired
`mathcalD_S,L_S`.

Proof 262 also supplies an exact abstract guard.  On the `n`th two-state block,
let

```text
mu_n=2^(-4n^2),
M_n=diag(1,mu_n),
H_n=M_n^(-1),
W_n=Q_n=|e_1><e_1|,
v_n=sqrt(1-mu_n)e_0+sqrt(mu_n)e_1,
E_n=|v_n><v_n|,
R_n=0.
```

In the physical basis, `M_n` is the probability average

```text
[(1+mu_n)/2]I+[(1-mu_n)/2]swap.
```

The detector kills the fixed mode, `Q_n` is invariant, and
`E_nQ_nE_n=mu_nE_n`.  Hence the prolate eigenvalues and detector commutator
trace norms are summable.  The endpoint response is

```text
1/(2-mu_n)-mu_n ->1/2.
```

The first `N` blocks have response `N/2+O(1)` while the cumulative detector
commutator and prolate trace masses stay bounded.  Metric order, Markov
averaging, fixed-mode annihilation, Q-invariance, nesting, and rapid prolate
decay therefore do not imply Gate 3U.  This guard is not a CCM24/CC20
counterexample because it lacks the real-line compact-root half-line geometry.

The research audit found no matching determinant theorem.  Strong Szego and
Toeplitz determinant results treat a single Hardy compression; determinant
invariants for almost commuting Fredholm operators do not construct or bound
the nested Sonin Schur complement uniformly in the Euler symbol.

The active theorem is now

```text
abs Tr_B(mathcalD_S*
  (C_0[W_g,E]B-[W_g,R]R L_S))
 <=C (1+B_root)^d norm(g)_(H^r)^2,
```

with constants independent of `S`.  Insert the CC20 crossing decomposition and
use root support before expanding the paired coframe/graph through a common
Markov path law.

The WSL certificate verifies the endpoint identities with maximum relative
error `2.82e-13`.  In the eight-block guard, the response grows to `3.95362`
while the cumulative detector-commutator and prolate masses stay at `0.491943`
and `0.0625153`; the guard algebra error is `2.22e-16`.

Gate 3U, the arithmetic same-object finite-S identity, negative-owner
integration, Burnol identity, and RH remain open.  No Lean owner or route
rewire is authorized.
