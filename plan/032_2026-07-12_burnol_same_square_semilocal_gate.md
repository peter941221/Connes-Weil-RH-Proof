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

## 2026-07-15 relative Jacobi to stopped-chirp square function

Proofs 263--268 replace the endpoint distribution search by one legal
determinant-line owner.  For each source projection `J in {E,R}`, define

```text
Theta_(J,s)
 =(J exp(sW)H J+(I-J))
  (J H J+(I-J))^(-1)
  (J exp(sW)J+(I-J))^(-1).
```

For fixed finite `S`, `Theta_(J,s)-I` is trace class near zero.  The band
response is

```text
Tr(W(B_S-B))
 =partial_s log[det(Theta_(E,s))/det(Theta_(R,s))] at s=0.
```

The source-specific relative Jacobi identity moves this quotient to the
complementary inverse-metric covariances.  With

```text
M=H^(-1)=A*A,
Z_X=B-C(C X C)^(-1)C X B,
Short_B|C(X)=Z_X*X Z_X,
```

the Schur envelope formula gives

```text
partial_s Short_B|C(X_s)=Z_(X_s)*X_s'Z_(X_s).
```

Causal triangularity then recovers the ordered first jet

```text
K* W K Gamma^(-1)-B W B
```

without cycling `Gamma^(-1)`.  Common forward translation history cancels in
the centered half-line numerator.  The survivor depends on relative
displacement, so large comparable prime paths remain.

Proof 268 also gives the raw innovation guard.  For

```text
b_a(theta)=(1-a)/(1-a exp(i theta)),
```

the defect norm is

```text
norm(I-b_a*b_a)=4a/(1+a)^2.
```

At `a=p^(-1/2)`, a prime square function applied before the physical crossing
retains the divergent half-power scale.

Proof 269 tests a direct coordinate-replacement repair and rejects it in the
periodic source screen.  Removing one prime from the complete endpoint gives
fitted root-operator slopes

```text
-0.583 at size=256, step=0.08,
-0.505 at size=512, step=0.08,
-0.655 at size=640, step=0.04.
```

These values resemble `p^(-1/2)`, not `p^(-1)`.  Periodic sections do not
preserve the second half-line, so the result blocks a raw Efron-Stein proof and
does not prove a continuous lower bound.

The normalized local inverse has the exact geometric law

```text
b_p(theta)
 =sum_(m>=0)(1-a_p)a_p^m exp(i m theta),
a_p=p^(-1/2).
```

Its pointwise defect telescopes across an ordered finite product:

```text
1-|product_j b_(p_j)|^2
 =sum_j |product_(i<j)b_(p_i)|^2(1-|b_(p_j)|^2).
```

This is the spectral form of Proof 266's orthogonal prime innovation
channels.  Proof 228 has already inserted the Euler coefficient into the
completed chirp.  Its weighted norm and square have scales

```text
norm(K_(p,m))~a_p^m,
norm(K_(p,m))^2~a_p^(2m)=p^(-m).
```

The former multiplication by the event weight `(1-a_p)a_p^m` reused the same
coefficient and produced the unowned cubic ledger

```text
(1-a_p)a_p^m norm(K_(p,m))^2
 ~p^(-3m/2).
```

Its scalar convergence is not route evidence.  The corrected first mode is
`sum_p 1/p`, which diverges.

The companion certificate verifies the local geometric and defect formulas
below `2.34e-12`.  At prime cutoffs `100,1000,10000,100000`, the raw
half-power ledger grows as

```text
5.54, 12.65, 29.14, 70.05,
```

while the degree-one cubic double-count ledger is

```text
3.90, 4.87, 5.29, 5.45.
```

The certificate labels that column `DOUBLE_COUNTED_NOT_ROUTE_OWNED`.  A valid
sum must obtain a second factor from the probability that the residual
relative displacement falls inside the compact support window:

```text
sum_p sum_(m>=1)
 (1+m log(p))^(2d)p^(-m) Q_(S,p,k)(4B_root).
```

The active theorem must construct one adapted column on the prime innovation
space.  Each component must contain the complete outer, second-support, and
prolate numerator before a norm, delete the scalar mode inside that channel,
and place its real-line kernel into Proof 228's restricted-Fourier form.  A
contractive dual coframe may then pair against the column without an Euler
condition number or a sum of mixed-Hessian norms.

Paulin--Mackey--Tropp's matrix Efron-Stein theorem controls fluctuations around
a mean; it does not construct this determinant-line channelization.  Petrov's
oblique BOGC theorem assumes an ambient identity-plus-trace-class operator; the
whole-line Euler multiplier fails that premise.  Use the relative Jacobi owner
from Proof 267 if a BOGC factorization is attempted.

Gate 3U now asks for the complete `E/R/Q/K_prol` channelization, chirp bound,
and compact-support concentration factor in Proof 269 equations
`(AF.17)--(AF.21)`.  The arithmetic same-object finite-S
identity, negative-owner integration, Burnol identity, and RH remain open.  No
Lean owner or route rewire is authorized.

## 2026-07-15 renewal observability collapse

Proof 270 constructs the channelization at the renewal level.  With

```text
K=E A B,
Gamma=K*K,
Delta=B-Gamma,
D=Delta^(1/2),
```

define the complete left reward

```text
L_W
 =-[W,E]* C A B
   +A R[W,Q]*(I-Q)B
   +A R W Q B.
```

The three adjoint products with `K` are Proof 266's outer, second-support, and
prolate branches.  Hence

```text
N_W=L_W* K.
```

Define two columns on the renewal path space:

```text
C_K x=(K D^k x)_(k>=0),
C_L x=(L_W D^k x)_(k>=0).
```

Since `Gamma=B-D^2`,

```text
C_K*C_K
 =sum_(k>=0)D^k Gamma D^k
 =B.
```

The right survivor column is an isometry.  Fixed-`S` trace legality from Proof
261 allows the cyclic move inside each completed renewal term, giving

```text
Tr_B(N_W Gamma^(-1))
 =sum_(k>=0)Tr_B((L_WD^k)*(KD^k))
 =Tr_B(C_L*C_K).
```

Thus the Gate 3U scalar contains no standalone `Gamma^(-1)`.  The left column
Gram is the observability operator

```text
X_W=sum_(k>=0)D^k L_W*L_W D^k,

X_W=L_W*L_W+D X_W D.
```

The default certificate verifies `N_W=L_W*K`, the right isometry, the column
pairing, and the Stein equation with maximum error `8.53e-16`.  An independent
run at multiplicity ten passes below `1.50e-15`.  A conditioning stress moves
the minimum eigenvalue of `Gamma` down to about `5.3e-3`; the observability
norm stays below `4.53e-2` in the tested blocks.

An ordinary observability operator norm cannot control the trace.  Under
`1,2,4,8,16` orthogonal copies, the response and `Tr(X_W)` grow linearly while
`norm(X_W)` remains fixed.  The right column's unweighted Hilbert--Schmidt norm
also grows like the square root of the multiplicity.  This direct-sum guard
blocks a dimension-free conclusion from `norm(X_W)` and `norm(C_K)=1`.

Proof 273 shows that the active object is the signed scalar pairing

```text
Tr_B(C_L*C_K).
```

Refine the missing-channel identity

```text
Delta=I_rand*I_rand+I_C*I_C
```

through Proof 269's prime innovation channels.  Keep the three summands of
`L_W` combined and pair them with the survivor row.  Take the scalar trace,
apply compact support, and only then use Proof 272's concentration sum.  A
positive `H^1` column norm loses this cancellation.  Gate 3U, the arithmetic
same-object finite-S identity,
negative-owner integration, Burnol identity, and RH remain open.  No Lean owner
or route rewire is authorized.

## 2026-07-15 first-missing prime row

Proof 271 refines the renewal column through the actual missing channels.  Put

```text
I_rand=(I-P_0)V B,
I_C=C A B,
mathcalM=column(I_rand,I_C).
```

Then

```text
mathcalM*mathcalM
 =I_rand*I_rand+I_C*I_C
 =Delta.
```

For `D=Delta^(1/2)`, define

```text
J_0=B,
J_(k+1)=mathcalM D^k.
```

Their Grams sum to the renewal inverse:

```text
sum_(k>=0)J_k*J_k
 =B+sum_(k>=1)Delta^k
 =Gamma^(-1).
```

The survivor and reward rows

```text
mathcalR_K=(K J_k*)_(k>=0),
mathcalR_L=(L_W J_k*)_(k>=0)
```

satisfy

```text
mathcalR_K mathcalR_K*=K Gamma^(-1)K*,

Tr_B(N_W Gamma^(-1))=Tr(mathcalR_L*mathcalR_K).
```

The right row is a coisometry onto `Ran(K)`.  Every nonzero renewal term now
passes through a named first missing event, either `I_rand` or `I_C`.

The random channel has an exact prime filtration.  If

```text
V_S=product_j V_j,
A_j=E[V_j],
```

and `P_j` averages the variables after prime `j`, then

```text
(P_j-P_(j-1))V_S
 =V_<j(V_j-A_j)A_>j.
```

Thus the prime difference contains a common unitary history, one centered
local geometric innovation, and a contractive future average.  The prime
differences are orthogonal and their Grams sum to `I_rand*I_rand`.

The default certificate verifies the missing-channel Gram, renewal row,
coisometry, and prime Doob formulas with maximum error `2.08e-15`.  An
independent multiplicity-ten run passes below `1.37e-15`.

The exact remaining left-row components are

```text
L_W D^k I_(rand,j)*

 =L_W D^k B A_>j*(V_j*-A_j*)V_<j*,
```

together with `L_WD^kI_C*`.  The deterministic contraction `D^k B A_>j*`
sits between the complete physical reward and the centered prime difference.
Do not replace it by its norm before the real-line chirp kernel is derived.

Proof 273 withdraws the predictable positive-column estimate `(AH.30)`.
Gate 3U requires a scalar disintegration after the compact-rooted left row has
paired with the coisometric survivor row.  The arithmetic same-object finite-S identity,
negative-owner integration, Burnol identity, and RH remain open.  No Lean owner
or route rewire is authorized.

## 2026-07-15 concentration-function stopping ledger

Proof 272 supplies the positive square-energy summation for the corrected
Proof 269 ledger.  Order Proof 271's Doob filtration from large primes to
small primes.
The future factor `A_>p` then contains the independent variables at `q<p`.
With independent copies `N_q,N_q'`, define

```text
Y_(S,<p)=sum_(q in S, q<p)(N_q-N_q')log(q),
Q_h(mu)=sup_x mu((x,x+h]),
h=max(1,4B_root).
```

For `a_q=q^(-1/2)`, the exact difference-geometric law gives

```text
1-Q_h(Law((N_q-N_q')log(q)))
 =2a_q/(1+a_q)
 >=q^(-1/2)
```

whenever `log(q)>h`.  Kolmogorov--Rogozin bounds `Q_h(Y_(S,<p))` by the
inverse square root of the available smaller-prime mass.  The corrected mode
energy satisfies

```text
E_d(p)=sum_(m>=1)(1+m log(p))^(2d)p^(-m)
 <=C_d(1+log(p))^(2d)/p.
```

List the primes with `log(p)>h` as `r_1<...<r_n`.  For `j>=2`, the smaller
variables contribute at least `(j-1)r_j^(-1/2)` concentration deficit.  Hence

```text
E_d(r_j)Q_h(Law(Y_(S,<r_j)))
 <=C_d(1+log(r_j))^(2d)
   /[r_j^(3/4)sqrt(j-1)].
```

Since `r_j>=j+1`, this has the summable envelope
`C_d(1+log(j))^(2d)j^(-5/4)`.  The primes below `exp(h)` cost at most
`C_d(1+h)^(2d+1)`.  Therefore

```text
sup_(finite S) sum_(p in S) E_d(p)Q_h(Law(Y_(S,<p)))
 <=C_d'(1+B_root)^(2d+1).
```

This uses no prime number theorem and keeps one fixed orthogonal filtration.
It does not close Gate 3U.  The actual source row is

```text
L_W D^k B A_>p*(V_p*-A_p*)V_<p*.
```

The factor `D^k` remains between the complete three-branch reward and the
classical future average.  Proof 273 shows that a positive row norm cannot
extract compact-support probability.  The source must keep `D^k` inside the
signed left/right scalar pairing.  The probability source is Juškevičius, arXiv:2201.09861,
`https://arxiv.org/abs/2201.09861`.

The default WSL certificate checks the difference-geometric atom and
prime-mode reduction with maximum exact error `1.39e-16`.  At `p<=1000000`,
the default unstopped ledger is `132.03` and the ordered-future stopped proxy
is `45.29`.  Gate 3U, the arithmetic same-object finite-S identity,
negative-owner integration, Burnol identity, and RH remain open.  No Lean owner
or route rewire is authorized.

## 2026-07-15 signed paired stopping guard

Proof 273 corrects the proposed source lift.  For one completed compact-root
crossing with `|b|>2B_root`, Proof 260 gives

```text
Tr(K_(I,b,g))=0,
norm(K_(I,b,g))_1=|I|norm(g)_2^2>0.
```

A one-element noncommutative column `H1` norm equals the trace norm.  The
obstruction persists for a diffuse path law: take `N` pairwise
support-separated shifts with uniform measure and equal crossing intervals.
Then

```text
Q_h(mu_N)=1/N,
Tr(directSum_j (1/N)K_j)=0,
norm(directSum_j (1/N)K_j)_1=|I|norm(g)_2^2.
```

Thus a positive left-row norm measures total variation and cannot receive the
Proof 272 concentration factor.  This withdraws Proof 271 `(AH.30)` and Proof
272 `(AI.20)`.

The fixed-`S` algebra survives.  Let `I_p` be the orthogonal prime Doob
channels and `I_C=CAB`.  Define

```text
X_(k,p)=L_W D^k I_p*,   Y_(k,p)=K D^k I_p*,
X_(k,C)=L_W D^k I_C*,   Y_(k,C)=K D^k I_C*.
```

Then the exact signed first-missing pairing is

```text
Tr_B(N_W Gamma^(-1))
 =Tr(L_W* K)
  +sum_(k>=0)
    [sum_p Tr(X_(k,p)*Y_(k,p))
      +Tr(X_(k,C)*Y_(k,C))].
```

The real-line source theorem must disintegrate this completed scalar, with
the renewal index and all three physical branches still present.  A sufficient
form is Proof 273 `(AJ.14)--(AJ.15)`: the scalar kernel vanishes outside the
compact displacement window, has a `p^(-m)` envelope, and leaves a uniformly
controlled base/outer remainder.  Proof 274 shows that this envelope is the
missing extra-half-power theorem, not the local scalar coefficient.  Proof 272
then sums the ordered-future probability mass only after that theorem is
proved.

The default WSL certificate reports zero crossing trace, crossing/H1 mass
`40`, uniform 16-atom concentration `0.0625`, and exact signed renewal pairing
error `5.44e-16`; its maximum checked algebra error is `2.13e-15`.  Gate 3U,
the arithmetic same-object finite-S identity, negative-owner integration,
Burnol identity, and RH remain open.  No Lean owner or route rewire is
authorized.

## 2026-07-15 signed-scalar coefficient ledger

Proof 274 audits the coefficient after Proof 273 withdraws the positive `H1`
route.  The three owners are

```text
weighted chirp norm             a_p^m=p^(-m/2),
positive square energy          a_p^(2m)=p^(-m),
signed scalar local coefficient a_p^m=p^(-m/2).
```

Proof 222's exact outer trace and Proof 264's ordered Gram response each carry
one `a_p^m`.  The two Stinespring legs also recover the geometric probability
once.  Reusing the square energy as the scalar coefficient would repeat the
same ownership error in a new form.

For the exact location-aware event

```text
q_(S,p,m)(B_root)
 =mu_(S,<p)([-m log(p)-2B_root,-m log(p)+2B_root]),
```

the scalar ledger is

```text
sum_(p in S)sum_(m>=1)
 (1+m log(p))^(2d)p^(-m/2)q_(S,p,m)(B_root).
```

Proof 272's Levy bound gives only the first-mode rank envelope
`C(log j)^(2d)j^(-3/4)`, which is not summable.  This shows only that the
available majorant is insufficient; it does not prove divergence of the
signed response.

The active Gate 3U target is the complete extra-half-power estimate

```text
|Phi_(S,p,m)(z;g)|
 <=C(1+m log(p))^(2d)p^(-m)norm(g)_(H^r)^2.
```

It must be derived after the outer, second-support, and prolate branches and
the renewal powers have recombined, or replaced by a sharper source-specific
location estimate.  The finite-S sign, arithmetic same-object trace identity,
negative-owner integration, Burnol identity, and RH remain open.  No Lean
owner or route rewire is authorized.

## 2026-07-15 one-prime first-jet source reduction

Proof 275 rewrites the one-prime part of the missing extra half-power as one
continuous source estimate.  For an orthogonal projection `J`, let `J_a` be
the projection onto `(I-aU_z)Ran(J)`.  Its exact first jet is

```text
partial_a J_a|_(a=0)
 =-(I-J)U_zJ-JU_z*(I-J).
```

Subtract this identity for the nested pair `R<=E`.  Once the detector root is
supported in `[-B_root,B_root]`, Proof 260 deletes the completed outer
half-line scalar for `z>2B_root`.  The one-prime dressed response is therefore

```text
exp(-z/2) q_B(z;g)=-exp(-z/2)q_R(z;g).
```

The target `O(exp(-z))=O(p^(-m))` is exactly equivalent to

```text
|q_R(z;g)|
 <=C(1+z)^(2d)exp(-z/2)norm(g)_(H^r)^2.
```

Using `R=E E_hat E-K_prol`, this is a signed combination of three dressed
half-line crossings and one prolate commutator.  The default WSL certificate
checks the projection derivative with error `6.97e-10`, gives zero outer
finite-window read-off, and finds extra-half-power decay in the finite Sonin
diagnostic.  The diagnostic is not the continuous estimate.

Proof 251's mixed Hessian guard remains active: proving the one-prime estimate
does not authorize absolute summation of distinct-prime tangents.  The
continuous Sonin/prolate decay must be inserted into Proof 273's complete
determinant-resummed renewal before any absolute value.  Gate 3U, the finite-S
sign, arithmetic same-object trace identity, negative-owner integration,
Burnol identity, and RH remain open.  No Lean owner or route rewire is
authorized.

## 2026-07-15 CC20 static half-power tail

Proof 276 audits the primary CC20 source rather than inferring decay from the
finite Sonin sections.  Its explicit trace remainder satisfies

```text
delta(rho)=O(rho^(-1/2)).
```

The exact prolate expansion

```text
epsilon(rho)
 =sum_n lambda_n/sqrt(1-lambda_n^2)
   <xi_n,theta(rho^-1)zeta_n>
```

has the same tail up to one logarithm:

```text
epsilon(rho)=O(rho^(-1/2)(1+log rho)).
```

The static Sonin trace is `W_infinity+epsilon`.  CC20's regular archimedean
coefficient is also `O(rho^(-1/2))` after half-density normalization, so the
complete static coefficient has the displayed half-power tail up to one
logarithm.

The proof combines a `1/y` Fourier-tail estimate with CC20's polynomial
prolate Sobolev bounds and super-exponential `lambda_n` decay.  At
`rho=exp(z)` this is exactly the candidate `exp(-z/2)` scale.  It belongs to
the static Sonin trace correction, not automatically to the moving projection
first jet.  CC20's displayed `Q epsilon` estimates cover only `1<=rho<=2`.

## 2026-07-15 Sonin Toeplitz covariance reduction

Proof 277 identifies the moving first jet as

```text
D_J(W,H)
 =Tr([W,J]*[H,J])
 =2Tr(T_(WH)^J-T_W^J T_H^J).
```

Proof 276 controls the first static displacement exponent only for fixed
support.  An absolute convolution over `|u|<=2B_root` costs `exp(B_root)`, so
the polynomial support ledger is still open.  The compressed product is not
controlled by that tail either.  An exact positive-detector guard has static
product trace `0`, compressed product `4/9`, and Dirichlet pairing `-8/9`.

The active one-prime theorem is therefore

```text
|Tr(T_(w h_z)^R-T_w^R T_(h_z)^R)|
 <=C(1+z)^(2d)exp(-z/2)norm(g)_(H^r)^2.
```

This covariance must be proved using the complete CC20
`E/E_hat/K_prol` structure.  Its distinct-prime version stays inside the
relative Jacobi determinant and Proof 273 renewal until after the scalar trace
and compact-support stopping.  Gate 3U, the finite-S sign, arithmetic
same-object trace identity, negative-owner integration, Burnol identity, and
RH remain open.  No Lean owner or route rewire is authorized.

## 2026-07-15 Burnol boundary Gram covariance

Proof 278 closes the exact base-Sonin algebra needed before a relative
Wiener--Hopf/BOGC attempt.  Let `P_0` be the source-interval projection,
`F_0=P_0 Fourier P_0`, and

```text
A(u,v)=u+Fourier(v),
G=A* A=[[I,F_0],[F_0,I]].
```

Burnol's projection formula is

```text
I-R=A G^(-1)A*.
```

For commuting self-adjoint multipliers `W,H`, Proof 278 derives the complete
Sonin covariance on the two-copy source interval:

```text
Tr(R W(I-R)H R)
 =Tr G^(-1)[
    A*H W A-A*H A G^(-1)A*W A
   ].                                                  (AO.8)
```

The two terms in this bracket are Proof 277's static compression and
compressed Toeplitz product.  They are one centered owner and must not be
estimated separately.

In finite dimension, Jacobi's complementary-minor identity gives

```text
det_(Ran R)(Q_R* M Q_R)
 =det(M) det(G^(-1)A*M^(-1)A).
```

For `M=exp(sW+tH)`, the mixed logarithmic derivative at zero is exactly the
covariance in `(AO.8)`.  This identifies the finite-window coordinate on which
Proof 267's relative determinant must be factorized; it does not authorize the
ambient determinant in infinite dimension.

Applying the complementary formula to `R<=E` before taking the ratio cancels
the ambient determinant exactly:

```text
det_E(E M E)/det_R(R M R)
 =det_(H_0)(P_0 M^-1 P_0)
  /det_(H_0 direct-sum H_0)(G^-1 A* M^-1 A).
```

Its mixed logarithmic derivative is `S_E(W,H)-S_R(W,H)`, the base
`D_E-D_R` owner.  This relative identity, rather than either separate
complementary determinant, is the finite model for the continuous successor.

The plus/minus channel diagonalization is

```text
G ->diag(I+F_0,I-F_0),

(I+F_0)^(-1)-(I-F_0)^(-1)
 =-2F_0(I-F_0^2)^(-1).
```

The displayed `F_0` belongs only to the odd resolvent difference.  It does not
divide the complete centered covariance.  Proof 278's exact ownership guard
sets

```text
F_0=0,
K_prol=0,
```

but still obtains

```text
default:   |S_R|=1.895109, |S_E-S_R|=0.5740917,
alternate: |S_R|=2.079365, |S_E-S_R|=0.5070580.
```

Hence the former identity-channel cancellation target is rejected.  The next
proof must retain an even/two-boundary channel together with the odd/prolate
channel.  Any extra half-power has to emerge from their complete relative
determinant after recombination, not from `F_0` alone.  Proof 278 does not prove
that estimate or the `exp(-z/2)` tail.

The same certificate verifies

```text
R=E E_hat E-K_prol,

[R,H]
 =E E_hat[E,H]
  +E[E_hat,H]E
  +[E,H]E_hat E
  -[K_prol,H],
```

and checks that all four branches recombine before the boundary covariance is
taken.  The default errors are

```text
maximum exact algebra error             3.27e-15,
Jacobi complementary determinant error  3.22e-15,
relative E/R determinant error           9.83e-17,
boundary covariance error               8.62e-16,
mixed log-determinant derivative error  5.72e-8,
relative mixed-derivative error          1.05e-8,
three-branch commutator error            3.95e-16.
```

### Scope and non-goals

Proof 278 owns only the complementary-subspace algebra and its finite
certificate.  It does not prove:

```text
the infinite-dimensional trace domain for (AO.8),
the Sonin covariance exp(-z/2) estimate,
a continuous relative BOGC theorem,
prime telescope through the boundary Gram,
Gate 3U, the finite-S sign, or RH.
```

No Lean source or route consumer is changed.

### Source evidence

```text
Burnol, Theorem 4, explicit Sonin projection:
https://arxiv.org/abs/math/0208121

Bufetov, continuous Hankel-product BOGC for the sine process:
https://arxiv.org/abs/2412.20902

Petrov, oblique Jacobi/BOGC architecture:
https://arxiv.org/abs/2605.24976
```

Bufetov treats the ordinary sine projection.  Petrov assumes an ambient BOGC
operator `I-K`, `K in S1`.  Neither theorem supplies the relative
Burnol-boundary factorization required here.

### Active data-bearing owner

The next proof must start from the fixed-`S` relative determinant of Proof 267
and produce a root-sandwiched identity of the form

```text
tau_(E/R,S)
 =det(I-completed Burnol-boundary Hankel product),     (AO.19)
```

where trace class appears only after the `E/R` subtraction and the compact
root are present.  Differentiating `(AO.19)` must recover every term of the
four-branch commutator above and hence Proof 266's three physical numerator
branches.

### Consumer path

```text
Proof 267 relative Jacobi quotient
  -> Proof 278 Burnol boundary coordinate
  -> source-relative continuous Hankel product
  -> derivative readback of every physical branch
  -> complete normalized Euler product telescope
  -> Proof 273 signed scalar disintegration
  -> Gate 3U.
```

### Rejection guards

Reject the successor immediately if any of the following occurs:

```text
it requires the ambient Euler multiplier to be I+S1;

its derivative omits an outer, second-support, or prolate term;

it claims that the complete covariance carries an `F_0` or `K_prol` factor;

it cycles the ordered Gram inverse across the trace;

it estimates the two terms of (AO.8) separately;

it uses a positive H1 or nuclear norm to express compact-support cancellation.
```

If the boundary Gram blocks the complete prime telescope, retain `(AO.8)` as
an exact base identity and fall back to Proof 277 `(AN.13)` inside Proof 273's
signed renewal.  Do not weaken the object to make a standard BOGC theorem fit.

### Reproduction and acceptance

```text
python3 -B docs/proofs/278_burnol_boundary_gram_covariance_probe.py

python3 -B docs/proofs/278_burnol_boundary_gram_covariance_probe.py \
  --size 34 --support-rank 8 --seed 2278
```

Success for Proof 278 means both runs verify the algebra and determinant jet,
the zero-prolate survivor guard rejects the prolate-only mechanism, the
document states the continuous gaps, and no Lean owner is changed.
Partial means the boundary covariance holds but the determinant jet or physical
branch readback fails.  Rejection means the centered Gram does not reproduce
the same Sonin scalar.  Closure of Gate 3U requires the later continuous
relative Hankel theorem and a uniform signed scalar bound; Proof 278 alone is
not closure.

## 2026-07-15 Burnol channel Schur cocycle

Proof 279 resolves the plus/minus ownership question left by Proof 278.  With
`J:H_0 -> H`, `P_0=J J*`, and `F_0=J*FJ`, define

```text
A_+=(J+FJ)/sqrt(2),       G_+=I+F_0,
A_-=(J-FJ)/sqrt(2),       G_-=I-F_0,

V_+=A_+G_+^(-1/2),        C_+=V_+V_+*,
V_-=A_-G_-^(-1/2),        C_-=V_-V_-*.
```

Then `V_+,V_-` are orthogonal isometries, `F V_+=V_+`, `F V_-=-V_-`, and

```text
I-R=C_++C_-.
```

For a positive invertible perturbation `M`, the normalized Burnol boundary is

```text
B_M=[[D_+,X],[X*,D_-]],

D_+=V_+*M^(-1)V_+,
D_-=V_-*M^(-1)V_-,
X  =V_+*M^(-1)V_-.
```

The static Gram diagonalization does not make `X` vanish.  Instead,

```text
X
 =V_+*[(M^(-1)-F M^(-1)F)/2]V_-
 =(1/2)V_+*[F,M^(-1)]V_-.
```

This is the exact distinction between the static overlap `F_0` and the
Fourier-odd perturbation `[F,M^(-1)]`.

With

```text
Omega_M
 =D_-^(-1/2)(D_- -X*D_+^(-1)X)D_-^(-1/2),
```

finite-dimensional Schur factorization gives

```text
det_E(E M E)/det_R(R M R)
 =det(J*M^(-1)J)
  /[det(D_+)det(D_-)det(Omega_M)].
```

For `M_(s,t)=exp(sW+tH)`, let

```text
S_Q(W,H)=Tr(QW(I-Q)HQ),
kappa=2 Re Tr(C_- W C_+ H C_-).
```

The exact mixed jets are

```text
partial_(s,t)log det(D_+)|_0=S_(C_+),
partial_(s,t)log det(D_-)|_0=S_(C_-),
partial_(s,t)log det(Omega)|_0=-kappa,

S_E-S_R=S_(P_0)-S_(C_+)-S_(C_-)+kappa.
```

The deterministic ownership guard is

```text
F=[[0,1,0],[1,0,0],[0,0,1]],
P_0=e_1 e_1*,
W=H=v v*,   v=(e_2+e_3)/sqrt(2).
```

It has `F_0=K_prol=0` but

```text
S_(C_+)=S_(C_-)=3/16,
kappa=1/8,
S_R=1/4,
S_E-S_R=-1/4.
```

Thus dropping the Schur coupling gives `-3/8`, while retaining only the
coupling gives `+1/8`.  Both direct boundary channels and the coupling are
route-owned even in the zero-prolate model.

The default certificate has maximum exact algebra error `4.67e-15`, maximum
mixed-derivative error `1.06e-7`, and deterministic target error `1.39e-16`.
The alternate `size=34,support-rank=8,seed=2279` cohort has maximum algebra
error `5.56e-15` and mixed-derivative error `9.07e-8`.

### Active analytic target

The next theorem must construct the continuous root-sandwiched relative
determinant line represented finitely by the complete formula above.  It may
use two mechanisms, but must recombine them before the final absolute value:

```text
Fourier-commutator coupling:
  exploit X=(1/2)V_+*[F,M^(-1)]V_- and compact-root displacement support;

diagonal relative channel:
  compare J*M^(-1)J with D_+ and D_- on the same source geometry.
```

Do not define the four determinants separately in infinite dimension.  Do not
assume that the diagonal relative channel is small because `F_0` or `K_prol`
is small.  Differentiation must still reproduce both outer orientations, the
second-support branch, and the prolate commutator.  Mixed-prime terms remain
inside the normalized Euler determinant until the signed scalar read-off.

See `docs/proofs/279_burnol_channel_schur_cocycle.md`.  The continuous trace
domain, relative BOGC theorem, complete prime telescope, Gate 3U, finite-S
sign, arithmetic same-object identity, negative-owner integration, Burnol
identity, and RH remain open.  No Lean owner or route rewire is authorized.

## 2026-07-15 Toeplitz semicommutator Fredholm cocycle

Proof 280 closes the fixed-`S` determinant domain for Proof 279's complete
mixed covariance without defining its separate infinite boundary
determinants.  For an orthogonal projection `J`, write

```text
T_J(X)=J X J|_(Ran J),
U_s=exp(sW),
V_t=exp(tH).
```

Use the detector-first ordered cocycle

```text
K_J(s,t)
 =T_J(U_sV_t)T_J(V_t)^(-1)T_J(U_s)^(-1).
```

It has the exact completed-crossing factorization

```text
K_J-I
 =J U_s(I-J)V_tJ
   T_J(V_t)^(-1)T_J(U_s)^(-1).
```

Proof 261 gives `[W,J] in S1` for `J in {E,R}`.  Duhamel gives
`[U_s,J] in S1`, and

```text
J U_s(I-J)=-J[U_s,J](I-J) in S1.
```

Therefore `K_J-I in S1` trace-norm continuously near zero and

```text
c_J(s,t)=det(K_J(s,t))
```

is a genuine Fredholm determinant.  No Schatten premise on `[V_t,J]` is used.
The order is mandatory: reversing it moves the trace-class obligation to the
raw Euler/generator leg.

Both axes are normalized, `K_J(s,0)=K_J(0,t)=I`, and

```text
partial_(s,t)log c_J(s,t)|_(0,0)
 =Tr(JW(I-J)HJ)
 =S_J(W,H).
```

For `R<=E`, define the relative determinant-line scalar

```text
c_(E/R)(s,t)=c_E(s,t)/c_R(s,t).
```

Then

```text
partial_(s,t)log c_(E/R)|_(0,0)=S_E-S_R.
```

In finite complementary coordinates, if

```text
d_J(X)=det(Q_(Jc)*X^(-1)Q_(Jc)),
rho(X)=d_E(X)/d_R(X),
```

Jacobi cancellation gives the exact multiplicative second difference

```text
c_(E/R)(s,t)
 =rho(U_sV_t)/[rho(U_s)rho(V_t)].
```

Proofs 278--279 identify `rho` with the one-copy outer boundary divided by the
complete two-copy Burnol boundary, including `D_+`, `D_-`, and `Omega`.  In
infinite dimension the interior cocycles define the determinant line; the
boundary factors remain coordinates and must not be defined separately.

The default certificate has maximum algebra error `1.27e-14`, maximum mixed
derivative error `8.94e-8`, and zero-prolate guard error `2.05e-8`.  The
alternate `size=34,support-rank=8,seed=2280` cohort has maximum algebra error
`2.05e-14` and mixed-derivative error `9.85e-8`.  The deterministic guard still
has `F_0=K_prol=0` and reads back `S_E-S_R=-1/4`.

### Active analytic target

The fixed-`S` determinant domain is closed.  The next theorem is the uniform
relative-crossing estimate

```text
|partial_(s,t)log c_(E/R)(s,t)|_(0,0)|
 <=C(1+B_root)^d
   norm(eta)_(H^r)norm(xi)_(H^r),
```

with constants independent of the visible finite set.  Compare `K_E-I` and
`K_R-I` before any trace norm, apply the real-line `2B_root` displacement clip,
and keep the complete second multiplier `V_t` whole.  Do not estimate the two
cocycles separately, reverse their order, expand `V_t` into absolute prime
words, or infer a uniform bound from fixed-`S` Fredholm legality.

See `docs/proofs/280_toeplitz_semicommutator_cocycle.md`.  The uniform bound,
complete prime stopping/telescope, Gate 3U, finite-S sign, arithmetic
same-object identity, negative-owner integration, Burnol identity, and RH
remain open.  No Lean owner or route rewire is authorized.

## 2026-07-15 band-shorted semicommutator

Proof 281 descends Proof 280's relative `E/R` cocycle to one ordinary
Fredholm determinant on the common band `B=E-R`.  With

```text
I=C direct-sum R direct-sum B,
E=R direct-sum B,
```

define

```text
S_B(X)=B X B-B X R(R X R)^(-1)R X B
```

and

```text
L_B(s,t)
 =S_B(U_sV_t)S_B(V_t)^(-1)S_B(U_s)^(-1).
```

Proof 261 gives `[U_s,E],[U_s,R] in S1`.  In `B(H)/S1`, the detector therefore
commutes with `C,R,B` and becomes block diagonal on `R direct-sum B`.  Direct
Schur algebra then gives

```text
S_B(U_sV_t)=S_B(U_s)S_B(V_t) modulo S1.
```

The possible outer path also vanishes modulo `S1` because

```text
E U_s C=-E[U_s,E]C in S1.
```

Hence

```text
L_B(s,t)-B in S1
```

trace-norm continuously.  Its ordinary Fredholm determinant is Proof 280's
relative determinant-line scalar:

```text
det_B(L_B)=det(K_E)/det(K_R).
```

This closes the ordinary band domain specifically for the two-parameter
semicommutator.  It does not assert that any raw one-parameter shorted
determinant exists.

At the mixed derivative, expand `E=R+B` and `I-R=C+B`.  The common `R-C`
crossing cancels exactly:

```text
S_E-S_R
 =Tr(B W C H B)-Tr(R W B H R).
```

Both terms are route-owned detector crossings because

```text
B W C=-B[W,E]C,
R W B=-R[W,R]B.
```

They must remain one signed scalar difference.  Separate trace norms recreate
the rejected outer/Sonin triangle estimate.

The block-diagonal detector guard uses

```text
U=1.13 C+0.91 R+1.27 B
```

and makes the outer, Sonin, and band cocycles identities to `2.00e-15` for an
arbitrary tested second multiplier.  The deterministic zero-prolate guard
still has `F_0=K_prol=0` but the band crossing scalar is exactly `-1/4`.

The default certificate has determinant-coordinate error `7.69e-15`, physical
crossing error `1.18e-16`, and mixed-derivative error `1.96e-8`.  The alternate
`size=34,support-rank=8,seed=2281` cohort has determinant-coordinate error
`1.98e-15`, boundary-coordinate error `1.67e-14`, physical crossing error
`3.38e-16`, and mixed-derivative error `2.65e-8`.

### Active analytic target

Proof 281 applies at each synchronized flow time `alpha`, with

```text
E=E_(S,alpha), R=R_(S,alpha), B=E-R, C=I-E,
H=M_(h_(S,alpha)).
```

The second leg is the complete time-dependent generator multiplier from Proof
253, not the endpoint metric `H_S`.  Since `D_J=2S_J`, the exact endpoint owner
is

```text
2 integral_0^1 [
  Tr(B W C M_(h_(S,alpha)) B)
 -Tr(R W B M_(h_(S,alpha)) R)
] dalpha.
```

The new lowest theorem is the uniform integrated same-object estimate

```text
|the displayed integral|
 <=C(1+B_root)^d
   norm(eta)_(H^r)norm(xi)_(H^r),
```

No pointwise-in-`alpha` estimate of either crossing is assumed.  Insert the
real-line kernels, retain time cancellation, cancel common translated paths,
apply the `2B_root` displacement clip, and only then expose the causal prime
law.  Do not return to separate E/R determinants, separate crossing norms,
condition-number bounds, absolute prime words, or periodic boundaries.

See `docs/proofs/281_band_shorted_semicommutator.md`.  The uniform bound,
stopped prime theorem, Gate 3U, finite-S sign, arithmetic same-object identity,
negative-owner integration, Burnol identity, and RH remain open.  No Lean
owner or route rewire is authorized.

## 2026-07-15 moving-band cocycle integral

Proof 282 composes Proof 281 with the actual synchronized finite-`S` flow and
repairs the second-leg owner.  Use distinct parameters:

```text
alpha in [0,1]       synchronized transport time;
(s,r) near (0,0)     cocycle deformation parameters.
```

At each `alpha`, the moving projections are

```text
E_alpha=E_(S,alpha), R_alpha=R_(S,alpha),
B_alpha=E_alpha-R_alpha, C_alpha=I-E_alpha.
```

The second operator is

```text
H_alpha=M_(h_(S,alpha)),
h_(S,alpha)=Re(T_S'(alpha)T_S(alpha)^(-1)),
```

not the endpoint metric `H_S=T_S*T_S`.  Apply Proof 281's shorted cocycle on
`B_alpha` to `exp(sW)` and `exp(rH_alpha)`.  Its mixed jet is

```text
S_(E_alpha)(W,H_alpha)-S_(R_alpha)(W,H_alpha)

 =Tr(B_alpha W C_alpha H_alpha B_alpha)
  -Tr(R_alpha W B_alpha H_alpha R_alpha).
```

Proof 277 has `D_J=2S_J`.  Therefore the exact endpoint response is

```text
Tr(W(B_(S,1)-B_(S,0)))

 =2 integral_0^1 [
    Tr(B_alpha W C_alpha H_alpha B_alpha)
   -Tr(R_alpha W B_alpha H_alpha R_alpha)
   ] dalpha.
```

This is the route-owned target.  No pointwise-in-`alpha` estimate of either
branch is required.  Cancellation may occur between the two branches and
between different flow times.

The actual synchronized certificate imports Proof 253's prime-log
translations, complete product, moving projections, generator, and compact
four-mode root.  Default errors are

```text
exact algebra                 1.25e-13,
endpoint integration          3.10e-8,
band cocycle mixed jet        8.42e-7.
```

The alternate `size=160,step=0.064` cohort gives `1.89e-13`, `1.49e-9`, and
`9.56e-7`.  At default cutoff `p=2`, the integral of separate branch absolute
values is `35.695` times the endpoint magnitude.  This is direct evidence
against a branchwise triangle estimate, not a continuous lower bound.

### Active analytic target

Prove a uniform bound for the complete time integral after placing both
detector crossings in one real-line coordinate.  Identify equal translated
histories, cancel paths missing both moving boundaries, apply the compact
`2B_root` displacement clip, and expose the causal prime residual only
afterward.  Keep one absolute value outside the full integral.

See `docs/proofs/282_moving_band_cocycle_integral.md`.  The uniform integrated
bound, stopped causal theorem, Gate 3U, finite-S sign, arithmetic same-object
identity, negative-owner integration, Burnol identity, and RH remain open.  No
Lean owner or route rewire is authorized.

## 2026-07-15 cross-root moving transgression

Proof 283 connects Proof 263's legal compact cross-root endpoint form with
Proof 282's synchronized moving-band integral.  For compact roots `eta,xi`,
put

```text
W_(eta,xi)=C_xi* C_eta,
F_(eta,xi)=xi^star*eta.
```

The endpoint response is

```text
Q_S(eta,xi)
 =Tr(C_eta(B_(S,1)-B_(S,0))C_xi*).
```

At each flow time, use the complex analytic band cocycle with first leg
`exp(sW_(eta,xi))` and second leg `exp(rM_(h_(S,alpha)))`.  Linearity of the
mixed jet and Proof 282 give

```text
Q_S(eta,xi)

 =2 integral_0^1 [
    Tr(B_alpha W_(eta,xi) C_alpha H_alpha B_alpha)
   -Tr(R_alpha W_(eta,xi) B_alpha H_alpha R_alpha)
   ] dalpha.
```

This is the moving-to-endpoint transgression.  The endpoint coordinate depends
only on `F_(eta,xi)`, whose support lies in `[-2B_root,2B_root]`; the moving
coordinate retains the complete synchronized cancellation.

Complex polarization recovers every cross response from four diagonal roots:

```text
Q_S(eta,xi)
 =1/4 sum_(k=0)^3 i^k
    Q_S(eta+i^k xi,eta+i^k xi).
```

All four roots remain in the same support window.  Therefore diagonal and
cross-root Gate 3U estimates are equivalent up to a fixed constant.

The actual finite-S default certificate has algebra error `3.18e-16`, endpoint
error `2.13e-10`, cocycle mixed-jet error `9.51e-9`, and polarization error
`1.29e-17`.  The alternate cohort gives `2.80e-16`, `2.38e-11`, `1.19e-8`,
and `5.48e-18`.  Both responses have nonzero real and imaginary parts.

Never define `Tr(U_z(B_S-B))` pointwise.  Proof 260 shows it need not be trace
class.  Compact support must enter through the factorized cross roots and stay
outside the complete moving integral until the one-sided causal path
representation is assembled.

See `docs/proofs/283_cross_root_moving_transgression.md`.  The causal path
representation, uniform cross-root bound, Gate 3U, finite-S sign, arithmetic
same-object identity, negative-owner integration, Burnol identity, and RH
remain open.  No Lean owner or route rewire is authorized.

## 2026-07-15 cross-root causal observability pairing

Proof 284 imports Proof 283's genuinely complex detector into the inverse-free
renewal owner.  For

```text
W=W_(eta,xi)=C_xi* C_eta,
K=E A B,
Gamma=K*K,
Delta=B-Gamma,
D=Delta^(1/2),
```

the centered numerator remains

```text
N_W=K* W K-B W B Gamma.
```

Proof 270 assumed `W=W*`.  The correct cross-root left rewards are

```text
L_O=-[W,E]* C A B,
L_S=A R[W,Q]*(I-Q)B,
L_P=A R W* Q B,
L_W=L_O+L_S+L_P.
```

The adjoint in `L_P` is mandatory.  It gives

```text
N_W=L_W* K,
```

whereas the old Hermitian-only `A R W Q B` produces the wrong prolate branch
for a cross detector.  The default and alternate certificates reject that old
formula with relative errors `1.01e-2` and `6.18e-3`, while the corrected
factorization errors are below `2.14e-16`.

With

```text
C_K x=(K D^k x)_(k>=0),
C_(L,W) x=(L_W D^k x)_(k>=0),
```

the right column remains an isometry and the exact chain is

```text
2 integral_0^1 movingBandJet_(eta,xi,alpha) dalpha
 =Q_S(eta,xi)
 =Tr_B(C_(L,W)* C_K).
```

The active bottom is now the first-missing-displacement scalar
disintegration of this already paired quantity.  Insert the compact
cross-correlation and its `2B_root` support clip before splitting causal
histories or taking any norm.  Keep `L_O+L_S+L_P` whole.  A raw point trace,
`norm(C_(L,W))`, separate branch norms, and prime-path expansion before the
support clip remain forbidden.

See `docs/proofs/284_cross_root_causal_observability.md`.  The stopped scalar
bound, Gate 3U, finite-S sign, arithmetic same-object identity, negative-owner
integration, Burnol identity, and RH remain open.  No Lean owner or route
rewire is authorized.

## 2026-07-15 support-first two-boundary renewal functional

Proof 285 recombines Proof 266's three numerator branches before expanding
the common renewal.  With `iota_B:Ran(B)->H`,

```text
K=E A iota_B,
Gamma=K*K,
Delta=I-Gamma,
```

the convolution detector satisfies

```text
N_W
 =-iota_B*A*C W K+iota_B*W R A*K.
```

Fixed-`S` completed trace cyclicity therefore gives the support-first
functional

```text
Q_S(eta,xi)=Lambda_(eta,xi)(Z_S),

Z_S
 =R A*K Gamma^(-1)iota_B*
  -K Gamma^(-1)iota_B*A*C.
```

The second-support and prolate terms have not been dropped: they recombine
into the complete `R` term before this step.  Expanding only after inserting
`F_(eta,xi)=xi^star*eta` gives

```text
Z_(S,k)
 =R A*K Delta^k iota_B*
  -K Delta^k iota_B*A*C.
```

Thus the `2B_root` displacement clip acts on one completed outer-minus-Sonin
scalar before missing-channel or prime paths are exposed.

The identity is only a trace-functional identity on the convolution
commutant.  It is not the operator equality `Z_S=B_S-B` and does not extend to
arbitrary detectors.  Default/alternate certificates have maximum exact
errors `5.58e-16` and `9.34e-16`; their operator gaps are `0.203` and `0.223`,
and noncommuting trace gaps are `0.0202` and `0.0177`.  Support clipping leaves
the scalar unchanged while discarding kernels with Frobenius masses `0.181`
and `0.194`, so positive kernel norms remain forbidden.

The `seed=408` cancellation guard has exact error `6.03e-16`; taking
absolute values per completed renewal costs `3.10x` the final response, and
separating the outer/Sonin terms raises that cost to `20.83x`.  These are
finite rejection ratios, not continuous lower bounds.  They forbid both
triangle-estimate orders in the successor.

The active bottom is now to factor the already support-clipped `Delta^k`
through Proof 271's actual missing channels, cancel equal histories, and
isolate the first unmatched prime/mode scalar without taking termwise
absolute values.  That scalar must still earn Proof 274's extra half-power.

See `docs/proofs/285_support_first_boundary_renewal.md`.  The first-missing
scalar theorem, extra-half-power bound, Gate 3U, finite-S sign, arithmetic
same-object identity, negative-owner integration, Burnol identity, and RH
remain open.  No Lean owner or route rewire is authorized.

## 2026-07-15 first-missing relative-mode scalar

Proof 286 factors every nonzero support-first renewal level through the actual
missing maps after compact support has acted.  With

```text
H_(S,k)(W)
 =iota_B* W R A*K Delta^(k-1)
  -iota_B*A*C W K Delta^(k-1),
```

one has

```text
Lambda_W(Z_(S,k))
 =Tr(M_C H_(S,k)(W)M_C*)
  +sum_p Tr(M_p H_(S,k)(W)M_p*).
```

For a Doob prime channel

```text
M_p=V_<p(V_p-A_p)A_>p iota_B,
```

the common unitary past `V_<p` disappears inside the completed scalar trace.
The predictable future `A_>p` remains.  If

```text
Y=A_>p iota_B H_(S,k)(W)iota_B* A_>p*,
```

then the exact local innovation is

```text
E Tr((V_p-A_p)Y(V_p-A_p)*)
 =1/2 sum_(r in Z)
   [(1-a_p)/(1+a_p)]a_p^|r|
   Tr((U_(r log p)-I)Y(U_(r log p)-I)*).
```

This identifies the first unmatched prime/mode and shows that its route-owned
coefficient contains exactly one `a_p^|r|=p^(-|r|/2)`.  The missing second
copy must come from the complete real-line outer-minus-Sonin second
difference.  It must not be inserted by squaring the coefficient.

Default/alternate maximum exact errors are `1.48e-15` and `2.02e-15`.
Deleting `A_>p` changes the scalar by about `2.9e-3`.  The `seed=1012` guard
has exact error `1.36e-15` but charges `12.7449x` after relative modes receive
separate absolute values.  These are finite algebra guards, not continuous
bounds.

Proof 287 corrects the active bottom.  Expand both future-average legs to
their relative law and sum every local relative mode before estimating.  The
result is one Markov defect.  Its outer component has three support windows
centered at `0,+r log(p),-r log(p)`; its Sonin component is noncompact and
requires the complete signed Toeplitz-covariance tail.  A per-mode additional
`p^(-|r|/2)` estimate is false.

See `docs/proofs/286_first_missing_relative_mode.md`.  The continuous
readback, extra-half-power estimate, uniform base/outer remainder, Gate 3U,
finite-S sign, arithmetic same-object identity, negative-owner integration,
Burnol identity, and RH remain open.  No Lean owner or route rewire is
authorized.

## 2026-07-15 future-cloud relative law and Markov defect

Proof 287 expands the two predictable-future legs in Proof 286.  If

```text
A_>p=integral U_y d nu_>p(y),
mu_>p=Law(Y-Y'),
T_ell=U_ell-I,
```

then completed trace conjugacy removes the common future history and gives

```text
Tr(T_ell A_>p X A_>p* T_ell*)
 =integral Tr_completed(T_ell U_z X T_ell*)d mu_>p(z).
```

When the individual coefficient `kappa_X(z)=Tr(U_zX)` is legal, the completed
second difference is

```text
2kappa_X(z)-kappa_X(z+ell)-kappa_X(z-ell).
```

Summing the full symmetric relative geometric law before any absolute value
gives

```text
kappa_X-P_p kappa_X,

(P_p kappa_X)(z)
 =sum_(r in Z)[(1-a_p)/(1+a_p)]a_p^|r|
    kappa_X(z+r log(p)).
```

This Markov defect annihilates constants exactly.  It is the correct
scalar-gauge owner.  Proof 288 licenses the completed coefficient for the
specific renewal reward; the unrelated raw endpoint point trace remains
forbidden.

For the outer half-line, compact support produces three windows:

```text
|z|<=2B_root
  or |z+r log(p)|<=2B_root
  or |z-r log(p)|<=2B_root.
```

The former single window is false.  A compact triangular profile with
`B_root=1,r=9,z=0` has second difference `6` outside that old window.  The
same guard rejects a per-mode half-power by a factor `841.777`; the alternate
`r=11` guard gives `2525.33`.  For a point profile, the complete Markov defect
is only `2a_p/(1+a_p)=O(a_p)`, not `O(a_p^2)`.  Centering alone therefore does
not supply the missing half-power.

The Sonin component is not compactly supported.  Proofs 275--277 require a
signed Toeplitz-covariance/prolate tail.  The active theorem must estimate the
complete prime-level Markov defect after the renewal sum, using outer
three-window concentration and the Sonin tail together before one absolute
value.

Default/alternate maximum exact errors are `2.22e-16`.  Future relative-law
errors are below `4.0e-18`, and mode-sum/Markov-defect errors are below
`5.64e-18`.

See `docs/proofs/287_future_cloud_markov_defect.md`.  The Sonin Markov-defect
bound, uniform base/outer remainder, Gate 3U, finite-S sign, arithmetic
same-object identity, negative-owner integration, Burnol identity, and RH
remain open.  No Lean owner or route rewire is authorized.

## 2026-07-15 completed Markov displacement trace domain

Proof 288 closes the fixed-`S` coefficient domain for Proof 287's specific
renewal reward.  With `B=iota_B iota_B*`,

```text
X_(S,k)(W)
 =B[W,R]R A*K Delta^(k-1)iota_B*
  -B A*C[W,E]K Delta^(k-1)iota_B*.
```

Proof 261 and cross-root polarization give

```text
[W,E],[W,R] in S1.
```

All remaining factors are bounded for fixed finite `S`, hence

```text
X_(S,k)(W) in S1.
```

Therefore

```text
kappa_(S,k)(z)=Tr(U_z X_(S,k)(W))
```

is an ordinary bounded continuous function.  This does not legalize the raw
endpoint trace `Tr(U_z(B_S-B))`.

For one prime,

```text
A_p=(1-a_p)(I-a_p U_(log p))^(-1),
G_p=A_p A_p*
   =sum_(r in Z)[(1-a_p)/(1+a_p)]a_p^|r|U_(r log p).
```

The complete Markov defect is the single trace

```text
kappa_(S,k)(z)-(P_p kappa_(S,k))(z)
 =Tr(U_z(I-G_p)X_(S,k)(W)).
```

It equals the completed relative-mode second-difference sum.  The exact local
defect norm is

```text
norm(I-G_p)=4a_p/(1+a_p)^2=O(p^(-1/2)).
```

This is only the existing half-power.  Bounding the scalar by
`norm(I-G_p)norm(X_(S,k))_1` is forbidden for Gate 3U: the trace norm depends
on `S`, loses the signed outer/Sonin cancellation, and grows exactly `8x` on
the eight-copy guard while local operator norms stay fixed.

Default/alternate maximum algebra errors are `7.30e-16` and `8.02e-16`; the
point-defect and completed-second-difference errors are below `2.64e-18`.

See `docs/proofs/288_completed_markov_trace_domain.md`.  The uniform Sonin
Markov-defect bound, base/outer remainder, Gate 3U, finite-S sign, arithmetic
same-object identity, negative-owner integration, Burnol identity, and RH
remain open.  No Lean owner or route rewire is authorized.

## 2026-07-15 complete-prime Markov telescope

Proof 289 removes the unnecessary primewise extra-half-power requirement.
For every nonzero renewal level the completed reward `X_(S,k)(W)` is common to
all Doob prime channels.  The future product retained by Proofs 286--288 is
the exact telescope factor:

```text
sum_(p in S)G_fut(p)(I-G_p)
 =I-product_(p in S)G_p
 =I-G_S.
```

Therefore

```text
sum_(p in S)Xi_(S,k,p)(W)
 =Tr((I-G_S)X_(S,k)(W)).
```

Complete the relative modes inside each `I-G_p`, then complete the prime sum
before taking an absolute value.  Do not continue toward a termwise
`O(p^(-1))` bound: Proof 274's extra-half-power contract is sufficient but not
necessary after the signed telescope is retained.

The active owner is

```text
Q_S(eta,xi)
 =Xi_(S,0)(W)
  +sum_(k>=1)[
     Xi_(S,k,C)(W)
     +Tr((I-G_S)X_(S,k)(W))].
```

The next theorem must combine the base level, random global defect, outer
escape, complete Burnol outer/Sonin boundary, and renewal sum into one
real-line killed-path estimate with polynomial root-support cost.  The order
bound `0<=I-G_S<=I` is not enough: never replace the signed scalar by
`norm(X_(S,k))_1`.

Renewal circularity guard: do not immediately add the global random defect and
the outer missing channel.  Their Grams sum to `Delta`, so the renewal levels
would reconstruct `Gamma^(-1)` and return to the old condition number.  The
next construction should instead seek a root-completed source coboundary

```text
H_(S,1)=V_S(I-Delta)+Rem_S,
```

where `V_S` is a fixed-boundary, compact-support object with no
`Gamma^(-1)`.  Prove a uniform trace bound for `V_S` and a uniformly summable
stopped-path bound for `Rem_S`; then telescope the first term in `k` before one
absolute value.

Default/alternate exact errors are `4.98e-16/6.07e-16`; primewise absolute
values cost `35.35x/47.64x` in the ownership guards.  See
`docs/proofs/289_complete_prime_markov_telescope.md`.  The global
renewal-boundary estimate, Gate 3U, finite-S sign, arithmetic same-object
identity, negative-owner integration, Burnol identity, and RH remain open.
No Lean owner or route rewire is authorized.

## 2026-07-16 biorthogonal finite-horizon renewal colligation

Proof 290 replaces the provisional `V_S(I-Delta)` coboundary by a finite path
identity which preserves the ordered Gram trace.  Put

```text
R_n x=(Kx,K Delta x,...,K Delta^n x,Delta^(n+1)x),
L_n x=(Kx,Kx,...,Kx,x).
```

Then

```text
L_n*R_n=I,
1/2 I<=R_n*R_n<=I,

sum_(k=0)^n N_W Delta^k
 =L_n*diag(W,...,W,W_B)R_n-W_B.
```

With the canonical dual `F_n`, path projection `P_n`, and null coframe
`Z_n=L_n-F_n`, use

```text
sum_(k=0)^n N_W Delta^k
 =F_n*(O_nR_n-R_nW_B)+Z_n*[O_n,P_n]R_n.
```

The right path and canonical dual are uniformly bounded by `1` and `sqrt(2)`.
Do not estimate the growing `L_n` or `Z_n` norms.  The active analytic theorem
is a root-completed uniform scalar bound for the displayed two-defect pairing,
with compact support applied before the horizon limit.  A valid source
readback of `[O_n,P_n]` must retain both Burnol channels; no identification of
`P_n` with the fixed Burnol projection has yet been proved.

Default/alternate maximum algebra errors are `1.02e-15/1.70e-15`; right and
dual path norms remain uniformly below their exact bounds while the left path
growth guard exceeds `3.68x`.  See
`docs/proofs/290_biorthogonal_finite_horizon_renewal.md`.  The path-commutator
estimate, Gate 3U, finite-S sign, arithmetic same-object identity,
negative-owner integration, Burnol identity, and RH remain open.  No Lean
owner or route rewire is authorized.

## 2026-07-16 single-generator path defect

Proof 291 removes horizon-dependent detector algebra.  Put

```text
d_W=WK-KW_B,
d_W^left=K*W-W_BK*.
```

Then

```text
[W_B,Delta]=d_W^left K-K*d_W,

W K Delta^k-K Delta^k W_B
 =d_W Delta^k
  +K sum_(j=0)^(k-1)
     Delta^j(d_W^left K-K*d_W)Delta^(k-1-j).
```

The tail survivor block has the same formula with `k=n+1`.  For diagonal
roots, `d_W^left=d_W*`; use Proof 263 polarization only after the diagonal
bound.

The fixed physical generator is

```text
d_W
 =[W,E]A iota_B
  +E A C[W,E]iota_B
  -E A R[W,R]iota_B.
```

No horizon step introduces a new detector support or source projection.  Keep
the three branches and every term in the power-commutator transform signed.
The active theorem is a uniform compact-root scalar bound for Proof 290's
canonical/off-range pairing after substituting this complete single-generator
transform.  Apply `I-P_n` only after the whole transform is assembled, and do
not norm `L_n`, the `j`-sum, or the physical branches.

Default/alternate maximum exact errors are `1.33e-15/9.66e-16`; path
generation errors are `1.01e-16/1.19e-16`, and the scalar fixed mode vanishes
exactly.  See `docs/proofs/291_single_generator_path_defect.md`.  The stopped
path-transform bound, Gate 3U, finite-S sign, arithmetic same-object identity,
negative-owner integration, Burnol identity, and RH remain open.  No Lean
owner or route rewire is authorized.

## 2026-07-16 causal two-boundary generator

Proof 292 removes Proof 291's returned-outer branch using the exact source
invariance already proved in Proof 256:

```text
E A C=0,
C A* E=0.
```

Hence the fixed detector generator is not a three-channel object.  It is the
signed two-boundary pair

```text
d_W
 =[W,E]A iota_B
  -E A R[W,R]iota_B.
```

The first commutator has the exact compact-displacement kernel

```text
[W,E](x,y)
 =(1_E(y)-1_E(x))F(x-y),
supp(F) subset [-2B_root,2B_root].
```

The second commutator must be recombined as

```text
[W,R]
 =[W,E]E_hat E
  +E[W,E_hat]E
  +E E_hat[W,E]
  -[W,K_prol].
```

Do not estimate those Sonin subbranches separately.  Substitute the complete
two-boundary generator and its left companion into Proof 291's path transform,
then apply `I-P_n`, then use compact support on the scalar, and take one
absolute value only afterward.

The default/alternate certificates report maximum exact errors
`1.26e-15/1.03e-15`; `EAC`, `CA*E`, the returned branch, scalar fixed mode,
and off-support outer crossing are exactly zero.  See
`docs/proofs/292_causal_two_boundary_generator.md`.  The uniform stopped-path
estimate, Gate 3U, finite-S sign, arithmetic same-object identity,
negative-owner integration, Burnol identity, and RH remain open.  No Lean
owner or route rewire is authorized.

## 2026-07-16 observable two-boundary path compression

Proof 293 applies an exact range compression before the hard estimate.  For
the finite-horizon ordered path, replace each emission detector by `E W E`.
The difference is the one-way escape

```text
q_W=C d_W=C W K,
```

whose stacked path is annihilated by `R_n*`, `L_n*`, and `P_n`.  Therefore the
ordered response and its canonical/off-range split are unchanged, even though
the escape block itself need not have small norm.  The only generator that
remains is

```text
g_W=E d_W
 =-E W C A iota_B-E A R[W,R]iota_B,
```

with left companion

```text
g_W^left
 =-iota_B*A*C W E+iota_B*[W,R]R A*E.
```

The complete Sonin commutator remains signed; no subbranch estimate is
allowed.  The default/alternate Proof 293 certificates report maximum exact
errors `1.05e-15/1.25e-15`, exact agreement of original and `EWE` responses,
and zero for all escape pairings.  See
`docs/proofs/293_observable_two_boundary_path.md`.  The visible stopped-path
estimate, Gate 3U, finite-S sign, arithmetic same-object identity,
negative-owner integration, Burnol identity, and RH remain open.  No Lean
owner or route rewire is authorized.

## 2026-07-16 Hankel path-projection block closure

Proof 294 computes the exact right-path projection after Proof 293's
observable compression.  Put

```text
H_n=(R_n*R_n)^(-1)
   =(I+Delta)(I+Delta^(2n+3))^(-1).
```

For `0<=j,k<=n`,

```text
(P_n)_(j,k)=K Delta^(j+k)H_nK*,
(P_n)_(j,tail)=K Delta^jH_nDelta^(n+1),
(P_n)_(tail,k)=Delta^(n+1)H_nDelta^kK*,
(P_n)_(tail,tail)=Delta^(n+1)H_nDelta^(n+1).
```

The emission blocks and their `EWE` detector commutators are Hankel in `j+k`.
Default/alternate maximum exact errors are `7.95e-16/9.89e-16`; projection
and commutator Hankel errors are below `2.21e-16`, and `I<=H_n<=2I` has zero
violation.  The positive sum of block Frobenius norms grows by
`1.692x/1.670x` through horizon `32`, while the full commutator operator norms
remain below `0.88/0.85`.  These are finite guards, not a continuous estimate.

The active target is the signed anti-diagonal summation by parts:

```text
Hankel path commutator
  + visible generator recurrence
  -> initial emission boundary
  + final survivor boundary
  + complete outer-return/Sonin physical boundary
  -> compact-support scalar estimate uniform in S,n.
```

Do not replace this identity by the block-cost sum, omit the mixed tail
blocks, or identify `P_n` with Burnol's fixed projection.  If an uncanceled
bulk term survives, reject this lane and fall back to Proof 267's relative
determinant line.  See `docs/proofs/294_hankel_path_projection.md`.  Gate 3U,
finite-S sign, arithmetic same-object identity, negative-owner integration,
Burnol identity, and RH remain open.  No Lean owner or route rewire is
authorized.

## 2026-07-16 reflected Hankel divided-difference pair

Proof 295 identifies the exact resource inside Proof 294's anti-diagonals.
For `N=n+1`,

```text
h_N(t)=(1+t)/(1+t^(2N+1)),
f_(N,r)(t)=t^r h_N(t),
beta_(N,r)=2-f_(N,r)-f_(N,2N-r).
```

The reflected filter satisfies

```text
0<=beta_(N,r)<=2,
beta_(N,r)(1)=beta_(N,r)'(1)=0.
```

Interior projection blocks therefore pair as

```text
P_(j,k)+P_(N-j,N-k)
 =K(2I-beta_(N,j+k)(Delta))K*.
```

All corresponding detector commutators are operator divided differences of
the single physical pair `g_W,g_W^left`.  Reflection across `0/tail` changes
carrier and requires the explicit correction terms in Proof 295
`(BF.23)`, `(BF.25)`, and `(BF.27)`.  The naive formulas fail by
`5.63e-2/4.48e-2` on the near-survival guard; corrected maximum exact errors
are `1.87e-15/3.28e-15`.

The next gate is the actual weighted scalar assembly:

```text
Z_n*[O_n^E,P_n]R_n
  -> pair every reflected interior block
  -> retain all 0/tail g_W corrections
  -> keep beta as one bounded double-zero filter
  -> substitute the complete outer-return/Sonin generator
  -> apply compact root support
  -> one absolute value.
```

Do not norm the divided differences separately: the quadratic quotient of
`beta` can be `O(N^2)`.  Do not infer the weighted assembly from the local
reflection formulas; it remains to be proved.  See
`docs/proofs/295_reflected_hankel_divided_difference.md`.  Gate 3U, finite-S
sign, arithmetic same-object identity, negative-owner integration, Burnol
identity, and RH remain open.  No Lean owner or route rewire is authorized.

## 2026-07-16 weighted reflection parity

Proof 296 inserts Proof 295's blocks into the actual off-range owner

```text
T_n^off=Z_n*[O_n^E,P_n]R_n.
```

The interior path grid splits exactly as

```text
T_n^int=T_(+++)+T_(+--)+T_(-+-)+T_(--+).
```

The all-even sector has only one fixed-mode zero, with slope `N/2`.  The
other sectors have minimum zero orders `3,2,2`.  All pairs touching path
index `0` or the survivor tail stay in a named boundary strip.  The
default/alternate certificates have maximum errors `1.19e-15/9.48e-16`; the
boundary strip carries relative Frobenius magnitude `0.788/0.780` and cannot
be discarded.

The correct hard package is provisionally

```text
canonical response + T_(+++) + T_n^partial,
```

with the three soft sectors retained as one filtered remainder.  This is an
operator decomposition only; no sector receives a separate absolute value.

## 2026-07-16 emission-grid trace-anomaly guard

Proof 297 rejects the finite-section inference that the interior sector traces
vanish.  On `ell2(N)`, set

```text
X=(S+S*)/2,
Y=(S-S*)/(2i),
M=(Y+2I)/4,
K=M^(1/2),
Delta=I-M.
```

Then `[X,M]` is rank one but

```text
Tr(K[X,M]K)=-i/16.
```

Every finite shift section adds an artificial far-boundary `+i/16` and
reports zero.  Thus fixed-`S` trace-class membership of the completed
commutator and commutation of the scalar filters do not permit cycling the two
expanded non-trace-class terms separately.  Never delete `T_(+++)` from a
finite sector-trace diagnostic.

The next source attack is

```text
canonical + all-even + path boundary
  -> substitute g_W=-E W C A iota_B-E A R[W,R]iota_B
  -> recombine outer, second-support, and prolate branches
  -> prove source-specific anomaly cancellation/control
  -> attach the three soft stopped sectors
  -> compact support
  -> one absolute value.
```

See `docs/proofs/296_weighted_reflection_parity.md` and
`docs/proofs/297_emission_trace_anomaly_guard.md`.  Gate 3U, finite-S sign,
arithmetic same-object identity, negative-owner integration, Burnol identity,
and RH remain open.  No Lean owner or route rewire is authorized.

## 2026-07-16 relative Gram heat boundary layer

Proof 298 tests the entire finite path at the scale missed by the local
reflection ledger.  Set

```text
K_epsilon=sqrt(epsilon)K,
Gamma_epsilon=epsilon Gamma,
epsilon=T/N.
```

Then Proof 290's complete `N`-step ordered response converges to

```text
Tr_B(N_W integral_0^T exp(-t Gamma)dt).
```

For `Delta=exp(-x/N)` and path indices proportional to `N`, all six parity
filters have explicit nonzero hyperbolic limits.  All four Proof 296 sector
products can survive.  The fixed-horizon double/triple-zero ledger is correct
but cannot be combined with horizon-independent positive block norms.  The
reflected DOI block-estimate lane is rejected as Gate 3U.

Use instead the ordered relative heat pair

```text
Gamma_W(s)=K*exp(sW)K,
C_B(s)=B exp(sW) B,
Gamma_ord(s)=C_B(s)Gamma.
```

Proof 266 gives

```text
Gamma_W(s)-Gamma_ord(s) in S1,

Gamma_W(s)Gamma_ord(s)^(-1)
 =Gamma_W(s)Gamma^(-1)C_B(s)^(-1).
```

Hence its ordered heat first jet is exactly

```text
partial_s Tr(
  exp(-t Gamma_W(s))-exp(-t Gamma_ord(s)))|_(s=0)
 =-t Tr(N_W exp(-t Gamma)).
```

Do not replace `Gamma_ord(s)` by its positive similar representative
`C_B(s)^(1/2)Gamma C_B(s)^(1/2)`.  Finite determinants agree, but Proof 264's
similarity anomaly has physical/far boundary values `0.25/0.25` while the
finite total trace is zero.  Such a replacement can erase the ordered
arithmetic channel.

The active sufficient Gate 3U theorem is now

```text
sup_(finite S,T>=0)
 |integral_0^T
   Tr_B(g_(W,S)^left K_S exp(-t Gamma_S))dt|

 <=C(1+B_root)^d
   norm(eta)_(H^r)norm(xi)_(H^r),
```

with

```text
g_W=-E W C A iota_B-E A R[W,R]iota_B.
```

Keep the outer, second-support, and prolate pieces inside this one numerator;
apply compact displacement support before the signed time integration receives
one absolute value.  The default/alternate Proof 298 certificates have
maximum exact errors `4.91e-10/9.86e-10`, heat-jet errors
`6.41e-11/1.38e-10`, and discrete-to-heat refinement ratios `4.05/4.04`.
See `docs/proofs/298_relative_gram_heat_boundary_layer.md`.  Gate 3U,
finite-S sign, arithmetic same-object identity, negative-owner integration,
Burnol identity, and RH remain open.  No Lean owner or route rewire is
authorized.

## 2026-07-16 positive heat and diagonal joint-torsion cancellation

Proof 299 factors the ordered endpoint determinant before attempting the
uniform estimate.  Put

```text
G_s=K*exp(sW)K,
C_s=B exp(sW)B,
A_s=C_s^(1/2),
Gamma_sym(s)=A_s Gamma A_s.
```

Then

```text
R_ord(s)=G_s Gamma^(-1)C_s^(-1),
R_sym(s)=G_s Gamma_sym(s)^(-1),
J(s)=Gamma_sym(s)Gamma^(-1)C_s^(-1),

R_ord(s)=R_sym(s)J(s).
```

Proof 266 and positive functional calculus give all three operators as
identity plus `S1`.  The anomaly factor satisfies

```text
J(s)
 =[A_s,Gamma]_mult [Gamma,A_s^2]_mult,

det J(s)=d(A_s,Gamma)^(-1).
```

This is a genuine determinant-invariant/joint-torsion factor.  Elgart--Fraas
`arXiv:2110.00599` gives only sufficient hypotheses for such a multiplicative
commutator determinant to equal one; those hypotheses are not route-owned.
Migler `arXiv:1403.4882` and `arXiv:1409.6289` provide the determinant-
invariant and functional-calculus architecture.  Never delete `J(s)` from a
finite determinant calculation.

At the first detector jet, split

```text
N_ord=K*WK-W_B Gamma,
N_sym=K*WK-(W_B Gamma+Gamma W_B)/2,
N_anom=[Gamma,W_B]/2.
```

For the route diagonal `W=C_g*C_g`, Proof 263 gives a real original endpoint
trace and Proof 265 gives `N_ord in S1`.  Hence

```text
Tr(N_sym Gamma^-1) is real,
Tr(N_anom Gamma^-1) is purely imaginary.
```

Their sum is the same real endpoint response, so

```text
Tr(N_anom Gamma^-1)=0,

Q_S(g,g)
 =Tr(N_sym Gamma^-1)
 =partial_s log det(R_sym(s))|_(s=0).
```

This is the source-specific anomaly theorem left open by Proof 264.  Its scope
is only the diagonal first jet at `s=0`; it does not imply `J(s)=I`,
`det J(s)=1`, or cross-root anomaly cancellation.  Apply Proof 263 complex
polarization after the diagonal estimate.

The active Gate 3U endpoint theorem is now

```text
sup_(finite S)
 |partial_s log det(R_(sym,S,g)(s))|_(s=0)|

 <=C(1+B_root)^d norm(g)_(H^r)^2.
```

Equivalently, use the complete real heat owner

```text
integral_0^infinity
 Re Tr_B(g_W* K exp(-t Gamma))dt,

g_W=-E W C A iota_B-E A R[W,R]iota_B.
```

Keep the outer/second-support/prolate terms inside the real part and take one
absolute value afterward.  Proof 298's `sup_T` bound is no longer a required
gate; it remains a stronger sufficient theorem.  Proofs 282--283 retain the
same endpoint in the moving synchronized coordinate and may still be used for
Euler-time cancellation.

Default/alternate Proof 299 certificates have maximum exact errors
`2.38e-10/1.69e-10`, ordered/symmetric trace errors
`7.07e-19/3.85e-19`, and generic infinite anomaly magnitudes
`0.175/0.225`.  See `docs/proofs/299_positive_heat_joint_torsion.md`.
Gate 3U, finite-S sign, arithmetic same-object identity, negative-owner
integration, Burnol identity, and RH remain open.  No Lean owner or route
rewire is authorized.

## 2026-07-16 positive polar readback and one-prime no-gain guard

Proof 300 identifies exactly what Proof 299's positive symmetric determinant
buys.  With

```text
V=K Gamma^(-1/2),
P_S=V V*,
```

the diagonal first jet is the original projection response:

```text
partial_s log det(R_sym(s))|_(s=0)
 =Q_S(g,g)
 =Tr(W_g(P_S-B)).
```

This is a scalar readback through Proofs 263, 264, and 299.  It does not cycle
`Gamma^(-1/2)` through two separately non-trace-class terms, and it does not
promote the finite normalized determinant identity to a nonlinear
infinite-dimensional identity.

The exact commuting one-prime guard is

```text
U=diag(1,-1),
T_a=I-aU,
B=|(1,1)/sqrt(2)><(1,1)/sqrt(2)|,

Tr(diag(2,1)(P_a-B))=-a/(1+a^2),
Tr(diag(1,2)(P_a-B))=+a/(1+a^2),

a=p^(-1/2).
```

Both detectors are strictly positive and commute with `U`.  Hence positivity
gives neither sign nor the extra half-power: the response is
`O(p^(-1/2))`, while a uniform `O(p^(-1))` estimate fails in this abstract
class.  The guard omits the actual Sonin geometry, so it does not reject a
source-specific cancellation.

Default/alternate Proof 300 certificates have maximum exact errors
`7.66e-11/9.08e-11`, measured amplitude exponents `0.9982/0.9991`, and
largest-prime `p`-scaled responses `1000.0/1414.2`.  See
`docs/proofs/300_positive_polar_no_gain_guard.md`.

The active analytic lane is no longer another endpoint-coordinate change.  It
is Proof 277's complete Sonin Toeplitz covariance estimate `(AN.13)`, inserted
inside Proof 283's complete signed moving-band transgression `(AT.18)` before
any primewise or branchwise absolute value.  Gate 3U, the finite-S sign,
arithmetic same-object identity, negative-owner integration, Burnol identity,
and RH remain open.  No Lean owner or route rewire is authorized.

## 2026-07-16 support-first two-point covariance cocycle

Proof 301 gives the exact projection-kernel identity

```text
S_J(w,h)
 =1/2 sum_(x,y)
    (w(x)-w(y))(h(x)-h(y))|J_(x,y)|^2.
```

For a compact root, the multiplier is reconstructed from its correlation
`F_(eta,xi)`, with

```text
supp(F_(eta,xi)) subset [-2B_root,2B_root].
```

Therefore support enters before any raw mode or prime disintegration.  The
nested route uses the signed kernel `|E_alpha(x,y)|^2-|R_alpha(x,y)|^2`; the
outer, second-support, and prolate terms remain recombined.

The actual synchronized flow is also checked.  With

```text
X_alpha=T_alpha' T_alpha^(-1),
h_alpha=Re(X_alpha),
```

the moving derivative is the complete signed two-point pairing, and linearity
in `h_alpha=sum_p h_(p,alpha)` preserves the full moving `E_alpha/R_alpha`
kernel in every prime channel.  Default/alternate exact errors are
`3.54e-17/2.86e-17` for support pairing, `4.86e-17/4.51e-17` for the complete
prime-generator sum, and `2.08e-17/8.68e-17` for endpoint integration.

The static normalized product difference has an exact telescope, but it is not
the moving owner.  Replacing the moving projection kernel by the base kernel
has relative gaps `0.890/0.907`; this shortcut is explicitly rejected.

The provisional next theorem was a source-specific analytic strip for the
combined moving `E/R/K_prol` two-point kernel.  Proof 302 rejects its unpaired
global `Qdelta` contour form because of the `-2 Dirac_0` residue and oscillatory
post-`Q` tail.  The active successor is now the source divided-difference
bridge, with compact support and the residue paired before any estimate.  See
`docs/proofs/301_support_first_two_point_cocycle.md` and
`docs/proofs/302_quantized_divided_difference_residue_guard.md`.

## 2026-07-16 quantized divided differences and post-Q residue guard

Proof 302 corrects the contour successor using CC20's actual source formula.
Before `Q`,

```text
sqrt(rho)|delta(rho)|=O(1).
```

But `delta'(1+)=1`, so in the logarithmic coordinate

```text
Q_+ delta(exp(|x|))=-2 Dirac_0+q_reg.
```

The regular post-`Q` tail is oscillatory and does not satisfy a global
`exp(-z/2)` bound: the rejection ratios at `rho=1024/2048` are `4096/8192`.
The weak distribution split is verified numerically, so the residue cannot be
absorbed into an ordinary continuous kernel.

CC20 Appendix D/E instead gives the source divided-difference kernel

```text
([H,f])(s,t)=i/pi * (f(s)-f(t))/(s-t),
```

whose diagonal singularity is removable and whose constant mode vanishes.
Proof 302's two cohorts verify the divided-difference kernel at below
`3e-16`, the double-pairing readback at below `9e-16`, and the weak Dirac split
at `5.12e-11/2.71e-10`.

The active successor is now a source-specific divided-difference bridge for the
full moving `E/R/K_prol` kernel.  Isolate the diagonal residue, apply the
quantized kernel to completed root pairings, recombine all physical branches,
and only then seek the Gate 3U estimate.  Do not apply a global contour bound
to `Qdelta` or `Qepsilon` before this split.  See
`docs/proofs/302_quantized_divided_difference_residue_guard.md`.
