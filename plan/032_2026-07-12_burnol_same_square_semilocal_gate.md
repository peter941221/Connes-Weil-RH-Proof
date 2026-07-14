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
