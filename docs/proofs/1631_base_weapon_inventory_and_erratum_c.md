# 1631 — The base weapon inventory: fifteen tools, their hypotheses against the committed symbol, and Erratum C

Date: 2026-09-18.

Status: analytic record, no Lean brick. This round executes item 1 of the
1630 report's next steps: a **weapon inventory** (武器盘点) for the carrier base
— every available infinite-type existence tool, listed with its verbatim
statement, its source, its hypotheses audited against the committed symbol `m`,
and what it would buy. The point is to convert "wall 1" (the assertion that no
retrieved criterion is in class) into a *checklist of named questions* with
named sources. Two executable rigs land (`scripts/dvi_extract.py`,
`scripts/phase_budget_1631.py`), one **erratum** is recorded (1630 section 8's
two-tap form), and one line of 1630 section 4 is **flagged as not re-verified**.

RH is not claimed. The carrier base stays **OPEN**.

Consumer (named, unchanged): the healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g` through `G8SameOwnerReadbackData`
([012](../map/012_g8_same_owner_readback_rh_reachability.md)).

## 1. Verdict

```text
(A) WHAT WALL 1 IS    the base of the carrier (1629 sec 3; 1630 sec 5):
                      BASE  <=>  exists H in H^2(C_+)\{0}, U_tree H in H^2(C_-),
                      U_tree(xi) = e^{4 pi i (log lambda) xi} m(-xi).
                      "No criterion in class" was an ASSERTION after 1630.
                      After this round it is a 15-row checklist with 5 named
                      quantitative questions (Q1-Q5) and 5 retrieval targets
                      (R1-R5).  No row changed the verdict; three rows changed
                      their STATUS (audited vs assumed).

(B) THE PHASE BUDGET  the committed symbol's continuous argument is, to 6
                      digits over five decades,

                          gamma(xi) = -2 pi xi log|xi| + 2 pi xi + pi/4
                                      - 6.631e-3/xi + O(xi^{-3}),
                          gamma'(xi) = -2 pi log|xi| + O(xi^{-2}),
                          gamma(-xi) = -gamma(xi)   (exactly: m(-xi)=conj m(xi)),

                      so the criterion's phase psi = -gamma - a xi is
                      SUPER-LINEAR with exponent 1 + o(1) (i.e. x log x), with
                      |gamma'| of LOGARITHMIC growth - below every polynomial,
                      hence inside the survey's generalized (power-law) form and
                      outside the classical |Psi'| <~ 1 form.  Rig sec 4.

(C) THE TWO BUDGETS   for model data of exponent beta:
                          h in L^1(dPi)  requires  beta < 1   (density),
                          inner arguments require  beta < 2   (measure),
                      and our phase sits at exponent 1 + o(1): strictly INSIDE
                      the measure budget, strictly OUTSIDE the density budget.
                      Consequence: in any decomposition psi = arg Theta + h~ the
                      super-linear part must be carried by Theta (the measure
                      side), not by h~.  This is the first non-trivial
                      quantitative statement the inventory produces (rig sec 2).

(D) THE FIFTEEN ROWS  three tools APPLY at our question (Thm A(ii)/Corollary,
                      sec 4.1 proposition, maximal-vector structure); one
                      applies only to the strictly weaker FINITE-TYPE question
                      (Krasichkov-Tumarkin, committed 1628: it re-proves 1627's
                      obstruction and is silent on infinite type); six are OUT
                      OF CLASS with a named failing hypothesis (Thm B, big
                      multiplier as stated, crux sub-problem, BM density
                      criterion as stated, de Branges classical machinery,
                      classical multiplier); three are dictionaries or parallel
                      lanes, not criteria (Smirnov identity, model spaces, CCM
                      prolate); one is the target itself ((1.6) at p = 2); and
                      one is a phase-choice tool (sec 6 Krein shift).  All row
                      quotes and URLs are in sections 3 and 6.

(E) ERRATUM C        1630 section 8's two-tap form

                          w(.- a_tilde/(2 pi)) * h = w * g       [WRONG]

                      is replaced by

                          w(-.) * h(. + c) = w * g,   c = 2 log lambda <= 0,

                      i.e. the shift acts on the SIGNAL, not on the tap, and the
                      left tap is w(-.), not w(.).  Three independent checks in
                      section 7 (lambda = 1; m = 1 where the two forms agree
                      because delta is even; and a shifted-tap model
                      m(xi) = e^{2 pi i mu xi} where the printed form predicts a
                      mu-INDEPENDENT threshold and the corrected form predicts
                      mu > c, which is the true answer).

(F) FLAG             1630 section 4's audit line "power-law hypotheses of B/C
                      and section 5.1 ('~') FAIL" is NOT re-verified and is
                      likely wrong for section 5.1: in the retrieved survey the
                      power-law condition is imposed on the MULTIPLIER psi
                      (which the theorem chooses), its general form allows
                      |psi'| <~ |x|^kappa, and our phase derivative grows only
                      logarithmically.  Section 8, item F.

(G) NOT CHANGED      lambda-behaviour, the p < 1/2 nontriviality (Theorem
                      A(ii)), the vacuity of the shortness sum, the B4 verdicts,
                      and the Toeplitz-probe numbers of 1630 stand.  The
                      inventory adds no witness and refutes no candidate.
```

## 2. What the inventory replaces, and how a row is priced

Before this round the base's status rested on a sentence: *"the retrieved
criteria are not in class"*. That sentence mixes four independent things, and
the inventory separates them, one column per row:

```text
+----------------+-----------------------------------------------------------+
| column         | meaning                                                   |
+----------------+-----------------------------------------------------------+
| STATEMENT      | the theorem verbatim, with its own quantifiers             |
| SOURCE         | URL or committed record; primary preferred to survey       |
| HYPOTHESIS     | the hypothesis list, checked against the COMMITTED symbol  |
|                | m (its phase regularity, its class, its growth)            |
| FIT            | applies / out of class / dictionary / pointer, plus the    |
|                | ONE failing hypothesis when out of class                   |
| BUYS           | what the base gains if the row applies: an equivalence, a  |
|                | witness class, a normalization, or nothing                 |
+----------------+-----------------------------------------------------------+
```

Three failure modes are distinguished on purpose, because conflating them is
what makes "wall 1" sound stronger than it is:

```text
(1) CLASS failure       the theorem is about a different kernel class
                        (N_p vs H^2; SN vs Hardy)            -> Thm A(ii), B
(2) HYPOTHESIS failure  same class, but the symbol's phase violates one of
                        the theorem's regularity conditions -> Thm 8.4, 8.5
(3) GAP failure         the theorem decides a PERTURBED object (epsilon-gap),
                        or an object at a distance (transfer gap)  -> 8.5, 4.1
```

Only (3) is a "gap" in the sense of something still missing from the
literature read; (1) and (2) are facts about our symbol.

## 3. The inventory (15 rows, three groups)

### Group A — phase-decomposition tools (Makarov–Poltoratski chain)

```text
   #   tool                                   fit vs the committed m                 verdict
+--+----------------------------------------+--------------------------------------+--------------------------+
|A1| MP 2010 (1.6), Hardy clause:           | the target statement itself          | THE TARGET               |
|  | the p = 2 criterion                    |                                      |                          |
|A2| MP 2010 (1.6), SN clause               | same shape, class N^+ not H^2        | dictionary               |
|A3| Theorem A(ii) + Corollary              | (1.4) satisfied; d = 0 transfer gap; | APPLIES, p < 1/2         |
|  |                                        | p-range gap                          |                          |
|A4| section 4.1 little multiplier          | statement covers d = 0; proof is     | APPLIES with transfer    |
|  | proposition                            | written for intervals away from 0    | gap                      |
|A5| Theorem B (p >= 1 under inner factor J)| needs J inner; m is not inner, m     | OUT OF CLASS             |
|  |                                        | not in N                             |                          |
|A6| section 5.1 big multiplier             | gamma real-analytic yes; bounded     | OUT OF CLASS as stated   |
|  | (= survey Thm 8.5)                     | variation no; gamma' bounded below   |                          |
|  |                                        | no; eps-gap                          |                          |
|A7| classical BM multiplier                | needs |Psi'| <~ 1; ours is log-growth| superseded by A6         |
|A8| the "crucial part" sub-problem         | needs h~' <~ 1; our phase's          | hypothesis FAILS as      |
|  |                                        | conjugate is log-scale               | posed                    |
|A9| section 6 approximation by inner       | psi not increasing; statement        | PARTIAL (phase choice)   |
|  | functions (Krein shift)                | formula-damaged in the extract       |                          |
+--+----------------------------------------+--------------------------------------+--------------------------+
```

### Group B — density/completeness tools

```text
   #   tool                                   fit vs the committed m                 verdict
+--+----------------------------------------+--------------------------------------+--------------------------+
|B1| BM density criterion (survey Prop 8.6):| needs the symbol to be (meromorphic  | OUT OF CLASS as stated   |
|  | completeness radius = D^+_BM           | inner) e^{iaz}, i.e. Ibar B_Lambda;  |                          |
|  |                                        | ours is not (law F40)                |                          |
|B2| Krasichkov-Tumarkin (1960s ancestor)   | committed 1628: kills FINITE type    | APPLIES, finite type     |
|  |                                        | only; silent on infinite type        | only (weaker question)   |
+--+----------------------------------------+--------------------------------------+--------------------------+
```

### Group C — structure, class, spectral

```text
   #   tool                                   fit vs the committed m                 verdict
+--+----------------------------------------+--------------------------------------+--------------------------+
|C1| model spaces and maximal vectors       | symbol-agnostic structure theorem    | APPLIES (normalization)  |
|  | (Camara-Partington 2017)               |                                      |                          |
|C2| Smirnov identity N^+ cap L^2 = H^2     | dictionary                           | APPLIES (why p = 2 is a  |
|  |                                        |                                      | Hardy problem)           |
|C3| de Branges space existence (1626, 1590)| base = de Branges pattern; A is NOT  | FRAMEWORK, no criterion  |
|  |                                        | Hermite-Biehler                      |                          |
|C4| CCM prolate spectrum (1623, T4 lane)   | parallel spectral lane; the tree's   | NOT A BASE TOOL          |
|  |                                        | "prolate" is a different object      |                          |
+--+----------------------------------------+--------------------------------------+--------------------------+
```

## 4. The phase budget of the committed symbol (rig section 1–2)

`scripts/phase_budget_1631.py`, run at 30 digits, section 1:

```text
   xi        gamma(xi)             model -2pi xi log xi+2pi xi    rel.err     resid vs model+pi/4   gamma'(xi)          -2 pi log xi
   1e2       -2264.4099024          -2265.19523425               3.47e-04   -6.631e-05            -28.9351369865      -28.9351376497
   1e3       -37118.7357758         -37119.5211673               2.12e-05   -6.631e-06            -43.4027064679      -43.4027064745
   1e4       -515870.114524         -515870.899921               1.52e-06   -6.631e-07            -57.8702752993      -57.8702752993
   1e5       -6605465.0963          -6605465.8817                1.19e-07   -6.631e-08            -72.3378441242      -72.3378441242
   1e6       -80522226.8564         -80522227.6418               9.75e-09   -6.631e-09            -86.805412949       -86.805412949
   odd check: gamma(-xi) + gamma(xi) at xi = 1e3 : 0.0
```

Three readings:

1. The residual after `pi/4` decays exactly like `1/xi` (`-6.631e-3/xi` at every
   decade), so the closed form is `gamma(xi) = -2 pi xi log|xi| + 2 pi xi +
   pi/4 + O(1/xi)` — the constant is the Stirling constant of
   `logGamma(1/4 + pi i xi)`, so this is a self-check of the committed symbol,
   not new information about it.
2. `gamma' ~ -2 pi log|xi|`: **logarithmic** growth, negative, unbounded below.
   This is what makes A6's "γ′ bounded from below" fail and, at the same time,
   keeps the phase inside the *generalized* power-law form
   (`|psi'| ≲ |x|^kappa` holds for every kappa > 0).
3. `gamma` is odd, so `psi = -gamma - a xi` is *not monotone* on ℝ: it is odd
   with the sign of `xi`, while the inner-function clauses of A1/A9 are stated
   for *increasing* phases.  The reflection bookkeeping (1629 section 3, 1630
   section 5) is what makes the criterion's `psi` an increasing object; the
   inventory therefore lists this as a convention item, not as a failure.

Section 2 of the rig: the two membership budgets, read off from tail
increments (for a power tail the successive-increment ratio over a factor 1000
is exactly `1000^(beta-1)`):

```text
   beta     int_1^1e3      int_1^1e6       int_1^1e9      incr ratio 1000^(b-1)   verdict
   0.5      1.6707004      1.731946        1.7338827       0.0316     0.0316    converges
   0.9      4.6610454      7.161031        8.413992        0.5012     0.5012    converges
   1.0      6.5611822      13.468937       20.376692       1.0000     1.0000    LOG DIVERGES
   1.1      9.5842996      29.442392       69.064499       1.9953     1.9953    diverges
   1.5      60.758079      1997.5125       63243.066       31.6228    31.6228   diverges
   1.9      555.06146      279096.68       1.398806e+08    501.1872   501.1872  diverges
   2.1      1812.0802      3619154.3       7.2211658e+09   1995.2623  1995.2623 diverges
```

The same table is the budget of two different classes: a *density* `h` with
`h in L¹(dΠ)` needs exponent `< 1`; a *measure* `μ` (the Blaschke/singular data
of an inner function, whose argument is built from `dμ`) needs exponent `< 2`.
Our phase needs exponent `1 + o(1)`. So:

```text
+---------------------------+----------------+-------------------------------+
| carrier of the growth      | budget         | our phase (exponent 1+o(1))    |
+---------------------------+----------------+-------------------------------+
| h~ of an L^1(dPi) function | beta < 1       | OUTSIDE  -> h~ cannot carry it |
| arg of an inner function   | beta < 2       | INSIDE   -> Theta can carry it |
+---------------------------+----------------+-------------------------------+
```

That is a *positive* structural statement: the decomposition demanded by the
p = 2 criterion is not obstructed by a crude growth count. It is the reason the
five questions Q1–Q5 below are quantitative, not qualitative.

## 5. The criterion, its two clauses, and the class-direction table

The criterion (A1) as committed in 1630 section 5:

```text
BASE  <=>  there are an inner function Theta and h in L^1(dPi) with
           e^h in L^1(R) such that      -gamma(x) - a x = arg Theta(x) + h~(x),
           a = 4 pi log(1/lambda).
```

The MP 2010 extract (`tmp`-scratch source retrieved this round; see section 6
for the URL) shows this is the *second* clause of (1.6); the first clause is
the Smirnov–Nevanlinna case. Verbatim, with the DVI prose damage marked by
`[...]` (formulas are not recoverable from the prose extract):

```text
"[:] is a smooth function. Then [Ker ...] = 0 if and only if [gamma] = [d] + h~,
 [d] increasing function and some [h in] L^1[dPi].  There is a similar [statement]:
 [...] = 0 if and only if [gamma] admits [gamma = -phi - h~] being the argument of
 some inner function and with [h in] L^1[dPi] such that [e^h in] L^2(R).
 (1) the usual weak L^1-space with respect to the Poisson measure [L^1(dPi)];
 [L^1_(1)] where L^1_(1) stands for the 'little o' subspace of L^1_(1), i.e.
 [...] (1.7)"
                          -- MP 2010 section 1, lines 443-490 of the MIF2 extract
```

Two things are visible despite the damage, and both matter:

* the second clause says **"some inner function"** (no "meromorphic"), and it
  pairs `h in L¹(dΠ)` with an **exponential-space clause** whose exponent the
  extract prints as `L^2(R)`;
* immediately after comes a "little-o subspace" refinement referenced as (1.7):
  the criterion's `h` may be asked to lie in a small subspace of the weak-L¹
  space, which is exactly where a growth budget would bite.

The survey's prose states the same criterion twice, and the two statements do
not agree on the exponential clause:

```text
"h in L^1(dPi), and morover e^h in L^1(R)"
      -- survey (arXiv:1511.08326), section 8, describing the Hardy-case criterion

"(2) in addition to condition h in L^1(dPi) we would also need the condition
 e^h in L^2(R).  The second problem is much harder and its solution lies much
 deeper."
      -- same survey, the two-problem decomposition of the big multiplier theorem
```

So `L¹(ℝ)` vs `L²(ℝ)` is a **source-level ambiguity** (Q2), not a slip in a
record; 1630 section 5's parenthetical `e^h in L^1(R)` is the survey's first
reading and stays as the committed one.

**Direction, with classes attached.** "Short" in this literature is a property
of the family `Σ(γ)` of BM intervals (1630 section 3 computed ours: one
interval containing the origin, d = 0, right edge λ⁻²; shortness sum vacuous).
The same word drives three *different* conclusions:

```text
+---------------------+--------------------------------+----------------------+
| kernel class        | conclusion from shortness       | source               |
+---------------------+--------------------------------+----------------------+
| Smirnov-Nevanlinna  | gamma(x) - eps x = d + h~       | survey Thm 8.4(ii);  |
| (N^+)               | (representable after an eps     | long case: Thm       |
|                     | shift); long => even gamma+eps x| 8.4(i)               |
|                     | is NOT representable            |                      |
| N_p, p < 1/2        | N_p[U_eps S_eps] != {0}: the    | MP 2010 Thm A(ii);   |
|                     | perturbed kernel is NON-trivial | 1630 sec 4 (applies) |
| H^2 (p = 2)         | the PERTURBED symbol U e^{-i eps| survey Thm 8.5;      |
|                     | psi} has TRIVIAL kernel; long =>| 1630 sec 4           |
|                     | the perturbed symbol is NOT     |                      |
|                     | injective                       |                      |
+---------------------+--------------------------------+----------------------+
```

There is no contradiction between row 2 and row 3: different class, different
operator, and an `eps` perturbation in both. This is law F42 sharpened into a
table — **a criterion's kernel class, exponent, and ε-gap are part of its
statement** — and it is the reason 1630's (C) "short ⟹ nontrivial" must not be
carried into the p = 2 discussion.

## 6. Row detail, with sources

**A1 — the p = 2 criterion (THE TARGET).** Statement in section 5. Cited by
MP 2010 for the analogue in the general case as "[23], Section 3.1" and in
1630 section 5 for (1.6) as "[23, section 2]". **[23] identified this round**:
N. Makarov, A. Poltoratski, *Meromorphic inner functions, Toeplitz kernels and
the Uncertainty Principle*, in: Perspectives in Analysis, Math. Phys. Stud. 27
(Springer, 2005), 185–252 — full text retrieved as DVI from
`https://people.math.wisc.edu/~poltoratski/MIF.dvi` (the author's publication
page lists the 2010 Inventiones paper as `MIF2.dvi` and the 2005 chapter as
`MIF.dvi`; the two were told apart by their title lines in the prose extract).
The (1.6) and section 6 quotes in this record are from the **2010** paper,
`https://people.math.wisc.edu/~poltoratski/MIF2.dvi`; both files were read with
the committed `scripts/dvi_extract.py`. Buys: the base is one decomposition
question with a named source for the answer.

**A2 — the SN clause.** Verbatim from the survey: *"It can be shown that for a
unimodular symbol U = e^{iγ} the Toeplitz kernel Ker⁺T_U is trivial if and only
if the argument γ can be represented as a sum d + h̃ of a decreasing function d
and some h ∈ L¹(dΠ)."* Buys: shows exactly what changes from N⁺ to H² — `d`
becomes `arg Θ` with Θ inner, and the exponential clause appears.

**A3 — Theorem A(ii) + Corollary.** Committed 1630 section 4: applies
(`(1.4)` one-sided Lipschitz satisfied), gives nontriviality in `N_p` for
`p < 1/2` (corollary `p < 1/3`). Buys: a *true* nontriviality statement about
our symbol — at the wrong exponent. This is where the p-range gap is measured,
not asserted.

**A4 — §4.1 proposition.** Committed 1630 section 4, caveat 1: the statement is
for every phase satisfying (1.4) *including* `d = 0` intervals, but its proof
consumes `l ≳ d` and a level constraint that our interval (deficit
`f(0) = 2π R_a`) does not meet. Buys: the atoms machine that would build the
`Θ`-side; the transfer to `d = 0` is Q4.

**A5 — Theorem B.** Committed 1630 section 4: needs an inner factor `J`;
`|m(x + iy)| ~ |x|^{2πy}`, `m` is not inner and not in `N`. Buys: nothing —
and it is precisely the p = 2 statement we would want, which is why the search
for a p = 2 criterion had to leave MP 2010's Theorem B.

**A6 — §5.1 big multiplier (survey Theorem 8.5).** Verbatim (survey section 8):

```text
"Theorem 8.5. ... (i) If [Σ(γ) does not satisfy shortness] then for every ǫ > 0
 the Toeplitz operator T_V : H^2 → H^2 with symbol V = U e^{iǫψ} is NOT
 injective.  (ii) If Σ(γ) satisfies the shortness condition 8.2, then for every
 ǫ > 0 the Toeplitz operator T_V : H^2 → H^2 with symbol V = U e^{-iǫψ} is
 injective.  In fact, Makarov and Poltoratski proved a more general result which
 also includes Toeplitz operators for which the function ψ appearing in the above
 theorem is allowed to satisfy |ψ′(x)| ≲ |x|^κ as x → ∞."
```

and the survey's own gloss of the hypotheses and the epsilon:

```text
"It shows that under some rather mild regularity assumptions on γ the shortness
 condition above is enough (up to an arbitrary small ǫ gap) to determine whether
 a function γ : R → R can be represented in the form γ = −φ − h̃, where φ is
 argument of some meromorphic inner function, h ∈ L^1(dΠ), and morover
 e^h ∈ L^1(R)."
```

and the two problems into which the proof decomposes:

```text
"To prove this one needs to address the following two problems: (1) replace the
 decreasing function d with a stronger requirement that d = −φ, where φ is an
 argument of some meromorphic function, (2) in addition to condition h ∈ L^1(dΠ)
 we would also need the condition e^h ∈ L^2(R).  The second problem is much
 harder and its solution lies much deeper."
```

and the "crucial part":

```text
"The crucial part of this problem can be formulated in the following way: Given
 a non-negative real-analytic function h ∈ L^1(dΠ), with h̃′ ≲ 1, and ǫ > 0,
 find a function m : R → R such that h ≤ m and ǫx − m̃(x) is essentially an
 increasing function."
```

Note the survey's description of the conclusion says *"φ is argument of some
**meromorphic** inner function"*, while the MP 2010 extract's analogous clause
says *"some inner function"*. **Q1** is exactly this, and it is not cosmetic: a
meromorphic inner function's argument is built from a Blaschke (density-side,
budget `< 1)` term plus a linear term; a general inner function may use a
singular measure (budget `< 2)`. Section 4's budget table shows our phase needs
the measure side.

**A7 — classical BM multiplier.** Survey: *"…which corresponds to case when the
characteristic function Ψ for the operator satisfies the condition |Ψ′(x)| ≲
1"* — the subtype of A6 that our log-growth phase exceeds (in the harmless
direction: it needs the κ-general form, which the survey says exists).

**A8 — the crux sub-problem.** Quote above. Our phase's conjugate is
log-scale in `x` (rig section 1), so `h̃′ ≲ 1` fails *as posed*; whether a
further reduction (choose `Θ` first, then `h` small) makes it hold is Q3.

**A9 — §6 approximation by inner functions.** Extract, §6 opening and the
Krein-shift sentence (formula-damaged):

```text
"6. Non-triviality of Toeplitz kernels in Hardy spaces
 In this final section we finish the proof of Theorems A and B.
 Approximation by inner functions.  It is well known that given any two in[...]
 ... there exists a meromorphic inner function [Θ] such that [...] (6.1)
 ... and we can define [Θ] in C_+ by the (Krein's shift) formula
 log [...] (6.2) [...] is the Schwarz integral (1.5), so [...] is the Poisson
 extension of [...]  ... for any increasing, continuous function [φ : R -> R],
 there exists a meromorphic [inner function Θ] such that [...]
 We will need the following version of this statement.
 Lemma.  If [hypothesis on φ, formula] , then there is a meromorphic inner
 function [Θ] such that [...]"
```

Buys: the `Θ`-side of the criterion is *chosen*, not found — the criterion is a
phase-budget statement. Does not buy: our `ψ` is odd (not increasing), so the
lemma applies to the reflected/order-corrected data only; and the lemma's exact
hypothesis on φ is not recoverable from prose (R1).

**B1 — BM density criterion (Prop 8.6), with the model-space dictionary.**
Verbatim:

```text
"Proposition 8.6. Let Λ = {λn} ⊂ R be a discrete sequence of real numbers. Let
 Θ = e^{iθ} be some meromorphic inner function whose increasing argument θ
 satisfies θ(λn) = 2nπ for all n.  (i) If |θ′(x)| ≃ |x|^κ, then
 sup{a ≥ 0 : Ker T_{Θ̄ S_a} ≠ {0}} is equal to D⁻_BM(Λ), the interior
 Beurling-Malliavin density of Λ.  (ii) For general θ we have
 inf{a ≥ 0 : Ker T_{S̄_a Θ} ≠ {0}} is equal to D⁺_BM(Λ), the exterior
 Beurling-Malliavin density of Λ.  ... the radius of completeness for the
 sequence of complex exponentials {e^{iλ_n x}} ... is equal to D⁺_BM(Λ)."

"We have already mentioned in the introduction that the completeness of a
 sequence of reproducing kernels {k_{Iλ}}_{λ∈Λ} in a model space K_I can be
 characterized by the injectivity condition of T_{Ī B_Λ}."
```

Fit: the dictionary needs the symbol to be `(meromorphic inner)·e^{iaz}` up to
a unimodular constant; ours is `e^{4πi(log λ)ξ} m(−ξ)` with `m` *not* inner
(law F40). Buys: the *language* (densities, radius of completeness) and the
confirmation that our object is the right kind of object; does not buy a
criterion for it.

**B2 — Krasichkov–Tumarkin.** Committed in 1628 (N6), verbatim from that
record: *"The classical criterion for the existence of a nonzero entire
function of exponential type τ with |f(x)| ≤ M(x) on ℝ is
∫ (log M(x) − τ|x|)/(1 + x²) dx > −∞."* Fit: applied to our obligation with the
real-axis ceiling `ρ(x) ~ e^{−π²|x|/2}` (1627 section 2, corrected in 1628
section 5) it gives `−∞` for every finite τ, so no finite-type witness exists —
independently of the second half-plane condition. Verdict: **applies, but only
to the finite-type question**, i.e. to the sub-problem 1627 already closed; it
is silent on infinite type, which is where the base lives. Buys: a second,
criterion-based proof of the finite-type obstruction (and a caution: the
infinite-type question has no analogue with a finite `M`). Source pin and exact
hypotheses (measurability, regularisation of the integral) are R5.

**C1 — model spaces and maximal vectors.** Verbatim abstract
(arXiv:1711.04511, Câmara–Partington, *Toeplitz kernels and model spaces*):
*"We review some classical and more recent results concerning kernels of
Toeplitz operators and their relations with model spaces, which are themselves
Toeplitz kernels of a special kind. We highlight the fundamental role played by
the existence of maximal vectors for every nontrivial Toeplitz kernel."*
Buys: a normalization — if `BASE ≠ {0}`, the witness may be taken maximal
(isometric multiplier structure). Symbol-agnostic, hence applies.

**C2 — Smirnov identity.** `N⁺ ∩ L² = H²` (1630 section 5): the reason the
carrier problem is a Hardy-space problem at all.

**C3 — de Branges space existence.** Committed 1626/1590: the base is the
pattern `∃W entire ≠ 0, W/A ∈ H²(ℂ₊), W/B ∈ H²(ℂ₋)`, with `A` not
Hermite–Biehler, so the classical de Branges apparatus (structure functions,
canonical systems) does not engage. Buys: a standard container, no criterion.

**C4 — CCM prolate.** Committed 1623: the prolate route is the T4 lane
(Connes–Moscovici, *The UV prolate spectrum matches the zeros of zeta*), and
"prolate" in this repository's tree is a *different* object (strict-angle
band-crossing factors). Buys: nothing for the base; it is the other wall.

## 7. Erratum C: the two-tap form

1630 section 8 printed:

```text
BASE  <=>  there are h in L^2((-inf,0]), g in L^2([0,inf)), not both zero, with
           w(.- a_tilde/(2 pi)) * h  =  w * g,          a_tilde = 4 pi log(1/lambda) >= 0.
```

The correct pullback of `e^{2πicξ}A(−ξ)H(ξ) = B(−ξ)G(ξ)` (`c = 2 log λ`,
`A = 2F(w)`, `B = A(−·)`) to the `u`-line is:

```text
BASE  <=>  there are h in L^2((-inf,0]), g in L^2([0,inf)), not both zero, with
           w(-.) * h(. + c)  =  w * g,          c = 2 log lambda <= 0.
```

**Mechanism of the slip.** In the time domain, `e^{2πicξ}` acts on the *signal*
(`F^{-1}(e^{2πicξ}V) = F^{-1}(V)(· + c)`), never on the tap; and after clearing
denominators the coefficient of `H` is `A(−ξ)`, whose inverse transform is the
*flipped* tap `w(−·)` (while the coefficient of `G` is `B(−ξ)`, whose inverse
transform is the unflipped `w`). The printed form moves the shift onto the tap
and uses `A(ξ)` where `A(−ξ)` belongs — i.e. it solves the base for the symbol
`m ≡ 1` (an even tap) instead of `m = A/B`.

**Three checks** (`scripts/phase_budget_1631.py` section 3, exact algebra):

```text
model                     true threshold        corrected form      printed 1630 form
m = 1            (mu = 0) c < 0                 c < 0  [ok]         c < 0  [ok, delta even]
lambda = 1       (c = 0)  m(-xi) h^ = g^        same equation       h^ = g^  -> h = g = 0
                          (committed base)                            [WRONG: forces empty]
mu = 1, c = 0.5           true (0.5 < 1)        c < mu  [ok]        lambda < 1  [WRONG]
mu = 1, c = -1            true (-1 < 1)         c < mu  [ok]        lambda < 1  [wrong reason]
```

Check 2 is analytic: at `λ = 1` the printed form gives `ĥ = ĝ` (since `F(w)`
has no zeros — `A` is zero-free), hence `h = g` with opposite half-line
supports, hence `h = 0`: the printed form asserts an EMPTY base at `λ = 1` for
*every* symbol, which contradicts nothing in 1630 only because 1630's model
check used `m ≡ 1`. Check 3 is the discriminating one: for the shifted-tap
model `m(ξ) = e^{2πiμξ}` the true threshold is `μ > c` (equivalently
`λ < e^{μ/2}`), the corrected form reproduces it exactly
(`h(s + c − μ/2) = g(s + μ/2)`, supports `(−∞, μ/2 − c]` and `[−μ/2, ∞)`), and
the printed form's threshold is `μ`-independent (`λ < 1`), hence wrong for
`μ ≠ 0`. 1630 section 8's model check passed for both forms because `δ` is even.

What survives from 1630 section 8 unchanged: the tap identity
`∫_ℝ w = Γ_ℝ(1/2)/2`, the clearing of denominators `B(−ξ) = A(ξ)`, the
Schwartz class of both sides, and the B3 verdict.

## 8. Checklists

**Five quantitative questions (the replacement for "wall 1").**

```text
Q1  inner or meromorphic?  is the (1.6) clause's Theta an arbitrary inner
    function (measure budget < 2, our phase inside) or meromorphic (density
    budget < 1, our phase outside)?  Extract says "inner function"; the survey's
    prose says "meromorphic inner function".  PIN AT [23] sections 2-3.
Q2  e^h in L^1(R) or L^2(R)?  the survey states both in different sentences
    (section 5); the extract prints L^2.  PIN AT [23] and at MP 2010 (1.7)'s
    "little o subspace" refinement.
Q3  the joint constraint:  for h in L^1(dPi), what is the sharp ceiling of h~,
    and does the pair (Theta, h) have a density/atoms condition beyond the two
    separate budgets?  Source: [23] section 2 (Hilbert-transform lemmas),
    MP 2010 section 2 (Lemmas 1-5, one-sided Lipschitz estimates).
Q4  transfer to d = 0:  does the section 4.1 machine (statement: yes; proof:
    intervals away from the origin) produce the Theta of the p = 2 criterion on
    a d = 0 interval?  1630 section 4 caveat 1.
Q5  the epsilon gap:  is "short => representable" available WITHOUT the eps
    shift at our symbol, and does MP 2010 section 5.1's hypothesis list admit
    |gamma'| ~ log|x| (the survey's own gloss says the general form allows
    polynomial growth of |Psi'|)?  Opens from flag (F).
```

**Five retrieval targets.**

```text
R1  MP 2010 sections 1-2 and 4.1-6 from a FORMULA-BEARING copy (the polished
    DVI prose extract drops every displayed formula; (1.5)-(1.7), (6.1)-(6.2)
    and the section 6 lemma's hypothesis are all damaged).
R2  MP 2010 section 5.1's exact hypothesis list (settles flag F and Q5).
R3  [23] = MP 2005 sections 2 and 3.1 (the quantitative Hilbert-transform
    layer and the general radius-of-completeness statement).
R4  the survey's Theorem 8.5 hypothesis sentence (the text immediately before
    item (i), which the retrieval chunking has not yet returned).
R5  the source pin and exact hypotheses of the Krasichkov-Tumarkin criterion
    (row B2 has the statement from committed 1628 but not its source), and the
    de Branges (1968) / Baranov (2011) circle on derivatives of meromorphic
    inner functions (pointer: arXiv:1309.6728, Rishika Rupam, "Uniform
    boundedness of derivatives of meromorphic inner functions on the real
    line") as a possible sharpening of Q1.
```

**One flag on 1630 section 4 (not an erratum).** The line *"power-law
hypotheses of B/C and section 5.1 (='~') FAIL"* is not re-verified this round.
The retrieved survey says the power-law slot belongs to the *multiplier* `ψ`
(the theorem's own free choice, `|ψ′| ≲ |x|^κ`), and our phase's derivative
grows only like `log|x|` — i.e. inside every κ > 0 class. Until R2 is closed,
the base must not cite that line.

## 9. Laws

```text
F45  AN INVENTORY ROW IS ITS HYPOTHESES.  A tool may be listed only with
     (statement verbatim, source URL, hypothesis list, single failing
     hypothesis when out of class).  A criterion priced from its name or its
     conclusion is not priced.  Corollary: a row without a retrieved statement
     is a POINTER, and pointers carry no verdict (row B2).

F46  CLASS, EXPONENT AND eps-GAP ARE PART OF A STATEMENT.  "Short" drives
     nontriviality in N_p (p < 1/2), representability up to eps x in N^+, and
     triviality of the PERTURBED symbol in H^2.  Quoting the word across
     classes is the same error as quoting a theorem without its exponent
     (sharpens F41/F42 into the direction table of section 5).

F47  A RE-TYPING MUST BE TESTED AT THE DEGENERATE PARAMETER AND ON AN
     ASYMMETRIC MODEL.  1630's two-tap form passed its m = 1 model check only
     because the delta tap is even; the lambda = 1 degeneracy and a shifted-tap
     model (mu != 0) separate the correct pullback from the wrong one.  A
     symmetric test cannot discriminate a symmetric error.
```

## 10. Housekeeping

* `scripts/dvi_extract.py` — minimal DVI prose extractor (opcode walk, text
  fonts only, version-1 and version-2 opcode tables, page-synchronised
  parsing).  Used to read the 2005 source; committed so the retrieval is
  repeatable.
* `scripts/phase_budget_1631.py` — the three self-contained checks of section 4
  and 7 (30 digits; no external data).
* Source pins this round: `[23]` = Makarov–Poltoratski 2005,
  `https://people.math.wisc.edu/~poltoratski/MIF.dvi`; MP 2010 (the (1.6) and
  section 6 quotes), `https://people.math.wisc.edu/~poltoratski/MIF2.dvi`;
  survey `https://arxiv.org/abs/1511.08326` (Hartmann–Mitkovski, *Kernels of
  Toeplitz operators*); `https://arxiv.org/abs/1711.04511`
  (Câmara–Partington); `https://arxiv.org/abs/1309.6728` (Rupam); the
  publication page itself, `https://people.math.wisc.edu/~poltoratski/publications.htm`,
  is what ties each file name to its paper.

## 11. Boundaries

1. No Lean brick this round; nothing here changes a committed declaration.
2. The inventory is a *reading* of sources, not a proof: every row's verdict is
   stated against the committed symbol `m` and against the sources as retrieved
   (DVI prose for MP 2010; HTML/PDF prose for the survey).  Formula-level
   statements carry the damage marks and the retrieval targets.
3. The two budget thresholds (density `< 1`, measure `< 2`) are elementary and
   are checked numerically; the *joint* constraint (Q3) is not proved here and
   is not claimed.
4. Erratum C corrects a committed formula (1630 section 8).  It changes no
   verdict of 1630: the B3 strike, the class audit, the BM interval, and the
   B4/Toeplitz numerics are independent of the two-tap bookkeeping.
5. RH is not claimed; the carrier base remains OPEN, with three applying tools
   (A3, A4, C1), one target criterion (A1) and five named questions.