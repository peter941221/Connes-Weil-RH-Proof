# 011 — the Arakelov bridge program: audited category-change experiment

Binding preregistration, opened 2026-09-14 by owner decision. This document
supersedes, **for this face only**, the freeze posture recommended by records
1411 and 1415. Nothing else is superseded: the Lean mainline, the tower, the
B0b equivalence and the psi-bundle keep their committed status and their
acceptance discipline.

**AUDIT OUTCOME — same day, read this before spending.** Record
[`1418`](../proofs/1418_arakelov_path_reachability_audit.md) was commissioned
to answer one question: does this program reach RH? The answer is **no**, on
two independent grounds. (R1) The bridge *re-encodes* the gate instead of
reducing it: given `phi` the last three steps are free, so all of RH's
difficulty sits inside "does `phi` exist", and identity (i) is exactly the
EXTERNAL-dictionary kind of claim 1415 §3 already ruled can never be a machine
fact. (R2) A4's Lean leg is not statable in the pinned library: a grep of
Mathlib v4.30 returns **zero** occurrences of Arakelov, adelic, arithmetic
Chow, Hodge index, arithmetic surface, `WeilDivisor` or any intersection
pairing. The milestones below are kept, not deleted; the **spend order is
reversed** and section 7 restates the shape.

Companion records: the mathematical derivation and the reason this category
was selected is proof record
[`1417`](../proofs/1417_phase_density_filter_and_arakelov_bridge_selection.md);
the obstacle ledger this program is answering is
[`004`](004_endpoint_literature_interface_audit.md) section 8; the process this
program runs inside is [`006`](006_new_math_creation_workflow.md); the
generation machinery it replaces for this face is
[`010`](010_bone_foundry.md).

## 0. The decision, stated plainly

```text
   Inside the current category (CompactLogTest, Mellin nodes, windows):
     L1 Gamma-only symbol          -- density level
     L2 support => exponential type -- density level
     L3 {log p} independence + PNT  -- density level
     GOAL  0 <= qw(g)               -- phase level, ~ e^{R/2} oscillating terms
     ==> no theorem with L1+L2+L3 hypotheses can conclude it (1417 s3)

   Therefore: stop generating bones inside the category. Change the category.
```

The chosen category is **Arakelov / adelic line-bundle intersection theory**.
It is chosen for exactly one reason, and the reason is a citation, not a hope:

```text
  arXiv:1304.3538, X. Yuan and S.-W. Zhang, "The arithmetic Hodge index
  theorem for adelic line bundles I" (45pp, MSC 14G40), abstract:

    "We prove an arithmetic Hodge index theorem for adelic line bundles on
     projective varieties over number fields. It extends the arithmetic
     Hodge index theorem of Faltings, Hriljac and Moriwaki on arithmetic
     varieties."
```

The target-side theorem is **proved**. That distinguishes this program from
every previous attempt on this face, all of which searched for a positivity
*statement* and found only restatements of the wall
(`004:476-478`). Here the positivity statement is about line bundles on a
fixed variety, and it does not mention zeta zeros at all.

What adelic geometry supplies that `Spec Z` seems not to: an adelic line bundle
carries norms at **every** place, so the metric component of the arithmetic
Chow group is infinite-dimensional even where Neron-Severi is finite rank.
**That metric direction is the substitute for the second factor
`Spec Z x Spec Z = Spec Z` lacks.** This is the whole wager.

## 1. The obligation, in one box

Find a linear map `phi` from the test space to adelic line-bundle classes with

```text
  (i)    widehat{deg}( phi(g)^2 )  =  -c * qw(g)         for a fixed c > 0
  (ii)   widehat{deg}( phi(g) )    =  0                  for EVERY g
```

```text
   (ii) puts phi(g) in the degree-zero / "vertical" hyperplane
                    |
                    v
   Yuan-Zhang Hodge index: intersection form negative definite there
                    |
                    v
   (i) converts  -<phi(g),phi(g)> >= 0   into   qw(g) >= 0
                    |
                    v
   1416 weilGate_unconditional_iff_sourceRH   ==>   SourceRH
```

Note what 1416 did to this program's difficulty. Because the committed gate is
side-condition-free, **(ii) cannot be satisfied by shrinking the test class**;
`phi` must be renormalized so that its ample-direction vanishes identically.
1416 turned "find a bridge" into "find a map whose arithmetic degree is
identically zero", which is a checkable identity rather than a hope.

## 2. Milestones, with prices fixed in advance

Per law F15 every price is set from the milestone's exit hypothesis, not from a
file count. Law F17/F19: statements are transcribed from sources, never
reconstructed from memory.

```text
+-----+-------------------------------------+------------+------------------+
| id  | milestone                           | cost       | exit / kill      |
+-----+-------------------------------------+------------+------------------+
| A0  | Transcribe verbatim the precise YZ  | 1-2 days   | either the       |
|     | Hodge index statement: the vector   | paper only | statement needs  |
|     | space, the numerical-equivalence    |            | a hypothesis we  |
|     | relation, the signature, and the    |            | cannot discharge |
|     | exact hypotheses on the class being |            | (typed kill), or |
|     | tested. Source: arXiv:1304.3538 and |            | it does not      |
|     | the vertical-class form in          |            | (-> A1)          |
|     | arXiv:2503.14099.                   |            |                  |
+-----+-------------------------------------+------------+------------------+
| A1  | Pin C' in Phi(r) = -Re psi(1/4+ir/2)| 1 day      | C' fixed and     |
|     | + C2pi under the repository's OWN   | symbolic,  | r_0 located; or  |
|     | Fourier convention, and re-derive   | zero Lean  | the derivation   |
|     | (D1)/(D2) from the committed        |            | fails at a named |
|     | definitions.                        |            | step (-> fix)    |
+-----+-------------------------------------+------------+------------------+
| A2  | THE DECIDING TEST. For the most     | 1 day      | constants match: |
|     | natural candidate phi, compute the  | paper +    | escalate to A3.  |
|     | constant part of widehat{deg}(phi(g))| sympy/    | Constants do NOT |
|     | symbolically and compare against the| exact      | match: state     |
|     | committed head coefficient          | algebra    | WHICH term of    |
|     |   log(4*pi) + gamma = 3.1083...     |            | the arithmetic   |
|     |                                     |            | degree cannot    |
|     |                                     |            | match, and close |
|     |                                     |            | the transport    |
+-----+-------------------------------------+------------+------------------+
| A3  | Identify an X and a phi satisfying  | 1-4 weeks  | bridge exists on |
|     | (i) at the level of FORMULAS: match | paper      | a testable class |
|     | the prime measure sum_{p,m}         |            | -> first Lean    |
|     | (log p) p^{-m/2} delta_{m log p}    |            | contact; or the  |
|     | against an arithmetic degree /      |            | match is         |
|     | Fourier coefficient of an           |            | structurally     |
|     | Eisenstein series (Kudla shape).    |            | impossible (kill)|
+-----+-------------------------------------+------------+------------------+
| A4  | Extend (i) to an IDENTITY including | open-ended | RH, via the      |
|     | (ii) on the whole test space, and   | research   | committed 1416   |
|     | discharge the citation leg O4 with  | program    | equivalence      |
|     | a Lean formalization of the         |            |                  |
|     | translation.                        |            |                  |
+-----+-------------------------------------+------------+------------------+
```

**A0 before A2, always.** Stating a theorem's hypotheses from memory is the
failure mode records 1407/1408 were created to punish.

**A2 is the gate on all further BRIDGE spend.** It is one symbol. Nothing beyond
A2 is authorized until it reports.

**The A table is ordered by headline, not by spend. Corrected spend order
(1418 §6): `W0` -> `A2` -> `W1` -> `A3`.** `W0` runs first because it is
derivable from definitions already committed in this repository, needs no
external paper, and is a precondition of Track A's own arithmetic: `A1` and
`W0` are the *same* symbolic computation (pin `C'` under the repository's
Fourier convention), so running them as two milestones double-books a one-day
job. Merge them: the single task is "pin `Phi` exactly, from committed
definitions", filed under `W0`, satisfying `A1`.

**A4's Lean leg is blocked as written (1418 §3).** "Discharge the citation leg
O4 with a Lean formalization of the translation" presupposes that the pinned
library can state an arithmetic Hodge index theorem. It cannot - the five-level
prerequisite chain (intersection pairing -> Chow groups -> arithmetic surfaces
-> arithmetic degree/nef -> adelic line bundles) is absent at every level. Any
future authorization of A3/A4 must either budget that formalization separately
or declare the program paper-first and say so in the same breath.

### Track W: the window theorem (added 2026-09-14, from 1417 section 3b)

Reading the committed brick pinned the obligation's direction, and it exposed a
second, unrelated-to-the-bridge target that is plausibly closable. On the
committed root-support class the prime sum vanishes identically
(`finitePrimeSum_eq_zero_of_support_subset_open_log_two`, used at
`C1MinimalWeilCriterion.lean:255`), so there is no oscillating prime sum to
control and the whole gate reduces to

```text
  (OB)   archimedeanTerm (g * g~) <= 0
    ?==  sup { <g0, T_K_eff g0> : g0 in PW_R, ||g0||_2 = 1 } <= 0      R = log2/2
     K_eff = (1/2) e^{|y|/2}/sinh|y|  (renormalized)  +  (log(4pi)+gamma) delta_0
```

one explicit truncated convolution **form**, over an explicit Paley-Wiener class.

**The `?==` is deliberate; 1418 section 5 explains it.** This box first read
`<=> lambda_max( T_K_eff restricted to L2(-log2/2, log2/2) ) <= 0` and the line
below it said "one number". Both were wrong, in the same direction.
`Phi(r) = -Re psi(1/4 + i r/2) + C' ~ -log|r/2| + C' -> -infinity`, so
`T_K_eff` is an **unbounded** multiplier: `lambda_max` on a window is not a
well-formed quantity until a form domain is named; and because the kernel is
not in `L1` (the `1/|y|` singularity at the origin), `T` is not Hilbert-Schmidt,
so whether the supremum is attained is itself a question. Independently, `C'` is
unpinned and it shifts the whole form by `C' * ||g||_2^2`, i.e. by `C'` on the
unit sphere - so the head term `3.1083...` does not yet have a numeric rival.
The eigenvalue phrasing also quietly invites a finite discretization, and a
mesh's top eigenvalue is a proxy with no a priori relation to the supremum;
this kernel family has already produced a negative direction of exactly this
shape (263 section 8, `det = -0.707084047558...`).

So W0's job is threefold, not one: **pin `C'`, name the form domain, and
rewrite `(OB)` as the supremum above.** Until W0 reports, the operator form of
`(OB)` carries no numeric content at all.

```text
+-----+-------------------------------------+------------+------------------+
| W0  | FIRST SPEND OF THE PROGRAM. Pin C', | 1 day      | C' pinned, form  |
|     | name the form domain, and rewrite   | paper +    | domain named and |
|     | (OB) as a supremum of a quadratic   | sympy,     | sup decided, or  |
|     | form over PW_R, from the committed  | zero Lean  | a mismatch named |
|     | definitions. This satisfies A1 as   |            | (then A2)        |
|     | the same computation. Do NOT trust  |            |                  |
|     | 1417 s2 or s3b's operator wording.  |            |                  |
+-----+-------------------------------------+------------+------------------+
| W1  | Prove or refute: the sup of the     | 1-3 weeks  | PROVED: first    |
|     | archimedean form over PW_R with     |            | unconditional    |
|     | ||g0||_2 = 1 is <= 0. NOT an eigen- |            | archimedean sign |
|     | value - 1418 s5. A test g with      |            | theorem          |
|     | A > 0 falsifies (OB) ONLY, not RH:  |            | REFUTED: (OB)    |
|     |                                     |            | closed, 125's    |
|     | it leaves the all-supports scope    |            | demand stays open|
|     | untouched.                          |            |                  |
+-----+-------------------------------------+------------+------------------+
```

**W0 LANDED 2026-09-17 — [1578](../proofs/1578_w0_archimedean_symbol_pinned_and_window_class_correction.md),
and it found a third defect in the 1417 §3b box.**

```text
  C' = log pi = 1.1447298858494001741...          (five-step hand derivation,
                                                   no quadrature, from
                                                   SelectedWeilFormula:96-109 +
                                                   C1SameOwnerWeil:61-64 +
                                                   psi(1/2) = -gamma - 2 log 2)
  symbol   Phi(r) = log pi - Re psi(1/4 + i r/2)
  max      Phi(0) = log pi + gamma + pi/2 + 3 log 2 = 5.37218341922566558
  first 0  r_0 = 6.28983598883690278  (1417 s2's deferred constant, now named;
                                       within 0.1% of 2 pi)
  head     log(4pi)+gamma = 3.108239911870824  -> CANCELLS against the -gamma
                                                 inside psi(1/2); it never
                                                 reaches the final symbol, so
                                                 the "one number plus one
                                                 unknown constant" worry of
                                                 1418 s5 (defect 5b) is closed
                                                 in favour of ONE number
  domain   D = {g in L2 : supp g ⊆ [-R,R], int |g-hat|^2 log(1+|xi|) < ∞}

  THIRD DEFECT IN 1417 s3b (in addition to lambda_max and unpinned C'):
  the box maximizes over PW_R, but the committed theorems that own the window
  (C1MinimalWeilCriterion.lean:263-271) carry TWO hypotheses - support AND
  `CC20VanishesOn ... {half}`, which unfolds through CC20TestSpace:28-34 +
  CC20RHExit:28 + C1HealthyTestSpace:44-47 + CC20YoshidaConvolution:35-56 to

       laplaceAt g (1/2) = 0   <=>   int g(x) e^{x/2} dx = 0
                                <=>   g-hat(i/4pi) = 0.

  So (OB) is a supremum over a codimension-one COMPLEX subspace of PW_R, and
  the constraint sits exactly on the unique maximum of Phi. 1417 s3b's
  "uncertainty principle as positivity source" therefore has a much sharper
  mechanism than the support-width argument it was given: the admissible g must
  change sign (e^{x/2} varies only over [2^{-1/4}, 2^{1/4}] on the window).
```

**Correction to the W1 row's falsifier claim.** The row says "A test g with
`A > 0` falsifies (OB) ONLY, not RH". As written that is unsound in BOTH
directions, and the direction matters: a `g` that lies in the committed window
class (support AND vanishing) with `A(g) > 0` gives `qw g = -A < 0` by
`qw_eq_neg_archimedeanTerm_of_vanishesOn_halfOnly_of_rootSupport_logTwoHalf`
(the prime sum vanishes there), and the gate `(∀ g, 0 ≤ qw g) ⟺ SourceRH` is
machine-checked side-condition-free (1416/B0b) - so a VALID falsifier refutes
RH, not merely `(OB)`. Conversely a `g` outside the class refutes nothing at
all, including `(OB)`. There is no middle tier: **on this face the only
interesting falsifier is an RH disproof, which is why any positive extremum is
first evidence of a scoping error in the computation (law F28).** A
Galerkin pass over unconstrained `PW_R` returning a positive maximum is in that
second, worthless tier - see 1578 §2 and §6.

W1 is the deliverable with the best ratio on the board: it is a **consequence
of RH that can be proved without RH**, it lives entirely in the repository's
committed vocabulary (`archimedeanTerm`, `convolutionSquare`,
`supportRadius`), it names its consumer, and its falsifier is a single
eigenvalue. It does not need the bridge and is not gated by A2.

It must not be oversold: a proof of `(OB)` settles the gate on ONE window and
leaves O2's radius gap exactly where it was. Its value is that it would be the
first unconditional archimedean sign theorem this face produces, and the
technique (Slepian/Selberg extremal for a `1/sinh` kernel) is precisely the
"strictly lower property" that record 125 demanded for reopening the Suzuki
injectivity route.

## 3. Cost and honest priors

```text
+------+----------------------------------+----------+----------------------+
| mile | successful outcome               | P(succeed| value if it fails    |
|      |                                  | s at     |                      |
|      |                                  | A0-A2)   |                      |
+------+----------------------------------+----------+----------------------+
| A0   | the needed hypothesis is         | ~0.7     | tells us the         |
|      | dischargeable                    |          | category is wrong in |
|      |                                  |          | a named way          |
+------+----------------------------------+----------+----------------------+
| A1   | Phi and r_0 pinned; a new named  | ~0.95    | nearly certain;      |
|      | archimedean constant             |          | low ambition         |
+------+----------------------------------+----------+----------------------+
| A2   | the bridge survives a one-symbol | ~0.15    | a TYPED impossibility|
|      | coincidence test                 |          | of the Arakelov      |
|      |                                  |          | transport - closes a |
|      |                                  |          | class for everyone   |
+------+----------------------------------+----------+----------------------+
| A3+  | construction                     | < 0.05   | this is where RH     |
|      |                                  |          | would live           |
+------+----------------------------------+----------+----------------------+
```

The program is worth running because the A>=2 row's failure branch is a real
result. A2 is designed so that **both** outcomes are deliverables, which is the
foundry rule (`010` section 1: "a dead attack is a result only if it is typed")
applied at program scale.

## 4. Standing constraints carried into this program

* Law 65: every number is MODEL evidence until Lean certifies it. The
  `3.1083...`, `4.2274...`, `2 e^{u/2}` figures in 1417 are unchecked.
* Law F18: quote premises verbatim, including our own. `qw = -archimedean -
  finitePrime` must be quoted from `C1MinimalWeilCriterion` Part 4, and the
  **1214/1216 sign-convention audit must be re-read before any inequality
  direction is used anywhere in this program.** This is a blocking item, not a
  caveat.
* Law F15: prices in section 2 are final; re-pricing requires an entry here.
* The freeze posture (1411/1415) is lifted **only** for this face. No
  numerical campaign is authorized anywhere: 1228's finding that the next
  action is equation-led generation rather than a numerical prototype still
  stands, and this program is equation-led.
* No Lean spend before A3. If A3 produces a bridge, the first Lean contact is
  a `GENERATION-CARD` under `006` and a preregistered brick, not a spike.
* This document is repo-owned and must be readable by a new contributor
  without any private context: no local paths, no tool-directory state, no
  working-note files. Every claim in it is either a quoted committed source
  location, a quoted external reference with an identifier, or a
  self-contained paper derivation labeled as such.

## 5. Reference set (0 repo hits before 2026-09-14)

```text
+-------------------+--------------------------------------------------+
| arXiv:1304.3538   | Yuan-Zhang, arithmetic Hodge index for adelic    |
|                   | line bundles I  (THE target-side theorem)        |
| arXiv:1304.3539   | Yuan-Zhang, II (applications: non-arch Calabi-   |
|                   | Yau uniqueness, preperiodic-point rigidity)      |
| arXiv:2503.14099  | local arithmetic Hodge index; the "L nef, M      |
|                   | vertical" hypothesis form                        |
| arXiv:2105.13587  | adelic line bundles on quasi-projective          |
|                   | varieties; finitely generated field case         |
| arXiv:2606.27116  | Jun 2026 expository account: adelic line bundles,|
|                   | arithmetic positivity, Diophantine geometry      |
|                   | (entry point for A0)                             |
| arXiv:2409.00611  | abstract divisorial spaces; Yuan-Zhang           |
|                   | intersection numbers in a wider setting          |
| arXiv:1810.06342  | arithmetic Hodge index + rigidity in dynamics;   |
|                   | Faltings-Hriljac via the Neron pairing           |
| arXiv:2110.07457  | expository survey, arithmetic Siegel-Weil /      |
|                   | Kudla program  (entry point for A3)              |
| arXiv:2607.06285  | Jul 2026, the Siegel-Weil formula in geometry    |
|                   | and arithmetic  (live A3 frontier)               |
| arXiv:2508.15971  | Morishita, Deninger foliated systems <->         |
|                   | Connes-Consani adelic spaces (v5 2026-01,        |
|                   | Muenster J. Math.) - background, not load-bearing|
| arXiv:2606.09096  | Suzuki, Weil quadratic form via the screw        |
|                   | function  - Form C, screened at 125; the         |
|                   | "strictly lower property" demand it states is    |
|                   | what this program is an answer to                |
+-------------------+--------------------------------------------------+
```

## 6. What this program does not claim

It does not claim RH is approachable. It does not claim the bridge exists; the
prior on surviving A2 is set at roughly one in seven. It does not claim the
Yuan-Zhang theorem has anything to do with zeta - that connection is precisely
the open question milestone A3 asks. It registers no numerical result, proves
no sign, and changes no committed Lean state.

What it does claim is narrower and is the point: **this is a paper-only
category-change experiment whose target-side theorem is already proved rather
than sought.** It is not an RH route unless a future construction supplies a
genuinely independent bridge map; the present program does not.

RH is not claimed, and this document does not register Track A as a reachable
RH proof route.

## 7. Reachability verdict (added the same day, from 1418)

The owner's question was whether the program reaches RH. It does not, and the
two reasons are of different kinds, which matters because they fail
differently.

```text
+-----------+--------------------------------------+------------------------------+
| reason    | statement                            | dissolvable by work?         |
+-----------+--------------------------------------+------------------------------+
| R1        |                                      |                              |
| structural| Condition (i) is an identity whose   | only by building phi itself, |
|           | verification implies the sign, so    | which IS the proof of RH in  |
|           | "does phi exist" carries RH's WHOLE  | another vocabulary: the far- |
|           | difficulty, not a share of it. 011   | side theorem then contributes|
|           | moved the wall; it did not shrink it.| nothing the identity did not |
|           | In Weil's function-field case the    | already assume.              |
|           | bridge exists for reasons independent|                              |
|           | of RH; here it would have to be built|                              |
|           | to order.                            |                              |
+-----------+--------------------------------------+------------------------------+
| R2        |                                      |                              |
| mechanical| A4's exit is a Lean citation, and the| no, not by this project; yes,|
|           | pinned library cannot STATE an adelic| eventually, by someone       |
|           | line bundle: zero occurrences of     | formalizing arithmetic       |
|           | Arakelov, adelic, Chow, Hodge index, | intersection theory first - a|
|           | arithmetic surface, WeilDivisor or   | program unrelated to RH.     |
|           | any intersection pairing.            |                              |
+-----------+--------------------------------------+------------------------------+
```

The consequence for how this program is run: **Track A is a paper route, and
this repository registers nothing that is not certified in Lean.** That is not
a reason to abandon A2 - A2 is one symbol, it is cheap, and its negative branch
is a typed impossibility that would close a class for everyone. It is a reason
to stop describing Track A as an attack on RH.

The realistic deliverables of the program as amended are, in order:

1. ~~`W0`~~ **LANDED (1578)** - `Phi` pinned with `C' = log pi`, form domain
   named, and the class corrected to include the committed
   `g-hat(i/4pi) = 0` constraint. New constants this face now owns: `log pi`
   and `r_0 = 6.28983598883690278`.
2. `W1` - one sign decided for one window, NOW STATED CORRECTLY as a
   **constrained** Slepian/reproducing-kernel extremum over
   `PW_R ∩ {h(i/4pi) = 0}`, not an unconstrained truncated-convolution maximum.
   The technique handle changes accordingly: the constraint is quotiented out by
   the Paley-Wiener reproducing kernel at `i/4pi`, and `A` restricted to its
   orthogonal complement is the object to bound. The first unconditional
   archimedean sign theorem this face would own, and the "strictly lower
   property" record 125 demanded for reopening the Suzuki route. **Does not
   imply RH.** (Its NEGATION does - see the falsifier correction above.)
   **OPENED by 1580**: the escape-form equivalence `(OB) <=> int |g-hat|^2 H
   >= Phi(0)||g||^2` with `H = Phi(0) - Phi(2pi .)` is hand-verified; two
   naive attacks are typed-dead (multiplier-only escape fails because `Phi(0)`
   lies below the crossing of `H` itself, so a leakage floor near 100% would
   be needed and the constraint never enters; termwise positive-kernel
   splitting diverges - the counter-term is non-LOCAL, third manifestation of
   the 1578 s1 structural fact). The live handle is variation-diminishing of
   the RENORMALIZED window kernel (a different object from the 263 s8 kernel
   whose total positivity was refuted), and the row splits into sub-milestones
   `W1a` (write `K(x-y)` on the window square from the committed spatial form,
   counter-term included), `W1b` (2x2 minor sign test - falsifiable, finite
   computation), `W1c` (comparison theorem + one 1-D inequality at the first
   mode). Registered gap for any future formal pass: the Gauss value
   `psi(1/4) = -gamma - pi/2 - 3 log 2` is a CONTRACT
   (`HalfAnchorGaussContract`, `C1XiCenterTwoGamma.lean:932-934`), not a
   committed theorem.
3. `A2` - a coincidence test on one symbol, whose failure is a result.
4. Anything beyond that requires a new owner decision, informed by R1 and R2
   rather than by the headline of section 0.

RH is not claimed.
