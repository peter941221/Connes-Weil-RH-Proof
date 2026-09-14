# 1418 — reachability audit of the Arakelov bridge program: does path A actually reach RH?

Wave: owner-directed audit, 2026-09-14. The instruction was conditional and the
condition is load-bearing: *"audit this plan - can it really reach RH? If there
is no problem, write it up completely into a new map document."* This record is
the audit. **It finds problems, so the new document it produces is this audit,
not an attainability claim.** Nothing in `011` is deleted; `011` is amended to
agree with what follows.

Depends on: 1417 (the derivation), `011` (the program), 1416 (the committed
gate), 1415 §3 (the internal/external dictionary taxonomy), 263 (a negative
minor of this kernel family), 125 (the reopening demand).

Status: **no Lean built, no digits produced, no sign claimed, RH not claimed.**
One new mathematical fact is established here from committed source (section
4); the rest is a verdict plus two technical corrections.

+========================================================================+
| [1] VERDICT                                                            |
+========================================================================+

```text
+---------------------------------------------------------------------+
| NO. The program does not reach RH, for two INDEPENDENT reasons,     |
| and one of them is checkable in fifteen seconds.                    |
|                                                                     |
| R1 (mathematical)  The bridge is a RE-ENCODING of the gate, not a   |
|     reduction of it. Condition (i) is an identity between two       |
|     vocabularies whose verification IS the difficulty. 011 moved    |
|     the wall; it did not shrink it.                                 |
|                                                                     |
| R2 (mechanical)    A4's Lean leg is IMPOSSIBLE AS WRITTEN against   |
|     the pinned library. The pinned Mathlib has ZERO occurrences of  |
|     Arakelov, adelic, arithmetic Chow, Hodge index, arithmetic      |
|     surface, WeilDivisor, or any intersection pairing. The target-  |
|     side theorem cannot be stated there, let alone cited.           |
|                                                                     |
| WHAT SURVIVES        W0 and A1 are real, cheap, and inside the      |
|     repository's own vocabulary. W1 is the only plausibly closable  |
|     item on the board - and W1 DOES NOT IMPLY RH by construction.   |
|                                                                     |
| PRIORITY INVERSION   The closable items were ranked second. Fixed   |
|     in 011: W0 becomes the first spend of the program.              |
+---------------------------------------------------------------------+
```

Good news / bad news, stated where it belongs: **the audit is bad for the
claim "we will get RH by changing category" and good for the claim "we have
found, in 1417 §3b, the first self-contained decidable theorem on this face in
months".** Both are in the box above rather than only in prose, because the
second is easy to lose under the first.

+========================================================================+
| [2] R1: WHY A CATEGORY CHANGE IS NOT AUTOMATICALLY A REDUCTION         |
+========================================================================+

The structure of the program, from `011:58-76`, is:

```text
  find phi  with  (i)  widehat{deg}(phi(g)^2) = -c * qw(g)
                    (ii) widehat{deg}(phi(g))  = 0  for every g
  (ii) + Yuan-Zhang  ==>  -<phi,phi> >= 0
  (i)                 ==>  qw(g) >= 0
  1416                ==>  SourceRH
```

Read the arrows in the direction of difficulty, not of proof. The last three
lines are **free**: given `phi`, the conclusion is three applications. So the
entire difficulty of RH now sits inside one existential: *does such a `phi`
exist?* The question the audit asks is whether that existential is **easier
than RH**. Three tests.

**Test 1 - does the source category supply the bridge for reasons independent
of the goal?** This is the test the function-field case passes and the number-
field case fails. Weil's proof runs through `C x C` (1417 §4): the surface, its
divisors and the signature `(1, rho-1)` of its intersection form **exist
whether or not the zeta function of `C` satisfies RH**. Nobody constructs the
surface in order to prove RH; the surface is there, and positivity is a
consequence. Over `Spec Z` there is no such independent object -
`Spec Z x Spec Z = Spec Z` (1417 §4, quoted there). So the bridge must be
*built to order*, and the only specification it must satisfy is an identity
whose consequence is the sign we want. *Argument, not citation: this is the
structural difference between "use a geometry that exists" and "manufacture a
geometry whose existence implies the theorem".*

**Test 2 - what did 1415 call this kind of claim?** 1415 §3 already built the
taxonomy, verbatim (`1415:97-104`):

```text
  (b) EXTERNAL DICTIONARY (model, NEVER a Lean Prop): that OUR
      formal `spectralWeilValue` is the PAPER'S classical Q of
      Yoshida/Chuk §2 with the same normalization and sign. This is
      a definitions-citation claim ... No Lean statement of (b) is
      needed or possible without importing the paper as a formal
      source.
```

Condition (i) is **exactly** an item of type (b): a normalization-and-sign
identity between a formal object of this repository and a paper's object. The
project has already decided, in 1415, how to treat such items - as citation
claims, never as machine facts, never as evidence of progress. 1417/`011`
introduced a new one and, in the excitement of finding a *proved* theorem on
the far side, applied a standard the previous day's record had just forbidden.
That is the root cause of this audit's negative finding, and it is a
governance failure, not a mathematics failure.

**Test 3 - is the previous analytic route any help?** The repository's own
committed route is already an adelic construction: the `CCM25Concrete`
namespace formalizes Connes-Consani-Moscovici, "Zeta Spectral Triples",
`arXiv:2511.22755` (cited verbatim at `docs/proofs/016_corrected_trace_identity.md:76-77`),
and `qw` is the Weil form of that construction transported into a computable
analytic shape. So the "category change" walks from the analytic
shadow *back toward* the geometric source. The reason the analytic form exists
is that it is where things can be computed; the reason the geometric form is
attractive is that it is where positivity is *assumed by a theorem*. Moving
toward the source does not import the theorem's content, because the missing
piece is precisely the translation between them - which is Test 2's item (b),
which is the wall.

```text
   analytic side                    geometric side
   (computable)                     (positivity theorem exists)
        |                                 |
        |   qw(g) := explicit integral    |   <L,M> := intersection pairing
        |                                 |
        +--------- MISSING: identity (i) ---------+
                     = the wall, relocated
```

**Verdict on R1.** 1417 §3's phase/density filter does NOT kill path A - Yuan-
Zhang is genuinely not a density-level hypothesis, so the escape from the
filter is real. What kills the *attainability* claim is weaker and simpler:
path A does not decompose the problem. It exchanges a sign that must be proved
for an identity that must be constructed, and there is no reason, in the
literature or in this repository, to price the second as easier. `011 §3` set
`P(A3+) < 0.05`; the honest reading is that no number in that table is an
estimate of *this* program's chance of RH, because the program's chance of RH
is the chance that somebody manufactures `phi`, which is the chance that RH
gets proved by a new construction.

+========================================================================+
| [3] R2: THE LEAN LEG IS BLOCKED BY A LIBRARY GAP, MEASURED NOT ASSUMED |
+========================================================================+

`011:127-131` prices A4 as "extend (i) to an identity ... **and discharge the
citation leg O4 with a Lean formalization of the translation**". This project
registers nothing without Lean (law 65), so A4's Lean leg is not decoration: it
is the exit. The grep below is against the pinned library actually on disk
(`lean-toolchain`: `leanprover/lean4:v4.30.0`), case-insensitive, whole tree.

```text
+--------------------------------------------+------+------------------------+
| term searched under Mathlib/               | hits | what a hit would mean  |
+--------------------------------------------+------+------------------------+
| Arakelov                                   |    0 |                        |
| adelic                                     |    0 | cannot STATE an        |
| arithmetic Chow                            |    0 | adelic line bundle     |
| Hodge index                                |    0 | cannot STATE the       |
| arithmetic surface                         |    0 | target-side theorem    |
| WeilDivisor (as a declaration)             |    0 | no divisor group       |
| selfIntersection / intersectionPairing     |    0 | no intersection form   |
|                                            |      |                        |
| ArithmeticGeometry divisor/intersect/chow  |  0   | files: none exist      |
|   FILES (find, by name)                    |      |                        |
| InfiniteAdeleRing.lean                     |    1 | the bare topological   |
|                                            |      | adele RING: no metrics,|
|                                            |      | no bundles, no pairing |
| divisor FILES (all of Mathlib)             |   16 | ring-theoretic and     |
|                                            |      | natural-number         |
|                                            |      | divisors, plus one     |
|                                            |      | complex-analysis file  |
+--------------------------------------------+------+------------------------+
```

The consequence is a chain of prerequisites, each independent of RH and each
absent:

```text
  A4 needs:  cite Yuan-Zhang in Lean
             ^ needs the theorem stated
             ^ needs adelic line bundles + arithmetic degree + nef
             ^ needs arithmetic surfaces / Chow groups
             ^ needs an intersection pairing with signature (1, rho-1)
  all five levels: ZERO occurrences in the pinned library.
```

So the *machine* exit of path A is not "hard until the construction is done";
it is closed until a separate, multi-year, RH-independent formalization program
builds arithmetic intersection theory in Lean. `011` priced A4 as "open-ended
research program" and never said why. Now it is said, and it is measurable.

Cross-check, so this is not a one-sided reading: the repository's own
algebraic-geometry vocabulary is equally absent - `grep -in
"arithmetic Chow|adelic line bundle|Hodge index"` over `docs/` and
`ConnesWeilRH/` returns hits **only in the files written today**
(`006:386-388`, `README.md:53`). There is no half-built bridge in the repo that
this audit overlooked.

+========================================================================+
| [4] WHAT THE AUDIT CONFIRMED: THE POSITIVITY CONE IS EXACTLY RIGHT     |
+========================================================================+

The audit began by suspecting 1417 §4.3's central step - `F-hat = |g-hat|^2 >=
0` - of being false, because `CompactLogConvolution.lean` documents its
reflection map as conjugation-free:

```lean
-- Source/CCM25Concrete/CompactLogConvolution.lean:46-48
/-- Reflection in the additive log coordinate, without complex conjugation. -/
noncomputable def reflection (f : CompactLogTest) : CompactLogTest := by
  let raw : Real -> Complex := fun x => f.test (-x)
```

`CompactLogTest.test` is `Real -> Complex` with no reality field. So the fear
was: a complex `g` gives `F-hat = g-hat(r) g-hat(-r)`, which is not
nonnegative, and then the whole "the only brake is positive-definiteness"
argument in 1417 §3b/§4 would be against the wrong cone. **The fear was
unfounded, and the reason is worth recording as a lemma.**

`convolutionSquare` does not use `reflection`; it uses `involution`, and that
one conjugates:

```lean
-- Source/CCM25Concrete/CompactLogConvolution.lean:114-119
noncomputable def convolutionSquare (g : CompactLogTest) : CompactLogTest :=
  g.involution.convolution g

@[simp] theorem convolutionSquare_apply (g : CompactLogTest) (x : Real) :
    g.convolutionSquare.test x =
      integral t : Real, star (g.test (-t)) * g.test (x - t) := by
-- :122-124
/-- The genuine convolution square is Hermitian: `F(-x) = conj (F x)`. -/
theorem convolutionSquare_neg (g : CompactLogTest) (x : Real) : ...
```

And both legs of the gate read `F` only through the symmetrized combination,
then take the real part:

```lean
-- Dev/C1SameOwnerWeil.lean:36-45   (finite leg)
  ... * (F.test (Real.log n) + F.test (-Real.log n))) ... ).re
-- Dev/C1SameOwnerWeil.lean:48-52   (archimedean numerator)
  Complex.ofRealCLM (Real.exp (y / 2)) *
      (F.test y + F.test (-y)) -
    2 * F.test 0
-- Dev/C1SameOwnerWeil.lean:61-64   (archimedean term)
    ... + integral y in Set.Ioi (0 : Real), archimedeanIntegrand F y).re
```

Therefore, for every `g`, with `F = g.convolutionSquare`:

```text
  F(-x) = star (F x)               [Hermitian, :122-124]
  F(x) + F(-x) = 2 * (F x).re      [so both readouts see only Re F]
  F(0) = integral \{|g(u)|^2\} u   [substitute u = -t in :119: real, >= 0]
  F-hat = |g-hat|^2                [star present in :119: nonnegative]
  ==> qw, archimedeanTerm and finitePrimeSum all factor through
      the nonnegative function |g-hat|^2.
```

Two consequences. (1) 1417 `:79`'s hypothesis "with `g` real" is **not needed**
- `Re F` does the job, and the complex test space adds nothing to the gate.
(2) Form D's admissible cone is exactly `{nonnegative |g-hat|^2 : g-hat in the
Paley-Wiener image of compactly supported smooth functions}`, which is what
1417 §4.3 and the "uncertainty principle as positivity source" argument assume.
The argument stands.

+========================================================================+
| [5] TECHNICAL CORRECTION: "(OB) IS ONE NUMBER" IS CURRENTLY TWO        |
+========================================================================+

`011:151-153` states

```text
  (OB)   archimedeanTerm (g * g~) <= 0
     <=> lambda_max( T_K_eff restricted to L2(-log2/2, log2/2) ) <= 0
```

and `1417:293-294` calls it "the top of the spectrum of ONE explicit truncated
convolution operator ... ONE number". Two defects, both fixable, both at W0.

**Defect 5a - the symbol is unbounded below, so there is no `lambda_max`.**
By 1417 §2, `T_K_eff` is the multiplier by
`Phi(r) = -Re psi(1/4 + i r/2) + C' ~ -log|r/2| + C' -> -infinity`.
Multiplication by an unbounded function is an **unbounded** self-adjoint
operator; its compression to `L2(-R,R)` is not defined without a form domain,
and where it is defined, the spectrum is unbounded below, so
"`lambda_max <= 0`" is a category error. The correct object is

```text
  sup { A(g0 * g0~) : g0 in PW_R,  ||g0||_2 = 1 }   <= 0
```

a **supremum of a quadratic form over a type-constrained unit sphere** - which
is exactly the Selberg/Beurling-Slepian extremal shape 1417 `:307-310`
correctly names, and exactly NOT an eigenvalue. The distinction is not
cosmetic: `lambda_max` invites a finite discretization, and a discretized top
eigenvalue is a proxy with no a priori relation to the sup. This family
already bit the project once: 263 §8 exhibits a 2x2 minor of the same shape of
kernels with `det = -0.707084047558... < 0`, i.e. negative directions are
real, and which direction a mesh exposes is an artifact of the mesh. Also,
since the kernel is not in `L1` (`1/|y|` at the origin), `T` is not Hilbert-
Schmidt, so attainment of the sup is itself an open question, not a given.

**Defect 5b - `C'` is a free parameter and `3.1083` is not yet a competitor.**
`Phi` is pinned only up to an additive `C'` (1417 `:110-114`, deliberately), and
`C'` shifts the form by `C' * integral |g-hat|^2 = C' * ||g||_2^2`, i.e. by
`C'` on the unit sphere, i.e. **it moves the quantity under test by an unknown
constant**. So `1417:302-303`'s "the competition is therefore a NUMBER, not a
mood: how negative can the `1/sinh` part be, against `-3.1083...`" is one
number plus one unpinned constant. The arithmetic constant `log(4*pi) + gamma`
is committed source (`:62`); `C'` is not. W0 must produce `C'`, the Fourier
normalization, and the form domain, in that order. `011`'s W0 row already
assigns `C'` and the `2*pi` convention to W0; what it did not say is that until
W0 reports, `(OB)`'s operator form has no numeric content at all.

```text
   before W0            after W0
   --------             --------
   Phi up to C'   -->   C' pinned, exact
   "lambda_max"   -->   sup over PW_R unit sphere
   -3.1083 rival  -->   (log4pi+gamma) + C', one number
   no domain      -->   form domain named
```

+========================================================================+
| [6] PRIORITY INVERSION AND THE CORRECTED SHAPE OF THE PROGRAM          |
+========================================================================+

`011` headlines the bridge and appends Track W at `:141`, after A0-A4. The
audit says the order is backwards on three independent measures.

```text
+--------+---------------------------+---------------------+-----------------+
|        | Track W (window theorem)  | Track A (bridge)    | which wins      |
+--------+---------------------------+---------------------+-----------------+
| needs  | committed definitions     | a 45-page           | W: W0 reads     |
|        | only: archimedeanTerm,    | transcription plus  | code that is    |
|        | convolutionSquare,        | an external         | already here    |
|        | supportRadius             | coincidence         |                 |
+--------+---------------------------+---------------------+-----------------+
| closes | plausibly (1-3 weeks for  | P(A3+) < 0.05,      | W               |
|        | W1)                       | and R1 says the     |                 |
|        |                           | table understates   |                 |
|        |                           | it                  |                 |
+--------+---------------------------+---------------------+-----------------+
| Lean   | yes: a real brick in the  | no: blocked by R2   | W               |
| leg    | repo's own vocabulary     | until arithmetic    |                 |
|        |                           | intersection theory |                 |
|        |                           | exists in Lean      |                 |
+--------+---------------------------+---------------------+-----------------+
| reaches| NO - and it says so       | only via A4, which  | neither, today  |
| RH     | (011:181-187)             | R1+R2 close         |                 |
+--------+---------------------------+---------------------+-----------------+
```

So the corrected program is:

```text
  1. W0   first spend of the whole program. Re-derive A(F) = form of
          |g-hat|^2 with Phi pinned exactly, from committed definitions.
          Fixes defects 5a/5b. 1 day, no external reading, no Lean.
  2. A1   same arithmetic, bridge-facing (pin C' and r_0). Fold into W0;
          they are the same computation, and 011 listing them separately
          double-books a one-day job.
  3. W1   the decidable theorem. This is the deliverable. It does not
          reach RH and must never be sold as doing so.
  4. A2   KEEP. It is a genuine one-symbol gate on the bridge, cheap, and
          its negative branch is a typed result. It is simply no longer
          the headline, because passing it buys permission to attempt a
          construction whose difficulty equals RH's.
  5. A3/A4  not dead, but re-labelled: an A4 success would be an RH proof
          that this project could not register without first formalizing
          Arakelov theory. Any future authorization of this branch must
          budget that separately or state it as out of scope.
```

The uncomfortable part of the honest answer: **this project's own acceptance
rule (law 65 - nothing is a result until Lean certifies it) means path A cannot
count as an RH route here, even in the world where the bridge exists**, because
its endpoint is not statable in the pinned library. Path A is a *paper* route.
That is a legitimate choice to make deliberately; it is not legitimate to make
it under a headline that says "attacking the gate from outside its category"
while the exit arrow silently leaves the formalization as well as the
difficulty.

+========================================================================+
| [7] WHAT THIS RECORD DOES NOT CLAIM                                    |
+========================================================================+

* It does not claim path A is mathematically void. It claims the program as
  registered reduces nothing, and that its registered exit is not reachable
  in the repository's machine. A researcher with a different objective
  function (paper first, Lean later) may still rationally buy the bridge.
* It does not claim `(OB)` is false, or true. W0/W1 are untouched by this
  audit; defects 5a/5b are about how `(OB)` was *written*, not about its
  content, and the sign direction `archimedeanTerm <= 0` is unchanged and is
  confirmed again from `:61-64` here.
* It does not claim the phase/density filter (1417 §3) was wrong. It is the
  reason W1 is the only place a sign can be decided from density-level data,
  and 1418 §5 makes that harder, not easier.
* The Mathlib grep is a claim about the pinned version on disk
  (`v4.30.0`), not about every library: an external Mathlib-adjacent
  formalization of Arakelov theory could exist and would change R2's dates
  but not R1.
* No Lean was built. No number here is certified: `0`, `1`, `16` are grep
  counts (mechanical, reproducible), `3.1083...`, `-4.2274...` and
  `-0.707084047558...` are quoted from committed text and standard values,
  and `C'` remains unpinned.

RH is not claimed.
