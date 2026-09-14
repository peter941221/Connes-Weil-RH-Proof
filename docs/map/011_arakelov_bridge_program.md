# 011 — the Arakelov bridge program: attacking the gate from outside its category

Binding preregistration, opened 2026-09-14 by owner decision. This document
supersedes, **for this face only**, the freeze posture recommended by records
1411 and 1415. Nothing else is superseded: the Lean mainline, the tower, the
B0b equivalence and the psi-bundle keep their committed status and their
acceptance discipline.

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

### Track W: the window theorem (added 2026-09-14, from 1417 section 3b)

Reading the committed brick pinned the obligation's direction, and it exposed a
second, unrelated-to-the-bridge target that is plausibly closable. On the
committed root-support class the prime sum vanishes identically
(`finitePrimeSum_eq_zero_of_support_subset_open_log_two`, used at
`C1MinimalWeilCriterion.lean:255`), so there is no oscillating prime sum to
control and the whole gate reduces to

```text
  (OB)   archimedeanTerm (g * g~) <= 0
     <=> lambda_max( T_K_eff restricted to L2(-log2/2, log2/2) ) <= 0
     K_eff = (1/2) e^{|y|/2}/sinh|y|  (renormalized)  +  (log(4pi)+gamma) delta_0
```

one explicit truncated convolution operator, one number.

```text
+-----+-------------------------------------+------------+------------------+
| W0  | Re-derive A(F) = <g0, T_K_eff g0>   | 1 day      | operator form    |
|     | from the committed definitions,     | paper +    | confirmed, or a  |
|     | pin K_eff and the head coefficient  | sympy      | mismatch named   |
|     | exactly, and fix the 2*pi           |            | (then A1)        |
|     | convention. Do NOT trust 1417 s2.   |            |                  |
+-----+-------------------------------------+------------+------------------+
| W1  | Prove or refute one inequality:     | 1-3 weeks  | PROVED: first    |
|     |   lambda_max( T_K_eff on                |            | unconditional    |
|     |     L2(-log2/2, log2/2)  )  <=  0       |            | archimedean sign |
|     |                                         |            | theorem          |
|     | A test g with A > 0 is a counterexample |            | REFUTED: (OB)    |
|     | to (OB) ONLY, not to RH: it leaves the  |            | closed, 125's    |
|     | all-supports scope untouched.           |            | demand stays open|
+-----+-------------------------------------+------------+------------------+
```

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

What it does claim is narrower and is the point: **this is the first attempt on
this face whose target-side theorem is already proved rather than sought.**

RH is not claimed.
