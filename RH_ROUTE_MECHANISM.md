# The RH Route, in Three Mechanism Views

> Data cut-off 2026-08-31. All numbers recomputable from the tree; the axiom
> list is a live run on the warm build (3775-job footer, zero error lines).
> Route states: README.md. Working rules: AGENTS.md. Round records: docs/proofs/.

```text
+===========================================================================+
|  VIEW (a) — REDUCTION: RH -> a five-line checklist                        |
+===========================================================================+

   +---------------------------------------------------------------+
   |  RH: every nontrivial zero of zeta sits on Re(s) = 1/2        |
   |  problem: infinitely many zeros, none individually checkable  |
   +---------------------------------------------------------------+
                         |
                         | [step 1] Weil criterion (classical theorem,
                         |          restated in Lean): zeros -> signs
                         v
   +---------------------------------------------------------------+
   |  RH  <==>  q_w(g) >= 0 for every probe g vanishing at         |
   |  the three points {0, 1/2, 1}                                 |
   +---------------------------------------------------------------+
                         |
                         | [step 2] attack the sums through ONE
                         |          concrete finite matrix (CC20 paper)
                         v
   +---------------------------------------------------------------+
   |  finite-rank operator T on a fixed log window                 |
   |  T >= 0  ==>  q_w(g) >= 0                                     |
   +---------------------------------------------------------------+
                         |
                         | [step 3] whole chain formalized; every
                         |          arrow = already-checked theorem
                         v
   +---------------------------------------------------------------+
   |  coverage root -> SourceRH -> cc20 finite-vanishing           |
   |  -> rhDefinitionBridge -> _root_.RiemannHypothesis            |
   +---------------------------------------------------------------+
                         |
                         | [step 4] #print axioms
                         |  (Lean's transitive borrow-list; total)
                         v
   +---------------------------------------------------------------+
   |  CHECKLIST  (what the final audit still assumes)              |
   |                                                               |
   |  ( ) (1) C1 criterion: every probe's energy >= 0              |
   |  ( ) (2) finite-prime arithmetic data package                 |
   |  ( ) (3) remainder rows: "outside, no bulk"                   |
   |  ( ) (4) trace-package remainder data                         |
   |  ( ) (5) detector coverage: no off-line zero escapes          |
   |                                                               |
   |  (1),(5) = cores: each proved equivalent to RH                |
   |  (2),(3),(4) = data slots: certificates pending               |
   |  nothing else is borrowed beyond Lean's own foundations       |
   +---------------------------------------------------------------+
```

> **Interview script — view (a)** (read down the arrows)
> - "The top box is RH in its usual form: infinitely many zeros, none individually checkable."
> - "The first arrow applies the Weil criterion — a classical theorem that converts a statement about zeros into a statement about the sign of a sum."
> - "The next box is the engine: a finite-rank operator from the CC20 paper on a fixed log-window. Proving that single matrix positive proves the sums positive."
> - "Below it, every link from the criterion to Mathlib's statement of RH is already a checked theorem."
> - "The bottom box is one command's output: five assumptions remain — two equivalent to RH by proved theorems, three data obligations."

```text
+===========================================================================+
|  VIEW (b) — OPERATING SYSTEM: one round, every round                      |
+===========================================================================+

   [claim in the published paper]
        |
        | recompute independently at certified precision
        | (floats may generate candidates, never count as evidence)
        v
   [numeric probe]
        |
        | trust the probe only after it reproduces an identity that
        | is already machine-proved, and matches the paper's own
        | printed anchor value
        v
   [machine-checkable data]
        |
        | exact rationals with source-hashed provenance, or interval
        | certificates — approximate numbers do not survive this step
        v
   [Lean theorem]  +  its own audit file
        |
        | build ladder from the edited module up to a full-route
        | aggregate; acceptance reads the build log, not an exit code
        v
   +=================================== GATE ==================================+
   |   is the axiom print exactly Lean's three standard foundations?           |
   +===============+-----------------------------------------------+===========+
         YES       |                                               |  NO
         v         |                                               v
   +-----------------------------+     +------------------------------+
   | MAINLINE (imported trees)   |     | FRONTIER                     |
   | audit-clean theorems only   |     | incomplete work and visible  |
   |                             |     | placeholders live here ONLY  |
   +-----------------------------+     +------------------------------+

   WHAT THE MACHINE ALREADY PRODUCED (the scaffold under the checklist):

   foundations -> arithmetic=spectral equality -> spectral bridge ->
   window operator floor -> detector inequalities -> CC20 interface
   (paper data re-encoded in checkable form) -> GATE 1 assembly [WIRED]

   WHAT THE CHECKLIST LINES STILL OWE (obligations, not estimates):

   (1)   hardest item: a coercivity certificate at the paper's own
         scale; then mode enclosures; then one certified grid
   (2)(3)(4)   interval certificates for three published numbers
   (5)   a new construction — none on the table yet

   CENSUS: of every assumption ever declared on the frontier, exactly
   these five lines touch the RH output. "The rest contribute nothing"
   is a transitivity consequence of the audit, not an estimate.
```

> **Interview script — view (b)** (read down the loop, then the three summaries)
> - "Every round starts from a claim in a paper; nothing printed is taken on trust."
> - "We recompute the claim at certified precision, validate the computation itself against a known anchor, and re-encode it as data Lean can check: exact values with hashed provenance, or interval certificates."
> - "One gate decides membership — a theorem enters the mainline only when its axiom print shows nothing beyond Lean's standard foundations; incomplete work keeps its placeholders visible in the frontier instead."
> - "That is why 'it compiles' cannot masquerade as 'it is proven' here: the boundary is printed by the checker, not asserted by us."

```text
+===========================================================================+
|  VIEW (c) — WHAT REMAINS: the five lines, explained one by one            |
+===========================================================================+

   The audit of the RH output assumes exactly five named sentences.
   Two are cores: each carries a proved theorem of the form
   "this sentence <==> RH" — they are the mountain, restated.
   Three are data slots: no new mathematics, only certificates.

   +---------------------------------------------------------------+
   |  (1)  C1 criterion                            [CORE: iff RH]  |
   |  says: every probe that vanishes at 0, 1/2, 1 has             |
   |  nonnegative Weil energy                                      |
   |  why hard: the published positivity argument closes only      |
   |  below the paper's own scale; at scale it needs a             |
   |  repair term that no textbook bound supplies                  |
   |  owes: a certificate chain — coercivity certificate at the    |
   |  paper's scale, then mode enclosures, then one                |
   |  certified grid; the comparison stage is already              |
   |  wired and waits                                              |
   +---------------------------------------------------------------+

   +---------------------------------------------------------------+
   |  (2)  finite-prime arithmetic data              [DATA SLOT]   |
   |  says: the prime-side terms of the explicit formula take      |
   |  exactly the packaged values                                  |
   |  owes: one interval certificate; the exact-rationals          |
   |  machinery for this already exists                            |
   +---------------------------------------------------------------+

   +---------------------------------------------------------------+
   |  (3)  remainder rows: outside, no bulk          [DATA SLOT]   |
   |  says: the tail rows cut off outside the window carry no      |
   |  bulk mass                                                    |
   |  owes: one interval certificate                               |
   +---------------------------------------------------------------+

   +---------------------------------------------------------------+
   |  (4)  trace-package remainders                  [DATA SLOT]   |
   |  says: trace data is compatible across the cutoff scales      |
   |  within the stated bounds                                     |
   |  owes: one interval certificate                               |
   +---------------------------------------------------------------+

   +---------------------------------------------------------------+
   |  (5)  detector coverage                        [CORE: iff RH] |
   |  says: every zero off the line would be caught by our         |
   |  test family — a counterexample cannot hide outside it        |
   |  why hard: a construction claim, not a bound; the one         |
   |  natural candidate family was closed by verdict               |
   |  owes: a genuinely new construction — none on the table yet   |
   +---------------------------------------------------------------+

   +---------------------------------------------------------------+
   |  Balance: 2 cores need new mathematics or the completion of   |
   |  a published argument; 3 slots need certificates, which is    |
   |  production work                                              |
   |                                                               |
   |  Every road that bypasses these five lines is closed with a   |
   |  graded certificate (theorem / verdict / screened / frozen);  |
   |  the road map and round records live in README.md and         |
   |  docs/proofs/                                                 |
   +---------------------------------------------------------------+
```

> **Interview script — view (c)** (read the five boxes top to bottom)
> - "The audit's entire residual is these five sentences; this view reads them one at a time."
> - "Lines (1) and (5) are cores: each carries a proved equivalence theorem, so working on either is working on RH itself."
> - "(1) is the sign statement over the probe space; the published proof runs short at the paper's own scale, and closing that gap is a staged certificate chain."
> - "(5) is the coverage claim for the test family; it is a construction problem with no candidate on the table — stated plainly."
> - "(2)-(4) are data slots: three published numbers awaiting interval certificates — production, not research."

---

## Reading the ledger

```text
   the only accepted progress event:
        line converts axiom -> theorem   ==>   one row disappears
                                                  from #print axioms
   everything else (probes, wiring, records) = making that event
   possible, checkable, and honestly counted
```

The five lines were identified on 2026-07-10 and are stable by design — that
is what a checklist is for. The public stance is unchanged: no unconditional
proof of RH is claimed; the checklist names exactly what remains.
