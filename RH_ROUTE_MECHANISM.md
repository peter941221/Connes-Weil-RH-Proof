# The RH Route, in Three Mechanism Views

> Data cut-off 2026-08-31. All numbers recomputable from the tree; the axiom
> list is a live run on the warm build (3775-job footer, zero error lines).
> Route states: README.md. Working rules: AGENTS.md. Round records: docs/proofs/.

```text
+===========================================================================+
|  VIEW (a) — REDUCTION: RH -> a five-line checklist                        |
+===========================================================================+

   +---------------------------------------------------------------+
   | RH: every nontrivial zero of zeta sits on Re(s) = 1/2        |
   | problem: infinitely many zeros, none individually checkable  |
   +---------------------------------------------------------------+
                         |
                         | [step 1] Weil criterion (classical theorem,
                         |          restated in Lean): zeros -> signs
                         v
   +---------------------------------------------------------------+
   |  RH  <==>  q_w(g) >= 0 for every probe g vanishing at        |
   |            the three points {0, 1/2, 1}                      |
   +---------------------------------------------------------------+
                         |
                         | [step 2] attack the sums through ONE
                         |          concrete object (CC20 paper)
                         v
   +---------------------------------------------------------------+
   |  finite-rank operator T on the log window [-log2/2, log2/2]  |
   |  eq-(115/119/121) interface; T > 0  ==>  q_w(g) >= 0        |
   +---------------------------------------------------------------+
                         |
                         | [step 3] whole chain formalized; every
                         |          arrow = already-checked theorem
                         v
   +---------------------------------------------------------------+
   |  coverage root -> SourceRH -> cc20 finite-vanishing          |
   |        -> rhDefinitionBridge -> _root_.RiemannHypothesis    |
   +---------------------------------------------------------------+
                         |
                         | [step 4] #print axioms
                         |  (Lean's transitive borrow-list; total)
                         v
   +---------------------------------------------------------------+
   |  CHECKLIST  (five named sentences, written 2026-07-10)      |
   |                                                             |
   |   ( ) (1) C1 criterion: every probe's energy >= 0           |
   |   ( ) (2) finite-prime arithmetic data package              |
   |   ( ) (3) remainder rows: "outside, no bulk"                |
   |   ( ) (4) trace-package remainder data                      |
   |   ( ) (5) detector coverage: no off-line zero escapes       |
   |                              |                              |
   |   (1),(5) = cores: each iff RH -- proved theorems           |
   |   (2),(3),(4) = data slots: certificates pending            |
   |                                                             |
   |   audit line = 8 = these 5 + Lean ticket [propext,          |
   |                Classical.choice, Quot.sound]                |
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

   [paper fact]  (e.g. CC20 eq-(115) table, Fact-1 L1 ~ 0.00122)
        |
        | recompute independently; floats may only generate,
        | never evidence (law 11: validated values need
        | mpmath/ARB; law 12: constants inside workdps)
        v
   [numeric probe]  docs/proofs/NNNN_*_probe.py
        |
        | pre-trust law (1): first reproduce a Lean-proven identity
        | convention pins must match the paper's published number
        | (this anchor test caught our own sqrt errata, 1059->1062)
        v
   [machine-checkable data]
        |   exact rationals + per-node SHA-256 provenance
        |   (scripts/cc20_eq115/)          interval certs
        |   (scripts/yoshida_intervals/)
        v
   [Lean brick]  Dev/<Leaf>.lean  +  paired <Leaf>Audit.lean
        |
        | build ladder: owner -> import probe -> #print axioms
        |  -> Dev batch -> full-root (milestones only)
        | acceptance = log footer + zero "^error:" lines; the
        |  exit code is untrusted in both directions (AGENTS 7a)
        v
   +========================== GATE ==============================+
   |  axiom print == [propext, Classical.choice, Quot.sound]?     |
   +==============+---------------------------------+--------------+
        YES      |                                 |  NO
        v        v                                 v   (stays frontier work)
   +-----------------------------+     +--------------------------+
   | imported trees (Source/     |     | Dev/ frontier: 1022 files|
   |  Route): 598 files,         |     | 41 sorry, probes only;   |
   |  266,381 lines,             |     | freeze guard fail-closed |
   |  8,402 theorems, 0 axioms   |     | on frozen namespaces     |
   +-----------------------------+     +--------------------------+

   WHAT THE SCAFFOLD ALREADY CARRIES (README route map):

   +----------+------------------------------------------+-----------+
   | floor    | content                                  | state     |
   +----------+------------------------------------------+-----------+
   | st.1     | same-owner foundations, log bridge,      | CLEARED   |
   |          | pole/archimedean/prime readbacks         |           |
   | st.2     | GATE 2 arithmetic = spectral (center-2)  | CLEARED   |
   | st.3     | W-mountain W1..W4b (spectral split)      | CLEARED   |
   | st.4     | operator floor on window, eq-(121) fold  | BUILT     |
   | ridge    | detector: Wirtinger (8.13), (8.11)       | CLEARED   |
   | iface    | CC20 finite-rank + 1732-entry table      | LANDED    |
   | assembly | GATE 1 conditional chain                 | WIRED     |
   +----------+------------------------------------------+-----------+

   THE FIVE LINES, SIDE BY SIDE:

   +-----+------------------------------+-----------------+---------------+
   | #   | plain words                  | face            | still owes    |
   +-----+------------------------------+-----------------+---------------+
   | (1) | every admissible probe has a | analytic;       | gamma, alpha, |
   |     | nonnegative energy account   | iff RH proved   | beta; delta   |
   |     |                              | (:1518, :1537)  | wired         |
   | (2) | prime-term data package      | data slot       | L1 interval   |
   |     |                              |                 | certificate   |
   | (3) | tail ledger, no bulk         | data slot       | rows cert     |
   | (4) | trace-package remainders     | data slot       | trace cert    |
   | (5) | no off-line detector escapes | construction;   | NEW design    |
   |     |                              | iff RH proved   | (none yet)    |
   +-----+------------------------------+-----------------+---------------+

   CENSUS OF ALL DECLARED axiom ROOTS (39):
   +--------------+-----------------+-----------------------------+
   | 5 LIVE       | 8 wrapped       | 26 declared-unconsumed      |
   | under RH     | off-RH contract | deadweight (prune           |
   | closure      | lanes           | candidates)                 |
   +--------------+-----------------+-----------------------------+
        "the other 34 contribute nothing to the RH output" is a
        transitivity consequence of the audit, not an estimate.
```

> **Interview script — view (b)** (read down the loop)
> - "This is the per-round procedure. It starts from a claim in the published paper."
> - "We recompute that claim at certified precision; ordinary floating-point output never counts as evidence."
> - "It is then re-encoded as machine-checkable data: exact rationals with per-node provenance hashes, or interval certificates."
> - "Finally it becomes a Lean theorem, and the audit below the gate asks one question: is its axiom print exactly the three standard axioms?"
> - "Passing results enter the imported tree — 8,400 theorems so far, all axiom-clean. Anything else remains frontier work."
> - "The closing table is the full assumption census: 39 roots declared, 5 of them load-bearing — and that split is machine-checked, not estimated."

```text
+===========================================================================+
|  VIEW (c) — PRUNING + REMAINING GATES                                     |
+===========================================================================+

   OFF-BOARD ROADS - four grades, not one
   (nothing here "counts as progress"; only grade F was ever
   completed, and completed != an RH step):

   +---------------------------+--------------+------------------+--------+
   | road                      | GRADE        | instrument       | record |
   +---------------------------+--------------+------------------+--------+
   | bare whole-line HS        | DEAD by      | theorem: false   | 59f8ff8|
   | premise                   | THEOREM      | for every        | 08-24  |
   |                           |              | nonzero test     |        |
   | pure-analysis budget      | DEAD by      | theorem:         | 08-26; |
   | ladder to ROOT window     | THEOREM      | B(log2)=+3.9>0,  | 3 rungs|
   |                           |              | top rung proven  | carved |
   |                           |              | unreachable      | first  |
   | plain-window cutoff trace | DEAD by      | theorem: empty   | -      |
   | family                    | THEOREM      | producer         |        |
   | canonical positive-kernel | DEAD by      | theorem: D2      | 1052   |
   | cutoff bridge             | THEOREM      | obstruction      | no-go  |
   +---------------------------+--------------+------------------+--------+
   | semilocal prolate         | DEAD by      | no mechanism     | 1054/  |
   | asymptotic family         | VERDICT      | (1054 exact      | 1055;  |
   | (sole STATION 5-6 cand.)  |              | counterexample)  | d330e90|
   |                           |              | + no decidable   | 08-29; |
   |                           |              | eval (precision  | revival|
   |                           |              | wall)            | conds  |
   |                           |              |                  | written|
   | raw F1 semilocal crux     | DEAD by      | 4-octave, dt-    | 1063   |
   |                           | VERDICT      | invariant number-| 08-31; |
   |                           |              | ic falsification;| D-wt   |
   |                           |              | D-weighted F1'   | F1'    |
   |                           |              | survives instead | survives|
   | F1 brick-2b               | DEAD by      | own pre-flight   | 1059   |
   | (perturbation scheme)     | VERDICT      | margin check     |REVOKED |
   +---------------------------+--------------+------------------+--------+
   | Nyman, Burnol, Sonin,     | SCREENED     | named coeff/     | plan/  |
   | adelic, Clifford,         | OUT          | ideal-class/     | 80     |
   | Fredholm, log-Poisson,    | (verdict-    | density/domain   | files  |
   | Xi-nullspace, ...         | grade)       | obstructions     |        |
   +---------------------------+--------------+------------------+--------+
   | Lane R, Gamma_R prefix/   | FROZEN,      | work EXISTS;     | 271b8fd|
   | tail sign experiments     | NOT DEAD     | doesn't imply    | 08-19; |
   |                           |              | global spectral  |arch/   |
   |                           |              | nonnegativity    |lane_r  |
   | Gate 3U physical branch   | FROZEN,      | finite-band      |arch/   |
   |                           | NOT DEAD     | Route-A deliver- |diagnos-|
   |                           |              | able COMPLETE,   | tic_   |
   |                           |              | audit-clean -    | gate3u;|
   |                           |              | not an RH step;  |ident-  |
   |                           |              | infinite-carrier | ities  |
   |                           |              | identities OPEN  | OPEN   |
   +---------------------------+--------------+------------------+--------+

   REOPENING RULES, by grade:
   +--------------+------------------------------------------------+
   | DEAD by      | needs a NEW checked theorem implying the RH    |
   | THEOREM      | root; the old statement is refuted for good    |
   +--------------+------------------------------------------------+
   | DEAD by      | written revival conditions (e.g. 1055 s5:      |
   | VERDICT      | proved self-adjoint realization + analytic     |
   |              | one-crossing identity, else citation is frozen)|
   +--------------+------------------------------------------------+
   | SCREENED     | re-entry must address the named obstruction    |
   | OUT          | head-on                                        |
   +--------------+------------------------------------------------+
   | FROZEN,      | nothing disproved it: Unfreeze Rule             |
   | NOT DEAD     | (RH_MAINLINE_FREEZE.md) - only a checked       |
   |              | implication to the coverage root reopens it    |
   +--------------+------------------------------------------------+

   WHAT IS LEFT — dependency graph to the first checkmarks:

            +-------------------------------------------+
            | gamma: paper-scale coercivity certificate |  <-- hardest:
            | Toeplitz finite-section at lam~1.05158>1  |   textbook
            | (Bessel branch only works for lam < 1)    |   bounds fail
            +-------------------------------------------+
                  |                        |
                  v                        v
   +------------------------+   +---------------------------+
   | delta: (141)-(143)     |   | alpha: 11-mode ODE        |
   | chain -- ALREADY WIRED |   | enclosures + B1-B3 bricks |
   +------------------------+   +---------------------------+
                  |                        |
                  |                        v
                  |              +---------------------------+
                  |              | beta: certified L1 grid   |
                  |              | 2*int|chi-tau| <= eps1    |
                  |              +---------------------------+
                  |                        |
                  +------------+-----------+
                               v
                    +------------------------+
                    | LINE (1) can be ticked |
                    +------------------------+
   +-----------------------------------+   +---------------------------+
   | interval certificates -> (2)(3)(4)|   | NEW CONSTRUCTION -> (5)   |
   | (exact-rationals machinery ready) |   | (none on the table yet)   |
   +-----------------------------------+   +---------------------------+

   +---------------------------------------------------------------+
   | NET TERRAIN: 39 roots declared -> 34 machine-proven off-closure|
   | -> the 5-line board is irreducible; closed roads are why       |
   |   these are the only gates left on this route                  |
   +---------------------------------------------------------------+
```

> **Interview script — view (c)** (read the table top to bottom, then the graph)
> - "The roads here are closed, but at four distinct grades rather than one label."
> - "Four are refuted by theorem; those are final."
> - "Three were closed by written verdicts; their reopening conditions are recorded next to them."
> - "Two are frozen, not refuted. Gate 3U is the instructive case: its finite-band deliverable is complete and audit-clean, but it does not consume the RH root, so it earns no progress credit."
> - "The graph below is the remaining path: gamma is the hardest item, alpha and beta follow from it, and line (5) has no candidate yet — stated plainly rather than papered over."

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
