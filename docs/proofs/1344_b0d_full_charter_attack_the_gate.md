# Record 1344 - B0d-FULL charter: attack the gate, not the doorknob (+ A1 pre-registration)

```text
+------------------------------------------------------------------+
| TRIGGER: owner directive 2026-09-12 ("no precedent != cannot" /   |
| "interface-only is pointless"). PREMISE RETRACTION (7k F5): the  |
| "zero precedent for model-made new-structure RH mathematics"     |
| claim is DEAD - it died on 2026-08-10 (Anthropic note, below).   |
| MISSION: attempt a DIRECT proof of the gate                      |
|   (forall vanishing g, 0 <= qw g) == SourceRH == RH             |
|   (weilCriterion_iff_sourceRH, d767a1d). Interfaces are          |
|   scaffolding only, never the product.                           |
+------------------------------------------------------------------+
```

## 0. The frontier evidence that changed the decision (all cited, 2026-09-12)

- **Claude-RH (Anthropic, 2026-08-10)**: unreleased Claude model, prompted in
  Claude Code to attempt RH. Pass 1: 650 ideas, zero worked. Pass 2: ~60
  subagents, ~1.5 days, ~2400 shell commands, hundreds of Python scripts,
  mutual validation; 2 subagents held the core ideas. OUTPUT: proportion of
  zeta zeros provably on the critical line, **41.6% -> 67.2%**, with a
  machine-checkable **Lean** formalization; reviewed internally and by
  B. Conrey and D. Goldston; "The result stands, is significant and
  interesting." Mechanism: *"treating a certain space of functions with both
  positive and negative definite parts at once rather than separately"* -
  i.e. a DEFINITENESS-FUSION move, the same language as our gate.
  (datacamp.com/tutorial/claude-and-the-riemann-hypothesis;
  techcrunch 2026-08-11.)
- **Lambda squeeze (2026-08)**: RH <=> `Lambda <= 0`; unconditional
  `0 <= Lambda <= 0.1787854`, assembled from 3,149,013 + 883 + 1
  machine-checked interval certificates and ~3.1M certified zero-free
  windows - i.e. exactly the certifier technology class this repo runs
  (G8/certified-box lineage). The writeup itself states the ceiling:
  "Why this method cannot reach Lambda <= 0" - BOUND/PROPORTION results
  structurally cannot close RH (capacity dichotomy, 1335/1339 sibling).
  (judegomila.com/posts/riemann-lambda-0.1787854.)
- **External claim on the table (2026-02)**: an arXiv paper claiming
  "we prove the positivity of Li's criterion" (= RH) circulating on r/math -
  unaudited; first prey for lane A3.

Consequence for capability priors (7k F2, date-stamped): model-made novelty
INSIDE the RH problem family is now demonstrated; closure is not. The
correct experiment is the one that measures the unmeasured, at a budget
whose outcomes are each real regardless.

## 1. Attack-surface ledger

| lane | what it is | why OUR infrastructure | standalone value (non-RH) | status |
|---|---|---|---|---|
| **A1 definiteness-fusion / capacity scaling** | measure how the 1342 Gram minimum lambda_min(m) decays as the bump net refines (m -> inf). The gate's uniform-positivity program lives or dies on this exponent; Claude's 67.2% is proportion-grade, and the proportion->ALL gap IS the capacity gap | probe is built (1342 machinery + inv12 fidelity gate), object deterministic | theorem-grade map either way: exponent alpha < 1 => net-program alive (candidate uniform constant); alpha > 1 => net-program provably capacity-dead | PREREG BELOW; runs pending |
| **A2 Lambda-squeeze** | push the unconditional upper bound below 0.1787854 with our G8-faithful DQ dictionary + interval certifiers | Polymath-style finite-window certification is exactly our certified-box/G8 technology; Claude-RH proves agent-swarms can find lemmas here | every increment is a published-grade bound; ceiling known (never reaches 0) - this lane TURNS EVIDENCE, it does not pretend to close | queued after A1 |
| **A3 compiler audit lane** | machine-adjudicate external RH/Li-criterion claims (2026-02 Li-positivity paper first; Astra/Anthropic RH follow-ups when published) | B0b gate = the Lean statement every candidate proof must answer; G8 = independent numerical falsifier; both already green | refutation or acceptance of any real claim is a result; makes the repo the world's RH-claim customs office | async, per claim |
| A4 (existing) | registered analytic surface | - | - | unchanged |
| NM lane (existing) | candidate-inequality generator | - | feeds A1/A2 | companion |

## 2. Honest priors (F2 date-stamped, 2026-09-12, subject to every frontier event)

```text
P(RH closed within 12 months | A1+A2+A3 at this budget)  ~ 1-2%
P(>= 1 genuine new result on-lane within 12 months)      ~ 60-75%
   (lambda_min asymptotics; a Lambda bound; audits that resolve)
P(the net-program question itself is answered)           ~ high (A1 IS that question)
```
Decision-theoretic note (the owner's point made structural): unlike the
knocker-only framing, EVERY terminal branch of A1/A2/A3 pays; the campaign
is no longer all-or-nothing on RH, which is what made the previous framing
pointless by its own admission.

## 3. A1 pre-registration (spec BEFORE any new digit; 1342 is SPENT and stays spent - this is a NEW probe, estimation not verdict class)

- Object: exactly the 1342 bump family (Rp = R/(1+1.6/m), w_b = 0.8*spacing,
  support subset (-log2, log2), polarization Gram, 3 x m vanishing
  constraints, SVD nullspace Z, Gm = Z^T B Z), with m in {24, 48, 96}.
  Grid: smallest power of two NQ >= 2^17 with w_b >= 10 DX (m=24 reproduces
  1342's +3.083243887e-03 as a REPRODUCE gate before any new-m digit is
  trusted; mismatch => ABORTED-UNINFORMATIVE).
- Rig gates: G3b (nullspace residual), G5 (polarization identity),
  G7 (prime-free support), G8-control per 1342 inv12 (self-calibrating
  ladder, band UNCHANGED). No witness/G8w adjudication (no witness object).
- Readout per m: lambda_min, lambda_2; log-log least-squares fit
  lambda_min(m) ~ c * m^{-alpha} with 1e16-level float determinism
  (double the grid at one m to re-confirm G4-style stability).
- Reporting rule (estimation probe, no FIRE/NO-FIRE bands): alpha is
  reported with spread from {24,48,96} and a doubling-check; the
  interpretation branches (alpha<1 vs >1) are declared HERE: alpha > 1 with
  stable sign => REGISTER "uniform-positivity-by-finite-nets capacity-dead"
  as a model-level theorem-shaped map (mirror of 1339 capacity);
  alpha <= 1 => net-program ALIVE: next prereg attempts the uniform-constant
  proof route. NO branch falsifies the gate itself either way.
- Budget: three official runs <= ~4h total compute + analysis; kill = if
  the m=24 reproduce gate fails, abort, fix rig, rerun reproduce, THEN m.

### 3a. A1 implementation amendment (committed BEFORE launch, law 42; section-3 object, bands, and branches UNCHANGED)

- **NQ rule computed, not assumed.** From committed constants (R = log2/2 -
  0.01, QL = 28): w_b(m) = 1.6*R/(m+1.6), DX = 2*QL/NQ. Requiring
  w_b >= 10*DX at the 2^17 floor: margins 2.46x (m=24), 2.54x (m=48),
  1.29x (m=96) => all three run at NQ = 2^17; the doubling check runs at
  m=24, NQ = 2^18. The rule is recomputed in-script from the imported 1342
  module constants (constants are DATA).
- **Cost structure and the two-path split.** 1342 measured 2682.9 s wall
  for one m=24 official pass; the per-call cost is dominated by the prime
  term (qmax = e^(2*A_DET) ~ 4.85e8, ~2.4e7 primes x 2 np.interp ~ 2 s per
  qw call). Gram needs m + m(m-1) calls => 576 / 2304 / 9216 for
  m = 24/48/96; the verbatim path at m=96 alone would cost ~5-6 h,
  violating the section-3 4 h budget. Resolution: m=24 (reproduce) and the
  doubling check run the 1342 module VERBATIM (importlib import; zero
  copied arithmetic); m in {48, 96} run an ALGEBRAICALLY IDENTICAL refactor
  of the prime term only: psum = c . F.real with c the per-grid sparse
  accumulation of the SAME interpolation stencils (same qmax, same
  coefficients log(q)/sqrt(q) and log(p)/sqrt(p^k), same linear weights on
  the same QS grid); equality up to FP summation order only (~1e-16 rel).
- **New gate G9 (path equivalence).** At m=24, NQ=2^17: the FULL Gram is
  built by both paths; PASS = max|dB|/(1+|B|) < 1e-12 AND
  |dlambda|/(1+|lambda|) < 1e-12. G9 FAIL => fast-path digits INADMISSIBLE
  => ABORTED-UNINFORMATIVE before m=48/96 (gate breach is never arbitrated
  post-hoc).
- **REPRODUCE gate operationalized.** Committed lambda_min is parsed at
  runtime from 1342_falsifier_results.json (never hand-typed); PASS =
  relative difference < 5e-13, i.e. the committed display digits
  +3.083243887e-03 are retained. FAIL => abort; no new-m digit is trusted
  (section 3).
- **Fidelity pins.** Runner pins numpy==2.5.3 and mpmath==1.4.1 (the
  versions that produced the committed 1342 digits, per its results JSON);
  environment drift would attack the REPRODUCE gate itself.
- **Anchor provenance + control.** G1a/G1b carried verbatim (aborting);
  the G8 control is m-independent (inv11b anchor-grid control) => run ONCE
  per official process; inv12 ladder and band unchanged. No witness/G8w
  (section 3).
- **Sign-flip escalation (estimation class; no verdict band).** If
  lambda_min <= -1e-8 at any m on the fast path: digit is flagged
  ESCALATION-CANDIDATE and the Gram is re-run on the VERBATIM path before
  any trust (this re-run may exceed the 4 h budget; authorized here as the
  rare branch). First hypothesis = rig artifact (1342 section-5 clause, by
  analogy); adjudicating a class extension belongs to a NEW prereg, not to
  A1. Confirmed-negative-on-both-paths => digits reported, branch
  SIGN-UNSTABLE, no alpha verdict.
- **Smoke policy.** P_SMOKE=1: m in {4,6}, module grid 2^15, SMOKE-ONLY
  reduced G8 ladder (400/800) that never touches official digits, and a
  quick two-path qw cross-check on 3 random span vectors (< 1e-12 rel).
  Smoke output is machinery evidence only.
- **Batch/log/sentinel.** Batch 1547; log
  docs/proofs/1344_logs/1547_1344_a1_official.log (mirror side); sentinel
  "DONE 1344-A1"; acceptance by LOG CONTENT, not exit code. Budget
  re-estimate: ~60-100 min (m=24 verbatim ~25 min + doubling ~25 min +
  fast m=48/96 ~5 min + G9 ~1 min + anchor/G8c ~3 min).

### 3b. Fusion interpretation pre-declaration (committed 2026-09-12, BEFORE the A1 digits land; law 42)

Context (deep read, same day): arXiv:2608.13637v2 (Alpoege-Furman; proof
discovered by Claude, Lean 4 verified, Aug 2026) proves >=2/3 of zeros
simple+on-line by a RANK-TRACE inequality on a FINITE COMPRESSION of Weil's
Hermitian form with Sylvester inertia counting the off-line pairs; their
Appendix B records that the negative index of any finite compression of the
form is identically zero (all negativity comes from off-line zeros) and
that the route was found by DUALIZING an empty index-bound attack into a
positive-eigenvalue count. This is the same object species as our G8
dictionary + 1342 nullspace Gram: A1's lambda_min(m) is the capacity
spectrum of that species restricted to the GATE observable (positivity on
the vanishing class). Their ceiling is a proportion; the field's open
question at the method level is why not ALL. The fusion branches, declared
HERE, before any alpha digit exists:

- alpha > 1 (section-3 CAPACITY-DEAD-MAP branch): register at MODEL grade
  "compression-capacity obstruction on the gate class": no bump-net
  compression of the vanishing class carries a uniform positivity constant;
  within this species the proportion->ALL gap is NOT attributable to
  bookkeeping slack on our subclass. Feeds directly into any follow-up on
  the 2608.13637 method ceiling.
- alpha <= 1 (section-3 NET-PROGRAM-ALIVE branch): register the NEGATIVE of
  that statement: the capacity obstruction is absent on our dictionary and
  subclass; the gap is then bookkeeping/analysis slack, and the
  uniform-constant proof route is the justified next prereg.
- Escalation clause (3a sign-flip) overrides both: no fusion reading until
  the verbatim-path recheck settles the digits.

Honesty rails (part of the declaration, not caveats added later):
(i) their compression lives on ALL even test functions with support <= log X
and a height sample grid; ours is the vanishing class via the 3m moment
constraints (nullspace Z). A capacity fact about one does NOT transfer as a
theorem to the other; the fusion is species-level MAP evidence, MODEL grade,
never a statement about their Lean-verified theorem, whose validity is not
touched in either direction. (ii) No RH claim; no implication from their
proportion result to our gate or back is asserted here.
Consequence for portfolio ORDER (owner decision input, 7k F6 taxonomy): the
fusion reading of A1 supersedes the 1346 H1/H2 harvest and the arXiv:
1703.03827 A3 audit as the next commitment; harvest and audit move to
backlog, not archive.

## 4. What this charter does NOT claim

- Not that RH will be proved here; not that proportion/bound lanes can close
  it (ceiling cited in s0); not that 1342's NO-FIRE becomes evidence in any
  new direction by re-running - A1 asks a DIFFERENT (asymptotic) question of
  the same deterministic object.
- RH NOT claimed anywhere in this campaign; every artifact stays MODEL/cert
  graded per repo law.
