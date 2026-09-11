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

## 4. What this charter does NOT claim

- Not that RH will be proved here; not that proportion/bound lanes can close
  it (ceiling cited in s0); not that 1342's NO-FIRE becomes evidence in any
  new direction by re-running - A1 asks a DIFFERENT (asymptotic) question of
  the same deterministic object.
- RH NOT claimed anywhere in this campaign; every artifact stays MODEL/cert
  graded per repo law.
