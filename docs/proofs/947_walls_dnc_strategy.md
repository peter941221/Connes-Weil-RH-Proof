# 947 — Divide-&-conquer route: the two decisive OPEN walls and their sub-steps

Date: 2026-08-10. Status: strategy note (not a proof, no new axiom, RH NOT claimed).
Companion verified state: Docs/946 (Task-2 verified seam), MEMORY change log.

## 0. Why this note

分而治之 = decompose each remaining wall into the smallest concrete, verifiable
sub-steps, and never conflate a verified helper with the route bottom.  The two
walls below are the ones that separate the current axiom-clean healthy-carrier
machinery from an unconditional RH claim.  Each is a real analytic step, not a
Lean-assembly leaf.

## 1. Wall A — lane-B total archimedean term (SCAB, global-restricted balance)

Verified so far (Dev/CompactSCealBalance.lean, axiom-clean):
  * finitePrimePart_scaled : globalSum - restrictedSum = omittedSum         (C)
  * restrictedWeilValue_re_eq_weilValue_re_add_omitted_re : restricted.re =
    global.re + omitted.re (owner-level real balance, arch absorbed)

Remaining open attacker (this is Weil-explicit-formula content):
  - The healthy carrier `Test = TestFunction = SchwartzMap R C` is the FULL
    Schwartz space; the library `archimedeanTerm` (CCM25 Eq 3.7) is per-owner
    and only defined once a test has compact support.  So a total
    `healthy.archimedeanTerm : TestFunction -> R` that equals Eq 3.7 on compact-
    support square and yields a closed `psi`/`qwLambda` = explicit formula needs
    (a) an explicit extension rule on non-compact-support Tests, and (b) the Weil
    explicit-formula theorem tying the arch/pole global-plus-prime to the M-zeros.

D&C sub-steps:
  1.1 CLOSED: lift `SelectedWeilFormulaOwner.archimedeanTerm` to a `def` on
      `CompactLogTest` (`compactLogArchimedeanTerm`,
      Dev/CompactLogArchimedeanLift.lean), axiom-clean.
  1.2 CLOSED: the total healthy arch term `totalArchimedean : TestFunction -> R`
      (Dev/CompactArchTotal.lean) with a "compact-support? use Eq 3.7 else 0"
      rule, plus `totalArchimedean_eq_compact` matching the CCM25 Eq.3.7 real
      term on any compact-log input. The healthy carrier's `archimedeanTerm`
      slot was re-pointed off `fun _ => 0` onto `totalArchimedean`
      (Dev/WellFormHealthyRepoint.lean) with
      `healthyArchimedean_matches_compactTerm`. Axiom-clean; see docs/948.
  1.3. Prove the healthy `psi`/`qwLambda` identities under that arch term for the
       finitely-supported common test — i.e. the owner-level `weilValue` balance.
  1.4. Closing SCAL on the healthy symbols then shrinks the lane-B residual.

## 2. Wall B — Lane C, the infinite-carrier Gate identity (I-P)F = -(I-P)D

The original infinite-carrier Gate (Proof-717 / Gate-3U seam, docs/928/872)
reduces to the single operator identity
    (I-P)F = -(I-P)D,  equivalently
    sourceActualBandCombinedCoframeLeakage =
        sourceActualBandForwardCoframe + sourceSoninCoframeLeakage = 0
on non-empty prime families.  No theorem forces it; the deciding F-term (the
exact Sonin intersection R0) is not numerically reachable (AGENT 818/819);
probe 884 shows the outer channel stays ~0.61-0.62 across physical lambda scale
and never decays.

D&C sub-steps (honest, not-yet-closed):
  2.1. Isolate the *purely-algebraic* content of the channel split (the
       orthogonal decomposition is already in-library at
       `ChFinityChannelSplit.lean:84-101, JetOrientation:312`).
  2.2. Reduce `F == implicitly` to a concrete candidate: the ONLY remaining
       hope is the exact cancellation `F == -D + J` (docs/872).
  2.3. Establish the transport/measure-theoretic injectivity needed before any
       identity can be verified on the infinite carrier (the compact-support
       action must happen first — rejected condition-number routes
       785/786/776/777/778/796).
  2.4. Only then the numeric probe can check the identity faithfully (grid
       proxies of projections are traps, AGENT 813).

## 3. Non-goals / guard

  - No sorry/axiom/fake producer (AGENTS 6).  Every statement above is either
    verified or explicitly open.
  - No claim of RH.  Wall A residual reduction is a step, Wall B closure is new
    math, the RH-equivalent C1 discharge (Docs/946 (b)) is a real RH proof.

RH NOT claimed.
