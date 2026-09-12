# 1369 - L2/hBridge bone attack plan: self-created mechanisms for the window frame lower bound and the off-line theft bound

Date: 2026-09-12.

Status: BINDING COMPANION attack plan, subordinate to the route ruling
[`003`](003_b1_b5_minimal_exit_route_selection.md) and the NM process
authority [`006`](006_new_math_creation_workflow.md). Aligned with the
1358 direct-attack charter and the 1368 corridor. Opened by owner
commission 2026-09-12 ("self-create; gnaw the bone"). RH is not
claimed. No bridge instance is claimed to exist. This plan registers
NO digits: the P0 bands are locked later, in their own prereg record,
before any run (law 42).

Map role: this record plans the attack on the single registered
missing object - the `hBridge` instance of the A2 form (record 1368,
`ConnesWeilRH.Source.C1H2Corridor.sourceRH_of_A2Bridge`). It appends
its candidate card to 006 and changes no other authority.

## 1. The bone, in its registered shape

The consumer is committed and green (batch 1560). Its type, verbatim
from `Dev/C1H2Corridor.lean` (record 1367 s2 lock):

```text
  hBridge_A2 :
    ∀ g : CompactLogTest,
      CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g →
      targetA2Schema W T1 eps A → windowMassBalance g W
```

with `A : Int → Real` the spread functional, UNINTERPRETED by
adjudication (record 1365 s1(b)): its intended realization is the
prolate/frame energy ratio of the window's on-line ordinates. The
count-only sibling (`sourceRH_of_countBridge`) is registered
DEAD-DIRECTION inside the leaf (record 1353: cluster-vs-spread
information asymmetry 70.6x full-class / 145.7x realized vs an allowed
factor <= 2; `1353_c6_placement_audit...md:140`).

## 2. Anatomy: the bone is three lemmas, not one

```text
  hypothesis (geometry)          conclusion (energy), per window I:
  spread(Γ_on ∩ I) ≥ A(I)          Σ_{γ∈I on}  mult |G(iγ)|²
  N_off-nearline(I) < f*(A)·N(I)     ≥ Σ_{ρ∈I off-nearline} 4·mult·Re[G(w)G(−w)]
        |                                   (quartet factor 4: 1345 s1,
        |                                    reverified 1346:74-76)
        v
  [B1] spread -> frame lower bound on the vanishing subspace
  [B2] off-line theft bound: |G(w)G(−w)| controlled by on-line averages
       for δ = |β−1/2|·log T ≤ c₀  (pinch reading: 1346:78-80 via 1350 L4)
  [B3] window decoupling: neighbor tails ≤ sinc²-decay (1346:74-75)
        |
        v
  windowMassBalance  ->  (1368 corridor, all green)  ->  SourceRH  ->  RH
```

| Lemma | Mathematical species | In-register assets | Must invent |
|---|---|---|---|
| B1 | finite-window Ingham / "BM-lite" frame bound for clustered nodes, constant c(A) explicit | prolate/Slepian machinery + numerics (law 7c(11); 1353 smoke rig: λ₁(J)=0.01103, λ₁(I∖J)=0.78098, lam1/pred=1.000 pre-locked) | the A-dependence of the lower bound |
| B2 | subharmonic theft bound in the strip + kernel ratio uniform on the vanishing class | CC20 explicit-estimate idiom; Bernstein-type pointwise bounds | uniform ratio bound for δ ≤ c₀/log T on the class |
| B3 | bandlimited gluing | sinc² tail scaling already located (1346:74-75) | nothing (mechanical) |

The contest algebra that must close at the end is already registered:
f*(A) = A/(A+2) (1360:80-83; A=0 forces zero near-line off-line
zeros; A=1 gives the 1/3 sanity threshold = H1's majority constant,
machine-checked as `fstar_one` in batch 1560). B1/B2 produce the two
saturating quantities; the f* geometry is where they meet. This plan
does not re-derive that algebra; it builds the analysis that feeds it.

## 3. Why self-creation is the only door (screened routes, with evidence)

| Route | Verdict | Evidence |
|---|---|---|
| Connes adelic migration | coordinates, not force | 1364: Q2 no subclass-positivity lemma exists (Goldfeld p.50); char-0 gap = same wall |
| Global Beurling-Malliavin / Seip theorems as-is | unusable | they need global density (D²) conditions on the real zero multiset; nobody has them; our window hypothesis is a log-scale SUBSTITUTE that must be proved finite-window |
| Maynard-Pratt / located density families | COLD | 1363 s3: output is count-type bounds, no cluster⇒exclusion-energy arrow; W1 seven-family scan A_tech = 0 (1360 s3) |
| Pure count assembly | DEAD-DIRECTION | 1353:140 (70.6x/145.7x); registered inside the 1368 leaf |

In 006's vocabulary this candidate is GENERATION-side (beat 0), not
sweep-side: no located family supplies the mechanism, so the mechanism
is invented against the registered consumer.

## 4. Two structural opportunities (why this bone is gnawable by us)

**O1 - the operator is already in the building.** B1's Gram matrix
`K_ij = sinc((γ_i−γ_j)W/2)` is the same integral-operator family as the
Slepian/prolate detector this project has run since 1224 (law 7c(11):
per-step eigenvalue decay ~ (C/n)²; 1353 smoke verified λ₁ against the
σ|J|/π prediction at ratio 1.000). We can already MEASURE the rank
deficit that clustering creates; B1 is the task of turning that
measurement into a proved lower bound with explicit A-dependence.

**O2 - the margin grows with height while the obstruction is constant.**
Per-window effective measurements scale like the occupancy band
[0.4993, 0.9433]·log T (DERIVED in 1360 from the Trudgian constants;
smooth figure 0.72·log(T/2π), 1350 s5), while the vanishing class is a
FINITE condition: `cc20TripleFiniteVanishingSet : Finset
CriticalVanishingPoint` (`ConnesWeilRH/Source/CC20RHExit.lean:21`).
Cluster-degenerate modes can be absorbed only up to a constant
codimension; N_eff − codim → ∞ with T. **Flag: O2 is a HEURISTIC
directional argument (linear absorption is assumed, not proved); P0
measures the true absorption.**

## 5. NM-loop compliance (006): beat map and promotion cards

| Beat | Status for candidate CB-HB1 | Where |
|---|---|---|
| 0 GENERATE | GENERATION-CARD filed: "prolate frame lower bound with explicit spread functional + subharmonic off-line theft bound, consumed by sourceRH_of_A2Bridge" | this record s1-s2 |
| 1 SWEEP | TO-RUN at P1 entry (literature retrieval only, never dialogue - external-AI directive 2026-09-03): Ingham 1936; Beurling-Malliavin; Levinson; Kahane; Seip (multiplicities); Isralowitz-Seip; Slepian/prolate concentration | this record s5 |
| 2 PRIOR-ART + TRANSLATION | PRIOR-ART-CARD provisional (families listed above; novelty delta = finite-window quantitative bound keyed to the spread functional A, plus off-line complex-node theft control on a finite-codimension vanishing class - to be sharpened by beat 1). B5-TRANSLATION-CARD filed: same-owner consumer = `C1H2Corridor.sourceRH_of_A2Bridge` (batch 1560 green); new lemmas = B1, B2, B3 | this record s2, s5 |
| 3 SCREEN | SCREENED-LIVE: typed no-go applicability checked - 1353's verdict kills the count-form bridge only; A_tech=0 confirms no located mechanism; falsifier registered = P0's negative control (below) | this record s5-s6 |
| 4 PROTOTYPE | = P0 (next section), two-control MODEL dry-fire, law-65: every digit a MODEL twin until Lean certification | s6 |
| 5 PREREG + PROVE | P1-P4; Stage-0 audit (criterion f) gates the ANALYTIC campaign weeks before P1 starts | s6 |

Two controls for P0 (criterion e), taken verbatim from the committed
1353 rig so rig fidelity is checkable against registered digits:

```text
  POSITIVE control: spread configuration I∖J  -> λ₁ ≈ 0.781, inequality
     must PASS with margin.
  NEGATIVE control: cluster configuration J    -> λ₁ ≈ 0.011, inequality
     must FAIL at the registered 70.6x/145.7x scale.
  A P0 rig that does not reproduce BOTH registered readings is
  INVALID-INSTRUMENT (no verdict may be drawn; repair first).
```

## 6. Phase plan

| Phase | Scope | Deliverable | Cost | Advance / kill |
|---|---|---|---|---|
| P0 | discrete closure certificate: min over vanishing-subspace g (‖g‖=1) of [on-energy − off-theft] vs f*(A)-scaled bound, on synthetic configurations across an A-grid | record 1370 (prereg: configuration families, A-grid, verdict bands, rig-fidelity gates - locked BEFORE any digit) + outcome record | 2-3 days, MODEL | CLOSES → P1 funded shape known; GAP-SHAPE → repair path named by the failing family; FAILS → kill-ledger row in 006 + A2-form re-adjudication |
| P1 | B1: finite-window frame lower bound, c(A) explicit (Gram/prolate: interlacing, Schur-complement, commutator estimates) | analytic theorem + conditional-theorem harvest at each intermediate strength | weeks | Stage-0 audited before campaign weeks (006 s7.3) |
| P2 | B2: subharmonic theft bound + kernel-ratio uniformity on the vanishing class (CC20 explicit idiom) | analytic theorem | days-weeks, parallel to P1 | independent of P0 outcome shape |
| P3 | B3: sinc² gluing assembly | lemma chain | days | mechanical after P1+P2 |
| P4 | Lean: instantiate hBridge_A2, run the 1368 corridor, official batch | GREEN certificate; stop-word check (1358 s4) | days | the only phase allowed to utter the stop word |

Subjective prior, flagged as such: P0 closes ≈ 70% (the f* algebra was
reverse-engineered for closure; the risk lives in absorption
nonlinearities O2 assumes away). P0 closing is NOT RH: P1 is the real
mathematics and carries the campaign's main risk.

## 7. Harvest rails (every phase pays)

Each phase produces register-able output independent of the final
closure: P0 = a measured failure/success geometry (the H3 margin-map of
1345 s5, at last with an instrument); P1/P2 = conditional theorems
("spread ≥ A ⇒ frame bound ≥ c(A)" at successive strengths); P4 = the
certificate itself. Law-65 stands over all digits. Nothing here
re-litigates the dead-route archive; the count-form bridge stays dead
unless new committed evidence appears (006 s6).

## 8. What this record does NOT change

003's route ruling, 004's endpoint scope, and 007's producer-target
repair are untouched. No Lean statement is added or amended. No number
is produced. RH is not claimed; the stop word remains the gate
certificate (1358 s4).

## 9. Next actions

1. Owner go-word "打 P0" → record 1370 prereg (configurations, A-grid,
   verdict bands, rig-fidelity gates including both 1353 controls) →
   run on the mirror rig → outcome record with the c(A)-vs-f*(A) table.
2. Beat-1 literature retrieval runs at P1 entry; its PRIOR-ART-CARD
   delta sharpens s5's provisional card.
3. README authority table gains the 008 row (this commit).
