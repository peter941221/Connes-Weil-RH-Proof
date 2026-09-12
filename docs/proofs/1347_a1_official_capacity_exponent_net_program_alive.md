# Record 1347 - A1 OFFICIAL: capacity exponent alpha = 0.988, NET-PROGRAM-ALIVE, fused with arXiv:2608.13637

```text
+---------------------------------------------------------------------+
| VERDICT QUALITY: OFFICIAL run, ESTIMATION class (no FIRE/NO-FIRE     |
| bands apply). All preregistered gates PASS incl. REPRODUCE at        |
| rel = 0.0 (bit-exact) and G9 path-equivalence at 0.0/0.0.            |
| Branch adjudicated per 1344 s3/s3a/s3b committed BEFORE digits       |
| (commits 7921dae, fca5a07): alpha_3pt = 0.9884 <= 1  =>              |
| NET-PROGRAM-ALIVE (tier-limited to m in {24,48,96}, NQ = 2^17).      |
| Model-level readout; the probe certifies nothing; RH NOT claimed.    |
+---------------------------------------------------------------------+
```

## 0. What this is / why / how (zero-base)

What: A1 asks - as we refine the bump NET (m test bumps filling the
prime-free window, then project away the 3m moment constraints), how fast
does the smallest eigenvalue lambda_min(m) of the Weil-form Gram decay?
That decay rate is the CAPACITY of finite compressions to carry strict
positivity on the vanishing class - i.e. whether "prove the gate
(0 <= qw(g)) by finding a positivity floor that survives net refinement"
is a program with room to run.

Why it matters: the gate is RH (1343/B0b machine-checked equivalence).
1335/1339 had already falsified CAPACITY on the Gamma-only model; A1 is
the first capacity measurement on the REAL G8 dictionary. And one month
ago the field's own compression method produced a landmark:
arXiv:2608.13637 (Alpoege-Furman; proof discovered by Claude; Lean 4
verified) gets >=2/3 of zeros simple+on-line by rank-trace + Sylvester
inertia on a FINITE COMPRESSION of Weil's Hermitian form - a proportion,
not ALL. The open method-level question "why does compression top out at
a proportion?" is exactly what an alpha reading speaks to (1344 s3b).

How: 1344 s3 prereg (m in {24,48,96}, NQ-rule 10*DX <= w_b, verbatim
1342 path for m=24 + doubling, sparse-refactored fast path for m=48/96
gated by G9 full-Gram equivalence, REPRODUCE gate against the committed
1342 digit). Script: docs/proofs/1344_a1_m_scaling_probe.py; runner
1344_a1_official_runner.sh (numpy==2.5.3 / mpmath==1.4.1 fidelity pins);
batch 1547; log docs/proofs/1547_1344_a1_official.log; sentinel
"DONE 1344-A1"; wall 1153.7 s (budget 4 h; 1/12 spent).

## 1. Official digits (log-parsed, verbatim)

| m | NQ | lambda_min | lambda_2 | path | gates G3a/G3b/G5/G7 |
|---|---|---|---|---|---|
| 24 | 2^17 | +3.0832438870712037e-03 | +3.7871787e-03 | verbatim | T/T(2.51e-17)/T(1.57e-13)/T(3.59e-16) |
| 48 | 2^17 | +1.559255371407266e-03  | +1.9320679e-03 | fast (G9-admitted) | T/T(1.40e-17)/T(5.92e-14)/T(6.94e-16) |
| 96 | 2^17 | +7.833531534466537e-04 | +9.7403850e-04 | fast (G9-admitted) | T/T(8.00e-18)/T(1.20e-14)/T(2.47e-16) |

- REPRODUCE (m=24, verbatim): rel = 0.00e+00 vs committed
  0.0030832438870712037 from 1342_falsifier_results.json (parsed at
  runtime, constants-are-DATA). Bit-exact under the pinned environment.
- G9 (full m=24 Gram, both paths): max|dB|/(1+|B|) = 0.0,
  |dlambda|/(1+|lambda|) = 0.0 -> fast path admitted at BIT level
  (the sparse prime-sum refactor is exactly equivalent in value here).
- DOUBLING (m=24, verbatim, NQ 2^17 -> 2^18): 3.083243887e-03 ->
  3.083243849e-03, delta = 3.85e-11 < 1e-8 gate: PASS (same magnitude as
  the 1342 G4 witness delta 3.85e-11 - the grid-convergence fingerprint
  is stable across objects).
- G8 control (once, anchor grid, inv12 ladder): gap 2.10e-07, drift 0.0
  (ladder 800/1600) PASS; G1a provenance rel 2.10e-07 PASS; G1b arch dev
  4.26e-16 PASS.
- No escalation: lambda_min > 0 at every m; the s3a sign-flip clause
  never armed.

## 2. Capacity exponent and branch adjudication

```text
 alpha_3pt   = 0.98836   (log-log LSQ over m in {24,48,96})
 pre-factor  c = 7.138840e-02   (lambda_min(m) ~ c * m^-alpha)
 pairwise    alpha(24->48) = 0.98359   alpha(48->96) = 0.99312
 branch (1344 s3, locked): alpha <= 1 with stable positive sign
   ==> NET-PROGRAM-ALIVE
```

Reading rules committed in s3b, applied:

- REGISTERED (model grade): on the G8 dictionary and the vanishing
  subclass, the finite compression does NOT capacity-starve at these
  tiers - lambda_min decays marginally slower than 1/m, never
  super-linearly. The uniform-positivity-by-nets program is not
  provably dead by capacity on this object; the next prereg (uniform
  constant route) is JUSTIFIED, not yet funded.
- HONESTY RAIL 1 (boundary risk): 0.9884 is 1.2% from the branch
  boundary 1, and the pairwise slope is RISING toward it (0.9836 ->
  0.9931, +0.0095 per m-doubling). Three points cannot exclude the
  limit alpha(m) -> 1 or a crossing deeper in the ladder. The verdict
  is explicitly TIER-LIMITED; the deeper tiers m = 192/384 are the
  resolving measurement (cost below).
- HONESTY RAIL 2 (what alpha does and does not mean): alpha is a
  property of THIS bump basis at THIS support radius (R = log2/2 - 0.01,
  realized 0.3230/0.3294/0.3328 vs bound 0.336574); it is not a theorem
  about all admissible test families, and it says nothing about the
  gate's truth value. A positive lambda_min at three tiers is expected
  under RH-true either way; the ALPHA is the quantity with program
  meaning (slack exponent vs collapse exponent for limit-exchange
  estimates of the L4 Fork B type, 1340).
- Three-way interpretive map for the uniform-constant route: alpha < 1
  bounded away => polynomial slack (best case for limit exchanges);
  alpha -> 1 (critical) => harmonic/logarithmic delicacy (every
  epsilon costs a log; proof possible but knife-edge); alpha > 1 =>
  capacity-dead on this ladder (1344 s3 branch, mirror of 1339). The
  present data sit between the first two labels, closer to critical.

## 3. Fusion reading of arXiv:2608.13637 (per 1344 s3b, rails included)

What their Appendix B states (deep read, committed quotes): the negative
index of any finite compression of Weil's form (prime side) is
IDENTICALLY ZERO, so all negativity flows from off-line zeros; their
engine is the DUAL positive-eigenvalue count (Sylvester + Cauchy-Schwarz
+ rank-trace tr P + 2n_+(Q) <= N(I) + O(sqrt(T) log T)), ceiling 2/3
(0.6725 with the Montgomery-Taylor window), inputs Aryan [Ary22] and
BGSTB second moments.

Species-level fusion (MODEL grade, non-transferable by construction):

```text
 their object: compression on ALL even test functions, supp <= log X,
   observable = PROPORTION of zeros -> ceiling 0.6725 at T -> inf
 our object:   compression ON THE VANISHING CLASS (3m moment kills),
   observable = GATE-floor lambda_min(m) -> exponent 0.988 (this run)

 s3b branch applied (NET-PROGRAM-ALIVE side): at the measured tiers the
 compression species does NOT capacity-starve on the gate observable.
 Therefore, IF a ceiling exists for the species, it is NOT attributable
 to compression capacity on our subclass; the proportion ceiling of
 2608.13637 is then evidence about ANALYSIS SLACK in their observable
 (inertia-count factor 2 + mean-value constant 3/4), not about a
 structural capacity wall. This is a MAP statement, not a transfer
 theorem: the two compressions live on different subspaces and measure
 different functionals.
```

Cross-check note for the backlog: their route to 1/2->2/3 (dualizing an
EMPTY index-bound attack) is structurally the same maneuver as our
record 1345 N1 (dualizing the falsifier probe into a lossless
sampling-contest restatement) - independent recurrence of the
"bound-fails => count-positively" move in the same form species;
logged as AGENTS 7c(72) material.

## 4. Portfolio consequences

1. Task #7 CLOSED. A1 consumed its prereg; the probe is SPENT (a deeper
   ladder is a NEW prereg, see 2).
2. Proposed next prereg "A1b deeper tiers": m in {192, 384}, NQ rule
   forces 2^18 / 2^19 (margins 1.30x / 1.30x); fast path G9-admitted,
   estimated cost m=192 ~15-20 min, m=384 ~2-2.5 h - total inside a
   4 h budget. Objective: resolve alpha < 1 (bounded) vs alpha -> 1
   (critical) vs crossing, with pairwise drift as the discriminating
   statistic. AWAITING OWNER FUNDING - not started.
3. Fusion (s3b) DELIVERED: branch NET-PROGRAM-ALIVE, tier-limited,
   rails in s2. The Alpoege-Furman method ceiling now has a measured
   counterpart on the gate observable, and the "why not ALL" question
   is sharpened to slack-vs-wall with our alpha as the discriminator.
4. Backlog order unchanged (1344 s3b): C7 H1/H2 harvest, A3 audit of
   arXiv:1703.03827, thermometer remaining families (explicit S(T)
   primary parse; short-interval existence reformulation), Lean brick
   for the (★)-uniform <-> SourceRH chain (1345 s2 - now also covering
   the "same-species" framing vs 2608.13637).
5. First-wave sweep readout (task #9, owner question "先打C7"): five
   candidate families checked at primary-abstract level
   (Maynard-Pratt 2206.11729 - vertical only, conditional density;
   Guth-Maynard via 2607.04632 - integrated, far-region; Alpoege-Furman
   2608.13637 - integrated proportion; GGOS/Chirre - on-line gaps;
   Lemke Oliver log-free - integrated). NONE gives near-line LOCAL
   majority exclusion; COLD-STRUCTURAL (1346 s5) SURVIVES first contact
   with the 2026 frontier. Task #9 rest to backlog.

## 5. What this record does NOT claim

- Not that the gate is true, false, or approachable; alpha is a
  property of one bump ladder on one subclass (rails in s2).
- No transfer between 2608.13637's theorem and our objects in either
  direction (s3 rails); their Lean-verified result is untouched.
- No RH claim; all grades MODEL per repo law. Estimation class: no
  verdict bands were consumed or producible.
- The 0.988 is not an asymptotic statement: three points, tier-limited,
  boundary at 1 within 1.2% with rising pairwise drift.

## 6. Artifacts

- docs/proofs/1344_a1_m_scaling_probe.py (importlib 1342-verbatim reuse;
  fast prime path; G9; commit 7921dae)
- docs/proofs/1344_a1_official_runner.sh (batch 1547, fidelity pins)
- docs/proofs/1547_1344_a1_official.log (acceptance source, DONE
  1344-A1 sentinel, 1153.7 s)
- docs/proofs/1344_a1_results.json (all digits, gates, spectra)
- 1344 charter s3a + s3b (implementation amendment + fusion
  pre-declaration; commits 7921dae, fca5a07)

## 7. Next steps

1. Owner decision: fund A1b (m=192/384, ~3 h) to settle the
   criticality of alpha - it directly prices the uniform-constant
   prereg.
2. If A1b confirms alpha < 1: draft the uniform-constant route prereg
   (L4 Fork B bridge, 1340 family-general PositiveTraceOperatorLimit).
3. Lean brick (1345 s2 chain, incl. the (★) species framing) can start
   in parallel with any owner choice - it is verification, never
   falsifiable by digits.
