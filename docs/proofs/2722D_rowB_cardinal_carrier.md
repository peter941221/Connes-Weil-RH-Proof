# 2722D — Row-B contradiction on the explicit cardinal carrier (CARRIER-INSTANTIATION-GREEN; four transport premises PROVED, not renamed; zero RH-core premises removed)

Verdict: the 2722C wired variant is instantiated at the record-1958
explicit cardinal carrier, and the four remaining transport-side
premises are DISCHARGED as theorems rather than assumed:
`hbase` and `hcorr` become definitional (`rfl`), `hvanish` becomes a
FINITE DATA condition on the node sets (contain the shifted CC20
triple `{1/2, 1, 3/2}` in `targets`, vanish `y` there), and `hsupport`
becomes the convolution support growth theorem with explicit radius
`5 * (2 * r + 1)`. The new theorem
`fourPointContradictionRowBCarrier2722D` carries ten named hypotheses:
the seven RH-core/pin hypotheses (`hNorm`, `hIm`, `hcontractPin`,
`hquarticPin`, `hquadraticPin`, `hgate24`, `hprefix`) plus the three
finite data conditions (`hsub`, `htri`, `hy`). Binder-diff against the
parent is machine-checked: removed = `{hvanish, hsupport, hbase,
hcorr}` exactly, added = `{hsub, htri, hy}` exactly.
Checker `scripts/check_rowB_carrier_2722d.py`, 36/36 GREEN
(`results/2722d_rowB_carrier.json`). Lean build green (footer
3866 jobs), 0 error, 0 sorry, 0 entry-path warnings, five-declaration
axiom census exactly `[propext, Classical.choice, Quot.sound]`.
No producer GO, no RH claim, map-103 freeze unchanged; the witness is
NOT produced (nodes stay quantified).

## 0. Binding-route audit (start-of-round declaration)

- Consumer: `fourPointContradictionRowBWired2722C` (record 2722C),
  itself calling the untouched 2721C parent. Downstream chain:
  selected detector `qw < 0` -> same-owner `qw >= 0` -> `SourceRH` ->
  Mathlib RH. This record acts only on the reopen-motion premise list
  of the wired row-B contradiction.
- Owner: the record-1958 cardinal carrier FAMILY
  `base = correction targets (explicitSeed r hr) (fun _ => 1)`,
  `correction = correction nodes (explicitSeed r hr) y`, row-B lane
  (gamma_2, N = 5, n = 3, lambda gate row 24). The family stays
  quantified in `targets`, `nodes`, `r`, `y`: this round converts
  ASSUMED transport premises into PROVED theorems of the family, it
  does not choose the witness.
- Current assumptions consumed: the 2722C variant and its parent
  (frozen, md5-bound by the checker's blob-continuity section); the
  1958 master interpolation brick
  `selectedOwner_explicit_base_and_correction_target`; the support
  growth law `convolutionIterate_convolution_support_subset_Ioo` and
  `halfDensityShift_support_subset` from the pinned CC20 lane.
- Premise effect (per the core-progress gate): FOUR named premises
  removed from the wired contradiction path — proved, not renamed:
  `hvanish`/`hsupport` discharged by two new theorems, `hbase`/`hcorr`
  by definitional equality. Three finite data conditions added in
  place of the analytic assumption content; net wired-list count 11
  -> 10 with the remaining items all concrete (pins on the explicit
  cardinal sum, gate/prefix RH core, rho caps).
- Measurable completion criterion: Linux-native build log acceptance
  triple (footer "Build completed successfully", zero `error:` lines,
  zero sorry) + five-declaration standard-trio census + 36/36 checker
  incl. binder-diff asserts and feasibility-checked mutation controls.
- Budget and stop: one module (final 247 lines) + paired audit,
  three focused lake builds (measured fresh compile 46 s, audit 1.3 s,
  footer 3866 jobs); checker < 1 s. Stop at GREEN artifact. No pin
  discharge, no witness instantiation, no gate motion this round.

## 1. What it is: the centered reading that makes vanishing FINITE

The wired `hvanish` demanded
`CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet`
of `(selectedOwner base correction 3).sourceTest`, i.e. vanishing of
the source test at the three absolute points `{0, 1/2, 1}`. Two pinned
facts turn this into data:

1. `healthyCC20TestSpace.mellinAt` IS `CompactLogTest.laplaceAt`
   (`healthyMellinReadoff`, definitional).
2. The 1958 master brick reads the carrier's source test at the
   CENTERED point: for every `s` in the target set,

   ```text
   laplaceAt (selectedOwner ... 3).sourceTest (s - 1/2) = y s
   ```

   (`selectedOwner_explicit_base_and_correction_target`, whose
   `sourceTest` unfolds through `halfDensityShift` — the centered
   identity carries the shift).

So the value of the source test at `w` is `y` at the shifted node
`s = w + 1/2`. Vanishing at `w ∈ {0, 1/2, 1}` is exactly

```text
y = 0   on the shifted triple  {1/2, 1, 3/2} ⊆ targets ⊆ nodes,
```

a FINITE membership-and-value condition — not an analytic premise.
(design-stage catch: for `w = 1` the node is `s = 3/2`, not `2`; the
shifted triple literal in Lean is `{(1 / 2 : ℂ), 1, (3 / 2 : ℂ)}`, and
the checker re-derives it in exact Fractions from the committed
`criticalVanishingPointValue` arms, section D.)

`hsupport` likewise: `explicitSeed_correction_support` gives the
carrier factor support in `Icc (-(2r)) (2r)`, widened to
`Ioo (-(2r+1)) (2r+1)`; the growth law at `n = 3` prices the base
`convolutionIterate` against the correction with
`radius = (3+1)*(2r+1) + (2r+1) = 5*(2r+1)`, and
`halfDensityShift_support_subset` preserves it. The coercion
`↑(3+1)` lands on the dyadic-free side via `norm_num` before `ring`.

`hbase`/`hcorr` need no motion: the variant is instantiated with
`base := cardinalOwner targets (explicitSeed r hr) (fun _ => 1)` and
`correction := cardinalOwner nodes (explicitSeed r hr) y`, so both
identification equalities are `rfl`.

## 2. The module

Five declarations (final module 247 lines):

```text
+--------------------------------------------+-------------------------------------+
| declaration                                | role                                |
+--------------------------------------------+-------------------------------------+
| shiftedCC20Triple2722D                     | the finite data set {1/2, 1, 3/2}   |
| carrierSourceTest2722D                     | named carrier = (...).sourceTest    |
|                                            | (line-layout def, see section 4)    |
| carrier_cc20Vanishes2722D                  | hvanish as theorem (cases p over    |
|                                            | the triple, transported through the |
|                                            | 1958 master brick)                  |
| carrier_sourceTest_support2722D            | hsupport as theorem, radius         |
|                                            | 5 * (2 * r + 1)                     |
| fourPointContradictionRowBCarrier2722D     | the instantiated contradiction:     |
|                                            | 10 named hypotheses, refine ...     |
|                                            | rfl rfl pass-through to 2722C       |
+--------------------------------------------+-------------------------------------+
```

Paired audit `...Audit.lean` prints all five axiom lists.

## 3. Acceptance (log evidence, not exit codes)

- Build 3 (final): footer `Build completed successfully (3866 jobs)`;
  `Built ConnesWeilRH.Dev.C1RowBCardinalCarrier2722D (46s)`,
  `Built ...Audit (1.3s)`; zero lines starting `error:`; zero
  `sorryAx`/`declaration uses sorry`; zero entry-path warnings (the
  log's 300 warnings are all cached-closure replay of imported
  modules). Axiom census: five records, each flattening to exactly
  `[propext, Classical.choice, Quot.sound]` (record lines and bracket
  contents counted separately).
- Iteration disclosure: build 1 failed with a 13-error dot-projection
  parse family (section 4, law 1) plus an unsolved `convert` goal
  (law 2); build 2 left one `ICgate` continuation-argument misattach
  (law 3); build 3 GREEN with the named-carrier def. All three reads
  came from the full log, never the wrapper exit code.
- Checker `scripts/check_rowB_carrier_2722d.py`: 36/36 GREEN,
  `verdict: CARRIER-INSTANTIATION-GREEN`, artifact
  `results/2722d_rowB_carrier.json` (checker sha256 bound in
  `provenance`). Sections: A transcription guards (triple literal,
  vanishing/support statements verbatim, pin quantifiers verbatim
  through `Set.Icc (0 : Real) 1` / `64 ≤ |t|` / `‖t / (2 * Real.pi)‖
  ^ 4 / ^ 2`, def-carrier occurrence count exactly 8 and NO unfolded
  carrier text in the main theorem, refine call verbatim); B binder
  diff (parent 11 labels, new 10 labels, removed/added sets asserted
  exactly); C six mutation controls, each shown feasible by the
  original passing the same guard first; D exact-Fraction derivation
  of the shifted triple from the committed CC20RHExit arms; E parent
  blob continuity (`git hash-object` == `HEAD` blob for the 2722C,
  2721 and 1958 modules).

## 4. Instrument laws (new)

1. Dot-projection line-layout law (Lean 4): in an argument position,
   `(term)` followed by a NEW LINE beginning `.field` is parsed as
   passing the token `.field` as an ARGUMENT, not as a projection —
   symptoms were `Unknown constant Complex.sourceTest` (the dot was
   re-dispatched against the inferred result type) and `Function
   expected ... applied to the argument .convolution`. Every dot
   accessor must stay attached to its closing paren on the SAME line.
   Diagnosed from the full 13-error list before touching anything.
2. Convert-cast closer law: `convert h using 1 <;> push_cast <;> ring`
   fails on `↑(3 + 1)` endpoint goals (push_cast leaves the numeral
   cast uncollected); the stable closer is an explicit
   `have hcast : ((3 + 1 : ℕ) : ℝ) = (4 : ℝ) := by norm_num`,
   `rw [hcast] at h`, then `convert ... using 1` with `ring` on the
   pure-integer endpoints. Linter note: once one goal remains, the
   style linter flags `<;>` (`(tac1; tac2)` would suffice) — write
   `all_goals ring` and keep the entry path warning-free.
3. Named-atom layout law for long carriers: a multi-line receiver
   term inside `f\n  (g ...).involution.convolution\n  (next-atom)`
   hands the trailing continuation line to the OUTERMOST function's
   argument list (`ICgate` absorbed the partially applied
   `.involution.convolution : CompactLogTest -> CompactLogTest`).
   When an instantiated term no longer fits one line, NAME IT (a
   `def` applied to a short argument list restores the parent's
   proven line layout at every site; defeq unfolds at default
   transparency so the parent call still accepts the hypotheses
   positionally, `rfl`-style pass-through).

## 5. Honest status and residual discharge list

What moved: FOUR transport-side premises of the wired row-B
contradiction are now theorems/definitional equalities — the first
premise removals on the 2721B/C/C-transport path since 2721C's hmult
(the transport premises were introduced as named hypotheses by 2722C
itself; proving them for the 1958 carrier family removes them from
the carrier instantiation).

What is NOT done (each a named residual, none closed by this record):

1. Witness instantiation. `targets`/`nodes`/`r`/`y` stay quantified.
   The concrete reopen witness must (i) include the shifted triple in
   its targets with `y = 0` there, (ii) re-price the three cardinal
   pins FOR ITS OWN node set — the 2720 D-ladder constants are row-B
   stored-list specific, and enlarging the node set changes the
   coefficient matrix, the node products `Q_z` and the envelope.
2. Pin certification. `hcontractPin`/`hquarticPin`/`hquadraticPin`
   remain named hypotheses on the explicit cardinal sum (proxy-tie
   doctrine 2657/2721B): their Lean-grade discharge still needs the
   2720 D-ladder + interval-cell envelope inside Lean, today
   artifact-grade only.
3. `hgate24` (P5 gate sign) and `hprefix` (P2 prefix) — the RH core
   itself — untouched, exactly as in 2721B/C/2722C.
4. Tail beyond the registered 2722C scan (`t ≤ 1e7`, stated tendency
   past it) and the ideal-vs-stored convention gap of the pins.

Route state unchanged: the map-103 four-point B5 family remains
`DEAD_ON_CURRENT_FAMILY`; this record operates in the reopen-motion
premise-shrink lane (binding route authority unchanged, so the only
route document touched this round is the map-103 section). No producer
GO; no RH claim.

Evidence: `ConnesWeilRH/Dev/C1RowBCardinalCarrier2722D.lean` (+
Audit), `scripts/check_rowB_carrier_2722d.py`,
`results/2722d_rowB_carrier.json`, this record, and the map-103
`## 2722D` section.
