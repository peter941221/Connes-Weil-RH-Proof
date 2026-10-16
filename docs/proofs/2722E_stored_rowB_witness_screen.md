# 2722E — Stored row-B witness data-leg screen (STORED-WITNESS-DATA-LEG-GREEN; the finite-data, cap and pin legs hold on the stored configuration exactly; no node-set enlargement is required; the RH core is untouched)

Verdict: the witness question left open by the 2722D residual (1) is
decided on the stored class. The record-1980 row-B configuration — the
8 healthy targets, the 56-node owner and the stored correction values
at `gamma_2 = 21.022039638771556`, `re = 0.55`, `N = 5` — ALREADY
satisfies the shifted-triple finite-data condition exactly: the
targets contain `{1/2, 1, 3/2}` (binary64-exact dyadic values, stored
owner indices `[53, 54, 55]`), the stored correction `y` vanishes
there (`0j` exactly), the base coefficients are `1` exactly, and
`targets ⊆ owner` holds entrywise in exact rational arithmetic. Both
wired rho caps hold (`‖rho‖² = 442.228651 ≤ 484`, squared margin
`41.771349`; `|Im rho| = 5917178117733711 / 281474976710656 ≤ 421/20`,
exact margin `39350710127989 / 1407374883553280 ≈ 2.796e-2`). The
three cardinal-sum pins reprice on the stored lists IN THE SAME RUN to
bitwise the committed 2722C tie (anchors `rel 0.0`): C4 margin
`475701.37` (0.780% of the pin), C2 margin `838655.78` (2.892%), q
margin `7.518e-18` (2.892%); the 2722C tail extension over `[600, 1e7]`
re-anchors bitwise (`0.0` on all three channels) and sits at
`1.95e-68 / 2.40e-17 / 4.53e-53` of its pins, mp-strictly decreasing.
37/37 guards GREEN (`results/2722e_witness_data_screen.json`,
`scripts/witness_data_screen_2722e.py`, WSL python 3.12.3, 26.3 s).

What this decides: the finite-data and pin legs of
`fourPointContradictionRowBCarrier2722D` need NO new witness node
list — the stored row-B lists are the data-leg witness at model grade.
The binding legs of the reopen motion are therefore exactly
`{hgate24, hprefix}` (the RH core, frozen) plus the Lean-side bricks:
pin certification, exact capture of the stored lists, and the
model-seed / node-radius transfer. No wired hypothesis is removed by
this screen; no producer GO; no RH claim; the map-103
`DEAD_ON_CURRENT_FAMILY` freeze is unchanged.

## 0. Binding-route audit (start-of-round declaration)

- Consumer: the ten hypotheses of `fourPointContradictionRowBCarrier2722D`
  (record 2722D) at a concrete carrier `(targets, nodes, r, hr, y,
  rho)`. Downstream chain unchanged: selected detector `qw < 0` ->
  same-owner `qw >= 0` -> `SourceRH` -> Mathlib RH. This round acts on
  the 2722D residual (1) (witness instantiation) and consumes residual
  (4)'s tail machinery only as an anchor.
- Owner: the stored row-B lane configuration from the record-1980
  builder (`scripts/fourpoint_actual_owner_1980.py: healthy_targets,
  build_owner, target_value`), evaluated through the record-2720
  certified envelope engine (`p3_certified_strip_constants_2720.py`),
  at the same candidate `CANDIDATES[1]` as the committed rows.
- Current assumptions consumed: the committed 2720 artifact row B
  (`q_star_T64`, `C4_star`, `C2_star_corr`), the committed 2722C tie
  and tail extension, the wired pins/caps of
  `C1FourPointRowBWired2721` (`26 / 10^17`, `61000000`, `29000000`,
  `22`, `421 / 20`).
- Premise acted on: the witness-EXISTENCE question on the data-side
  legs. Screened, not removed: the pin hypotheses stay named in Lean
  (proxy-tie doctrine); the screen shows they are artifact-grade
  satisfiable on the stored lists, with quantified headroom.
- Measurable completion criterion: every leg machine-checked — exact
  Fraction membership/value predicates for `hsub`/`htri`/`hy`, exact
  cap comparisons for `hNorm`/`hIm`, same-run reprice bitwise-anchored
  against the committed artifacts, feasibility-checked mutation
  controls. Zero failures => `STORED-WITNESS-DATA-LEG-GREEN`.
- Budget and stop: one script, one artifact, no Lean build, no
  enlargement enumeration, no gate-matrix motion. Stop at the verdict.

## 1. Why the stored lists were built to pass the triple condition

The 2722D finite-data reading says the CC20 vanishing of
`(selectedOwner base correction 3).sourceTest` at the absolute triple
`{0, 1/2, 1}` is, through the record-1958 centered identity
`laplaceAt ... (s - 1/2) = y s`, the data condition

```text
{1/2, 1, 3/2} ⊆ targets ⊆ nodes,   y = 0 on the shifted triple.
```

The record-1980 healthy-target builder ends its list with
`0.5 + 0j, 1.0 + 0j, 1.5 + 0j` — the shifted triple in plain binary64
— and its correction-value function returns `0j` for exactly the three
active nodes `rho -> 1`, `1 - conj(rho) -> -1`, `rho + 0.5 -> -1`
being nonzero. So the stored model was constructed with the vanishing
triple from the start; the 2722D hypothesis `htri` is not an extension
demand on this witness, it is a property the witness already has. The
screen makes that machine-checked: `Fraction(0.5) = 1/2`,
`Fraction(1.0) = 1`, `Fraction(1.5) = 3/2` are exact (the triple
values are dyadic), so the capture into Lean will carry zero error
radius on these membership and vanishing data.

## 2. Results

```text
+----------------+----------------------------------+-------------------+
| leg            | predicate                        | measured          |
+----------------+----------------------------------+-------------------+
| htri           | {1/2,1,3/2} ⊆ targets            | owner idx 53-55   |
|                |                                  | exact, dyadic     |
| hsub           | targets ⊆ owner (8 of 56)        | entrywise exact   |
| hy             | stored y == 0j on triple         | exactly 0         |
| base y         | all base values == 1             | exactly 1         |
| hNorm          | ‖rho‖² ≤ 22² = 484            | 442.228651        |
|                |                                  | margin² 41.7713   |
| hIm            | |Im rho| ≤ 421/20 = 21.05        | margin ≈ 2.796e-2 |
| pin q          | q*(64) ≤ 26/10^17               | star 2.5248e-16   |
|                |                                  | margin 7.518e-18  |
|                |                                  | = 2.892% of pin   |
| pin C4         | C4* ≤ 61,000,000                 | star 60,524,298.6 |
|                |                                  | margin 475,701.4  |
|                |                                  | = 0.780% of pin   |
| pin C2         | C2* ≤ 29,000,000                 | star 28,161,344.2 |
|                |                                  | margin 838,655.8  |
|                |                                  | = 2.892% of pin   |
| tail [600,1e7] | all three channels ≤ pins        | ≤ 1.95e-68 /      |
|                |                                  | 2.40e-17 /        |
|                |                                  | 4.53e-53 of pin   |
+----------------+----------------------------------+-------------------+
```

Same-run anchors (section E3/E4): the recomputed stars equal the
committed 2720 renders with `rel 0.0`; the recomputed tail maxima equal
the committed 2722C renders with `rel 0.0`; the recomputed tie equals
the committed 2722C `numeric_tie` in every field (`E3.tie_equals_2722C`).

## 3. Acceptance (log evidence, not exit codes)

- Run: WSL python 3.12.3, numpy 2.5.3, mpmath 1.4.1 — the same engine
  and environment as the committed 2720/2722C runs, which is what makes
  the bitwise anchors achievable; elapsed 26.3 s.
- Guards: 37 boolean checks, 0 failures, artifact
  `results/2722e_witness_data_screen.json` carrying every guard value
  in `checks` (checker sha256 bound in `provenance`; the artifact was
  regenerated after the docstring hygiene edit and the hashes
  re-verified).
- Mutation controls (each shown feasible: the original passes the same
  predicate first): dropping the triple point `1` from a targets copy
  kills `htri`; flipping the stored `y` at owner index 53 kills `hy`;
  `Im = 21.06` kills `hIm`; a pin at `60,000,000` (below the certified
  star `60,524,298.63`) kills the C4 tie.
- First-run disclosure: the initial run died on the E2 cap parser — the
  regex `(\S+)` captured `421` from `421 / 20` and the spelling assert
  fired loudly (multi-token capture law, already recorded for this
  lane: a single non-space run never equals a spaced literal). Fixed
  with a whole-line capture before any artifact was trusted; the E1
  legs of that failed run were already all-GREEN and were re-verified
  bitwise in the fixed run.

## 4. Routing consequences

1. Witness search CLOSED on the data legs (model grade): no future
   work should re-enumerate node lists to satisfy `htri`/`hsub`/`hy`;
   the stored row-B lists pass, exactly and with dyadic-exact values.
2. The reopen obstruction is named and unchanged: `hgate24` (P5 gate
   sign) and `hprefix` (P2 prefix) — the RH core. The 2722D premise
   list is now fully adjudicated leg by leg: 5 legs pass at model /
   artifact grade (this screen), 2 are the frozen RH core, 3 remain
   Lean-side bricks.
3. Enlargement headroom quantified: any future witness that adds nodes
   to `targets` (e.g. a gate-index enlargement toward the tail-closure
   requirement) moves `Q_z`, the node products and the envelope, and
   must re-earn a 0.78% C4 headroom and 2.89% C2/q headroom; this
   screen is the reusable gate for that reprice (the registered class
   here is the stored configuration only — no enlargement class was
   priced).
4. Next rung unchanged in kind: the 2722D residual (2), pin
   certification inside Lean (2720 D-ladder + interval-cell envelope),
   then the capture bricks (exact-rational import of the stored 8/56
   lists and values; `explicitSeed` identification for the model seed;
   node-radius owner transfer).

## 5. Honest status

This is a screen, not a proof: `wired_hypotheses_removed = 0`. The
envelope certification is a sufficient-bound mechanism at model grade
(stored binary64 lists, model seed transform); passing it is artifact-
grade support for the pin hypotheses, never a discharged Lean theorem,
and a future failure of an enlargement reprice would likewise be a
certification failure, not a lower bound on the true cardinal sum (the
2722B erratum vocabulary applies). The map-103 four-point B5 family
remains `DEAD_ON_CURRENT_FAMILY`; nothing here changes route authority,
the producer status, or any RH claim.

Evidence: `scripts/witness_data_screen_2722e.py`,
`results/2722e_witness_data_screen.json`, this record, and the map-103
`## 2722E` section.
