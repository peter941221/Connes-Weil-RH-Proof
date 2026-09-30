# 2310 — GAP-CLOSURE-WIRED: the certified hgap split is pinned and joined in Lean; the producer consumes window + tail enclosures with the join arithmetic machine-checked

Record 2309 closed hgap at numeric grade end to end (window 477248.99 +
tail 1.96e-27 <= 1e7).  This record moves that closure into Lean: the two
certified uppers are pinned as exact rational constants in
`C1RouteAItem5Arithmetic.lean`, their join below `gapCharge2255` is proved
by `norm_num`, and the producer gains a consumer that replaces the single
opaque gap hypothesis by the registered 2275/2286/2304 decomposition plus
the two pinned enclosures:

    hgap_of_certified_split:
      gap <= windowCharge + tailCharge        (2275/2286/2304 split)
      windowCharge <= windowCharge2309        (2308/2309 certificate)
      tailCharge   <= tailCharge2307          (2307 certificate)
      ----------------------------------------------------------------
      gap <= gapCharge2255                    (1e7 budget)

Verdict: **GAP-CLOSURE-WIRED** — the join arithmetic of the certified
uppers is machine-checked (standard axioms only), the pin soundness and
tightness are machine-checked against the committed artifacts in exact
rational arithmetic, and the residual trust is exactly the three named
pieces above.  The split and the two numeric enclosures remain named
obligations; no Lean formalization of the certificates themselves is
claimed.  No producer GO, no gate sign change, no RH claim.

+--------------------------+----------------------------+---------------------+
| pinned Lean constant     | value                      | source record       |
+--------------------------+----------------------------+---------------------+
| windowCharge2309         | 477248.98581176            | 2308 + 2309         |
| tailCharge2307           | 0.000000000000000000000000002 | 2307            |
| join () le gapCharge2255 | 477248.98581176 <= 10000000 | norm_num (exact)   |
+--------------------------+----------------------------+---------------------+

## Pin soundness and tightness (exact rational check)

The pin check `scripts/routea_gap_closure_lean_pin_2310.py` reads the Lean
source, extracts the two literals, and verifies in `Fraction` arithmetic:

+----------------+-----------------------------+------------+-------------+
| pin            | soundness reference         | slack      | bar         |
+----------------+-----------------------------+------------+-------------+
| windowCharge2309 | 45-digit directed-ceiling render of the | 2.575e-9 | (0, 1e-6] |
|                | certified interval upper (2309 den256)   |          |           |
| tailCharge2307 | float64 render 1.9586382184619955e-27   | 4.136e-29 | (1e-30,   |
|                | (2307 best rung, order 36)              |          | 1e-26]    |
+----------------+-----------------------------+------------+-------------+

The window reference is the render itself an upper of the exact binary
endpoint: `interval_text` renders the upper endpoint with `ROUND_CEILING`
at 45 significant digits (record 2294 convention), so
`pin >= render >= exact upper >= true charge` is chained by construction
and the pin comparison is an exact rational inequality.  The tail
reference is the stored float64 render; the pin slack 4.136e-29 sits 17
orders above the half-ulp bound of that render (<= 2.2e-43), so the
direction is safe under the declared float64 rendering model.  The
render-vs-float cross-reading of the window artifact is 5.82e-11
(consistency of the two committed renderings).

Join: 477248.98581176 + 2e-27 = 477248.98581176 (the tail is far below
the pin's own decimal resolution) <= 1e7 at margin **9522751.01418824**,
ratio **20.953423259749517** — matching the 2309 closure ratio
20.953423259749634 to 1.2e-13 (the pin's round-up shifts it down by
construction).  The Lean side proves the same inequality on these exact
rationals by `norm_num`.

## Lean acceptance (record 2310)

+-----------------------------------------------+--------------------------+
| artifact                                      | reading                  |
+-----------------------------------------------+--------------------------+
| C1RouteAItem5Arithmetic.lean                  | +2 defs, +2 theorems     |
| C1RouteAProducerWired.lean                    | +1 producer theorem      |
| C1RouteAItem5ArithmeticProbe.lean             | +2 #print axioms         |
| C1RouteAProducerWiredProbe.lean               | +1 #print axioms         |
+-----------------------------------------------+--------------------------+

Targeted build log `build_2310_step1.log`: `Build completed successfully
(3572 jobs)`, zero `error:` lines, zero `sorryAx`, zero `declaration uses
'sorry'`, and zero warnings attributable to the four touched files (the
66 warning lines in the log all belong to pre-existing Source modules
already carrying them).  Both probes print the standard axiom trio
`[propext, Classical.choice, Quot.sound]` for every printed declaration,
including the three new ones:

    windowCharge2309_add_tailCharge2307_le_gapCharge2255  ...
    hgap_of_certified_split                              ...
    a005_item5_producer_wired_certified_multiplicity_gap_split ...

Root aggregate re-verify log `build_2310_root.log`: `Build completed
successfully (4244 jobs)`, zero `error:` lines, zero `sorryAx` (both
greps), zero `warning:` lines from the four touched files, and the same
axiom trio for the three new declarations in the replayed probe output.
The 4195 warning lines in the root log all belong to pre-existing Source
modules (long-line style lints in the CCM25Concrete family).

The pin check ran clean on the first pass: verdict
PINNED-UPPERS-VERIFIED, all seven transcription guards true, controls
pass (synthetic parse, join direction, negative shifted-pin rejection);
artifact `results/2310_gap_closure_lean_pin.json` records the Lean md5s
cb124d1c97e90cd32b9a207ab12e2339 and d31862e8739d21c13a2e300a728384c5.

## Registrations updated

- The 2305/2307/2308-registered **localized [-2, 2] instrument (window
  successor) is retired**: it was named as a response to the precision
  wall of the global mesh (float64 owner transforms blind past |x| ~ 1,
  per-prime intervalization dead without grouping).  The regenerated
  evaluator (2301, extended coordinates) and the grouped S-moment ladders
  (2308, the 2291 law one level deeper) removed that wall, and the global
  dyadic mesh is now certified end to end over [-40, 40] with a 21x
  margin.  Localization is no longer on the critical path for closure;
  any future window-lane work is tightening, not certification.
- The producer's residual set is now: `hstrip` (2274-era strip envelope,
  2303 corrected owner), `hmargin` (2249 L1 enclosure), `hcharge-rest`
  (2109 known-error ledger), and the gap pair `hsplit` +
  `windowCharge <= windowCharge2309` + `tailCharge <= tailCharge2307`, the
  last two each backed by one certified numeric artifact chain.

## Non-claims

- The 2275/2286/2304 decomposition is consumed as a named hypothesis; it
  is registered analysis, not Lean-formalized.
- The two numeric enclosures remain artifact-level certificates (the
  2308/2309 window chain and the 2307 tail chain); this record pins and
  joins them, it does not re-derive them, and does not formalize them in
  Lean.
- The pinned decimals are the certified-upper renderings rounded up; the
  rounding-up is the sound direction and its slack is machine-checked
  against the committed artifacts, but the render conventions themselves
  (`interval_text` ceiling; float64 render model) are inherited.
- The strip, signed margin, and non-tail charge hypotheses remain open;
  no producer GO, no gate sign change, no RH claim.

## Provenance

- Lean: `ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean` (md5
  cb124d1c97e90cd32b9a207ab12e2339), `C1RouteAProducerWired.lean` (md5
  d31862e8739d21c13a2e300a728384c5) and their probes.
- Check: `scripts/routea_gap_closure_lean_pin_2310.py` ->
  `results/2310_gap_closure_lean_pin.json` (verdict
  PINNED-UPPERS-VERIFIED; controls: synthetic parse, join direction,
  negative shifted-pin rejection).
- Upstream certificates: `results/2309_hgap_transform_certified.json`,
  `results/2309_transform_step_den256.json`,
  `results/2307_hgap_tail_certified.json`.

Next registered obligation: the strip lane's formally checked interface
(following `C1RouteAMultiplicityBound`'s discharge pattern for the 2267/
2303 envelope), and the owner-identification bridge of the 2275 capture;
the selected-owner signed inequality remains the summit.