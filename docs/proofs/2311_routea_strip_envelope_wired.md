# 2311 — STRIP-ENVELOPE-WIRED: the certified 2303 strip envelope is pinned in Lean and consumed by the producer through a machine-checked join

Record 2303 certified the centered-strip envelope on the corrected
width-a^2 owner at artifact grade (continuum sup 2823660.8460007603 =
certified grid maximum times the log-derivative transfer factor, margin
3.3666x under the frozen bUpper2243), and registered two missing pieces:
the certificate interface and the owner bridge.  This record lands the
interface: the two certified factors are pinned as exact rational
constants in `C1RouteAItem5Arithmetic.lean`, their product below
`bUpper2243` is proved by `norm_num`, and the producer gains a consumer
whose strip input is the certified envelope shape:

    frozenStripHypothesis_of_certified_envelope:
      min(D2_b M_c, D2_c M_b)(sigma) <= stripGridMax2303 * stripTransfer2303
        for all sigma in [-1/2, 1/2]            (2303 envelope, artifact)
      stripGridMax2303 * stripTransfer2303 <= bUpper2243
                                                 (machine-checked join)
      ----------------------------------------------------------------
      FrozenStripHypothesis b c

Verdict: **STRIP-ENVELOPE-WIRED** — the envelope arithmetic is
machine-checked (standard axioms only), the pin soundness and tightness
are machine-checked against the committed artifact in exact rational
arithmetic, and the residual trust is exactly the named envelope bound
plus the owner bridge.  No Lean formalization of the 2303 reduction
itself, no owner bridge, no producer GO, no RH claim.

+--------------------------+-------------------------------+---------------+
| pinned Lean constant     | value                         | source record |
+--------------------------+-------------------------------+---------------+
| stripGridMax2303         | 2644542.8515                  | 2303          |
| stripTransfer2303        | 1.0677312                     | 2303          |
| join (product le bUpper) | 2823660.912... <= 9506275.10  | norm_num      |
+--------------------------+-------------------------------+---------------+

## Pin soundness and tightness (exact rational check)

The pin check `scripts/routea_strip_envelope_lean_pin_2311.py` reads the
Lean source, extracts the two literals, and verifies in `Fraction`
arithmetic against `results/2303_corrected_strip_envelope.json`:

+----------------+------------------------------+-----------+------------+
| pin            | soundness reference          | slack     | ulps       |
+----------------+------------------------------+-----------+------------+
| stripGridMax2303 | render 2644542.851480454    | 1.9546e-5 | 4.2e4      |
|                | (centered.max_point_B)       |           |            |
| stripTransfer2303 | render 1.0677311749439153  | 2.5056e-8 | 1.1e8      |
|                | (grid.transfer)              |           |            |
| product        | rendered product             | 6.6283e-2 | 1.4e8      |
+----------------+------------------------------+-----------+------------+

Each pin is an upper of the committed float64 render with slack above 100
ulps of that render (measured 4.2e4 / 1.1e8 / 1.4e8), so the direction is
safe under any render rounding; tightness bars are 1e-3 (grid maximum),
1e-6 (transfer), 0.1 (product).  The artefact's own last multiply is
internally consistent: the rendered product matches
`centered.sup_certified` to 1.08e-15 relative.  Join: pinned product
2823660.912283517 <= bUpper2243 at margin 6682614.19030081, ratio
3.366648970218073 — matching the certified 3.36664904924696 to 8e-8
relative (the pin round-up shifts it down by construction).  The Lean
side proves the same inequality on these exact rationals by `norm_num`.

## Lean acceptance (record 2311)

+--------------------------------+--------------------------------------+
| artifact                       | reading                              |
+--------------------------------+--------------------------------------+
| C1RouteAItem5Arithmetic.lean   | +2 defs, +1 join theorem             |
| C1RouteAProducerWired.lean     | +1 conversion, +1 producer variant   |
| C1RouteAItem5ArithmeticProbe   | +1 #print axioms                     |
| C1RouteAProducerWiredProbe     | +2 #print axioms                     |
+--------------------------------+--------------------------------------+

Targeted build log `build_2311_step1.log`: `Build completed successfully
(3572 jobs)`, zero `error:` lines, zero `sorryAx`, zero `declaration uses
'sorry'`, zero warnings from the touched files.  All three new
declarations print the standard axiom trio
`[propext, Classical.choice, Quot.sound]`:

    stripGridMax2303_mul_stripTransfer2303_le_bUpper2243  ...
    frozenStripHypothesis_of_certified_envelope            ...
    a005_item5_producer_wired_certified_multiplicity_gap_split_envelope ...

Root aggregate log `build_2311_root.log`: `Build completed successfully
(4244 jobs)`, zero `error:` lines, zero `sorryAx`, zero `declaration uses
'sorry'`, zero warnings from the touched files, same axiom trio for the
three new declarations in the replayed probe output.

## What this changes for the route

- The producer's strip input no longer needs the full 2243 cap: any pair
  whose centered-strip min-product is bounded by 2823660.912 satisfies
  `FrozenStripHypothesis` by a machine-checked chain.  The certified 2303
  envelope supplies exactly that bound on the captured owner at artifact
  grade, a 3.37x tighter envelope than the frozen constant.
- The new consumer
  `a005_item5_producer_wired_certified_multiplicity_gap_split_envelope`
  takes the envelope hypothesis in place of `hstrip` and otherwise
  consumes the 2310 certified gap split and the 2274 multiplicity
  discharge; the original conditional theorems remain for existing
  callers.
- The remaining strip-lane obligations are now exactly: the envelope
  bound `henvelope` itself (artifact-grade reduction on the captured
  owner; the 2303 non-claim "does not formalize the strip certificate" is
  now narrowed to "the certificate's terminal arithmetic is formalized,
  the reduction is not"), and the owner bridge (identification of the
  captured owner with the selected Lean test functions).

## Non-claims

- The 2303 reduction (pavement, zero-count gate, coefficient inflation,
  grid, transfer) is consumed as a named hypothesis; it is artifact-grade
  analysis, not Lean-formalized.  In particular the transfer law
  `|d/dsigma log N| <= 2 rmax` is only a registered derivation here.
- The pins are render-rounded uppers; the render conventions (float64
  renders of the 256-bit MPFR reduction) are inherited, and the pin slack
  is machine-checked against them.
- The owner bridge is not done: nothing identifies the captured owner
  with the selected Lean test functions, and no Lean statement here
  mentions the captured families.
- The signed margin, the non-tail charge, and the certified gap split
  remain open; no producer GO, no gate sign change, no RH claim.

## Provenance

- Lean: `ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean`,
  `C1RouteAProducerWired.lean` and their probes.
- Check: `scripts/routea_strip_envelope_lean_pin_2311.py` ->
  `results/2311_strip_envelope_lean_pin.json` (verdict
  PINNED-ENVELOPE-VERIFIED; controls: synthetic parse, join direction,
  negative shifted-pin rejection).
- Upstream certificate: `results/2303_corrected_strip_envelope.json`
  (record 2303, CORRECTED-STRIP-COVERED).

Next registered obligation: the owner bridge (identify the captured owner
with the selected Lean test functions), then the strip envelope's
analytic core (the transfer law as a Lean derivation), the signed margin,
and the non-tail charge; the selected-owner signed inequality remains the
summit.