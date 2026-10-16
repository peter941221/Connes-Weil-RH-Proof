# 2722C — Strip-envelope transport: identification rewrite plus artifact-tied cardinal pins (STRIP-TRANSPORT-GREEN; zero wired hypotheses removed, obligation relocated)

Verdict: the three quantified black-box strip premises of
`fourPointContradictionRowBWired2721C` (`hcontract`, `hquartic`,
`hquadratic`) are transported in Lean to pins on the EXPLICIT pipeline
cardinal sum, through the record-1958 identity
`laplaceAt_correction nodes seed y`. The transport is a rewrite, not
new analysis: the certified 2720 envelope object and the Lean
`laplaceAt` of the concrete finite-node correction are the SAME sum.
The wired variant `fourPointContradictionRowBWired2722C` now carries
TWO identification equalities plus THREE artifact-tied pins where the
parent carried three abstract-owner premises. No wired hypothesis is
removed; the strip obligation moves from an abstract owner to a
concrete finite sum whose certification exists at artifact grade.
Checker verdict STRIP-TRANSPORT-GREEN, 36/36 checks
(`results/2722c_strip_transport_tie.json`); Lean build green with the
five-declaration axiom census exactly `[propext, Classical.choice,
Quot.sound]`. No producer GO, no RH claim, map-103 freeze unchanged.

## 0. Binding-route audit (start-of-round declaration)

- Consumer: `fourPointContradictionRowBWired2721C` (the wired row-B
  contradiction inside the reopen-motion premise list). Downstream
  chain: selected detector `qw < 0` -> same-owner `qw >= 0` ->
  `SourceRH` -> Mathlib RH. This record acts on the `hcontract`/
  `hquartic`/`hquadratic` premises only.
- Owner: row B (gamma_2 = 21.022039638771556, N = 5, n = 3, lambda
  gate row 24), base = 8 target nodes with `y = 1`, correction = the
  56-node owner list with stored 1980 values (3 active).
- Current assumption: the record-2720 certified envelope constants
  (artifact `results/2720_p3_certified_strip_constants.json`, row B)
  dominate the weighted strip modulus of the corresponding cardinal
  sums; record 2722B froze the bridge-pin (triangle ladder) discharge
  route, routing the premises here.
- Premise effect: relocation, not removal — three premises replaced
  by two identification equalities + three pins (five named
  hypotheses), all machine-bound to committed sources by
  `scripts/check_strip_transport_2722c.py`.
- Failure criterion: (i) any transport lemma failing to rewrite
  through `laplaceAt_cardinalOwner`, (ii) a pin tie breaking against
  the committed 2720 renders in exact arithmetic, (iii) the envelope
  tail extension exceeding a wired pin anywhere in the registered
  scan range.
- Budget and stop: one Linux-native module build + one focused audit
  (measured: 43 s fresh compile, 1.3 s audit, footer 3865 jobs);
  checker full pass budgeted < 10 min wall (measured 34.11 s). Stop
  at GREEN artifact + landed module.

## 1. What it is, and why it is a rewrite (the key identity)

The wired premises quantify over the closed strip `sigma ∈ [0, 1]`,
`t ∈ ℝ`, at the Lean strip point `((sigma : Complex) + (t : Complex) *
Complex.I)`, bounding `‖laplaceAt base.test s‖`-type expressions with
weights `‖t / (2 * Real.pi)‖ ^ 4` (base quartic), `^ 2`
(correction quadratic), and a threshold form `64 ≤ |t| → ...`
(contract). Record 2720 instead certified constants for the model
cardinal sum

    cardinal(s) = sum_z (y z / (Q_z * laplaceAt seed 0))
                    * (nodeProduct z s * laplaceAt seed (s - z)),

`Q_z = prod_{w != z} (w - z)`, `nodeProduct z s = prod_{w != z}
(w - s)` — the sum whose per-term decay ladder `Psi_z = min(3 * Ez,
min_k Ez * D_k * 2^k / tau_z^k)`, `tau_z = |t - Im z|`, raised to the
tenth seed power, produces `C4_star`, `C2_star_corr`, `q_star_T64`.

The bridge is record-1958, verbatim (`laplaceAt_correction`, in
`ConnesWeilRH/Dev/C1ExplicitFiniteNodeCorrection.lean`):

    theorem laplaceAt_correction (nodes : Finset ℂ) (seed : CompactLogTest)
        (y : ℂ → ℂ) (s : ℂ) :
        laplaceAt (correction nodes seed y) s =
          ∑ z ∈ nodes, (y z / (nodeProduct nodes z z * laplaceAt seed 0)) *
            (nodeProduct nodes z s * laplaceAt seed (s - z)) := by ...

This is the pipeline cardinal in the SOURCE `exp (s * x)` Laplace
convention (record 1980's `cardinal_transform` is the same identity in
the normalized convention), so nothing had to be re-derived: `
cardinalOwner := correction`, `cardinalSum :=` the 1958 RHS, and the
identification theorem `laplaceAt_cardinalOwner` is a one-line
`exact laplaceAt_correction nodes seed y s`. The checker guards
`A1`/`A2` pin this: the captured call is literally
`laplaceAt_correction nodes seed y s`, and the `cardinalSum` body is
whitespace-token-identical to the 1958 RHS.

Why this shape was findable: 2722B's erratum (its section 7) corrected
the mechanism story — the 2720 envelope is a PER-TERM decay majorant
(`envelope_cell` sums `c_abs * MQ * Psi^10 * PAD_UP` over nodes), the
same triangle move the bridge pin makes. The gap between the two
prices is decay structure (pointwise, per-node, ten-factor), not
cancellation. That correction turned 2722C from "prove a new positive
object" into "rewrite through the existing 1958 identity".

## 2. Lean payload

Module `ConnesWeilRH/Dev/C1StripTransport2722C.lean` (imports:
`C1FourPointRowBWired2721`, `C1ExplicitFiniteNodeCorrection`; paired
audit `...Audit.lean`):

+------------------------------+----------------------------------------+
| declaration                  | role                                   |
+------------------------------+----------------------------------------+
| cardinalSum                  | the 2720 pipeline cardinal, as a Lean  |
|                              | def (1958 RHS verbatim)                |
+------------------------------+----------------------------------------+
| cardinalOwner                | the concrete strip owner: 1958         |
|                              | `correction nodes seed y`              |
+------------------------------+----------------------------------------+
| laplaceAt_cardinalOwner      | identification: laplaceAt of the owner |
|                              | IS the cardinal sum (= 1958 theorem)   |
+------------------------------+----------------------------------------+
| hcontractOfCardinalPin       | wired contract premise <- pin on the   |
|                              | explicit sum (rewrite + exact)         |
+------------------------------+----------------------------------------+
| hquarticOfCardinalPin        | wired quartic premise <- pin           |
+------------------------------+----------------------------------------+
| hquadraticOfCardinalPin      | wired quadratic premise <- pin         |
+------------------------------+----------------------------------------+
| fourPointContradictionRowB   | variant: two identification equalities |
| Wired2722C                   | + three cardinal-sum pins replace the  |
|                              | three abstract-owner premises; calls   |
|                              | the 2721C parent (untouched, 2ab       |
|                              | doctrine) via refine + three rewrites  |
+------------------------------+----------------------------------------+

The variant binders `hNorm`, `hIm`, `hvanish`, `hsupport`, `hgate24`,
`hprefix` are byte-identical to the 2721C parent (checker `A4`,
per-file region diff); the wired strip spellings (strip point, weight
exponents, threshold, pin constants, `Set.Icc (0 : Real) 1`) are
verbatim with measured counts 9/3/3/3/3/3/3/9 (checker `A3`, counts
taken from the compiled-good source, not guessed).

## 3. Build acceptance (Linux-native workspace, log content is the oracle)

    lake build ConnesWeilRH.Dev.C1StripTransport2722CAudit
    # footer: Build completed successfully (3865 jobs)
    # Built ConnesWeilRH.Dev.C1StripTransport2722C (43 s)
    # Built ConnesWeilRH.Dev.C1StripTransport2722CAudit (1.3 s)
    # lines beginning "error:"            : 0
    # "declaration uses sorry" / sorryAx  : 0
    # "#print axioms" records              : 5, every one exactly
    #   [propext, Classical.choice, Quot.sound]
    # warning lines in log                 : 300, ALL from cached-closure
    #   replay (grep intersection with the 2722C module paths = 0),
    #   per the log-replay law

## 4. Checker tie (`scripts/check_strip_transport_2722c.py`, 36 checks)

Numeric tie in exact `Fraction` arithmetic against the committed 2720
row-B renders (pinned row identity: `gamma == 21.022039638771556`,
`N == 5`):

+----------------+---------------------+--------------+---------------+
| premise        | 2720 certified      | wired pin    | margin        |
+----------------+---------------------+--------------+---------------+
| hcontract T64  | q*(64) 2.52482e-16  | 2.6e-16      | 7.5185e-18    |
| hquartic       | C4* 6.0524299e7     | 6.1e7        | 4.757e5       |
| hquadratic     | C2* 2.8161344e7     | 2.9e7        | 8.387e5       |
+----------------+---------------------+--------------+---------------+

Same-run anchor reproduction (the 2720 engine re-run inside the
checker): `C4`, `C2`, `q` anchor drift all `0.0` — the committed
renders are reproduced by the engine bitwise-in-float, so the pin tie
cannot hide a moved constant.

Tail extension (new obligation this record had to price): the 2720
scan stops at `TAIL_T = 600`, the wired pins quantify over ALL `t`.
Section C re-runs the same envelope formula (same constants, same
`certified_D_table` with its controls green, same 1.05 tail law) over
`t ∈ [600, 1e7]`, both signs, three channels:

+-------------------+--------------+-------------+-------------+-----------+
| channel           | max envelope | vs 2720     | vs wired    | mp tail   |
|                   | on [600,1e7] | star        | pin         | decreasing|
+-------------------+--------------+-------------+-------------+-----------+
| base_quartic      | 1.18990e-60  | 1.97e-68    | 1.95e-68    | True      |
| corr_quadratic    | 6.95742e-10  | 2.47e-17    | 2.40e-17    | True      |
| base_contract     | 1.17724e-68  | 4.66e-53    | 4.53e-53    | True      |
+-------------------+--------------+-------------+-------------+-----------+

Quantifier discipline: the verdict covers the REGISTERED scan (cells
of the 1.05 law from 600 to 1e7, both signs). Beyond 1e7 the fall-off
is the formula's own power law (`t^m * tau^-120 * t^p`, net exponent
negative on every channel since `m + p <= 55 + 4 < 120`), stated as a
tendency, not measured. Within the scan the last per-cell ratios are
representable floats (base ~4.9e-3 per cell, corr ~4.6e-2) and the
monotone-decrease gate runs in the engine's own mpmath precision.

Mutation controls (all feasibility-checked before shipping per the
control-feasibility law): a pin BELOW the certified render must be
rejected (`D1`: 60000000 vs C4* fails the tie — this is what caught
the 2721B mutation-control defect class); a weight-exponent rewrite
must fire the spelling guard (`D2`); a perturbed gate binder must
break the parent diff (`A4m`); the cubic weight spelling must be
absent (`A3m`).

## 5. Instrument note (disclosed restructure, anchor law 2b)

The first full run FAILED `C2_base_quartic_tail_decreasing` and
`C2_base_contract_tail_decreasing` while the smoke range (to 800)
passed. Diagnosis: the gate compared `float` renderings of the last
six cells; the base-channel envelope decays to ~1e-1100 there,
float64 renders both endpoints of every pair to `0.0`, and `0.0 <
0.0` reads as a plateau. The invariant (strict decrease) holds in the
engine's native mp precision for all three channels; corr_quadratic
had passed only because its decay kept the last cells representable
(~1e-257). Fix: compare mp-to-mp, render evidence as decimal strings
plus consecutive ratios. The object did not move; the reading did.
Law reinforced: tail evidence must be checked in the precision that
can SEE the values, never in a display float chain.

## 6. What this record does NOT do (residual obligations, named)

- Zero wired hypotheses removed. The three strip premises became five
  named hypotheses (`hbase`, `hcorr`, three pins). Nothing is
  discharged; the achievement is that all five are now about CONCRETE
  objects (the 1958 correction, the explicit cardinal sum) and are
  machine-bound to committed sources — the prerequisite for
  discharging them.
- Discharge list for later rungs: (a) instantiate `nodesB`, `nodesC`,
  `seed`, `yB`, `yC` at the stored row-B data and PROVE the
  identification equalities `hbase`/`hcorr` for the actual reopen
  witnesses (the record-2ay slab/support duty, still open); (b)
  certify the envelope inequality `‖cardinalSum ...‖ <= pin` in Lean
  — the D ladder, interval cells, and `PAD_UP` floats are
  artifact-grade today (this record follows the proxy-tie doctrine:
  the pins stay named hypotheses, the checker is the numeric tie);
  (c) the tail beyond the registered scan needs either a proved power
  law or a scan quantifier statement; (d) `hgate24`/`hprefix` are
  untouched black boxes (gate witness lane, records 2716-2719).
- The 2720 certification does not reach the CompactLog selected-owner
  health layer: this is the reopen-motion premise-shrinking lane, and
  the map-103 `DEAD_ON_CURRENT_FAMILY` freeze for the four-point B5
  family is unchanged.
- No producer GO. No RH claim. The numerics here are a transport tie,
  not a positivity result.

## 7. Erratum pointer

`docs/proofs/2722B_strip_pin_screen.md` section 7 (landed this round):
the 2720 envelope is a per-term decay majorant, NOT
cancellation-preserving; the 4.79e7 / 1.08e6 / 5.633e4 gaps price
decay structure, not cancellation blindness; all 2722B readings and
its scoped NO-GO verdict stand unchanged.

## 8. Reproduction

    python3 scripts/check_strip_transport_2722c.py          # ~34 s
    # artifact: results/2722c_strip_transport_tie.json
    # smoke mode (--smoke): same guards, tail scan truncated to [600, 800]
    python3 -I scripts/p3_certified_strip_constants_2720.py # upstream artifact

The artifact pins sha256 of both Lean modules, the 1958 and 2721
sources, the 2720 artifact, and the checker itself
(`864561dfbce06071e1353127cc28900d40ed4e16d0e410e6f1e9186109c59b3d`);
any edit to the checker invalidates the committed artifact and
requires a re-run.
