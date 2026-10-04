# Record 2570 — Cell2700 minus chain regenerated at the correction pair

Verdict: CORRECTION-PAIR REGENERATED. The cell2700 sigma = -1/2
correction-second certificate chain now exists as eight Lean modules
instantiated at the record-2338 `ideal_correction_coefficient` pair
(correction midpoints, 1e-28 per-family charge): the committed base-pair
certificates of 2563/2565 stand untouched, and the correction consumer of
the 2560 two-channel reduction has its own green chain
(`corrSecondCell2700MinusSummand_le_2570`: the 2562 three-piece summand of
the correction-coefficient function is at most 414652489/12500000000 =
3.317219912e-2 on cell 2700). All audited theorems carry exactly the axiom
trio [propext, Classical.choice, Quot.sound].

## What was built

`scripts/generate_correction_pair_2570.py` re-derives every layer of the
2565 chain through the 2567 remainder law (token-substituted generator
clones, executed), with three parameter changes and nothing else: the
coefficient-row key (`ideal_base_coefficient` -> `ideal_correction_coefficient`),
the center/error names (`baseCoefficient*2540` -> `correctionCoefficient*2570`
with the 1e-28 error), and the charge (1e-30 -> 1e-28). Position-keyed tables
(exp inputs, factors, rounded jets, the 90 third-envelope leaves) are
imported unchanged - they are coefficient-independent.

Modules emitted (all green, axiom trio audited):

- `C1RouteACorrectionCoefficientBoxes2570` - the 30 correction boxes.
- `C1RouteACorrectionCenterNode2570` - correction centers, the 1e-28 error,
  membership and error-of-box bridges.
- `C1RouteACorrMidpointDerivatives2570` - renamed copy of the
  coefficient-independent midpoint derivative leaves.
- `C1RouteACorrMidpointBounds2700Minus2570` - order-2 midpoint lane,
  5 theorems.
- `C1RouteACorrFirstJetMidpointMinus2570` - order-1 lane, 6 theorems.
- `C1RouteACorrSharedN02700Minus2570`, `C1RouteACorrSharedN02701Minus2570`
  - endpoint norms, 4 theorems.
- `C1RouteACorrectionSecondCell2700MinusCorr2570` - the assembly with the
  L1 bridge, aggregate, curvature and three-piece summand theorems.

Uppers: midpoint 305872159/12500000 (24.46977272), first jet
30638167/50000000 (0.61276334), endpoints 153245019/10^10 and
77279669/5000000000, third L1 aggregate 1270.647757874788 (chunked
literal, round-trip exact). The assembled cell bound
414652489/12500000000 covers the piece sum 0.033172199119954 with 4.6e-14
slack, and sits 1.0000000069x the 2569 external repricing bound as
expected from the 1/10^7 rounding quanta.

## Two generation-layer incidents, found and closed

1. Runtime-token trap, file-content form (extends the 2567 law): the
   derived generators build their bridge/main-theorem sections at RUNTIME
   by slicing committed modules (e.g. NonzeroNode2541), so the 2568
   center/error renames applied to the generator SOURCE cannot reach them.
   The composer now strips the four `baseCoefficient*2540` tokens from the
   emitted TEXT with an assert that none survive, imports the correction
   boxes/center modules, and regenerates the two per-family error-sum
   literals the slices carry (1/10^30 -> 1/10^28, 30/10^30 -> 30/10^28;
   the final linarith holds with 9e-8 of slack in the jet chain).
2. Chunked-literal powers with leading-zero chunks (sharpens AGENTS 2bj):
   the L1 denominator's last 68-digit chunk starts with 0, so accumulating
   powers by len(str(int(chunk))) shrank the later chunks' widths by one
   digit and inflated the whole literal by exactly 10x; the Lean kernel
   then correctly refused the assembly inequality. chunked() now
   accumulates RAW digit-slice widths and round-trip-asserts that the
   emitted literal evaluates back to the exact value.

## Validation

- Base-pair byte regression: the composer selfcheck reproduces the
  committed base modules byte-for-byte through the same derivation chain
  (boxes modulo header; midpoint bounds, first jet, both shared modules
  byte-equal), so the correction emission is the same generator with only
  the declared substitutions.
- Determinism: a full composer re-run reproduces all eight modules and the
  readback byte-for-byte.
- Pilot agreement: the four signed uppers cover and stay within one
  rounding quantum of the 2569 exact aggregates; the L1 literal is the
  pilot aggregate bitwise; the bound is within 1e-6 of the pilot bound.
- Independent arithmetic check: scripts/check_assembly_inequality_2570.py
  re-reads the six literals out of the emitted modules and evaluates the
  assembled inequality exactly (HOLDS, slack 4.6e-14).
- Build + axiom census + mirror byte-equality over the full import
  closure: see results/2570_correction_pair_validation.json (validator
  scripts/validate_correction_pair_2570.py, axiom trio everywhere, no
  sorry).

## Explicitly not claimed

The sigma = +1/2 cell2700 certificate (2563 counterpart) is not yet
regenerated; the 2566 grid lanes proceed at the correction pair as the
next record. Membership is unchanged (2564 numbers stand). The bound is a
single-cell statement over the correction coefficient pair; no RH claim,
and the two-channel product theorem keeps both endpoint inputs as
hypotheses.

Evidence: scripts/generate_correction_pair_2570.py,
scripts/validate_correction_pair_2570.py,
scripts/check_assembly_inequality_2570.py,
results/2570_generation_readback.json,
results/2570_correction_pair_validation.json,
docs/proofs/2569_cell2700_minus_correction_repricing.md,
docs/proofs/2568_row_scope_correction.md,
ConnesWeilRH/Dev/C1RouteACorrectionSecondCell2700MinusCorr2570.lean.
