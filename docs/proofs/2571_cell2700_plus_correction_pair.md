# Record 2571 — cell2700 plus chain: base fine aggregate, correction repricing, and the correction-pair certificate

**Verdict: CORRECTION-PAIR-PLUS-REGENERATED.** The sigma = +1/2 cell-2700
correction-second chain now exists at the ideal_correction_coefficient pair
as six Lean modules over the shared 2570 correction boxes and center node,
with the plus sign carried end-to-end by sign-parameterized derivations of
the committed minus generators. The three-piece summand of the 2562
decomposition is bounded by 302483963/200000000000 = 1.512419815e-3 on the
production cell at sigma = +1/2, the exact piece sum being
1.51241981420859e-3 (slack 7.9e-13). Together with the 2570 minus
certificate (3.317219912e-2), both endpoint signs of the 2560 two-channel
correction consumer now have a single-cell correction-pair certificate.
No RH claim; family centers and errors stay explicit at the boxes.

## Motivation

The committed sigma = +1/2 cell-2700 certificate (2563) rests on the coarse
2551 boundary envelope `boundaryCellCurvatureBound2551`, whose statement is
instantiated at `baseCoefficientCenter2540 / baseCoefficientError2540` — at
the correction pair the curvature runs ~1.4e5x above that envelope, so the
2563 shape is unusable there, exactly as 2568 found for the minus sign.
Record 2570 regenerated the minus chain; this record closes the plus side.

## Stage A — the base-pair plus fine chain (seven modules)

The 2558 signed-cell generator is sign-parameterized (`Cell(index, sign)`)
but the committed 2558 chain covered only sigma = -1/2 at cells 2700/2701.
The new driver `scripts/generate_plus_cell2700_2571.py` renders
`Cell(2700, +1)` through the committed generator, emitting

- C1RouteABatchC02700PlusMidpoint2558 (coefficient-independent plus leaves)
- C1RouteABatchC02700PlusLeftBounds2558 / RightBounds2558
- C1RouteABatchC02700PlusMidpointBounds2558
- C1RouteABatchC02700PlusFourth2558
- C1RouteABatchC02700PlusAssembly2558
- C1RouteABatchC02700PlusIntegral2558

with the endpoint/value layers read from the committed kernel Plus (2555)
and shared Plus (2556) modules. Scalar anchors: midpoint upper
8777/50000000, third aggregate bound 4373/500000, curvature bound
91/500000, cell integral bound 57/500000000000, right endpoint upper
873/10000000000. Two cross-checks pin the chain to the committed world:
the curvature bound equals the 2551 coarse envelope value bitwise (the
2551 envelope is this cell's coarse aggregate), and the right endpoint
upper equals `sharedN02701PlusUpper2556` bitwise. Lean build: 3924 jobs,
green, axiom trio on the Integral audits.

Independent revalidation (`validate_signed_cells_2558.check` at
`Cell(2700, +1)`): all payload classes replay, and the opposite-sign fourth
witnesses are rejected — the exponent-growth choice is verified against the
sign, not just the labels.

## The plus repricing (external pilot)

`scripts/price_cell2700_plus_correction_2571.py` mirrors the 2569 minus
repricing at sigma = +1/2 (results/2571_cell2700_plus_correction_repricing.json):

- base selfcheck: the repriced midpoint/first-jet uppers sit ~9e-8 under
  the committed stage-A/2563 bounds (rounding-quantum gap), the endpoint
  uppers match the 2556 chain to 1.4e-16, the exact base third aggregate
  sits under the coarse module scalar 4373/500000 by 2.84e-5 (thirty
  per-family round-ups — dominance, not tolerance), and the fine
  three-piece total 2.3554208598e-7 is under the coarse 2563 bound
  236901/10^12.
- correction repricing: pieces [1.4757e-3, 3.6546e-5, 2.2259e-7], exact sum
  1.5124195837e-3, curvature-dominated (mid aggregate 1.1156, third
  aggregate 58.184060482, curvature 1.15285), endpoint values 6.92e-4 and
  6.99e-4.
- 2561 trapezoid enclosure of the same cell: total 1.42176e-3, ratio
  three-piece/enclosure 1.0638 — same scale, as the minus side.
- grid extrapolation 15.49 against the correction pin 666472.585392: the
  plus sign is ~22x cheaper than the minus cell (3.3172e-2), as the
  exp-decay direction predicts. Cell-level sanity only, not a budget claim.

## Stage B — the correction-pair plus chain (six modules)

`scripts/generate_correction_pair_2571.py` reuses the 2570 correction boxes
and center node verbatim and emits

- C1RouteACorrPlusMidpointDerivatives2571 — renamed stage-A leaf copy
- C1RouteACorrMidpointBounds2700Plus2571 — the 2543 render (natively plus;
  the generator flips literals only for sigma < 0) derived with CENTER_SWAPS
- C1RouteACorrFirstJetMidpointPlus2571 — the 2565 first-jet generator
  derived to the plus sign: sigma constant, Lean sigma literal, prefix,
  record, target, lemma names, and the slice-section sign rewrite. The
  sliced 2541 statement is natively plus (the minus module was the one
  that needed `(1/2) -> (-1/2)`), so the sign rewrite becomes inert and
  the 2567 remainder law holds on every substituted token.
- C1RouteACorrSharedN02700Plus2571 / N02701Plus2571 — the 2542 shared
  render at sign +1
- C1RouteACorrectionSecondCell2700PlusCorr2571 — the 2565 assembly shape
  with the sigma literals, per-family leaf prefixes, kernel positions, and
  exported names swapped to plus; the aggregate/curvature bridge inserted
  at sigma = +1/2 over `batchC02700PlusThirdCell2558`.

Module uppers: midpoint 111561481/10^8, first jet 2781363/10^8, endpoints
1384031/2000000000 and 3494223/5000000000, third L1 aggregate
58.18406048188979, cell bound 302483963/200000000000. The composer's exact
aggregate recomputation matches the repricing displays to ~1e-14 at all
four points, and the assembly L1 bridge literal is bitwise the pilot
aggregate. Sign hygiene is asserted in the composer: no `(-1/2)` literal
and no Minus token survives in any emitted module.

An independent literal re-read (`scripts/check_assembly_inequality_2571.py`)
re-evaluates the six emitted literals in exact arithmetic:
assembled total 1.51241981420859e-3 <= bound, slack 7.914e-13. HOLDS.

## Validation

`scripts/validate_correction_pair_2571.py` (results/2571_correction_pair_validation.json):

1. token hygiene — no baseCoefficient and no minus-flavored token in the
   six modules;
2. stage A — driver re-run byte-identical on the seven modules and the
   inputs JSON; independent payload re-read green with opposite-sign
   rejection;
3. regeneration — composer re-run byte-identical on the six modules and
   the readback JSON;
4. base selfcheck — the composer at the base pair reproduces the committed
   stage-A MidpointBounds, the 2556 shared Plus endpoints, and the 2565
   minus first-jet module (slicing machinery) byte for byte;
5. pilot agreement — uppers cover and match the 2571 repricing within
   their quanta; bound vs pilot bound within 1e-6;
6. build + axiom census over the thirteen modules — success footer, no
   errors, no sorry, every #print target (182 across the thirteen modules)
   resolves with exactly [propext, Classical.choice, Quot.sound];
7. mirror — the thirteen-module import closure (758 files) byte-equal to
   the ext4 build mirror.

## Remaining obligations

- 2566 lanes 2b-2f at the correction pair (mass generation over the full
  10240-cell grid at both signs; the minus and plus single-cell pipelines
  are now both de-risked at the correction pair).
- Membership brick: 60 correction-row representatives (2^-200 truncations,
  smallest k 95) against correctionError = 1e-28 (2452 pattern).
- N(b) full-grid certificate and the final two-channel product theorem.

Evidence: ConnesWeilRH/Dev/C1RouteABatchC02700Plus*2558.lean,
ConnesWeilRH/Dev/C1RouteACorr*Plus*2571.lean,
ConnesWeilRH/Dev/C1RouteACorrectionSecondCell2700PlusCorr2571.lean,
scripts/generate_plus_cell2700_2571.py,
scripts/price_cell2700_plus_correction_2571.py,
scripts/generate_correction_pair_2571.py,
scripts/validate_correction_pair_2571.py,
scripts/check_assembly_inequality_2571.py,
results/2571_plus_cell2700_base_inputs.json,
results/2571_cell2700_plus_correction_repricing.json,
results/2571_generation_readback.json,
results/2571_correction_pair_validation.json,
build-logs/2571_plus_corr_build.log, build-logs/2571_full_build.log.
