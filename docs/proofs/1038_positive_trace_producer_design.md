# 1038 - Positive-trace producer design note (consumer #1)

Date: 2026-08-19.

Status: **Stages 1-2 implemented; Stage 3 remains open, with no RH claim.**
This document records the audit of the existing trace-side bricks and the
constraint set that any `PositiveTracePairLimitFamily` producer must satisfy.
The finite common-carrier and Euler-log readback layers are implemented in
`Dev/C1CrossingCommonCarrier.lean`,
`Dev/C1CrossingCommonCarrierTransport.lean`, and
`Dev/C1CrossingEulerLogReadback.lean`.

## Target contract (already proven exits, missing producer)

```text
PositiveTracePairLimitFamily basis g
  (ConnesWeilRH/Dev/C1PositiveTraceLimitBridge.lean:55)
    traceData : Nat -> BasisHilbertSchmidtPairData (G := G) basis
    self_pair : left = right              -- positivity source
    remainder : Nat -> Real, -> 0
    readback : Tr(traceProduct n).re - remainder n -> qw g
  -> 0 <= qw g                     (:127, proven)
  -> 0 <= spectralWeilValue g^2    (:140, via Gate 2, proven)
  -> healthyCriterionState         (:150, proven)
```

One producer feeds consumers #1 -> #2 -> #3.  The exits are axiom-clean and
wait for the analytic construction only.

## Audit of existing trace-side bricks (all same owner)

| Brick | State | Key statement |
|---|---|---|
| finite-window F.F-dagger producer | CLOSED | window Hilbert basis, exact cutoff growth |
| crossing pair trace (one orientation) | CLOSED | `pairData ... traceProduct` trace = `b * F(b)` |
| crossing pair sum | CLOSED | `pair_traces_add_eq_mul_symmetric_convolutionSquare` = `b (F(b)+F(-b))` |
| Euler-log weighted readback | CLOSED | `eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow` = `finitePrimeTerm (p^m)` |
| coefficient owner screen | PASS (1037) | m=2 carries crossing length only; mixed primes additive |
| plain-window family | DEAD (1016) | trace = window-length x mass, zero arithmetic |
| Mellin-conjugated Hilbert detector | DEAD (1036) | bulk slope diverges; m=2 coefficient wrong |
| positive producer with remainder -> 0 | OPEN | this note |

Source: `ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingKernel.lean:351-413`,
`SelectedSingleCrossing.lean:35-83`.

## Sharpened design constraints (from the audit)

1. **Carrier mismatch.**  Each prime-power crossing pair lives on
   `Lp 2 (KernelInterval a c b)` with `b = m log p`.  The family contract
   needs ONE basis on ONE Hilbert space.  Any producer must first transport
   the finitely many crossing traces to a common carrier.

2. **Individual pair traces are indefinite.**  `reversePairData` trace is the
   pairing of two different kernel sections (`leftKernel` vs `rightKernel`),
   so `left != right` and no single orientation is a self-pair.  The contract
   admits only ONE positive square `A-dagger A` per stage; a polarization
   rewrite `2 Re Tr(X-dagger Y) = |X+Y|^2 - |X|^2 - |Y|^2` introduces
   subtractions that the contract forbids.  Positivity must be reorganized,
   not bookkept.

3. **The arithmetic sum is finite for a compactly supported owner.**
   `C1SameOwnerWeil.globalPrimeIndexSet F` is an exact finite set (AGENTS.md
   "C1XiArithmeticPrimePowerAssembly"), because `F(b) + F(-b)` vanishes once
   `|b|` exceeds the support radius.  So the producer faces a finite
   reorganization problem, not a tail-convergence problem.  Any design that
   introduces an infinite cutoff must justify why the tail is not already
   zero on the owner.

4. **Bulk obstructions are exact.**  1016 gives `trace = window-length x
   integral |g|^2` for plain windows; 1036 shows Mellin-conjugated Hilbert
   commutators have an unbounded bulk slope and the wrong m=2 coefficient.
   A producer family may only use structures whose window/bulk contribution
   is computed exactly and vanishes or is absorbed with a remainder that
   still tends to zero.

5. **Positivity can only come from the vanishing constraints.**  For a fixed
   `g0`, a producer family exists only if `qw g0 >= 0`; its construction is
   the proof.  The triple vanishing at `s in {0, 1/2, 1}` is the only
   same-owner mechanism available to convert the indefinite kernel into a
   square.  This is the research crux; it is not resolved by this note.

## Staged attack (each stage names consumer #1)

- **Stage 1 - common-carrier adapter (CLOSED, design-independent).**
  For one owner `g0` with support in `[a, c]` and its finite
  `globalPrimeIndexSet`, build ONE Hilbert space carrying all
  `KernelInterval a c b` sections for `b` in the owner set (direct sum or a
  common ambient `L2` interval), with extension maps that are isometries on
  the kernel sections.  Transport each `pairData`/`reversePairData` trace to
  `ordinaryTraceAlong` on the common basis with remainder identically zero.
  Output: the finite prime part of `qw` read back as traces on one carrier.
  `crossingCommonCarrierData` supplies the inhabitant from explicit interval
  and source Hilbert bases; the trace transport audit is axiom-clean.

- **Stage 2 - finite Euler-product readback on the carrier (CLOSED).**
  Sum the transported Euler-log weighted pair traces over the exact finite
  owner set; match the pole and Gamma_R parts against the already-proved
  center-2 Gamma_R readback contract on the same owner.  Output: `qw g0`
  as an explicit finite trace expression (still indefinite).  The
  `minFac`/`factorization` enumeration is reconstructed locally, without an
  import from the frozen Gate-3U finite-S family.

- **Stage 3 - positivity reorganization (research crux).**
  Use the triple vanishing to write the Stage 2 expression as one
  `A-dagger A` trace with vanishing remainder, or prove that a specific
  structured candidate (e.g. a paired-profile square in the spirit of the
  center-2 Gamma_R diagonalization) attains it.  Every candidate must pass
  the 1036 coefficient test (m=2 crossing length only) and the 1016 bulk
  test (exact bulk, zero arithmetic residue) BEFORE any Lean detector
  namespace is created.

## Numerical-work boundary (per the 2026-08-19 guard)

No numerical experiment is planned for Stage 1-2: the facts are formal
(isometric transport, finite sums).  A Stage 3 candidate may be screened
only as a bounded kill-test with the two named criteria (m=2 coefficient,
bulk slope bounded) before Lean implementation.

The Stage-2 endpoint is a finite identity only.  It does not provide the
moving-cutoff remainder, positive `A-dagger A` reorganization, global
spectral nonnegativity, or RH.  RH remains unproved.
