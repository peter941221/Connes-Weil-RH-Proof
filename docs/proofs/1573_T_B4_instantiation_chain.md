# 1573 — T-B4: the instantiated 1536 consumer chain for the actual boundary columns

Date: 2026-09-17.

Status: PAPER WIRING over committed bricks. Zero Lean spend, zero digits.
Step T-B4 of the 1568 order of battle asks: instantiate the radial-tail
consumer chain for the ACTUAL forward-Euler-exposed boundary columns, and
state exactly what remains. This record does the wiring only: every
theorem named below is committed (records 1499/1531-1536); none is re-proved
here; the two live premises are registered, not discharged. RH not claimed.

## 1. The chain, slot by slot (transcribed statements)

```text
(1) exact defect decomposition            (record 1533)
    sourceSoninHardySubId_comp_sourceInclusion_eq_radial_fourierDefect
      C1G8R3BoundaryOutputFactorizationBridge.lean:448
    (E Q E M - M) ∘L sourceInclusion
      = -(I - E) M ∘L sourceInclusion - E (I - Q) E M ∘L sourceInclusion

(2) two-column consumer                   (record 1534, :510)
    sourceSoninHardySubId_sourceBasis_normSq_summable_of_radial_fourierDefects
      (lambda) (M D) (N) (sourceBasis) hradial hgap
    hradial : Summable i, ‖(D ∘L (I - E) M ∘L sourceInclusion ∘L N) e_i‖^2
    hgap    : Summable i, ‖(D ∘L E (I - Q) E M ∘L sourceInclusion ∘L N) e_i‖^2
    ==>     Summable i, ‖(D ∘L (E Q E M - M) ∘L sourceInclusion ∘L N) e_i‖^2

(3) radial self-adaptation shortcut       (record 1535, :594)
    sourceSoninHardySubId_sourceBasis_normSq_summable_of_sourceRadialSupport
      additionally takes  hM : E ∘L M ∘L sourceInclusion = M ∘L sourceInclusion
      and removes the hradial premise:  hgap alone concludes.

(4) Fourier-gap normal form               (record 1536, :478)
    sourceSoninHardyFourierGap_comp_sourceInclusion_eq_hardyRadialLeakage
      E (I - Q) E M ∘L sourceInclusion = E H (I - E) H E M ∘L sourceInclusion
    (uses only Q = H E H and the HT involution law; no commutation assumed)

(5) per-output reassembly                 (record 1499, :1140 / :1198)
    g8AmbientSourceLeg_energy_normSq_summable_of_legs      (three legs -> energy)
    g8MetricVisibleBoundary_root_energy_summable_of_legs   (aggregate -> hBoundary)
```

Composition (1)-(4) turns the B4 obligation of record 1568 section 1 into
exactly one square-sum:

```text
B4_actual(M, D, N)  :=  Summable i,
  ‖(D ∘L E ∘L H ∘L (I - E) ∘L H ∘L E ∘L M ∘L sourceInclusion ∘L N) (sourceBasis i)‖^2
```

with the radial defect gone IF AND ONLY IF the shortcut premise `hM` is
available for the actual factor (item 2 below). Step (5) then feeds any
legwise proof into the committed `hBoundary` assembly unchanged.

## 2. The two live premises for the ACTUAL columns

The consumer is quantified over arbitrary ambient factors `M : finiteSCarrier
→L[ℂ] finiteSCarrier`; record 1534 already warned that the committed radial
finite-window certificates are owner-root only and "do not cover arbitrary
actual M". For the actual B4 instantiation (the `M_p` factors of the record
1499 B2 factorization `M_p ∘L J ∘L N_p`) two questions are live:

- **Q-hM (identity, not an estimate):** does
  `E ∘L M_p ∘L sourceInclusion = M_p ∘L sourceInclusion` hold for the actual
  forward-Euler-exposed factors? This is the `hM` premise of slot (3). It is
  a support-localization statement - the columns `M_p (sourceSoninCarrier)`
  living inside the log-radial support region - so it is in principle
  decidable from the committed support data of `M_p` and the Sonin carrier.
  If YES: the first estimate (`hradial`) is discharged EXACTLY and B4
  collapses to `B4_actual` alone. If NO: both premises of slot (2) must be
  estimated and the 1534 warning stands.
- **B4_actual itself:** the gap square-sum. Its only decay inputs are the
  phase of the HT multiplier `m` (`|m| = 1`, phase `theta` with T0a/T0b
  explicit bounds from record 1570) and the prolate absorption already
  committed in records 1531/1532 (`sourceSoninCommutator_sourceBasis_normSq_
  summable_of_hardySubId_sub_prolate`, `..._of_hardySubId_factor`). Record
  1572 has just closed the third hoped-for input (window symbol decay): it
  does not exist - the window is a sharp indicator.

## 3. What this buys the wave, honestly

1. B4 is now ONE named square-sum plus ONE named identity question. There
   is no longer an implicit "instantiate the consumer" step left: the
   instantiation is the display in section 1, and every slot has a line
   number.
2. B4 and (★) share their fate (record 1572 section 1.2: `Q = H E H` makes
   the two tail families identical): the same T0/T2 phase analysis feeds
   both, and a stage-1-style exponent failure on `B4_actual` would price
   (★) the same way. Concentration is deliberate (1568: "shared entry fee").
3. The next paper action is Q-hM, because it is an identity (cheap to try,
   exact if true, and it deletes an entire estimate obligation), whereas
   `B4_actual` is the phase-typed hard core whose treatment must follow the
   T2 verdict. No Lean brick is authorized for B4 before Q-hM is adjudicated
   and T2 exists on paper with explicit constants (1568 section 4.5).

No prior moved. The gate (★), B4, the rho5 combined-row identity, the
source/ambient transport, and the R4 wrapper stay OPEN. RH not claimed.
