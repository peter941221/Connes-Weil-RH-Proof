# Record 1216 - Gate-convention correction and the true matrix verdict

Date: 2026-09-07.  Status: CORRECTION to record 1214 (F2/F3) + probe
verdict.  Tooling: `1216_true_gate_matrix_probe.py` (float64 quadrature,
independent of the 1112 arb pipeline; official log
`1216-true-gate-probe2.log`).  No P2, no SourceRH, no RH.

## 0. Correction (error in record 1214, made by this same workstream)

Record 1214 F2 stated that the Lean gate functional is
`archPair(i,j) - primePair(i,j)`, and F3 reported the Gram-whitened top
`+1.713` for that "gate convention" on ker R.  Both claims are WRONG.
The verbatim Lean definitions are:

```lean
-- C1LocalConfigurationDomination.lean
def ICgate (F : CompactLogTest) : Real :=
  archimedeanTerm F + finitePrimeSum F            -- PLUS, not minus

-- C1SameOwnerWeil.lean
def finitePrimeTermComplex (F) (n) : Complex :=
  (vonMangoldt n) * ((1 / sqrt n) * (F.test (log n) + F.test (-log n)))
                                                  -- BOTH-SIDED readout

-- C1GateMatrixRepresentation.lean
def gateMatrix w := Matrix.of fun i j => ICgate (pairTest w i j)
gate_qform_span   : ICgate ((spanObj w y).convolutionSquare)
                      = y (gateMatrix w * y)      -- no sign flip
hrep_of_gateMatrix_eq : gateMatrix w = M_true -> ...  -- no sign flip
```

The `arch - prime` matrix (and its +1.713 whitened top) was a phantom
introduced by the 1214 probe script, which computed the polarization
with the wrong sign and a single-sided prime readout.  F1 (degenerate
point box) and the F2 parity STRUCTURE survive unchanged; F3 is void.

## 1. Where the real fracture sits

The committed 1112 bundle certifies the SINGLE-SIDED prime readout
`2 * Lambda/sqrt(q) * C_ij(+log q)` (probe reproduction of the
committed M_mid: max error 1.55e-12 over all 64 entries).  The Lean
`gateMatrix` carries the BOTH-SIDED readout
`Lambda/sqrt(n) * (C_ij(+log n) + C_ij(-log n))`.  By the parity law
`C_ij(-x) = (-1)^(i+j) C_ij(x)` (now a Lean theorem, see section 3):

```text
same parity  (i+j even):  both-sided = 2 * single-sided  EXACTLY
                          -> the two conventions coincide entrywise;
mixed parity (i+j odd):   both-sided = 0 EXACTLY
                          -> the committed box (+-0.35 class) cannot
                             contain the Lean entry, so the hM slot of
                             absolute_true_q28 is structurally
                             unsatisfiable against the 1112 data.
```

## 2. The true matrix verdict (probe 1216)

Recomputed `M_true = arch + both-sided prime` from the Lean definitions
(class windows at a = 2, arch tail closed form, 24 visible prime
powers, 16x40-node Gauss quadrature):

```text
(1) same-parity entries (32 of 64, full matrix):
      max |M_true - committed M_mid| = 1.405e-12
(2) mixed-parity entries (32 of 64):
      max |M_true| = 5.326e-17   (EXACT structural zeros; the committed
      point boxes hold +-0.35-class values there -> 24 box violations,
      all of the same kind)
(3) Gram-whitened spectrum of M_true on V = ker R (dim 5):
      -1.4433e-06, -3.3154e-05, -7.3902e-05, -7.8793e-03, -8.4355e-02
      top(M_true|V) = -1.443313e-06
    committed top_mid = -1.443377e-06  (shift 6.4e-11)
    budget U = -1.043377e-06, DELTA = 4.0e-07: margin architecture
    SURVIVES on the true matrix with the full 4.0e-07 slack.
```

Consequence: the near-cancellation behind the 1112 margin lives in the
same-parity block, which the two conventions share entrywise.  The
Weil margin chain does NOT need a pole brick, a new functional, or a
restated consumer.

## 3. Landed artifact (D1 of prereg 1215)

`ConnesWeilRH/Dev/C1GateMatrixParity.lean` (+ paired Audit), build log
`c1gate-matrix-parity-build4.log`: footer `Build completed successfully
(3678 jobs)`, zero `error:` lines, zero `sorryAx`; all 9 theorems with
standard axioms `[propext, Classical.choice, Quot.sound]`.

```text
classPairTest_apply                  test = complex cast of the real
                                     correlation integral
classPairTest_neg                    C_ij(-x) = (-1)^(i+j) C_ij(x)
                                     (reflection against the 1127
                                     window parity)
classPairTest_neg_of_odd             mixed parity -> odd function
classPairTest_even_add_zero_of_odd   F(x) + F(-x) = 0   (D1 clause)
classPairTest_at_zero_of_odd         F(0) = 0           (D1 clause)
archimedeanTerm_..._zero_of_odd      the 1080 odd kill applies
finitePrimeSum_..._zero_of_odd       termwise even-part kill
ICgate_..._zero_of_odd               D1 headline
gateMatrix_zero_of_odd               16 of 36 independent entries
                                     are exact zeros
```

## 4. Revised repair (supersedes 1215 D2/D3/D4)

```text
D1  LANDED (this record).
D2  RETIRED - unnecessary: ICgate already IS arch + prime; the
    hrep_of_gateMatrix_eq slot needs no new functional.
D3  RETIRED - unnecessary: absolute_true_q28 works verbatim once hM
    boxes the true matrix.
D4  RETIRED - not needed for the M-side chain (margin verdict above).
D5  SCOPE REDUCED: only the 20 same-parity independent entries
    (12 off-diagonal + 8 diagonal) need certified real-width boxes;
    the 16 mixed entries take exact-zero boxes from D1.  Target
    widths <= 1e-9, rational outward rounding, new data module; the
    falsifier (widths exceeding the ~1.04e-6 row budget -> ABORT)
    is unchanged.
```

Prereg discipline note: the amendment lands BEFORE any certificate
generation run (law 42 untouched); 1215 D1 scope is unchanged.
