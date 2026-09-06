# Record 1214 - M-side convention-fracture audit (the 1146 gap, restated)

Date: 2026-09-07.  Status: FORMAL interface audit + numerical feasibility
data.  Follows `1146_m_side_true_matrix_supplier_audit.md`.  No P2, no
SourceRH, no RH.  Tooling: `1214_m_side_feasibility_probe.py` (numpy
float64, independent of the 1112 arb pipeline; reproduction checks
against the committed bundle below).

## 0. Headline

The M-side supplier gap of record 1146 is NOT a missing-data problem.
Three findings reframe it:

```text
F1  The committed M bundle is a DEGENERATE box: M_lo = M_hi = M_mid
    entrywise (1112_cert.json classes[0]).  A point box can only be
    proved for a Lean-side real object by reproducing the identical
    real expression - impossible for analysis-defined matrices.
    `q28_hbox_of_concrete_certificate`'s hM premise is therefore not
    merely open; it is UNSATISFIABLE against the committed data.

F2  The hrep slot forces the gate convention.  `absolute_true_q28`'s
    hypothesis `ICgate w.convolutionSquare = c (M_true c)` is
    discharged (via 1121 `hrep_of_gateMatrix_eq` / `gate_qform_span`)
    ONLY by `M_true = gateMatrix w`, whose entries are
    `ICgate (pairTest w i j)` = archPair(i,j) - primePair(i,j).
    The committed 1112 M is the OPPOSITE convention
    (archPair + 2 Lambda/sqrt(q) C_ij(+xi), see
    `build_class` in 1112_true_interval_whitened_probe.py:
    `M_MAT[i,j] = A_MAT[i,j] + P_MAT[i,j]`).
    The two matrices differ STRUCTURALLY, not numerically: with
    C_ij(-x) = (-1)^(i+j) C_ij(x),
      - same parity (i+j even):  prime parts are exact negatives;
      - mixed parity (i+j odd):  primePair = 0 EXACTLY (the gate
        functional reads only the even part of the correlation), while
        the 1112 prime part is nonzero (committed M_mid[0][1] = 0.352).

F3  In the gate convention the box inequality on ker R is FALSE.
    On V = ker(Q28.R) (dim 5, rank(R) = 3), Gram-whitened top
    eigenvalues, independently recomputed:
        gate convention (arch - prime):  top = +1.713
            (spectrum 1.713, 1.190, 0.620, 0.299, -0.0259)
        1112 convention (arch + prime):  top = -1.443e-06
            (reproduces the committed top_mid = -1.4433774e-06).
    So `c (gateMatrix c) <= U (c (G_true c))` with U = -1.04e-6 < 0
    cannot hold on ker R.  The chain survives only on the negative
    cone of gateMatrix|V (bottom whitened eigenvalue -2.59e-02).
```

## 1. What was verified (evidence, not estimates)

- Independent recomputation of the 1112 convention from the Lean
  definitions (classWindowFun = Legendre x exp(-1/(1-x^2)) bump at a=2,
  archimedean denominator e^y - e^-y, tail closed form
  F(0) log tanh(2), visible prime powers n <= 53):
  max over 64 entries |recomputed - committed M_mid| = 1.55e-12
  (median 8.3e-13); whitened top on V reproduces the committed
  top_mid to 6.4e-11.  The 1112 numerics are fully owned.
- The gate convention (arch - prime, the 1121 polarization) computed
  to the same accuracy; mixed-parity entries land at <= 1e-17
  (structural zero), diagonal (0,0) = -1.1558e-01 vs committed
  M_mid[0][0] = +1.8439e+00.
- Parity identity used above: C_ij(-x) = (-1)^(i+j) C_ij(x) from
  Legendre parity and bump evenness - a Lean-provable lemma shaped
  like the landed 1126 class-Gram parity.

## 2. Why the fracture happened

The 1112 bundle was built for the (a)+(b) margin architecture: bound
`arch + prime` from above by the pole budget (`U = top_mid + DELTA`).
Record 1121 then represented the Weil functional's POLARIZATION
(`ICgate` = arch - prime) as the gate quadratic form and recorded the
hrep slot.  The two conventions were never reconciled: `Hbox` boxes the
1112 matrix, `hrep` demands the 1121 matrix, and `absolute_true_q28`
requires ONE matrix satisfying both.  No such matrix exists for the
class owner (F2), and in the 1121 convention no U < 0 works on ker R
(F3).

## 3. Route options (DECISION REQUIRED - not made by this record)

```text
Option A (narrow cone): regenerate the M box in the gate convention
    (real widths, certified interval quadrature - numerically feasible,
    probe accuracy 1e-12 vs needed ~1e-9), and consume
    absolute_true_q28 only at coefficient vectors in the negative cone
    of gateMatrix|V.  Requires a downstream re-check that a single-c
    consumption suffices for the final assembly.

Option B (chain repair): add a POLE-side brick (pole(w^2) lower bound
    over the class family) and restate the box chain to bound
    arch + prime (matching the 1112 data, boxes regenerated with real
    width), concluding Q(w) = pole - ICgate >= mu' > 0 directly.
    Touches the 1118-1121 interface statements.

Option C (freeze): freeze the q28 consumer chain (Line-B style) until a
    separate pre-registered repair record lands.
```

All three keep the G-side results (1145/1146 G-side, class moment
certificates) intact: the fracture is M-side and interface-side only.
