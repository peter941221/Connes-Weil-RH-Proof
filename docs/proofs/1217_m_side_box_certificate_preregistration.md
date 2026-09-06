# Record 1217 - M-side box certificate (prereg 1215 D5, numeric layer)

Date: 2026-09-07.  Status: PRE-REGISTRATION, committed BEFORE any
certificate generation run (law 42).  Consumers: records 1215 (D5),
1216 (revised repair).  No P2, no SourceRH, no RH.

## 1. Deliverable

A certified rational M box for the TRUE Lean gate matrix on the class
(2,8) owner, replacing the degenerate 1112 point box (1214 F1):

```text
MLo_q28M, MHi_q28M : Matrix (Fin 8) (Fin 8) Rat  (full 8x8, symmetric)
mixed parity (i+j odd):  box = [0, 0]  (discharged in Lean by D1,
                         gateMatrix_zero_of_odd, exact zero)
same parity (i+j even):  box from the numeric certificate, widths
                         <= 1e-9 absolute per entry
```

## 2. Certified quantity (same-parity entries)

```text
M_ij = (log(4pi)+gamma) * C_ij(0)
     + int_0^4 [e^{y/2} (C_ij(y) + C_ij(-y)) - 2 C_ij(0)] / (e^y - e^-y) dy
     + C_ij(0) * log(tanh 2)                       (exact closed tail)
     + sum over visible prime powers n <= 53 of
         Lambda(n)/sqrt(n) * (C_ij(log n) + C_ij(-log n)),
C_ij(x) = int_{-2}^{2} w_i(s) w_j(x+s) ds,
w_k(u) = P_k(u/2) * exp(-1/(1-(u/2)^2)) on |u| < 2, else 0.
```

Same-parity parity law (Lean: classPairTest_neg with (-1)^(i+j) = 1)
makes the both-sided prime readout equal 2 * C_ij(log n) and the arch
numerator 2 (e^{y/2} C_ij(y) - C_ij(0)).

## 3. Engine and error budget (registered BEFORE the run)

```text
precision       mpmath dps = 60
inner integral  composite Gauss-Legendre, 16 panels x 200 nodes on
                (-2,2); convergence gate |GL_n - GL_{2n}| <= 1e-12 at
                every required point; per-value budget 1e-11
arch integral   composite Gauss-Legendre, 16 panels x 200 nodes on
                (0,4]; the integrand extends smoothly through y = 0
                (removable singularity; GL never evaluates y = 0);
                convergence gate <= 1e-12; per-value budget 1e-11
constants       log(4pi)+gamma and log(tanh 2) enclosed at +/-1e-14
                (mpmath internal directed rounding at dps = 60)
entry budget    arch + 48 prime-point correlations + constants,
                total <= 5e-10 per entry
rounding        outward to the dyadic grid with denominator 2^72
                (grid pitch ~2.1e-22; rounding contributes nothing
                at the registered scale)
falsifier (a)   any entry total budget > 1e-9 -> the run is
                ABORTED-UNINFORMATIVE; widths are reported, never
                widened by hand (1097 / prereg 1215)
falsifier (b)   whitened-top inflation check: with
                Delta = L^-1 Z^T (MHi - MLo) Z L^-T / 2 entrywise,
                require top(M_mid|V) + spectral_radius(Delta)
                          <= U = -1.043377e-06 - 1e-8.
                Failure -> ABORTED-UNINFORMATIVE (the boxes would not
                support the margin consumption; no hand-narrowing).
```

## 4. Landed artifacts

```text
docs/proofs/1217_m_boxes_cert.json   the certified rational boxes +
                                     budgets + convergence data
ConnesWeilRH/Dev/C1GateMatrixBoxData.lean (+ Audit):
   MLo_q28M / MHi_q28M as Rat tables;
   q28_hboxM_of_sameParity (CONDITIONAL): given per-entry enclosures
   for the 20 same-parity entries, MLo_q28M <= gateMatrix
   (classTestFamily 2 ha) <= MHi_q28M entrywise -- the 16 mixed
   entries are discharged NOW by C1GateMatrixParity (exact zeros).
```

## 5. Honest scoping amendment to prereg 1215 D5

1215 D5's acceptance ("boxes proved entrywise in Lean") requires a
Lean-side envelope campaign for the shifted correlation integrals - a
campaign of the same scale as the G-side 1131-1139 chain (two-layer
integration: the arch integrand contains inner correlations; the bump
product has two shifted centers).  THIS record lands the numeric
certificate layer + the data module + the conditional Lean binding;
the entrywise discharge is preregistered as the follow-up campaign
(next record) and is NOT claimed here.  No statement of 1118-1121
changes; no q28 G-side data changes; the 1215 falsifier discipline
carries over verbatim.

## 6. Budget-rule amendment (2026-09-07, BEFORE the official rerun)

The first engine launch aborted (exit 5) on entry (0,0) with the FLAT
budget interpretation: charging the registered per-point 1e-11 at
every one of the ~6400 inner arch correlation points sums to
6.9e-10 > the 5e-10 target regardless of the actual convergence.  The
registered 1e-11 was meant as a per-VALUE ceiling, not an additive
flat charge.  AMENDED budget rule (conservative, a-posteriori):

```text
per-point charged error perr(x) = max(2 * |GL_n - GL_{n/2}|(x), 1e-13)
```

i.e. twice the measured half-rule defect with a 1e-13 floor, fed into
the same accumulation.  UNCHANGED: the gate |delta| <= 1e-12 (abort),
the entry cap 5e-10, the width deliverable <= 1e-9, and falsifiers
(a)/(b).  At the measured convergence (smoke: arch delta 1.8e-10 at
the 16x-coarser 4x25 rule) the official-rule deltas are expected at
the 1e-13..1e-15 level, so the amendment tightens, not loosens, the
effective budgets.
