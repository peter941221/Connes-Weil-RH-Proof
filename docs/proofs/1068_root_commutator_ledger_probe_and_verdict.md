# 1068 - the D-weighted re-route's unmeasured bone: the four-branch ledger and the root commutator

Date: 2026-08-31. Follows 1067 (GROWTH -> ROUTE B: the unweighted
`IsTraceClassAlong K_S` FAILS for {2,3,5} in the model) and 1063/1066 (the
D-weighted repair, the single-contract collapse). ROUTE B consumes TWO named
contracts, and BOTH are unmeasured at root level. This probe measures them,
in the 1067 rig, before any design record is written. No numeric probe is a
proof; no PRODUCTION (生产) of any summability fact is claimed.
Probe: `docs/proofs/1068_root_commutator_ledger_probe.py`.

## 0. Operational verdict plan (stated BEFORE the run)

```text
(1) WHY THIS PROBE. The 1067 verdict routes F1' through the D-weighted
    statement, whose Lean machinery ALREADY EXISTS and is conditional on
    exactly two contracts:
      S1' : targetProlateDetectorRightSmoothingFactorSummable   (leaf :177-182)
      S2  : targetProlateDetectorRootCommutatorTraceLegality    (leaf :234-239)
    Both are root-level quantities. AGENTS 7c law (16) warns that the
    detector-level half-line pair for C†C is NOT by itself a producer for the
    root commutator, and the leaf says the same at
    C1ProlateResponseTraceLegalityUnitScale.lean:225-232 ("All four branches
    remain explicit analytic obligations here"). The 1063b saturation
    evidence measured only the COMPOSITE trace Tr(D M) - it never touched the
    branches, and a saturating trace does NOT imply what IsTraceClassAlong
    demands: `Summable fun i => <basis i, operator (basis i)>` over C
    (PositiveTrace.lean:37-39) is UNCONDITIONAL convergence, which for
    complex series is ABSOLUTE convergence. Signed operators therefore need
    their absolute diagonal mass measured, not their trace.

(2) PREDICTIONS (falsifiable, stated before running):
      P-branch  (right sandwich C† K_S C, positive):
        predicted SATURATION for every family incl {2,3,5} - any Schwartz
        convolution root beats the ~xi^0.4 raw mass (1063 owner-independence).
      Ledger L = [C, K_S]:
        predicted HS^2 SATURATION (commutator smoothing - the half-line
        boundary branches carry O(1) mass, the 1064 second-support estimate
        chain's shape).
      Ledger / S / T trace norms and absolute diagonal sums:
        GENUINELY UNKNOWN - this fork's purpose. Nobody has measured them.

(3) THE FORK (per family; {2,3,5} decides; the src S={} anchor must stay FLAT
    everywhere, else MODEL MISREAD and nothing is trusted):
      OUTCOME A (ALL SATURATE: P trace, L HS^2, L/S/T trace norms):
        the identity route is fully produceable in the model; S2 has a
        ready-made Lean supply path (the pairData theorem, leaf :243-265 /
        :301-320 - two HS legs supply S2 with NO separate trace-class proof
        of the four branches); schedule the Lean re-route brick + the two
        analytic producers with named mechanisms.
      OUTCOME B (P and L HS^2 saturate, but a TRACE NORM grows):
        the pairData route is dead at trace level (trace-class => HS, so
        HS saturation alone cannot revive it); S2 must be produced DIRECTLY
        against the named basis. The predicate-shaping question (which
        rig basis images the leaf's abstract globalBasis?) becomes
        LOAD-BEARING and must be resolved before any producer is scheduled.
      OUTCOME C (L HS^2 GROWS ~xi^alpha):
        the whole active-order identity route is dead as shaped in this
        model - escalate to Peter with the numbers before any redesign.
      MODEL MISREAD (src anchor grows, or any identity/consistency gate
        fires): trust nothing, re-audit first.

(4) GO: run the probe this round on the four 1067 octave grids, the same four
    families, Gaussian convolution roots k in {0, 1, 3} (1063b convention),
    with the dt-invariance pair at the fixed window. Acceptance = the SUMMARY
    table + every identity/consistency gate green + the committed-1067
    cross-validation reproduced, not any single number.
```

## 1. Pinned objects (every line to a file:line)

Lean side (what the contracts literally say):

| object | pin | content |
|--------|-----|---------|
| `IsTraceClassAlong basis T` | Source/CC20Concrete/PositiveTrace.lean:37-39 | `Summable fun i => ⟪basis i, T (basis i)⟫_ℂ` - the named-basis diagonal series; Summable over ℂ is unconditional = absolute |
| D-weighted statement | Dev/C1ProlateResponseTraceLegalityUnitScale.lean:118-123 | `IsTraceClassAlong globalBasis (detectorOperator ∘L targetProlateRemainder unitSoninScale family)` |
| detector D, root C | Source/CCM25Concrete/CCM24FiniteSProjectionTrace.lean:282-284; Source/CCM25Concrete/CCM24FiniteSBandTrace.lean:36-39 | D = `cc20GlobalConvolutionPositive` (positive global convolution); C = `cc20GlobalLogConvolution` (its convolution root) |
| active-order identity | leaf:350-355 | `D K_S = targetProlateDetectorRightSandwich + C†[C,K_S]`, i.e. `C†K_SC + C†(CK_S − K_SC)` |
| right sandwich = (AC)†(AC) | leaf:142-159 | smoothing factor `A C := targetProlateRemainderFactor ∘L rootConvolution`; sandwich = its adjoint-square |
| S1' contract | leaf:177-182 | `Summable ‖(A C)(basis i)‖²` - HS of the RIGHT FACTOR along the named basis (basis-independent as a total) |
| S2 contract | leaf:226-239 | `IsTraceClassAlong globalBasis (C†[C,K_S])` |
| S2 supply path | leaf:243-265, :301-320 | pairData: `traceProduct = [the ledger]` with two HS legs => S2; "deliberately does not require the four terms to be trace-class separately" |
| four-branch ledger | Source/CC20Concrete/ThreeBranchCommutatorLedger.lean:26-58; leaf:269 | `[C,K_S] = −(E Q [E,C] + E [Q,C] E + [E,C] Q E − [R,C])` with R the Sonin projection |

Rig side (the 1067 rig, unchanged, plus the detector):

| object | rig |
|--------|-----|
| E, HT_S, Q_S, R_S, K_S, FK | exactly record 1067 s1 (E = diag(t≥0); HT_S = F* M_phase Flip F; Q_S = HT_S E HT_S; R_S = P_W meet; K_S = M − R_S; FK = Q_S(E−R_S)) |
| D_k = C_k† C_k | F* diag(w_k) F, w_k(ξ) = exp(−(kξ)²/2); C_k = F* diag(√w_k) F (1063b:57-59 convention). k=0 => C = I. MODEL GAP, stated: Lean's C is the selected source-test convolution; the rig's Gaussian root is its Schwartz stand-in - the probe measures the MECHANISM (does a Schwartz convolution root regularize the branches), owner-independent per 1063 |
| basis candidates | the leaf's globalBasis is abstract; the rig measures absolute diagonal sums in BOTH window bases (t-grid delta basis, xi-character basis) and brackets the named-basis value by their range; basis-independent norms (HS², trace norm) are primary |

## 2. The identities the probe must reproduce (all Lean-proven)

```text
(ID-1)  T := D K_S  ==  P + S,   P := C† K_S C,  S := C† [C, K_S]      (leaf:350)
(ID-2)  [C, K_S]  ==  −(b_outer + b_second + b_refl − b_prol)          (leaf:269)
        b_outer = E Q [E,C];  b_second = E [Q,C] E;
        b_refl  = [E,C] Q E;  b_prol  = [R, C]
(ID-3)  ‖F_K C‖²_HS == Tr(C K_S C)   ((AC)†(AC) = C K_S C, leaf:157)
(ID-4)  k = 0: C = I => S = 0, T = K_S; absdiag_t(T) must reproduce the
        committed 1067 fk_hs_sq table to 4 decimals (rig anchor).
(ID-5)  Any orthonormal basis:  absdiag(T) <= ‖T‖_1 (trace norm) - a hard
        internal check of the SVD path in EVERY measured case.
```

## 3. Measurement plan and gates

Grids (env `GRIDS_1068`, default = 1067): `[[1025,20],[2049,20],[4097,20],[8193,20]]`.
Families (env `SLIST_1068`): `[];[2];[2,3];[2,3,5]`. Weights (env `WEIGHTS_1068`):
`[0.0, 1.0, 3.0]`; k=3 SVDs only at N <= 2049 (budget), k=0 has no SVD (T = K_S
positive: trace norm = trace).

Per (grid, family, k) quantities:
`p_hs_sq` (‖F_K C‖_F²), `p_trace` (Tr C K_S C, gate vs p_hs_sq at 1e-10),
`l_hs_sq` (‖[C,K_S]‖_F²), per-branch HS² diagnostics (outer/second/refl/prol),
`l_tr1` (SVD trace norm of the ledger), `s_hs_sq`, `s_tr1`,
`s_absdiag_t`, `s_absdiag_xi`, `t_tr1`, `t_absdiag_t`, `t_absdiag_xi`,
`t_trace_re/im`.

Gates (SystemExit(2) on failure):
- 1067 rig gates unchanged: m-sym < 1e-10; HT involution/self-adjoint < 1e-8
  (src); Q_S idempotent/self-adjoint; positivity lambda_min(B) >= -1e-6;
  W invariance.
- ID-1/ID-2/ID-3 relative residuals < 1e-10 (algebraic identities, machine).
- ID-4: k=0 `s_absdiag_t` == committed 1067 table within 5e-3 (4-decimal
  source); k=0 `‖S‖_F < 1e-10`.
- ID-5: `absdiag <= tr1·(1+1e-8) + 1e-8` whenever an SVD was taken.
- src anchor flatness: `p_hs_sq` max/min over the four octaves <= 1.5 (1067's
  src flat band was 1.15); growth => MODEL MISREAD, stop.

Cross-validation (report): the k=0 numbers reproduce 1067 s5.1 exactly;
dt-invariance pair (env `DTINV_GRIDS_1068`, default `[[4097,20],[8193,40]]`,
k=1.0) reports rel-diffs for `p_hs_sq / l_hs_sq / s_tr1 / t_tr1`; the deciding
family {2,3,5} is expected at machine level (1067 saw 5.3e-5).

## 4. Decision criteria

| outcome | criterion | consequence for the re-route |
|---------|-----------|------------------------------|
| OUTCOME A | P trace, L HS², and L/S/T trace norms all saturate over the 8x window; src flat; identities green | identity route produceable end-to-end in the model; write the D-weighted re-route design record (capstone premise swap) + schedule the two analytic producers (S1' via the Schwartz mechanism; S2 via the pairData HS-legs path) |
| OUTCOME B | P trace and L HS² saturate; at least one trace norm grows | pairData dead at trace level; the named-basis shaping question becomes load-bearing; next brick = pin the leaf's globalBasis rig image before anything else |
| OUTCOME C | L HS² grows ~xi^alpha | active-order identity route dead as shaped in this model; full redesign, escalate with the numbers |
| MODEL MISREAD | src anchor grows or any gate fires | no verdict; re-audit the model reading |

## 5. Post-run addendum (filled after execution)

Run: two deterministic WSL runs - (a) the dt-invariance leg at the real pair
`[[4097,20],[8193,40]]` for all four families, k=1.0; (b) the four-octave
sweep (48 SUMMARY lines, complete log `/home/peter/1068_sweep.log`, Linux-side
verification environment, unversioned per the 1063 convention; case npz under
`/home/peter/1068_out/`). Acceptance rests on the flushed logs + saved npz,
not exit codes (AGENTS 7a). All gates green: m-sym 0, HT involution ~1e-13,
Q_S idempotent, positivity, every ID-1/2/3 residual <= 1e-11, every ID-4
anchor matched the committed 1067 table, every ID-5 absdiag <= trace-norm
check passed, src anchor flat gate 1.006 <= 1.5.

### 5.1 The measured fork table (k = 1.0, primary Gaussian weight)

```text
Deciding family {2,3,5}, octaves xi_max = 12.8 / 25.6 / 51.2 / 102.4:
+-----------+----------+----------+----------+----------+-----------------+
| quantity  | N1025    | N2049    | N4097    | N8193    | shape           |
+-----------+----------+----------+----------+----------+-----------------+
| p_hs_sq   |  3.5661  |  3.5458  |  3.5383  |  3.5356  | DECREASING      |
| l_hs_sq   |  0.2086  |  0.1855  |  0.1739  |  0.1688  | DECREASING      |
| l_tr1     |  1.3462  |  1.3145  |  1.2910  |  1.2850  | DECREASING      |
| s_tr1     |  0.5800  |  0.5569  |  0.5448  |  0.5395  | DECREASING      |
| t_tr1     |  3.7836  |  3.7527  |  3.7376  |  3.7319  | DECREASING      |
| (k=0 ctr) | 16.1996  |  20.1700 |  26.8715 |  34.2696 | growth, = 1067  |
+-----------+----------+----------+----------+----------+-----------------+
src anchor (k=1): p_hs_sq 2.3998/2.3905/2.3864/2.3844 (octave ratio 1.006);
the other three families have the SAME flat/decreasing shape (e.g. t_tr1:
src 2.58 -> 2.56, {2} 3.09 -> 3.07, {2,3} 3.52 -> 3.48).  k=3 rows are
smaller with the same shape (e.g. {2,3,5} p_hs_sq 2.50 at N8193).
```

Every k=0 row reproduces the committed 1067 s5.1 table within 5e-3 on the
same code path, and the strict meet d = 39/114/299/742 differs from 1067's
gap-split counts 42/117/303/746 by exactly the near-meet fringe {3,3,4,4} of
1067 s5.3 - two independent cross-validations.

### 5.2 VERDICT: OUTCOME A (all saturate - a fortiori, monotone DECREASE)

Per the pre-stated fork s0(3)/s4: no measured quantity grows anywhere; the
D-weighted branch quantities are O(1) constants that DECREASE slightly while
the unweighted control on the SAME rig grows +112% over the same octaves.
The three Lean identity residuals sit at 1e-15, dt-invariance at the real
pair is <= 3e-4 for every family, and the source anchor is flat.

```text
CONSEQUENCES (per s4 OUTCOME A):
  1. The D-weighted identity route IS produceable in the model. The next
     brick is the DESIGN RECORD for the Lean re-route: route the capstone
     premise through targetProlateRemainderDetectorWeightedTraceLegality_
     of_rightSmoothing_and_rootCommutator (leaf:370-381) instead of the
     single-contract S2-FK-HS corollary; all owner machinery already exists
     and is axiom-clean.
  2. Producer P1 (S1'): continuum HS of F_K oL C for the ACTUAL selected
     convolution root.  The probe's Gaussian root is the Schwartz stand-in
     (model gap, s1); the owner-independence transfer (1063: any Schwartz
     beats the ~xi^0.4 raw mass) must be argued per-owner in the record.
  3. Producer P2 (S2): four-branch ledger trace-legality via the pairData
     path (leaf:243-265/:301-320) - measured ||[C,K_S]||_1 ~ 1.29 flat.
     The proof class is the classical commutator-smoothing adaptation; the
     named difficulty is the quasi-periodic twist mu_S/conj(mu_S), exactly
     the mechanism that killed raw F1 (1063).
  4. NO Lean change this round (probe + record only).  1067's ROUTE B
     verdict stands; this record supplies the route's produceability
     evidence, not a proof.
```

### 5.3 Structural finds (banked for the design record)

```text
(1) BASIS-INDEPENDENCE IS FORCED, AND HELPS.  Every contract in the leaf
    quantifies universally over globalBasis (e.g. leaf:118-123, :177-182,
    :234-239) - a producer must supply the SAME arbitrary basis the
    downstream consumer uses, so no basis choice is available.  The correct
    produceable target is therefore basis-independent: trace-class-ness
    (any ONB satisfies sum |diag| <= ||T||_1), supplied via the pairData
    HS-legs path.  Consistently: in the xi-character basis (which
    diagonalizes C) the diagonal of S = C†[C,K_S] is ALGEBRAICALLY ZERO
    (measured 0.0000 to machine precision in every case) - the S2 danger
    lives only in bases not aligned with C, and the trace-norm route
    bypasses that分歧 entirely.
(2) BRANCH SHAPE: br_out = br_refl exactly (Hermitian symmetry), the
    second-support branch carries the most mass, and the Sonin branch
    collapses under k=3 (5.6e-2 -> 1e-5): the R-commutator is concentrated
    where the detector is.
(3) The ledger HS^2 and trace norms are not merely bounded but DECREASING
    in the window - consistent with the commutator being a boundary object
    (1064's second-support shape), not a bulk object.
```
