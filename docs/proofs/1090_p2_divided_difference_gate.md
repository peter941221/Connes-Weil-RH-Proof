# 1090 - P2 Route-1 gate pre-registration: the divided-difference commutator-smoothing route

Date: 2026-09-01. Follows 1073 (the D-weighted re-route that OWES producers P1/P2)
and 1068 (OUTCOME A: every D-weighted quantity O(1), monotone DECREASING over four
octaves). This record pre-registers the attack on **producer P2** before any numeric
probe is run, per the house rule that a falsifiable fork must exist before data.

Numbering note: this resumes the paused F1'/P1/P2 producer thread (lineage 1063 ->
1073). Committed HEAD is record 1087; numbers 1088 and 1089 are reserved in prose for
mainline ("endpoint audit = map 004" already delivered as `docs/map/004`; "CC20 re-anchor
design"). To avoid colliding with either reservation, this record takes the next free
number **1090**, assigned out of sequence. RH is unclaimed; GATE 1 mainline untouched.

## 0. The contract being produced (what P2 literally says)

```text
P2 = S2 = targetProlateDetectorRootCommutatorTraceLegality        (leaf:234-239)
     : IsTraceClassAlong globalBasis (cc20Commutator C K_S adjoint-dressed)
       i.e. Summable fun i => <globalBasis i, C^dagger[C,K_S](globalBasis i)>  over C
       (PositiveTrace.lean:37-39; Summable over C = UNCONDITIONAL = ABSOLUTE)

Consumed via ONE BasisHilbertSchmidtPairData whose traceProduct is the whole signed
four-branch ledger [C,K_S], through
     targetProlateDetectorRootCommutatorTraceLegality_of_threeBranchPairData  (leaf:301-318)
so NO per-branch trace-classness is required - two L^2 legs supply S2 by Cauchy-Schwarz
(traceProduct_isTraceClassAlong). The four branches are the ledger of 1068 s2 / 1073 s2:
     [C,K_S] = -(b_outer + b_second + b_refl - b_prol)
```

**Route 1 (the route pre-registered here)** is the classical commutator-smoothing
argument: `[Op(a), P]` with `a` a smooth, rapidly-decaying symbol and `P` a nice
projection is trace-class because the off-diagonal carries a divided difference
`(a(xi) - a(eta)) ~ (xi-eta) * avg_deriv`, which is an L^2 object. The removed diagonal
is represented by one committed object (`DividedDifferenceKernel.lean`) rather than an
`if xi = eta` case split.

## 1. Q1 - does C fit the divided-difference infrastructure?   [RESOLVED: YES]

The load-bearing worry from brainstorm was "C is a log-symbol; must it be verified C^1
on bounded support?" Reading the source shows that worry was over-cautious: the TYPE
already guarantees full regularity.

| object | pin | content |
|--------|-----|---------|
| C's symbol is `F(h)` in S(R) | Source/CC20Concrete/GlobalLogConvolution.lean:27-30, :43-44 | `cc20FourierMultiplier (h : SchwartzMap R C)` builds `(F h).toLp top`; `cc20GlobalLogConvolution (h : SchwartzMap R C)` is the operator itself. In xi-basis C is multiplication by `F(h)`, and Fourier is an automorphism of the Schwartz space, so `F(h) in S(R)`. |
| divided-difference witness for ANY Schwartz f | Source/CC20Concrete/DividedDifferenceKernel.lean:36-46 | `cc20DividedDifferenceDataOfSchwartz (f : SchwartzMap R C) : CC20DividedDifferenceData` - header: "Every complex Schwartz test function supplies the regularity witness WITHOUT an additional analytic premise." value := f, derivative := derivCLM, hasDerivAt via f.hasDerivAt. |
| the diagonal-removal identity | DividedDifferenceKernel.lean:67-84 | `cc20SegmentAverageDerivative_smul_eq_sub`: `(s - t) * segAvg(derivative)(s,t) = value s - value t`. This is exactly what turns `[Op(a),P]`'s removable singularity into a continuous L^2 kernel. |
| the witness structure itself | DividedDifferenceKernel.lean:29-32 | `CC20DividedDifferenceData { value : ContinuousMap; derivative : ContinuousMap; hasDerivAt }`. |

Argument (type-level, no numeric probe):

```text
  h : SchwartzMap R C          (C's convolution parameter)
      |  Fourier: S -> S is an automorphism
      v
  F(h) in S(R)                 (GlobalLogConvolution.lean:27-30)
      |  cc20DividedDifferenceDataOfSchwartz : S -> CC20DividedDifferenceData   (:36-46)
      v
  data := cc20DividedDifferenceDataOfSchwartz (F h) : CC20DividedDifferenceData
      |  segAvg identity                                          (:67-84)
      v
  [Op(F h), .] off-diagonal = (xi - eta) * bounded_segment_average   -> L^2 candidate
```

**Gate CLOSED.** C qualifies for Route 1 by construction; no separate "C is C^1 /
Schwartz symbol" lemma is owed. The infrastructure (`CC20DividedDifferenceData`, the
segment-average kernel, its audit) is already committed and actively imported (7 importers
incl. `RootSandwichedTrace.lean`, a sibling `MovingDividedDifferenceKernel.lean`), so dedup
matters when the Lean brick lands - see Next steps.

Residual pin-to-complete (does NOT block the gate): which specific `h` instantiates C as the
convolution ROOT of D = cc20GlobalConvolutionPositive in P2 (1068 s1 pins "C = the
convolution root"). Any Schwartz h works for Q1; the exact owner matters only for the final
numeric/owner transfer, which is owed regardless.

## 2. Q2 - does the divided-difference split give O(1) Hilbert-Schmidt legs?   [RESOLVED: Q2-OPTIMAL-TERMS, see s4]

### 2a. What committed data ALREADY says (this shrinks the question)

From 1068 s5.1, deciding family {2,3,5}, k=1, four octaves:

```text
+-----------+----------+----------+----------+----------+-----------------+
| quantity  | N1025    | N2049    | N4097    | N8193    | shape           |
+-----------+----------+----------+----------+----------+-----------------+
| l_hs_sq   |  0.2086  |  0.1855  |  0.1739  |  0.1688  | DECREASING      |   ||[C,K_S]||_F^2
| l_tr1     |  1.3462  |  1.3145  |  1.2910  |  1.2850  | DECREASING      |   ||[C,K_S]||_nuclear
+-----------+----------+----------+----------+----------+-----------------+
```

`l_tr1 = ||[C,K_S]||_nuclear` is O(1) and decreasing. Nuclearity implies trace-classness
along ANY orthonormal basis (`` Summable <basis i, T(basis i)> <= ||T||_nuclear ``), which is
precisely what S2 demands for the universally-quantified `globalBasis`. So **P2's conclusion
already holds in the model.** The probe is not testing whether P2 can be true - it is.

### 2b. What Q2 therefore reduces to

Not "life/death" but a CONSTRUCTION question: does a NAMED two-leg factorization of
`[C,K_S]` (the divided-difference kernel on one leg, a K_S-derived object on the other)
have BOTH legs O(1)-Hilbert-Schmidt? If yes, the Lean `BasisHilbertSchmidtPairData` is built
from named analytic objects; if only an SVD-eigenvector factorization stays bounded, P2 still
holds (nuclearity) but the brick needs a different - less transparent - leg construction.

### 2c. Why the twist does not add decay-loss here

The raw-F1 killer was the quasi-periodic twist `mu_S / conj(mu_S)` in the target multiplier
(1063). But it is a PURE PHASE (`|mu_S/conj mu_S| = 1`), hence POINTWISE-INVISIBLE to any
`|kernel|`-based HS or nuclear estimate; it only becomes dangerous if one DIFFERENTIATES the
symbol (the PsiDO bracket `{phi, psi}`). C's own symbol `F(h)` carries no twist; the twist
lives in HT_S/K_S, and K_S enters as the L^2 leg that 1068 already bounds O(1). So Route 1's
divided-difference split does not inherit extra decay-loss from the twist.

### 2d. PROBE-P2 specification (reuse the 1067/1068 rig)

In xi-basis C is diagonal `diag(c_amp)` with `c_amp(xi)=exp(-(k xi)^2/4)`, and
`K_tilde_S = F K_S F*`. Then `[C,K_S]` kernel is the pointwise product

```text
  L(xi,eta) = (c_amp(xi) - c_amp(eta)) * K_tilde_S(xi,eta).
```

Measure per (grid, family {2,3,5}, k=1), four octaves + dt-invariance pair:
- CROSS-VALIDATION anchor: `||L||_F^2` and SVD nuclear norm of L must REPRODUCE 1068's
  `l_hs_sq` / `l_tr1` to the committed table (if they drift, MODEL MISREAD).
- NAMED LEGS - the actual Q2 output; both must be O(1) over octaves:
    leg_K   = Hilbert-Schmidt norm of K_tilde_S-derived L^2 leg,
    leg_dD  = Hilbert-Schmidt norm of the divided-difference (symbol-difference) leg.

### 2e. The fork (stated before running)

```text
Q2-OPTIMAL   both legs O(1) (flat/decreasing): P2 = PLUMBING on the committed
             ContinuousKernelHilbertSchmidt / pairData path with NAMED legs; schedule the Lean brick.
Q2-PARTIAL   a leg grows ~ xi^alpha but ||L||_nuclear stays O(1) (as 1068 says): ROUTE STILL ALIVE,
             the named split needs finer windowing/absorption - escalate WITH NUMBERS to pick the
             split shape before writing Lean. (Construction hint, not route death.)
Q2-MISREAD   ||L||_F or ||L||_nuclear GROWS (contradicting committed 1068): re-audit the model reading first.
```

## 3. Honesty ledger / what does NOT change

- Q1 is resolved by TYPE argument (no numeric probe); Q2 was resolved by PROBE-P2 on
  2026-09-01 (result s4, branch **Q2-OPTIMAL-TERMS**). No Lean object added this turn yet;
  RH unclaimed; GATE 1 mainline untouched. The next owed step is the named-legs brick (s5).
- The model's C remains the Gaussian Schwartz STAND-IN (1068 s1) - the owner transfer to the
  actual selected root is still owed, but Q1 now shows it is a non-issue for the gate: any
  Schwartz h qualifies identically.
- Number 1090 assigned out of sequence to clear mainline's reserved 1088/1089; flagged here
  and in memory so neither number is double-claimed when mainline resumes.

## 4. PROBE-P2 RESULT (run accepted 2026-09-01, log evidence per AGENTS 7a)

Probe: `docs/proofs/1090_p2_divided_difference_probe.py` (imports the committed 1068 module
via importlib; context build + identity gates are byte-identical to record 1068). Run in WSL2
on ext4, four-octave {2,3,5} k=1 sweep + dt-invariance pair, log flushed on the Linux side.

### 4a. Decision table (verbatim from the run log)

```text
=== PROBE-P2 DECISION TABLE (S={2,3,5}, k=1; O(1) => |slope| < 0.15) ===
quantity                |N1025  N2049  N4097  N8193   slope8x
-------------------------------------------------------------
||L||_F^2 (anchor)      |   0.2086   0.1855   0.1739   0.1688  -0.102
||L||_nuc witness       |   1.3462   1.3145   1.2910   1.2850  -0.022
C o K_S HS^2 (named)    |   2.4673   2.4451   2.4369   2.4340  -0.007
K_S o C HS^2 (named)    |   2.4673   2.4451   2.4369   2.4340  -0.007
C o K_S nuclear         |   4.6636   4.6391   4.6280   4.6266  -0.004
K_S o C nuclear         |   4.6636   4.6391   4.6280   4.6266  -0.004
||K_S||_F^2 (control)   |   8.3477   8.3830  10.1132  11.4231  +0.151
```

Anchors reproduce committed record-1068 s5.1 to ~1e-5 at every grid (per-grid log lines, e.g.):

```text
[anchor 1068] l_hs_sq 0.2086 vs 0.2086 (d=2.42e-05); l_tr1 1.3462 vs 1.3462 (d=2.50e-05)  => OK
[anchor 1068] l_hs_sq 0.1688 ...; l_tr1 1.2850 ...  => OK        (N=8193, all four grids green)
```

=> **MODEL CONSISTENT** (no Q2-MISREAD): the probe's code path is byte-identical to the one that
produced the committed table, so every quantity measured below is trustworthy.

### 4b. dt-invariance (law 15: quantities track the WINDOW, not the grid)

```text
SUMMARY|dtinv|S[2,3,5]|l_hs_sq: 0.1739 vs 0.1739 (rel 1.62e-04)
        l_tr1: 1.2910 vs 1.2906 (rel 3.09e-04)
        ck_hs_sq: 2.4369 vs 2.4385 (rel 6.55e-04)
        kc_hs_sq: 2.4369 vs 2.4385 (rel 6.55e-04)
```

Fixed window, two resolutions: every O(1) quantity agrees to <7e-4 relative. The flatness in s4a
is therefore a property of the frequency WINDOW, not a grid-resolution artifact.

### 4c. Verdict (machine-printed line, verbatim)

```text
=== VERDICT ===
Q2-OPTIMAL-TERMS: L nuclear O(1) AND both named terms are NUCLEAR O(1)
(ck_tr1 slope -0.004, kc_tr1 -0.004); Lean brick may use PER-TERM pairData + isTraceClassAlong_add.
```

### 4d. Reading of the result

Two independent facts, both decisive:

1. **P2's conclusion holds in the model.** `||L||_nuclear = ||[C,K_S]||_nuclear` is O(1) and
   decreasing (slope -0.022). Nuclearity gives `Summable <b i, T(b_i)> <= ||T||_nuclear` along ANY
   orthonormal basis, which is exactly S2's universally-quantified `globalBasis`.

2. **Stronger than pre-registered: the split can be PER-TERM.** It was not only the combined
   divided-difference object that is nuclear-O(1); each NAMED commutator term `C o K_S` and
   `K_S o C` is INDIVIDUALLY nuclear with a flat O(1) norm (4.63, slope -0.004). The raw control
   `||K_S||_F^2` grows (+0.151), so the growth is real and is absorbed by the Schwartz symbol
   `c_amp`: in xi-basis C is diagonal `diag(c_amp)`, and weighting K_tilde's rows by the decaying
   Gaussian keeps `Diag(c_amp).K_tilde` nuclear-bounded - the same "any Schwartz weight beats the
   sub-polynomial raw mass" mechanism as 1063/1068.

Construction consequence (what this licenses, and what it does NOT yet prove):

```text
  L = [C,K_S] = C o K_S  -  K_S o C            (two named nuclear-O(1) operators)
      |                       |
      v                       v
  pairData_A: traceProduct = C o K_S     pairData_B: traceProduct = K_S o C
   (legs O(1)-HS; balanced-SVD bound    (same; legs O(1)-HS)
    ||leg||_F^2 <= nuclear(C o K_S) ~ 4.63)
      |                       |
      +----- isTraceClassAlong_add / _smul -----+
                                                  v
                        IsTraceClassAlong globalBasis [C,K_S]   =  S2
```

Because each term is individually NUCLEAR O(1), a bounded-leg `BasisHilbertSchmidtPairData` for
each term EXISTS (balanced-SVD legs have HS-norm^2 at most the nuclear norm). This is cleaner than
the pre-registered Q2-OPTIMAL-COMBINED fallback: no need to build one combined divided-difference
object. What remains owed (s5) is the NAMED leg construction - exhibit explicit analytic left/right
maps for `C o K_S` and `K_S o C` with square-summable columns and PROVE it; the flatness above is
the existence + uniform-bound evidence, not yet a Lean proof.

## 5. Next steps (after accepting s4)

1. [DONE] Author + run PROBE-P2 in WSL2; accept on flushed log evidence; all gates green; verdict
   Q2-OPTIMAL-TERMS recorded above.
2. OWED - land the Lean `BasisHilbertSchmidtPairData` brick for S2 via PER-TERM legs: one pairData
   with traceProduct = C o K_S and one with traceProduct = K_S o C (each O(1)-HS legs), combined by
   `isTraceClassAlong_add` (+ `_smul`) to yield IsTraceClassAlong [C,K_S]. Dedup against the 7
   existing importers of `DividedDifferenceKernel.lean` before adding a new leg helper; prefer the
   committed `ContinuousKernelHilbertSchmidt` / pairData path (PositiveTrace.lean:249-295).
3. OWED - owner transfer: replace the Gaussian Schwartz STAND-IN root with the ACTUAL selected
   convolution root per-owner (1068 s1; Q1 shows any Schwartz h qualifies identically, so this is a
   bounded bookkeeping step, not a gate re-open).
