# Record 1342 — B0a preregistration: minimum-eigenvalue falsifier search on the prime-free triple-vanishing class

Date: 2026-09-11.
Status: PREREGISTRATION (committed BEFORE any probe digit is produced, law
42). Executes beat B0a of record 1341 section 5. One-shot discipline: ONE
grid family, ONE verdict, NO ladder; a failure is adjudicated only through
the preregistered bands (gates breached => ABORTED-UNINFORMATIVE, never
arbitrated after the fact).

## 0. Objective and decision it feeds

Record 1341 dissolved the moving-family surface: the surviving gate
`forall vanishing g, 0 <= qw g` is SourceRH-equivalent in both committed
directions. B0a is the cheap formal due-diligence BEFORE that verdict is
spent: does a FALSIFIER of the gate exist on the prime-free subclass
(support of the square strictly inside (-log 2, log 2), where
`finitePrimeSum = 0` is the committed lemma
`finitePrimeSum_eq_zero_of_support_subset_open_log_two`,
`ConnesWeilRH/Dev/C1SameOwnerWeil.lean:167-189`)? A single machine-verified
`qw(g) < 0` on this class refutes the gate and therefore SourceRH (via the
committed forward capstone direction); finding none is the EXPECTED outcome
under RH (classical Weil-criterion anchor, record 1341 section 2), and its
value is calibration for the B0d owner decision: how far the prime-free
archimedean part sits from zero.

## 1. Object definitions (committed-source dictionary)

The probe runs on the 1225 MODEL dictionary (law 65: every statement below
is model-level, nothing is a Lean-side fact; the dictionary was anchored to
the committed control ground truth in 1225).

- Grid: `QS` on `[-QL, QL]`, `QL = 28.0`, `NQ = 2^17` official
  (`DQ = 56/131072`), `NQ = 2^15` smoke; constants verbatim from
  `docs/proofs/1225_positive_control_probe.py:139-145`.
- `qw_terms(g) = pole - arch - prime` of `F = g (*) g~*`: the ENTIRE
  `qw_terms` function and the control builder `build_g_control` are copied
  VERBATIM from `1225_positive_control_probe.py` (lines 270-343, 346-386).
  The `prime` loop is retained even though design guarantees it ~ 0
  (audit reports its realized magnitude; deletion is not allowed -
  constants are DATA).
- Half-density dictionary: committed vanishing at
  `cc20TripleFiniteVanishingSet = {0, 1/2, 1}` (`CC20RHExit.lean:21-24`)
  reads in this dictionary as the model `lap_h` at `{1/2, 1, 3/2}` on the
  `+1/2`-shifted side of 1225 (`build_g_control` docstring); with
  `g = e^{x/2} h` this is exactly `lap_g(sigma) = int g(x) e^{sigma x} dx =
  0` at `sigma in {0, 1/2, 1}`. The probe imposes the constraints DIRECTLY
  on `g`: `L_sigma(g) := DQ * sum(g * exp(sigma * QS)) = 0`.

## 2. Search span (registered, fixed)

- `R_root = log(2)/2` (the root window of 1225 gate C2; note the prime-free
  lemma needs the SQUARE support inside (-log 2, log 2), so `g` support
  inside `(-R_root, R_root)` suffices with margin `~2e-2` after the
  convolution).
- `m = 24` real C-infinity bumps `psi_j(x) = chi((x - c_j)/w_b)` with the
  committed 1225 `chi(u) = exp(-1/(1-u^2))` for `|u| < 1` else 0.
  Spacing self-consistency (design fix recorded at preflight, before any
  qw digit): `R = R_root - 0.01`; centers span `[-R', R']` with
  `R' = R / (1 + 1.6/m)`, `s = 2R'/m`, `w_b = 0.8 s`; then extreme bump
  support `<= R' + w_b = R < R_root` and overlaps hold because
  `2 w_b = 1.6 s > s`.
- Support is guaranteed BY CONSTRUCTION; the probe reports the realized
  max `|x|` where `|psi|` or `|g*|` exceeds `1e-15`.
- Real span suffices for a minimum search: the model form is a Hermitian
  quadratic form whose Gram on a real basis is real symmetric, so the
  complex Rayleigh minimum equals the real one on the same span (stated,
  not re-derived numerically).
- Nullspace: constraint matrix `C[j, i] = L_{sigma_j}(psi_i)` (3 x 24,
  trapezoid); orthonormal nullspace `Z` via SVD threshold `1e-10 *
  sigma_max` (`full_matrices=True` law 7c(69) applies to any wide slice -
  here only the null-space columns are taken, and the rank is CHECKED
  against 21 below).

## 3. Quadratic form assembly

- Gram by polarization on the basis: `B[i, j] = (qw(psi_i + psi_j) -
  qw(psi_i - psi_j)) / 4`, real part; `24*25/2 = 300` `qw_terms`
  evaluations, plus 3 random-vector consistency probes for gate G5.
- Reduced form `Gm = Z B Z^T`, symmetrized `(Gm + Gm^T)/2`, `lambda_min`
  by `numpy.linalg.eigvalsh` (dense 21x21).
- Witness: `g* = Z^T v_min`, rescaled to peak `|g*| = 1` (sign is
  scale-invariant), then re-measured end-to-end through `qw_terms(g*)`.

## 4. Anchors (constants are DATA, provenance cited)

- CONTROL_QW: parsed AT RUNTIME from the committed record
  `docs/proofs/1225_b5_target_satisfiability_audit_and_positive_control_preregistration.md`,
  line matching `control qw = \+([0-9.eE+-]+)` (the printed value is
  `+1.895768e-02`); never hand-typed into the script. Recomputed
  `qw_terms(build_g_control(0.03))` must match it (gate G1).
- The expected `rank(C) = 3` (independent functionals on this span) is an
  ASSERTION, not an assumption (gate G3b).

## 5. Gates and verdict bands (all preregistered; single run)

```text
G0  environment stamp: numpy/scipy/mpmath versions, mode, m, NQ.
G1  anchor: |recomputed control qw / committed - 1| < 1e-6 (the committed
    md digit carries 7 significant figures). FAIL => ABORTED-UNINFORMATIVE.
G2  support audit: realized max radius of every basis bump and of the
    witness <= R; square-radius proxy 2R < log 2 asserted numerically
    (margin printed). FAIL => ABORTED-UNINFORMATIVE.
G3  constraint quality:
    G3a  SVD of C: singular values s4/s1 < 1e-10 (exactly 3 constraints).
    G3b  rank check: on Z columns, |L_sigma(psi-mixture)| <= 1e-12 *
         ||Z||-norm scale for all sigma. FAIL => ABORTED-UNINFORMATIVE.
G4  resolution: full pipeline recomputed at NQ * 2;
    |lambda_min(2*NQ) - lambda_min(NQ)| < 1e-8. FAIL =>
    ABORTED-UNINFORMATIVE.
G5  Gram-vs-operator identity: for 3 fixed seeds, random coefficients q,
    |q^T B q - qw_terms(sum q_i psi_i)| / (1 + |qw_terms|) < 1e-9.
    FAIL => ABORTED-UNINFORMATIVE.
G6  witness consistency: |v^T Gm v - qw_terms(g*)| / (1 + |qw_terms|)
    < 1e-9, where g* is the peak-rescaled witness and v its coefficient
    vector. FAIL => ABORTED-UNINFORMATIVE.
G7  prime-free audit: realized |prime(g*)| < 1e-9 (design guarantee,
    measured, never assumed).
```

Verdict bands on `lambda_min` (official grid; NO-FIRE requires ALL gates
green):

```text
FIRE       lambda_min <= -1e-6  AND witness direct qw_terms(g*) <= -1e-6
           AND all gates green.
NO-FIRE    lambda_min >= -1e-8  AND all gates green.
ABORTED-UNINFORMATIVE   anything else (gray band (-1e-6, -1e-8) included:
           a near-zero mode at the noise edge is a rig/resolution finding,
           reported, not adjudicated).
```

Escalation clause (registered BEFORE digits): a FIRE witness is a
CANDIDATE, never a refutation by itself - the dictionary is model-level
(law 65), RH is numerically verified to large height, so the first-order
hypothesis on any FIRE is a rig artifact; the verdict record must document
the audit trail before the word falsifier is used. A NO-FIRE says exactly:
`no counterexample in the 21-dimensional real root-window vanishing span at
this resolution` - it is not a theorem about the class.

Completion acceptance: explicit `DONE 1342` sentinel printed only after all
gates pass and the JSON + verdict line are written (exit codes are not
trusted). Smoke mode (`P_SMOKE=1`, NQ=2^15, m=8, gates G2/G3/G5/G6/G7
active, G1/G4 anchor-only-scaled, `lambda` band NOT adjudicated,
`SMOKE-MACHINERY-GREEN` line) exercises machinery only; smoke digits are
non-representative (law 7c(69)).

## 6a. Registered amendments (committed BEFORE any official digit)

- inv8 (smoke-phase machinery, zero official digits under it):
  (a) reduced-form convention fixed to `Gm = Z^T B Z` for the
  column-basis nullspace `Z` (the section 3 line `Gm = Z B Z^T` was a
  transcription slip of the same statement); (b) G3a's `s4/s1` reading is
  VACUOUS for a 3 x m matrix (`s4 == 0` by shape, not by mathematics); the
  operative gate is therefore `rk == 3` AND non-degeneracy `s3/s1 > 1e-12`
  (the three vanishing functionals are independent on the span) AND
  `s_{rk+1}/s1 < 1e-10` as printed for audit; (c) the G1 anchor is
  evaluated at the 1225 committed resolution `NQ = 2^15` even in official
  mode (the committed digit is grid-dependent; constants are DATA).
- inv9 (RIG DEFECT, discovered smoke-phase by a unit test BEFORE any
  official digit - zero official digits are contaminated): the 1116-era
  hand-rolled `simpson_uniform` is a WRONG composite rule - disjoint
  `(y[3k], y[3k+1], y[3k+2])` triples skip every third subinterval; the
  sin-on-[0,pi] unit test returns exactly 2/3 of the true value. The rule
  shipped into `1116_d1_model_probe.py`, `1212_projection_trace_probe.py`,
  `1225_positive_control_probe.py` (and this probe's verbatim copy); the
  committed 1225 control "ground truth" +1.895768e-02 is a broken-rule
  number (corrected value, registered by the run: +0.1302074 - same SIGN,
  so every 1225 adjudication that keyed on positivity survives; the 1213
  H2 coefficient -3.321 is a broken-scale model constant whose
  qualitative verdict `FP != qw` is robust to the scale). NO Lean object
  is affected (the integrals there are definitions), and no 1330-1338 G8
  probe digit is affected (grep: the rule appears in exactly the four
  files above). The probe kernel is switched to `simpson_fixed` (standard
  composite Simpson + end-trapezoid for even point counts); the broken
  function is RETAINED under its old name for the provenance gate G1a.
- inv10 (anchor re-keying + fidelity gate, consequence of inv9):
  (a) G1 splits: G1a reproduces the committed broken-rule control digit
  (+1.895768e-02, rel < 1e-6) using the retained broken function - this
  proves the copied kernel is the 1225 kernel; G1b registers the CORRECTED
  control value computed by two independent paths inside the run
  (`simpson_fixed` vs `scipy.integrate.simpson` avg-mode; agreement <
  1e-10) - the corrected digit becomes the committed anchor in the JSON;
  (b) NEW gate G8 (dictionary fidelity - the check the 1212-era rig never
  had): for the control AND the witness, compare the geometric side
  `pole - arch_fixed - prime` against the spectral side
  `2 * sum_{0 < gamma_n <= T} |DQ * sum(g * exp(i*gamma_n*x))|^2`
  (multiplicity-1 zeros, both signs, mpmath `zetazero`, T ladder
  {300, 400} - corrected at registration time: the bump FT decay
  e^{-pi*w*gamma} with the official w ~ 0.021 makes T=150 tails ~3e-3,
  while at T=400 the remainder is ~3e-9; the T=300-vs-400 drift must be
  < 1e-6 AND the |geom - spect(300)| gap must be < max(1e-6,
  1e-5*|geom|) for BOTH tests). G8 failure is ABORTED-UNINFORMATIVE: it
  would mean the pole/arch/prime/square dictionary is unfaithful at some
  point beyond the quadrature fix, and no band verdict would then mean
  anything. G8 passing is the affirmative evidence that the FIRE/NO-FIRE
  sign reading is trustworthy on this span (it is the explicit-formula
  fidelity check the 1212-era rig never had);
  (c) the G4 doubling no longer needs the mod-3 length constraint (the
  fixed rule works for any grid).
- inv11 (G8 truncation ladder, smoke-phase calibration BEFORE any official
  digit - the inv10 {300,400} estimate "remainder ~3e-9 at T=400" was
  wrong): a smoke diagnostic measured the witness spectral-side tail
  convergence profile (peak-rescaled 5-dim nullspace witness, geometric
  value +2.324308785e-01):

  ```text
  T        spect(T)          band(T-prev)   resid = geom - spect(T)
  300      +2.323691480e-01  -              +6.17e-05
  400      +2.324162655e-01  +4.71e-05      +1.46e-05
  600      +2.324293196e-01  +1.31e-05      +1.56e-06
  800      +2.324306314e-01  +1.31e-06      +2.47e-07
  1200     +2.324308523e-01  +2.21e-07      +2.62e-08
  ```

  The bump Fourier tail decays sub-exponentially (Gevrey-2 bump), so the
  T=300-vs-400 drift (4.7e-5) exceeded the (unchanged) 1e-6 drift budget.
  AMENDMENT: the G8 T ladder becomes {800, 1200} for BOTH the control and
  the witness; the BAND (drift < 1e-6 AND gap < max(1e-6, 1e-5*|geom|))
  is UNCHANGED - only the truncation pair moves, chosen from the measured
  profile so the residual (+2.5e-7 at 800) and the drift (+2.2e-7 from
  800 to 1200) both sit more than one order below budget. The control was
  already sub-budget at {300,400} (gap 2.1e-07, drift 0) and remains so
  a fortiori. Justification of legitimacy: G8 is a dictionary-FIDELITY
  gate, not a FIRE/NO-FIRE band; no official digit had been produced; the
  amendment is calibrated on measured decay, not on a band outcome
  (law-42 spirit: the verdict bands of section 5 are untouched).

## 6. What this record does NOT establish

No Lean theorem, no sign statement, no claim about the full function
class, no claim that RH is or is not refuted (a model-level minimum on a
21-dim span is due diligence, nothing more), no authorization of any
ladder or rerun beyond the single preregistered resolution doubling in
G4. RH is not claimed.
