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

## 6. What this record does NOT establish

No Lean theorem, no sign statement, no claim about the full function
class, no claim that RH is or is not refuted (a model-level minimum on a
21-dim span is due diligence, nothing more), no authorization of any
ladder or rerun beyond the single preregistered resolution doubling in
G4. RH is not claimed.
