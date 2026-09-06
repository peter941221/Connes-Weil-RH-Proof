# Record 1212 - Projection-trace renormalization probe (pre-registration)

Date: 2026-09-06.  Status: PRE-REGISTRATION, committed BEFORE any run.

Consumer: `RH_MAINLINE_FREEZE.md` Allowed Work item 3 — semi-local
positive-trace/readback data for the selected detector on the healthy
owner.  This record pre-registers a numerical probe only.  It claims no
Lean theorem, no P2, no SourceRH, and no RH.

## 1. Why this probe (the formal hole it feeds)

Records 1210 and 1211 pin the only live shape of the positive-trace exit:

- 1210 (`not_nonempty_cutoffLimitContracts_of_test_ne_zero`,
  `C1PositiveTraceCutoffVerdict`): the plain-window cutoff traces equal
  `(cutoffUpper - cutoffLower) * integral ||g.test||^2` exactly, so they
  grow linearly without bound, while `CutoffLimitContracts.readback_tendsto_qw`
  plus `remainder_tendsto_zero` would force the same traces to converge to
  the finite `qw g`.  The contract type is empty for every nonzero test.
- 1211
  (`not_projectionCutoffLimitContracts_of_fixedResponse_and_traceDefect_vanishing`,
  `C1Stage3ProjectionContractObstruction`): the projection owner
  `C_n^* K C_n` is positive and trace class at every cutoff, but if the
  remainder-corrected trace readback converges to `qw`, the insertion
  defect's real trace tends to zero, and the response is fixed, then the
  exact three-owner ledger forces the window-to-response defect to be
  bounded, contradicting the cofinal unbounded-trace theorem.

Together these leave exactly two non-self-contradictory shapes for the
projection route, as stated in the 1211 module docstring: (A) retain a
DIVERGENT counterterm in the insertion trace and read back `qw` from the
renormalized finite part, or (B) use a genuinely moving/renormalized
response.  This probe tests shape (A) numerically on the pinned model
detector.  Shape (B) is not probed here.

## 2. Pinned objects (verbatim Lean conventions)

Operator family (`ConnesWeilRH/Dev/C1Stage3ProjectionWindow.lean`,
`C1PositiveTraceCutoffAdapter.lean`, `C1Stage3ProjectionKernel.lean`):

```text
cutoffRadius g n = C1SameOwnerWeil.supportRadius g + n + 1
cutoffLower g n  = -cutoffRadius g n
cutoffUpper g n  =  cutoffRadius g n
C_n = fullBoundaryPositiveOperator g (cutoffLower g n) (cutoffUpper g n)
    = fullBoundaryOutputZeroExtension a c oL fullBoundaryRootFactor g a c
K   = stage3ProjectionKernel lambda S
    = P_r oL P_f oL P_r - gramCorrectedTargetSoninProjection
      (P_r = star projection of ccm24LogRadialSupportClosedSubspace lambda,
       P_f = star projection of
             ccm24SemilocalFourierSupportClosedSubspace lambda S)
T_n = Re ordinaryTraceAlong globalBasis (C_n^* o K o C_n)
```

Exact ledger identities (`C1Stage3ProjectionOperatorFamily`; identities,
not estimates):

```text
ordinaryTraceAlong_cutoffProjectionOperator_eq_projectionResponse_add_defects:
  tr(T_n object) = tr(projectionResponse)
                 + tr(kernelInsertionSandwich(g, L_n, U_n, lambda, S))
                 + tr(windowToResponseDefect(owner, L_n, U_n, lambda, S))

realTrace_cutoffProjectionOperator_eq_selectedArithmetic_add_defects:
  T_n = selectedArithmeticCarrierSum owner + Re tr(sameObjectResidual)
        + Re tr(kernelInsertionSandwich) + Re tr(windowToResponseDefect)
```

Detector: the record-1116 model twin conventions at k=1, verbatim (orbit
target values, `e^{x/2}` half-density shift, `2sinh` archimedean
denominator, `Lambda(q)/sqrt(q)` visible primes).  This is the only
detector shape already validated S0 7/7 against Lean conventions in this
campaign.  The twin is labeled MODEL throughout (law 65); the comparison
`FP_n` vs `qw(g)` is same-owner by construction because both sides are
computed on the same conventions.

## 3. The probe questions

```text
Q0  Stability: is Re tr(projectionResponse) numerically stable across the
    ladder (it is n-independent by definition)?  This is evidence toward,
    not proof of, the trace-class premise hresponse of 1211.
Q1  Counterterm shape: does Re tr(kernelInsertionSandwich(L_n, U_n))
    diverge, and with which leading asymptotics c_n?  Primary candidate:
    linear in the window length 2 R_n with coefficient the window bulk
    mass (the 1210 mechanism transported to the projection family).
Q2  Finite part: with c_n fixed from Q1, does FP_n := T_n - c_n converge?
    If so, to what: qw(g) or something else?
Q3  Fidelity: does the exact three-owner ledger identity hold numerically
    to quadrature/discretization tolerance at every probed n, computed as
    three independent paths (law-47 style round trip)?
```

## 4. Pre-registered verdict branches

```text
H1 (renormalized identity TRUE):
    Q1 yields a clean c_n - a leading term whose fit residual stays within
    the measured noise floor across two consecutive ladder refinements -
    AND FP_n settles within the acceptance band of qw(g).
  Consequence: the next Lean brick is a finite-part/counterterm identity
  STATEMENT (renormalized ProjectionCutoffLimitContracts with an explicit
  divergent-counterterm field), pre-registered separately.  No RH claim
  attaches to H1.

H2 (refutation):
    FP_n settles outside the acceptance band, or fails to settle under the
    full ladder.
  Consequence: exit A is closed for this family; record the no-go and
  pivot to exit B (moving/renormalized response) or the 1209 signed-tail
  route.

No rescoping after the first official run (law 42).  If Q1 itself is
ambiguous - no leading term separates from the noise - the run is recorded
as ABORTED-UNINFORMATIVE, not reinterpreted (1097 protocol).  A third
branch is deliberately NOT registered.
```

## 5. Machine, ladder, budgets, noise floor

- WSL2, in-house only (no external AI, directive 2026-09-03):
  `mpmath` dps=40 for envelope/coefficient data, `numpy` float64 for the
  operator matrices, `uv run` through the resource runner.
- Window ladder: `R_n = R0 + n + 1` for `n in {8, 16, 32, 64}`, R0 from
  the pinned detector's `supportRadius`.  At each rung, a dt-refinement
  pair (coarse, fine = coarse/2); matrix dimension cap 16385 (the 1097
  budget precedent: (32769, 40) at 17.2 GiB is OUT of budget).
- Finite-size extrapolation stays WITHIN the registered ladder; no
  two-point fit may pick a third-point prediction without a refit
  (law 60).
- Noise floor, pinned before the run: relative quadrature tolerance
  `eps_q = 1e-8` per trace path on O(1) paths.  The H1 acceptance band is
  `|FP_inf - qw(g)| <= 10 * eps_effective`, where `eps_effective` is the
  MEASURED worst-path discrepancy across the ladder (coarse-vs-fine), not
  the nominal floor.
- `qw(g)` on the twin is computed by an independent path (certified
  interval Weil machinery, records 1101/1102 method) and cross-checked
  against the direct quadrature path before any verdict readout.
- Gate S0 (must be green before any sign readout): 1116-style
  lean-convention fidelity checks, the ledger identity Q3 at machine
  precision on the coarsest rung, and dt-invariance of the response path
  at the real pair.

## 6. Falsifiers / abort protocol

- If the discretization cannot resolve the window at `n = 64` within
  budget, report the ladder actually run; do NOT silently shrink the
  window, rescale the detector, or raise the cap.
- If `T_n` or any ledger path flips sign under dt refinement: ABORT-REACT
  with a canary audit (laws 53/54: measured leverage before any fix).
- No statement weakening, no `native_decide`, no q28 box changes, and no
  Line-B content (Line B is frozen by record 1196 and requires Peter's
  explicit instruction).

## 7. What this record does NOT claim

No Lean theorem is added by the probe.  A green H1 authorizes only a
future, separately pre-registered formal brick (the renormalized contract
statement).  P2, SourceRH, and RH remain open and unclaimed.
