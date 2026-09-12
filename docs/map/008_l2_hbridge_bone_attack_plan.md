# 1369 - L2/hBridge: complete conditional proof-obligation plan for the healthy B5 exit

Date: 2026-09-12. Revised after the source-level review and the owner-authorized first paper-analysis pass.

Status: BINDING COMPANION planning record, subordinate to [003](003_b1_b5_minimal_exit_route_selection.md), [004](004_endpoint_literature_interface_audit.md), [006](006_new_math_creation_workflow.md), and [007](007_b5_quantifier_repair_and_target_ladder.md). Candidate CB-HB1 is NEEDS-ANALYSIS at the repaired Stage-0 gate. No analytic producer, bridge instance, or RH proof is claimed.

Completion contract: **if every required mathematical obligation below is proved on its stated owner, every dependency is discharged, and the final Lean acceptance passes, the result is unconditional RH.** This is a dependency-complete research plan, not a proof that the proposed mechanisms work, a success probability, or a delivery-time guarantee. Unknown analysis is explicitly part of the work.

The current route and C3 status do not change: healthy `CompactLog`, selected-detector semi-local positivity remains open. This revision corrects the internal plan; it does not authorize a universal-B1 campaign. Evidence and the superseded judgments are recorded in [1370](../proofs/1370_hbridge_plan_completeness_review.md). The former reservation of record 1370 for a numerical preregistration is withdrawn; no numerical run is authorized by this revision.

**P0 progress, 2026-09-12:** the first analytic subpass is recorded in [1371](../proofs/1371_hbridge_sampling_residual_and_scale_paper.md). It derives residual sampling, the normalized anchor's sharp L2 cost, a signed Plancherel identity, and deterministic discrepancy/bin-error estimates. These are PAPER DERIVATIONS / PROJECT CANDIDATE inputs, not Lean certificates or an actual-zeta producer. Full P0 has not passed; CB-HB1 remains NEEDS-ANALYSIS. Section 8 gives the exact results and the next proof targets.

## 1. Exact destination and the existing conditional corridor

**FORMAL SOURCE READBACK**, not a new build: [C1H2Corridor](../../ConnesWeilRH/Dev/C1H2Corridor.lean) contains the following implication (namespace qualifiers abbreviated):

```text
sourceRH_of_A2Bridge (W eps T1 : Real) (A : Int -> Real)
  (hBridge : forall g : CompactLogTest,
    CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g ->
    targetA2Schema W T1 eps A -> windowMassBalance g W)
  (hA2 : targetA2Schema W T1 eps A) :
  RHDefinitionBridge.standard.SourceRH
```

Both `hBridge` AND `hA2` are required. Batch 1560 proved this conditional implication; it did not prove either input. Geometry assumptions needed to construct `hBridge` must also be supplied, even though they do not appear as named arguments in this interface. They cannot be silently inferred from the name `A`.

[C1TargetA2](../../ConnesWeilRH/Dev/C1TargetA2.lean) defines `targetA2Schema` using only an uninterpreted `A : Int -> Real` and a counting inequality. It has no assertion that actual on-line nodes have spread at least `A`. `sourceRH_targetA2_margin_reduction` assumes RH and is a positive control only; using it to produce `hA2` for an RH proof is circular.

The all-test `windowMassBalance` hypothesis is an RH-strength target: the file proves its sufficiency for `SourceRH` and proves `SourceRH -> windowMassBalance g W` for every `g,W`. This is a logical composition of existing declarations, not a new Lean equivalence declaration. Naming that hypothesis does not reduce its difficulty.

**Active consumer under 003.** The analytic work must ultimately prove the sign for the SAME selected healthy detector and its finite visible-prime owner. The existing endpoint is
`C1HealthyYoshidaSpectralNegativity.healthy_sourceRH_of_right_detector_specific_qw_nonneg`
in [the source leaf](../../ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean).
Its existential conjunction is an exit interface, not a data structure to construct by assuming both signs. Under a hypothetical right-hand off-line zero, construct the already-formal detector, derive its nonnegativity by independent analysis, and close against its formal negativity. Map 007's prohibition on treating an inconsistent detector-and-positive-contract package as source data remains in force.

The A2 all-test theorem above is retained for interface auditing. The default campaign is its detector-selected specialization, using `qw_nonneg_of_windowMassBalance` per selected test. No universal all-test positivity campaign is opened. If a stronger lemma is proposed, its selected-detector consumer and compatibility with 003/007 must be documented before work starts.

## 2. Stage-0: repair the mathematical target before construction

These are admission checks, not assumptions that may survive the final theorem.

### S0a. Finite sampling cannot coerce the full vanishing space

**PAPER ARGUMENT; not Lean-certified here.** Fix a nonempty support interval and finitely many sampling ordinates. Smooth compactly supported complex tests on that interval form an infinite-dimensional vector space. Triple vanishing and zero values at all those ordinates impose finitely many complex linear conditions, so their common kernel still contains a nonzero test. The sampling sum is zero for that test while its L2 norm is positive. Its Fourier transform is nonzero entire, so its integral squared modulus on a nonempty frequency interval is positive as well.

Consequently no positive full-space lower bound of either form

```text
sum_j m_j |G(i gamma_j)|^2 >= c * ||g||_2^2
sum_j m_j |G(i gamma_j)|^2 >= c * integral_I |G(i t)|^2 dt
```

can hold for all such tests with `c > 0`, irrespective of the spread of finitely many nodes. Finite codimension is not finite dimension. Increasing finite occupancy with height does not remove this kernel at any fixed height. This argument rejects the literal full-space sampling shape, not the healthy B5 route or every possible remainder-bearing inequality.

Required repair: define the actual space and norm. A candidate finite-dimensional projection `P` must carry a bound on its range AND a proved estimate of the complement and cross terms for the selected detector. Alternatively propose a different precisely stated estimate that survives the kernel test. Projecting a detector does not automatically preserve detection, triple vanishing, support, or the value of `qw`.

### S0b. Off-line evaluation cannot be controlled by a vanishing denominator

For any proposed bound using the finite on-line sampling sum as denominator, test its kernel first. A finite constant requires the controlled off-line functional to vanish appropriately on that kernel. Subharmonicity or a Bernstein estimate against a continuous/global norm alone does not supply this property. A finite-dimensional replacement needs its own evaluation-operator estimate and complement control.

Fix notation: `d = |Re(rho)-1/2|`, and, only for `T > 1`, `u = d * log T`. Then `u <= c0` means `d <= c0/log T`. Constants must include the actual support/exponential-type parameter, including any detector-dependent growth. The former document used delta inconsistently in its diagram and table.

### S0c. Maximum concentration is not a frame lower bound

**SOURCE READBACK of MODEL evidence.** [1353 section 4](../proofs/1353_c6_placement_audit_and_nlle_spec_repair.md) defines `lambda_1` as the MAXIMUM interval concentration over unit vectors. Its reported values near 0.781 and 0.011 are not minimum eigenvalues on the required vanishing space. They also concern continuous interval energies, not the discrete sampling operator.

The old P0 positive/negative controls are withdrawn as controls for the target lower bound. Reproducing them calibrates only the historical concentration instrument. A finite sample Gram matrix may be positive definite on its finite span while the full sampling operator has an infinite-dimensional kernel. A future certificate must state which operator and which subspace its smallest eigenvalue belongs to and certify the omitted space separately.

### S0d. Quantifiers and algebra must agree with the source

- `CompactLogTest` is complex-valued. [C1N1SamplingContest](../../ConnesWeilRH/Dev/C1N1SamplingContest.lean), `quadOrbit_re_sum`, uses TWO Hermitian pairs. A single fourfold real-part expression requires an additional real-test symmetry theorem. Retain the exact conjugations, centered coordinates, multiplicities, and pair ownership; do not inherit the old scalar factor 4.
- `Set.encard` in A2 counts distinct zeros; `spectralTerm` weights them by `xiMultiplicity`. Either prove a quantitative conversion adequate for the energy estimates or define weighted counts and prove a new adapter. No simplicity assumption is available for free.
- `targetA2Schema` controls only near-line zeros in nonvoid windows above `T1`; `windowMassBalance` concerns ALL off-line mass in ALL integer windows. The remaining regions need independent theorems.
- The current schema uses fixed `eps`; an analytic width `eps(T)` needs a compatible new schema/adapter or an explicitly proved comparison. Check strict versus weak band boundaries and window endpoints.
- `fstar A = A/(A+2)` is algebra. The threshold must be re-derived from the actual paired, weighted estimates and every error term. `fstar_one` proves only a scalar identity. At `A = 0`, the strict A2 inequality in a nonvoid window is impossible (`count < 0`), even if its off-line count is zero. The old statement that A=0 simply forces zero off-line count is withdrawn.

## 3. Required obligations and dependency ledger

Every proposed declaration gets a preregistered type, owner, dependencies, and falsifier under 006. IDs below name planned obligations, not existing Lean declarations. All analytic rows remain OPEN. No row may be discharged merely by adding its desired conclusion as a field.

| ID | Required result | Depends on / acceptance evidence |
|---|---|---|
| D0 | Lock detector selection, original support radius, square support, finite visible-prime set, complex transform convention, window width `W > 0`, height threshold, and near-line width; state allowed dependence on rho/g/k | Retain raw target and killed-prefix equations together with the SAME support/square/tail owner; the bare detector-data existential does not export the normalized anchor values. Distinguish support radius, interpolation-ball radius and ordinate-window width; no ROOT support substitution |
| D1 | Define a valid sampling space, projection if used, spread functional `A`, weighted node measure, and all norms; supply an exact decomposition of the selected test | Section 8 / 1371 gives the PAPER residual decomposition with `P` onto `range S*`. Auxiliary L2 projections are not new CompactLog tests; a future split of `qw` needs its own form-domain proof. No unrestricted finite-sample coercivity |
| D2 | Prove actual zeta geometry supplies the D1 spread data in every required window | An analytic theorem about the real source zero set, not synthetic configurations, a definition of A as the desired sign, or an RH assumption |
| D3 | Prove the actual near-line counting/exclusion budget, with all chosen constants and multiplicities | D0-D2; independent producer of `hA2` if the unchanged A2 interface is retained; otherwise prove the corrected weighted/variable-width premise and its consumer. D2 alone does not supply D3 |
| D4 | Prove the lower sampling estimate on the admitted space, with explicit constants | D1-D2; 1371 R9 is a PAPER remainder-bearing candidate using actual multiplicity-weighted discrepancy and selected-test concentration. R10 is its killed-prefix compatibility check; neither quantitative zeta input is supplied. Historical top eigenvalues do not discharge it |
| D5 | Prove the off-line evaluation/pair estimate uniformly over the required nodes and selected tests | D0-D1; retain both complex pairs and the exact `dR`/normalization cost from 1371 R4. Fixed-d continuous positivity is not discrete or variable-d positivity; R11/R12 charge the respective errors |
| D6 | Control complement, cross, neighboring-window, far-off-line, boundary, and unbounded-height contributions with a signed budget | D1, D4-D5; include sampling-kernel residuals, horizontal-bin errors and all localization terms. Do not sum replicated whole-line Plancherel baselines without separate summability, or replace discrete square-tail control by continuous root-energy control |
| D7 | Supply low-height, negative-height, exceptional and void-window coverage | Exact certificates or analytic proofs with completeness and multiplicities; conjugation for complex tests must transport the test as needed. A finite observed zero list or a verbal verified-height claim is not a proof |
| D8 | Assemble D2-D7 into nonnegativity for the same selected detector, preserving its entire `qw` identity | Exact all-region accounting, no discarded prime or spectral term; preferred interface is per-detector `windowMassBalance`, then the existing `qw_nonneg_of_windowMassBalance` |
| D9 | Close the off-line-zero contradiction, obtain SourceRH, then Mathlib RH with no project assumptions | Existing selected-detector exit plus proved producers from D0-D8; exact source-to-Mathlib declaration checked by final import/axiom audit |

D2 and D3 may share an eventual proof, but remain separately visible obligations. Defining `A` by an infimum energy ratio proves neither its positive margin nor the required zero-count comparison. Parameter choices must be produced by theorems; choosing `eps = 0`, a void region, or a singular value of `A` cannot replace coverage of all zeros.

If the A2 interface is used literally, the closure checklist includes D2's geometry, a proved `hA2` from D3, and `hBridge` with every extra geometric/analytic premise discharged. If the interface changes, record its exact replacement and prove the new same-detector consumer; there is no implicit arrow back to the old A2 theorem.

## 4. Exact assembly contract and why completion implies RH

The following is a proof-design schema, not a claimed theorem. For the fixed selected test `g`, set

```text
q_k = windowOnLineMass g W k + windowOffLineMass g W k.
```

D1-D7 must produce actual quantities `gain_k`, `loss_k`, `error_k` and prove, for EVERY integer k,

```text
q_k >= gain_k - loss_k - error_k
loss_k + error_k <= gain_k.
```

The error ledger must enumerate every projection complement, cross term, outside-band term, and boundary contribution used by the chosen decomposition. These two displayed inequalities are output proof obligations, not permitted input fields standing in for a producer. D4 supplies gain, D3/D5 supply loss, D6/D7 supply the remaining budget; if that accounting fails, D8 stays open.

Then elementary order reasoning gives `windowMassBalance g W`. The existing `qw_window_assembly` and `qw_nonneg_of_windowMassBalance` give `0 <= qw g`. Existing detector data gives `qw g < 0` for that SAME g under the hypothetical off-line zero, hence a contradiction. Functional-equation orientation and the existing B5 exit give SourceRH and its established Mathlib translation gives RH.

A proof may instead need compensation between windows. That is not the old `windowMassBalance` contract. Before pursuing that variant, preregister an explicit summable gain/loss/error decomposition and prove its total inequality implies `qw g >= 0` via `qw_window_assembly`. Every required convergence and cancellation statement becomes part of D6/D8. This remains a same-detector B5 variant, not a second universal campaign; a bare claim that sinc-squared tails decay does not supply the total budget.

Sufficiency is therefore explicit. Feasibility remains unknown: D2-D6 may require new mathematics, and the initially proposed form may fail. Failure of an auxiliary mechanism requires a revised proof obligation; it cannot be relabeled as completed progress toward D9.

## 5. Execution order and decision gates

| Phase | Work and deliverable | Advance condition |
|---|---|---|
| P0: paper-only admission | Exact D0/D1 statements; finite-rank/kernel falsifiers; multiplicity/pair/parameter audit; anti-circularity graph; corrected A2 signature if necessary | Every surviving shape is stated precisely and survives its matched obstruction. Otherwise NEEDS-ANALYSIS or a shape-specific rejection with evidence; do not start the old numerical P0 |
| P1: actual zero-data producer | D2/D3 theorem statements, source provenance, independent geometry and count/exclusion proofs | All real-zeta premises proved, or explicitly retained OPEN; conditional harvest does not close this phase |
| P2: sampling and off-line analysis | D4/D5 proofs on the admitted owner and space | Exact constants, complex pair law, and kernel/complement obligations accounted for; no timetable guarantee |
| P3: complete residual and region coverage | D6/D7 plus full D8 assembly | Every region and remainder appears once, convergence is proved, and the quantitative budget closes |
| P4: unconditional formal acceptance | D9 with all producer proofs integrated, audit leaves, import-facing check and milestone build | Final RH theorem has no undischarged project/analytic hypotheses or nonstandard axioms |

P1 and P2 can exchange intermediate analytic lemmas only through a written acyclic dependency graph. In particular, D3 may not depend on the RH conclusion, and D2 may not obtain spread from the positivity D8 is meant to prove. No claim that P2 is independent of the repaired space or P0 outcome survives this revision.

Numerics are optional diagnostics only after a faithful model and its precise mathematical consumer exist. The default next task is P0's paper audit. Any later experiment needs its own next-available proof-record number and pre-run protocol under law 42, a finite-space positive control with proved ground truth, a structural kernel/complement control, and a truncation/error analysis. Its result is MODEL evidence under law 65. A finite failure does not kill an analytic family without a matching proof; finite success does not certify omitted directions. The 70% subjective prior and day/week cost predictions are removed.

The first P0 subpass has now executed the three proposed paper tasks: identify the selected detector's invisible sampling component, compute its support/anchor normalization cost, and compare per-window versus total assembly with explicit errors (1371). The next subpass must supply useful compatible bounds on actual weighted discrepancy and detector concentration, or on the signed cell reference and summable errors of section 8. No new sign wrapper or numerical P0 is the next deliverable.

## 6. NM cards and evidence status

- GENERATION-CARD, CB-HB1: residual sampling onto `range S*` plus a signed continuous/discrete comparison; section 8 and 1371 give exact paper estimates and matched kernel/anchor controls. New work remains the actual-zero and detector-dependent inputs of D1-D7; consumer is D8/D9 on the selected healthy owner. No mechanism is yet certified feasible.
- PRIOR-ART-CARD: PROVISIONAL. Retrieve primary statements for finite-window sampling, interpolation obstructions, prolate concentration, and complex evaluation bounds before promoting a matching analytic candidate. Record hypotheses, norms, constants, multiplicities, and the precise new lemma needed. An unsuccessful literature search is not a mathematical impossibility theorem.
- B5-TRANSLATION-CARD: D0 pins rho, g, raw target values, support and visible-prime owner; D8 proves the same-g sign; D9 consumes it. 1371 makes the dependence on `R,d,Delta,theta,M,h` explicit for its auxiliary estimates. Compatible actual-zero bounds, a joint Lean owner export, and the final budget remain open.
- SCREEN-CARD: NEEDS-ANALYSIS. The full-space finite-sample shape fails the paper argument S0a. A repaired finite-space/complement mechanism is not rejected by that argument, but has not passed screening. No blanket death of CB-HB1 or A2 on actual zeta is claimed.
- PROTOTYPE-CARD: NOT OPENED. Historical 1353 controls do not test the repaired claim. An ANALYTIC-ONLY exemption is appropriate only when recorded with its nonnumerical falsifier under 006.
- PREREG + PROVE: starts only for precisely typed surviving obligations; downstream work remains conditional until its upstream theorem is proved. No stage is marked GREEN from the existence of a conditional interface.

Historical count-only annotations in 1353/1368 are retained as provenance. Their MODEL measurements and Lean docstrings are not a formal impossibility proof for actual zeta configurations. This plan relies on exact source types and the stated finite-rank argument, not on promoting those annotations to stronger no-go theorems.

## 7. Final acceptance: what 'all tasks completed' means

All of the following are mandatory:

1. D0-D9 have named proof artifacts, and a dependency manifest distinguishes proved declarations from remaining assumptions. No OPEN entry remains on the chosen D9 path. Any replacement lemma has its exact adapter and its own complete dependency closure.
2. The final exported theorem has type `_root_.RiemannHypothesis`, with no caller-supplied `hBridge`, `hA2`, spread/zero-density premise, sign certificate, uninhabited instance, or hidden section/typeclass assumption. Internally introduced hypothetical off-line zeros are discharged by contradiction.
3. The actual transitive dependencies are audited. No `sorry`, `admit`, `sorryAx`, project RH axiom, unproved analytic axiom, or disguised stored conclusion is consumed. The final theorem and audited leaves print exactly `[propext, Classical.choice, Quot.sound]` under the repository acceptance rule. An old conditional skeleton's axioms must not leak into the chosen exit.
4. Changed Lean leaves have paired Audit modules. Use the repository ladder: owning targets, import-facing check, focused axiom audit, route/Dev batch, then full-root milestone acceptance. Build logs must contain the success footer and zero `^error:` lines; exit codes alone do not count. Sync Windows sources to the WSL build mirror and verify the byte-exact run version under the resource runner.
5. Read back the final declaration and theorem type from a clean import-facing consumer. Check its exact source-to-Mathlib translation and complete dependency report, rather than accepting a theorem merely named 'RH'. Every external or numerical ingredient has been translated into a proved Lean theorem or exact checked certificate, with provenance.

Until this acceptance is met, the result is a conditional theorem or an open research task. The plan guarantees only the stated logical implication from completion to unconditional RH; it gives no assurance that the remaining mathematical tasks are solvable by the proposed mechanisms.

## 8. First paper-analysis results and the sharpened attack

Evidence: [1371, full proofs and source readback](../proofs/1371_hbridge_sampling_residual_and_scale_paper.md).
The estimates below are PAPER DERIVATIONS / PROJECT CANDIDATE inputs.
Only the explicitly cited existing declarations are FORMAL SOURCE READBACK.
No whole D0-D9 obligation is closed by these auxiliary results.

### 8.1 Residual sampling on the actual owner (D0/D1/D4/D5)

For fixed support `[-R,R]`, use the closed complex L2 subspace with the
ACTUAL healthy moments `G(0)=G(1/2)=G(1)=0`, where
`G(z)=integral g(x) exp(z*x) dx`. With `u_z` its evaluation representer, set

```text
(Sg)_j = sqrt(m_j) G(i*gamma_j),
P = orthogonal projection onto range(S*).
```

On the nonzero finite range, S has a smallest squared singular value
`lambda > 0`, but its quantitative lower bound is still D2/D4. The exact
identities and bound are

```text
Sg = S(Pg),  S(I-P)g = 0,
|G(z)| <= ||P u_z||/sqrt(lambda) * ||Sg||
           + ||(I-P)u_z|| * ||(I-P)g||.
```

The zero-range case uses P=0 without division. This is transform analysis
of the original g; Pg is not supplied as a smooth healthy test to `qw`.

The current normalized orbit construction kills on-line sampling inside its
controlled finite prefix. There `Sg=0` and `Pg=0`, while the anchor values
remain `G(d+i*t0)=1`, `G(-d+i*t0)=-1`. Consequently, for the residual
difference representer w,

```text
w = (I-P)(u_(d+i*t0)-u_(-d+i*t0)),
4 <= ||w||^2 ||g||_2^2.
```

This is the selected-detector version of the S0 kernel check. Nodes outside
that controlled prefix are not asserted to vanish. Finite-range positivity
does not control this invisible anchor, and replacing the sampling space
must account for it explicitly. A two-anchor residual Gram gives the sharper
minimum-norm relaxation `y* K^dagger y`, `y=(1,-1)` (1371 R3); it measures
interpolation cost, not `qw` positivity or a revived Line-B finite owner.

### 8.2 Exact anchor cost and the correct small parameter (D5/D6)

For `d=Re(rho)-1/2 > 0`, the normalized anchor forces the sharp unrestricted
L2 lower bound

```text
B_R(d) = 2*sinh(2*d*R)/d - 4*R > 0,
||g||_2^2 >= 4/B_R(d).
```

At fixed R and d tending to zero, the right side is asymptotic to
`3/(2*d^2*R^3)`. Triple vanishing and killed samples can only increase this
minimum cost. The bound is exact before taking this asymptotic.
The existing selected-owner horizontal defect at the anchor is exactly
`2*xiMultiplicity rho`; it does not become small when d becomes small.
Track `dR` and normalization together. An assumption about `d log T` cannot
replace a proved bound connecting the actual detector radius R to T.

### 8.3 A concrete remainder-bearing sampling inequality (D2/D4)

For a finite weighted node measure mu in `I=[a,b)`, with positive total mass
M, define the reference density and cumulative discrepancy

```text
eta = M/(b-a),
Delta = sup_(a<=t<=b) |mu([a,t)) - eta*(t-a)|,
theta_I(g) = integral_I |G(it)|^2 dt / (2*pi*||g||_2^2),  g != 0.
```

Equal total mass removes the endpoint term. Integration against the signed
measure and Plancherel prove

```text
sum_j m_j |G(it_j)|^2
  >= 2*pi*(eta*theta_I(g)-2*R*Delta)*||g||_2^2.
```

This bound survives finite sampling kernels because its coefficient need not
be positive. On the construction's killed-prefix samples it gives the
necessary compatibility condition

```text
eta*theta_I(g) <= 2*R*Delta.
```

The new mathematical inputs are useful bounds on BOTH actual weighted
discrepancy and the concentration of the SAME selected detector, with
compatible constants. Neither node count alone nor the old maximum prolate
concentration measurement supplies them. The empty-node case is separate.
This Delta is a newly specified functional; it is NOT silently the A in
`targetA2Schema`, and it supplies no hA2 or adapter to that schema.

### 8.4 Signed continuous comparison and full error accounting (D5/D6/D8)

For fixed d define `f_d(t)=Re(G(d+it) conj(G(-d+it)))`. The paper proofs give

```text
integral_R f_d(t) dt = 2*pi*||g||_2^2,
integral_R |f_d'(t)| dt <= 4*pi*R*exp(2*abs(d)*R)*||g||_2^2,
sum_j m_j f_d(t_j)
  >= eta*integral_I f_d(t)dt
       -4*pi*R*Delta*exp(2*abs(d)*R)*||g||_2^2.
```

The first identity retains Hermitian cancellation and holds for complex g.
It is a whole-line fixed-d identity; the local integral in the last line is
still signed. For actual horizontal distances d_j in a bin with
`0<=d_j,d_*<=Dmax` and `|d_j-d_*|<=h`, an additional error is bounded by

```text
4*M*h*R^2*exp(2*Dmax*R)*||g||_2^2.
```

Each actual source zero is counted once with its analytic multiplicity;
`f_-d=f_d` handles horizontal reflection, while negative ordinates remain
separate. There is no unproved quartet factor.

For total assembly, retain a genuine partition and prove summability of
reference terms c_k and nonnegative error bounds e_k. Then
`q_k >= c_k-e_k` and `sum c_k >= sum e_k` suffice through the existing
`qw_window_assembly`. This permits compensation between windows but does not
prove the reference sign or the budget. Never sum one whole-line Plancherel
baseline per window and subtract divergent outside-window sums. The bin-error
bound above also requires localization/height decay before infinite summation.

### 8.5 Next paper work and acceptance conditions

| Task | Concrete next result | Required check |
|---|---|---|
| N0: retain the actual construction | A single owner ledger tying normalized anchor, controlled-prefix zeros, support radius and square tail to the same g | Do not merge independent existential witnesses; a joint Lean export remains unbuilt |
| N1: quantify the residual | Bound the projected evaluation Gram or the selected detector's concentration using its actual construction | Must reproduce the invisible-anchor constraint and the exact norm floor; no artificial finite-span replacement |
| N2: supply actual zero information | Prove useful weighted discrepancy and counting/exclusion bounds, with their height/window dependence | Independent zeta analysis; old hA2 is still open, and any replacement needs an explicit consumer |
| N3: close one honest signed budget | Derive reference and error terms from the fixed owner, including horizontal bins, boundaries and all omitted regions | Establish their summability and net margin; neither R6 nor norm finiteness is a positivity producer |

N1/N2 must be designed together: the proved killed-prefix inequality already
constrains how strong their constants can simultaneously be under the
off-line-zero assumption. The existing fourth-order discrete SQUARE tail is
not a bound on the continuous ROOT energy outside I. Establish that bridge
before using it to estimate theta_I. A successful independent derivation of
incompatible inequalities under the off-line-zero assumption is a legitimate
B5 contradiction; merely storing both signs as source data remains forbidden.

The symbolic controls (zero-range/kernel case, exact two-anchor L2 minimizer,
constant-function discrepancy identity, and d=0/h=0 specializations) are
recorded with proofs in 1371. They validate these auxiliary shapes only.
Full P0, D2/D3, D6/D8 and unconditional RH remain open; no new numerical or
Lean campaign is promoted by this section.
