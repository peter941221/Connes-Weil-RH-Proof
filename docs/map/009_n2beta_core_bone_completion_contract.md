# 009 — N2beta core-bone completion contract

Date: 2026-09-13.

Authority: supporting status and dependency clarification. This record does
not replace the healthy-`CompactLog`, B5-shaped ruling in
[003](003_b1_b5_minimal_exit_route_selection.md), the producer-target ruling
in [007](007_b5_quantifier_repair_and_target_ladder.md), or the D0--D9
acceptance requirements in [008](008_l2_hbridge_bone_attack_plan.md). RH is
not claimed.

Evidence: formal source readback in record
[1380](../proofs/1380_n2beta_prerequisite_recon.md), the paper feasibility
analysis in [1379](../proofs/1379_n1c_joint_feasibility.md), and the
machine-checked first component in
[1381](../proofs/1381_l2_export_and_lemma_a.md).

## 1. What the current core bone is

The live total-variant offensive in [008 section 9](008_l2_hbridge_bone_attack_plan.md#9-total-variant-phase-diagram-offensive-record-1372-2026-09-1213)
needs nonnegativity of `spectralWeilValue` for the SAME healthy detector that
the formal orbit package makes strictly negative under a hypothetical
off-line zero. The pointwise vertical bridge is dead; the usable N1 object is
a local critical-line mass estimate with an error proportional to the final
detector's L2 cost.

The existing correction engine proves finite Mellin/Laplace interpolation by
surjectivity only. It exports neither a coefficient bound nor an L2 bound.
Consequently it cannot discharge the N1c norm-budget condition. The current
N2beta core bone is the following quantitative upgrade:

```text
For the actual finite orbit, vanishing, and target-value constraints, build
one smooth compactly supported correction whose assembled healthy detector
has an explicit L2 upper bound close enough to the constrained Gram optimum
to leave the N1c local-mass budget strictly positive.
```

This is a construction-and-budget obligation. It is not a new universal B1
positivity target, a producer on the rejected normalized owner, or a claim
that every finite interpolation problem has an affordable solution.

## 2. Completion ladder

The required objects must remain on one owner and one parameter choice.

1. **Finite Hilbert interpolation.** On the selected support window, identify
   the evaluation representers and prove the minimum L2 cost for the actual
   value vector. Use an inverse only after proving the Gram matrix is
   nonsingular; otherwise use a correctly stated rank/pseudoinverse result.
2. **Feasibility margin.** Compare that minimum cost with the N1c allowed
   budget for the same band and detector data. A strict margin is required;
   numerical sampling alone is not a producer.
3. **Smooth compact-support lift.** Taper the raw representers, control the
   perturbed Gram matrix and its inverse, solve the corrected finite system
   exactly, and retain a quantitative `(1 + eps)`-type L2 cost bound.
4. **Same-owner assembly.** Transfer the correction through the established
   multiplicative/log-coordinate isometry and convolution assembly. Young
   bounds must control the final assembled `CompactLogTest`, not an unrelated
   auxiliary interpolant.
5. **Quantitative consumer.** Recast the F1/F2 construction with the same
   detector's support, healthy data, values, and L2 upper bound; substitute it
   into N1c and prove a positive local-mass margin.

Record 1381 closes only the first analytic interface needed by this ladder:
`compactLogL2sq`, window Cauchy--Schwarz, and the support-weighted Laplace
evaluation bound are FORMAL and axiom-clean. That bound formalizes a necessary
anchor-cost lower bound; it does not construct an affordable correction,
prove Plancherel/localization, or prove spectral nonnegativity.

Record [1382](../proofs/1382_one_node_quantitative_mellin_gram.md) now closes
the one-node diagonal subcase of item 1: the required L2 cost lower bound,
the exact critical-line diagonal weight, and a strictly scoped budget no-go
consumer are FORMAL. It is not a multi-node Gram inverse or a feasibility
certificate for the orbit problem.

The same leaf also formalizes the configuration boundary for item 1: a
deduplicated finite-node owner carries only window/node/target/base-factor
data; exact division needs an explicit nonzero proof, and a zero factor with
nonzero target has a scoped no-correction theorem. This prevents an
unjustified inverse from entering the later multi-node construction.

## 3. What success would and would not close

If all five items above hold for one parameter choice and N1c consumes the
strict margin, then the central construction/budget obstacle for the CB-PD1
mechanism is closed: the route has a same-detector source of local
critical-line mass that survives its L2-coupled error.

This is still not an RH theorem. N3 must supply the actual-zero counting and
total signed-budget adapter, and N4 must cover the low-height/remainder
region. Only after those inputs yield nonnegative `spectralWeilValue` for the
same formal negative detector does the existing B5 contradiction interface
produce `SourceRH`.

Conversely, failure of a fixed Gram/budget comparison can formally kill that
specified support window, node family, bridge, and parameter range. It does
not kill B5, healthy `CompactLog`, or every future detector family unless its
no-go theorem quantifies over those larger classes.

## 4. Immediate work status

```text
N2beta component 1: L2 accessor and Lemma-A evaluation bound     FORMAL DONE
N2beta component 2a: one-node diagonal lower cost/no-go          FORMAL DONE
N2beta component 2b: finite Gram abstract core (positivity,
  moments identification, minimum-norm inequality)               FORMAL DONE
N2beta component 2c-core: actual Mellin representer instantiation,
  window Gram identities, same-owner cost comparison,
  closed-form entries                                      FORMAL DONE
N2beta component 2c-tail: window independence of the actual
  exponential family, Gram trivial-kernel/invertibility for
  distinct nodes, K_loc inverse-solve cost instance       FORMAL DONE
N2beta component 3: smooth taper lift to the one-plus-eps local
  budget, with the perturbed-Gram inverse consumed through the
  trivial-kernel law                                     FORMAL DONE
N2beta component 4: Young/convolution final-owner budget   FORMAL DONE
N2beta component 5: quantitative F1/F2 and N1c consumption      OPEN
N3/N4 total-budget closure                                       OPEN
```

The finite-node leaf now has the correct complex-Hilbert quadratic-form
interface: a Gram quadratic expression is exactly the inner product of the
corresponding representer sum with itself, and its real part is nonnegative.
Under a linear-independence proof for that family, every nonzero coefficient
has strictly positive real quadratic cost. This is FORMAL (WSL try16, 3547
jobs, zero errors, clean audit). It removes the invalid ordered-complex-matrix
shortcut, but does not yet establish the actual representer independence,
inverse, kernel-consistency, or minimum-cost branches.

The rank-deficient branch now has a typed compatibility boundary:
`FiniteMellinKernelCompatible` requires each right Gram-kernel vector to
annihilate the same configuration's target vector. This is FORMAL (WSL
try19, 3547 jobs, zero errors, clean audit). It is a necessary-condition API,
not a pseudoinverse, a feasibility theorem, or a claim that the actual Mellin
representers are rank-deficient.

The converse direction needed for a legitimate singular solve now begins with
a formal theorem: solvability of the finite Gram normal equations implies
`FiniteMellinKernelCompatible` (WSL try23, 3547 jobs, zero errors, clean
audit). This is still abstract finite-Hilbert machinery. An actual orbit must
separately supply the normal-equation solution or an independent reduction.

The abstract minimum-cost half of item 1 is now FORMAL (WSL try30, 3547
jobs, zero errors, zero `sorryAx`, all 24 audit prints on exactly the
standard three axioms): the Gram normal-equation row at a node is exactly
that node's inner product against the synthesized combination, every solved
system realizes all target moments, and the solved synthesis has squared norm
at most any moment-matching vector on the supplied family (abstract
Pythagoras). The ladder's "minimum L2 cost" item is therefore a precise
machine-checked statement — relative to an abstract representer family.

**Component 2c core is now FORMAL.** The leaf
`ConnesWeilRH/Dev/C1WindowMellinGram.lean` (paired Audit; WSL build
`009_window_gram_build1.log`: `Build completed successfully (3548 jobs)`,
zero errors, zero `sorryAx`, zero Dev warnings, all 14 audit prints exactly
`[propext, Classical.choice, Quot.sound]`) instantiates the exponential
window representers `r_s(x) = e^{conj(s) x}` on the genuine `CompactLogTest`
owner. It proves the Hermitian law of the concrete window Gram,
the `laplaceAt` window-restriction identity, the concrete quadratic identity
(the Gram quadratic is exactly the window integral of the squared modulus of
the representer combination), the raw-interval Cauchy–Schwarz dual bound,
and the deliverable `windowExpGram_cost_le_compactLogL2sq`: every test whose
moments factor through a solved Gram system pays at least the real Gram
quadratic cost `(star coeff ⬝ᵥ y).re ≤ compactLogL2sq f`. Both closed forms
of a window Gram entry are machine-checked: nonzero frequency
`(e^{(s+conj t)b} - e^{(s+conj t)a}) / (s+conj t)` under the explicit
nonzero premise, zero frequency the width `b - a` (the critical-line
diagonal of 1382). The path uses no `Lp`/`MemLp` API, keeps every damped
mass window-side as a genuine `ℝ`-valued integral, and registers no
independence, existence, invertibility, or feasibility claim.

**Component 2c is now complete, tail included.** The leaf
`ConnesWeilRH/Dev/C1WindowMellinIndependence.lean` (paired Audit; WSL build
`009_independence_build2.log`: `Build completed successfully (3549 jobs)`,
zero errors, zero `sorryAx`, all 7 audit prints exactly
`[propext, Classical.choice, Quot.sound]`) proves from scratch the linear
independence of the exponential family on any open window, derives the
trivial-kernel law and hence invertibility of the concrete window Gram for
distinct nodes, and instantiates the 2c cost comparison at the inverse solve,
certifying the record-1379 quantity `K_loc = y* G⁻¹ y` as a machine-checked
lower bound of `compactLogL2sq f` for every supported test realizing the
target values on distinct nodes. The rank-deficient branch is characterized:
it occurs only for coinciding nodes.

**Component 3 is now FORMAL.** The leaves
`ConnesWeilRH/Dev/C1WindowTaperCore.lean` (paired Audit; taper Gram
identities, per-node trivial-kernel invertibility of the tapered Gram for
distinct nodes, and the solve lemma) and
`ConnesWeilRH/Dev/C1WindowTaperLift.lean` (paired Audit; WSL build
`009_taperlift_accept.log`: zero errors, zero `sorryAx`, all 17 audit
prints exactly `[propext, Classical.choice, Quot.sound]`) realize the
smooth-taper lane end to end. The lift leaf proves the uniform bound of a
representer combination on the window, the strict positivity of the
untapered energy off the origin, its continuity and the sphere-minimum
spectral gap `α > 0` with `α ‖v‖² ≤ v* G v`, the sliver estimate for a
taper equal to one on a sub-window, and the `windowTaperCorrection` owner:
an actual `CompactLogTest` built from a `ContDiffBump` taper (support in
the open window, exact `laplaceAt` realization of every node value through
the SOLVED tapered system, cost at most the tapered quadratic). The budget
theorem squeezes the owner cost between the two solves,
`(α - η) · compactLogL2sq f ≤ α · (star z ⬝ᵥ y).re`, and the wrapper
delivers the contract quantity: for every `ε > 0` there exists a supported
owner realizing every node value with
`compactLogL2sq f ≤ (1 + ε) * K_loc`. The perturbed-Gram inverse is
consumed through the 1384 trivial-kernel law, so inverse stability is
machine-checked rather than assumed. No decay rate, no orbit instantiation,
and no numeric margin is registered on the formal lane.

**Component 4 is now FORMAL.** The leaf
`ConnesWeilRH/Dev/C1WindowTaperAssembly.lean` (paired Audit; WSL build
`009_taperassembly_accept.log`: `Build completed successfully (3552 jobs)`,
zero errors, zero `sorryAx`, zero Dev warnings, all 9 audit prints exactly
`[propext, Classical.choice, Quot.sound]`) puts the Young/convolution budget
on the FINAL assembled owner, not an auxiliary interpolant. It defines the
L1 accessor `compactLogL1 f = ∫ x, ‖f.test x‖`, proves the full-line
weighted discriminant Cauchy–Schwarz `(∫ W b)² ≤ (∫ W)(∫ W b²)` from
scratch (quadratic expansion via `integral_add`/`integral_smul`, the
`∫ W = 0` case killed by affine nonnegativity, the positive case read at
the vertex), and then the kernel Young law
`∫ x, ‖∫ t, F t * G (x - t)‖² ≤ (∫ ‖F‖)² * ∫ ‖G‖²` for continuous
compactly supported functions: pointwise at `x` via the triangle bound and
the weighted Cauchy–Schwarz at the weight `t ↦ ‖F t‖`, the line bound via
`integral_mono` against the REAL convolution majorant (continuous and
compactly supported by `HasCompactSupport.contDiff_convolution_right` at
`n = 0` and `HasCompactSupport.convolution`), and the Fubini swap packaged
by `integral_convolution`. Boundedness of `‖G‖` is read at the supremum
`⨆ i, ‖G i‖` through `Continuous.bddAbove_range_of_hasCompactSupport`, so
no support-window extraction enters the chain. The same-owner budget
`compactLogL2sq (f.convolution g) ≤ compactLogL1 f ^ 2 * compactLogL2sq g`
follows, the L1 factor is traded against width via the record-1381 window
Cauchy–Schwarz at the constant one (`compactLogL1_sq_le_of_window`), and the
assembly deliverable `exists_assembledOwner_cost_le` states: for any window
`Ioo c d` and any supported test `u`, the single owner `u.convolution f`
built from the record-1385 taper owner realizes `laplaceAt g (nodes i) =
laplaceAt u (nodes i) * y i` at every node, lives in the summed window
`Ioo (c + a) (d + b)`, and pays at most
`compactLogL2sq g ≤ (d - c) * compactLogL2sq u * ((1 + ε) * K_loc)` for the
record-1379 quantity `K_loc = y* G⁻¹ y`. No decay rate, no orbit
instantiation, and no numeric margin is registered on the formal lane.

What remains of 009 is component 5: the quantitative F1/F2 recast that
assembles one healthy detector and presents its `K_loc` to the N1c budget
digit-by-digit. No orbit is instantiated and no numeric margin is registered
in the formal lane.
