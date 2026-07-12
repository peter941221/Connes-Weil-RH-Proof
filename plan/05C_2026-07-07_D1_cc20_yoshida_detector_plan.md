# 05C D1 CC20 Yoshida Detector Plan

Date: 2026-07-07

Status: the single 05C plan file.  Do not create sibling `05C*` subplans.
Keep tree splits, status updates, rejection scans, build gates, and focused
axiom audits in this file.


## 1. Result First

Hard completion gate:

```text
Good for 05C:
  Lean proves:

    Source.normalizedCC20YoshidaDetectorExists :
      Source.CC20YoshidaDetectorExists
        Source.normalizedCC20TestSpace
        Source.cc20TripleFiniteVanishingSet

  The proof must construct the detector from a concrete compact test in
  normalizedCC20TestSpace.  It may not assume detector existence.

Good for Plan 05:
  05C Good plus:
    05D consumes the detector theorem in Proposition C.1.
    05E rewires normalizedCoreCC20RHExitObjectPackageFromTheorems.

Partial:
  Lean proves compact bumps, Mellin convergence, finite linear algebra,
  positivity from half-density rows, or conditional assembly, while the expanded
  finite Mellin interpolation theorem remains an input.

Rejected:
  Any proof that uses:
    detector existence as a field
    Nonempty over the detector as the first construction step
    a theorem for arbitrary C : CC20TestSpace
    an accepted-source theorem
    a raw Mellin-entry field
    a raw determinant field
    True
    Set.univ
    an arbitrary or zero test
```

Current direction decision:

```text
Keep 05C on one route:
  expanded node-value image Mellin surjectivity.

Primary tactic:
  Route C, dual separation, then analytic kernel detection.

Execution order:
  1. B3c is now implemented and audit-clean:
       span = top
         -> finite positive-interval compact combination
         -> exact finite target.

  2. B3b0/B3b1 image-level finite-dual socket is implemented:
       nonzero linear functional
         -> nonzero image coefficient vector
         -> weighted Mellin detection.

  3. Current active leaf:
       nonzero image coefficient vector
         -> nonzero finite power kernel at a positive point
         -> compact bump detects that point by nonzero integral pairing.

Routes A and B:
  Keep them as fallback analysis only.  Do not split them into separate 05C
  documents unless the main Route C proof fails and the main plan records the
  exact failure.

Documentation rule:
  All 05C status, trees, rejected routes, WSL commands, and focused audits stay
  in this file.
```


## 2. What 05C Is

05C constructs a Yoshida detector for the concrete CC20 test space.

The detector needs one test function `g` with four kinds of data:

```text
YoshidaDetector rho
|
+-- test:
|     g : normalizedCC20ConcreteTestAlgebra.Test
|
+-- compactness:
|     normalizedCC20TestSpace.compactSupportSmooth g
|
+-- vanishing/detection:
|     M(g, 0)     = 0
|     M(g, 1 / 2) = 0
|     M(g, 1)     = 0
|     M(g, rho)   != 0
|
+-- positivity:
      0 < normalizedCC20TestSpace.weilLocalSum
            (normalizedCC20TestSpace.starConvolution g)
```

The current concrete skeleton turns the positivity row into two extra Mellin
targets for the same `g`:

```text
M(g, I / 2)  = -1
M(g, -I / 2) = -1
```

So the active 05C target is not a four-node interpolation problem.  It is a
six-node expanded interpolation problem.


## 3. Why The Old Four-Node Route Is Prep Only

The old route built:

```text
nodes:
  0, 1 / 2, 1, rho

target:
  0, 0, 0, 1
```

That route cannot close 05C after the positivity reduction.

Reason:

```text
05C4 now needs the same g to satisfy:
  M(g, I / 2)  = -1
  M(g, -I / 2) = -1

Old four-node target says nothing about those rows.

If rho = I / 2 or rho = -I / 2, the old target M(g,rho)=1 also collides with
the required half-density target -1.
```

The old four-node material remains useful only as prep:

```text
four-node finite map
four-node finite linear solve
four-node Kronecker bridge
positive-interval convergence
compact bump construction
```

Do not mark 05C solved from any four-node theorem.


## 4. Current Expanded Image Target

Use the expanded node owner:

```lean
inductive CC20YoshidaExpandedMomentNode where
  | zero
  | half
  | one
  | targetRho
  | posHalfDensity
  | negHalfDensity
```

The node values are:

```text
zero            -> 0
half            -> 1 / 2
one             -> 1
targetRho       -> rho
posHalfDensity  -> I / 2
negHalfDensity  -> -I / 2
```

The label target values are:

```text
zero            -> 0
half            -> 0
one             -> 0
targetRho       -> -1
posHalfDensity  -> -1
negHalfDensity  -> -1
```

The six labels are still useful for the concrete target rows, but they are not
the active interpolation type.  Two labels can denote the same Mellin point:

```text
rho = I / 2   makes targetRho collide with posHalfDensity
rho = -I / 2  makes targetRho collide with negHalfDensity
```

The active interpolation type is the image of the node-value map:

```lean
abbrev NodeValueImage (rho : ℂ) : Type :=
  {z : ℂ // z ∈ expandedNodeValueFinset rho}
```

The concrete target on this image is well-defined because source nontrivial
zero exclusions and the off-critical-line hypothesis rule out collisions with
`0`, `1 / 2`, and `1`; collisions with `±I/2` both carry target value `-1`.

Implemented bridge:

```lean
targetValueOnNodeValue_eq_targetValue
concreteExpandedMellinRealizes_of_node_value_image_mellin_surjective
exists_concreteYoshidaMomentData_of_node_value_image_mellin_surjective
normalizedCC20YoshidaDetectorExists_of_node_value_image_mellin_surjective
```

Rejected active theorem shape:

```lean
∀ y : CC20YoshidaExpandedMomentNode → ℂ, ...
```

That shape is too strong when node values collide.  It remains useful only
under a future explicit pairwise-distinctness hypothesis.

Current finite-surjectivity form:

```lean
∀ y : CC20YoshidaExpandedMomentNode.NodeValueImage rho → ℂ,
  ∃ g lower upper,
    0 < lower ∧
    normalizedCC20TestSpace.compactSupportSmooth g ∧
    Function.support
      (fun x : ℝ =>
        normalizedCC20ConcreteTestAlgebra.legacy.encode g x)
        ⊆ Set.Icc lower upper ∧
    ∀ z : CC20YoshidaExpandedMomentNode.NodeValueImage rho,
      normalizedCC20TestSpace.mellinAt g z.1 = y z
```

Old six-label matrix/surjectivity forms are conditional compatibility routes,
not the main 05C route.

Old preferred matrix-basis form:

```lean
theorem exists_positive_interval_supported_expanded_mellin_basis
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    ∃ basisTest lower upper,
      (∀ j, 0 < lower j) ∧
      (∀ j, normalizedCC20TestSpace.compactSupportSmooth (basisTest j)) ∧
      (∀ j, Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode
            (basisTest j) x) ⊆ Set.Icc (lower j) (upper j)) ∧
      (Matrix.of fun i j =>
        normalizedCC20TestSpace.mellinAt
          (basisTest j)
          (CC20YoshidaExpandedMomentNode.nodeValue rho i)).det ≠ 0
```

Old equivalent six-label finite-surjectivity form:

```lean
∀ y : CC20YoshidaExpandedMomentNode → ℂ,
  ∃ g lower upper,
    0 < lower ∧
    normalizedCC20TestSpace.compactSupportSmooth g ∧
    Function.support
      (fun x : ℝ =>
        normalizedCC20ConcreteTestAlgebra.legacy.encode g x)
        ⊆ Set.Icc lower upper ∧
    ∀ i,
      normalizedCC20TestSpace.mellinAt g
        (CC20YoshidaExpandedMomentNode.nodeValue rho i) = y i
```


## 5. Current Proof Tree

Full 05C tree:

```text
05C normalizedCC20YoshidaDetectorExists
|
+-- A. concrete test-space owner
|   |
|   +-- normalizedCC20TestSpace
|   +-- cc20TripleFiniteVanishingSet
|   +-- concrete TestFunction owner from 05B
|
+-- B. expanded node-value image finite Mellin interpolation
|   |
|   +-- B1. compact positive-interval test family
|   |   |
|   |   +-- already good as prep:
|   |       exists_testFunction_supported_Icc_eq_one
|   |       exists_yoshida_indexed_testFunction_basis_supported_Icc
|   |
|   +-- B2. positive interval -> Mellin convergence
|   |   |
|   |   +-- already good as prep:
|   |       testFunction_mellinConvergent_of_support_subset_Icc
|   |
|   +-- B3. image-level determinant or finite surjectivity
|   |   |
|   |   +-- B3a. finite-dimensional Route C socket
|   |   |   |
|   |   |   +-- already good conditionally:
|   |   |       PositiveIntervalCompactTest
|   |   |       expandedMellinVector
|   |   |       imageMellinVector
|   |   |       expandedMellinVector_span_top_of_linear_dual_separation
|   |   |       imageMellinVector_span_top_of_linear_dual_separation
|   |   |
|   |   +-- B3b. analytic separation leaf:
|   |   |   |
|   |   |   +-- B3b0. already good conditionally:
|   |   |   |   linearFunctionalCoordinates
|   |   |   |   linearFunctional_apply_eq_sum_coordinates
|   |   |   |   linearFunctionalCoordinates_ne_zero
|   |   |   |   linear_dual_separation_of_weighted_expanded_mellin_detection
|   |   |   |   imageLinearFunctionalCoordinates
|   |   |   |   imageLinearFunctional_apply_eq_sum_coordinates
|   |   |   |   imageLinearFunctionalCoordinates_ne_zero
|   |   |   |   image_linear_dual_separation_of_weighted_mellin_detection
|   |   |   |
|   |   |   +-- B3b1. reduced to kernel analytic leaves:
|   |   |       weightedMellinKernel
|   |   |       image_weighted_mellin_sum_eq_kernel_integral
|   |   |       image_weighted_mellin_detection_of_kernel_integral_detection
|   |   |       image_weighted_mellin_detection_of_kernel_point_and_bump_separation
|   |   |
|   |   |   +-- B3b2. open lower leaf:
|   |   |       WeightedMellinKernelPositivePointSeparation
|   |   |       WeightedMellinKernelBumpSeparation
|   |   |
|   |   +-- B3c. already good conditionally:
|   |       PositiveIntervalCompactTest finite Finsupp combination
|   |       positiveIntervalCompactTestCombination_compactSupportSmooth
|   |       positiveIntervalCompactTestCombination_support_subset
|   |       expandedMellinVector_positiveIntervalCompactTestCombination
|   |       imageMellinVector_positiveIntervalCompactTestCombination
|   |       positive_interval_expanded_mellin_surjective_of_span_top
|   |       positive_interval_expanded_mellin_surjective_of_linear_dual_separation
|   |       positive_interval_node_value_image_mellin_surjective_of_span_top
|   |       positive_interval_node_value_image_mellin_surjective_of_linear_dual_separation
|   |       positive_interval_node_value_image_mellin_surjective_of_weighted_detection
|   |
|   +-- B4. finite linear solve
|       |
|       +-- already good conditionally:
|           CC20YoshidaExpandedMomentNode.expandedFiniteLinearCombination
|           CC20YoshidaExpandedMomentNode.expandedMellinAt_finiteLinearCombination
|           CC20YoshidaExpandedMomentNode.concreteExpandedMellinRealizes_of_basis_matrix_det_ne_zero
|           CC20YoshidaExpandedMomentNode.concreteExpandedMellinRealizes_of_positive_interval_supported_basis
|
+-- C. same-test moment data
|   |
|   +-- already good conditionally:
|       concreteYoshidaMomentData_of_expanded_mellin_realizes
|       exists_concreteYoshidaMomentData_of_positive_interval_supported_basis
|       exists_concreteYoshidaMomentData_of_node_value_image_mellin_surjective
|
+-- D. positivity
|   |
|   +-- already good for current skeleton:
|       normalizedCC20Yoshida_weilLocalSum_positive_of_half_mellin_values
|       concreteYoshidaMomentData_weilLocalSum_positive
|
+-- E. detector assembly
    |
    +-- already good conditionally:
        normalizedCC20YoshidaDetectorExists_of_moment_data
        normalizedCC20YoshidaDetectorExists_of_positive_interval_supported_basis_provider
        normalizedCC20YoshidaDetectorExists_of_positive_interval_expanded_mellin_surjective
        normalizedCC20YoshidaDetectorExists_of_node_value_image_mellin_surjective
        normalizedCC20YoshidaDetectorExists_of_node_value_image_weighted_detection
        normalizedCC20YoshidaDetectorExists_of_node_value_image_kernel_separation
```

The active hard leaf is B3b2.  Once B3b2 supplies point separation for the
finite power kernel and bump separation for nonzero kernel values, Lean
constructs `normalizedCC20YoshidaDetectorExists` through the image-level route.


## 6. B3 Proof Routes

Use Route C as the main route.  Do not create another wrapper record that
stores the target theorem.  Routes A and B stay here as fallback analysis, not
as active implementation lanes.

Route A, log-coordinate exponential moments:

```text
t = exp u

Mellin(g, s)
  = ∫ t^(s - 1) g(t) dt
  = ∫ exp(s * u) h(u) du

Need:
  compact h on a real interval
  prescribed moments against six exponentials exp(s_i * u)
```

This route can reduce B3 to finite interpolation for exponentials on an
interval, but it is not the current implementation lane.

Route B, bump/Vandermonde:

```text
choose six real centers x_j > 0
choose narrow compact bumps around x_j
show Mellin matrix tends to:
  x_j^(s_i - 1)
prove that this generalized Vandermonde determinant is nonzero
choose the bump width small enough
```

This route needs more epsilon control, so keep it as a fallback if Route C
gets blocked at the analytic separation leaf.

Route C, dual separation:

```text
Suppose a linear combination of the six Mellin functionals vanishes on every
positive-interval compact smooth test.

Then:
  sum_z c_z * t^(z - 1) = 0
  on a positive interval, as a distribution or locally integrable function.

Analytic independence of the distinct node-value image powers gives:
  c_z = 0 for every image point z.

Finite-dimensional linear algebra gives:
  the evaluation map TestFunction -> (NodeValueImage rho -> C) is surjective.
```

Current Route C split:

```text
B3b2 analytic kernel separation
  |
  v
B3b1 weighted Mellin detection through kernel integral identity
  |
  v
B3b0 image finite-dual separation
  |
  v
B3a imageMellinVector_span_top_of_linear_dual_separation
  |
  v
B3c span-to-surjectivity with positive-interval finite combinations
  |
  v
expanded node-value image finite Mellin surjectivity
  |
  v
normalizedCC20YoshidaDetectorExists
```

B3a is implemented conditionally for both old six-label vectors and the active
image vectors.  The active target spans
`CC20YoshidaExpandedMomentNode.NodeValueImage rho -> C`.

B3c is implemented conditionally for both old six-label targets and the active
image targets.  It turns `span = top` into one positive-interval compact finite
linear combination.

B3b0/B3b1 now lower the remaining proof to one open analytic leaf plus one
closed analytic leaf:

```text
B3b2 active analytic leaves
|
+-- B3b2A. log-line finite power independence
|   |
|   +-- implemented bridge:
|   |     WeightedMellinKernelLogLineIndependence
|   |       -> WeightedMellinKernelPositiveLineIndependence
|   |       -> WeightedMellinKernelPositivePointSeparation
|   |
|   +-- open math leaf:
|         if weightedMellinKernel rho coeff (exp u) = 0 for every real u,
|         then coeff = 0.
|
+-- B3b2B. strict phase bump detection
    |
    +-- implemented bridge:
    |     WeightedMellinKernelStrictPhaseBumpDetection
    |       -> WeightedMellinKernelBumpSeparation
    |
    +-- closed analytic leaf:
          choose phase and a positive-interval compact bump so the real part
          of the phase-rotated kernel integral is strictly positive.
```

05C remains open until B3b2A is proved without a stored detector, determinant
row, Mellin row, or accepted-source theorem.

Expanded lower trees:

```text
B3b2A log-line finite power independence
|
+-- A1. rewrite positive variable by t = exp u
|   |
|   +-- current Lean owner:
|       WeightedMellinKernelLogLineIndependence
|
+-- A2. identify the log kernel
|   |
|   +-- mathematical target:
|       weightedMellinKernel rho coeff (Real.exp u)
|         =
|       sum_z coeff z * exp ((z.1 - 1) * u)
|
+-- A3. prove finite exponential independence
|   |
|   +-- input facts:
|       z values live in NodeValueImage, so duplicate Mellin points are already
|       quotient-collapsed.
|
|   +-- target theorem:
|       if sum_z coeff z * exp ((z.1 - 1) * u) = 0 for all real u,
|       then coeff = 0.
|
+-- A4. output:
    WeightedMellinKernelPositivePointSeparation
```

```text
B3b2B strict phase bump detection
|
+-- B1. start with positive point:
|     t > 0 and K(t) != 0, where K = weightedMellinKernel rho coeff
|
+-- B2. choose phase:
|     phase = conjugate K(t), or any nonzero scalar making
|     Re(phase * K(t)) > 0
|
+-- B3. use continuity:
|     choose an interval (a,b) around t, with 0 < a,
|     where Re(phase * K(x)) remains positive
|
+-- B4. choose compact smooth bump:
|     exists_contDiff_tsupport_subset gives f with support in (a,b),
|     range in [0,1], and f(t)=1
|
+-- B5. prove strict positive real-part integral:
|     0 < Re(phase * integral K(x) f(x) dx)
|
+-- B6. output:
    WeightedMellinKernelBumpSeparation
```


## 7. Evidence Already In Lean

Files:

```text
ConnesWeilRH/Source/CC20YoshidaCriterion.lean
ConnesWeilRH/Source/CC20YoshidaMellin.lean
ConnesWeilRH/Source/CC20YoshidaConstruction.lean
ConnesWeilRH/Source/CC20ConcreteTestSpace.lean
```

Load-bearing declarations:

```text
Yoshida detector structure:
  Source.YoshidaDetector
  Source.CC20YoshidaDetectorExists

Four-node prep:
  Source.CC20YoshidaInterpolationNode
  Source.CC20YoshidaInterpolationNode.concreteMellinEvaluationMap
  Source.CC20YoshidaInterpolationNode.ConcreteMellinRealizesDesired
  Source.CC20YoshidaInterpolationNode.concreteMellinRealizesDesired_of_basis_matrix_det_ne_zero
  Source.CC20YoshidaInterpolationNode.concreteMellinRealizesDesired_of_positive_interval_supported_basis
  Source.CC20YoshidaInterpolationNode.concreteMellinRealizesDesired_of_positive_interval_mellin_surjective

Six-node active path:
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.expandedNodeValueFinset
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.NodeValueImage
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.targetValueOnNodeValue
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.targetValue_eq_of_nodeValue_eq
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.targetValueOnNodeValue_eq_targetValue
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.expandedMellinVector
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageMellinVector
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positiveIntervalCompactTestCombination
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positiveIntervalCompactTestCombination_compactSupportSmooth
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positiveIntervalCompactTestCombination_support_subset
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.expandedMellinVector_positiveIntervalCompactTestCombination
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageMellinVector_positiveIntervalCompactTestCombination
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.expandedMellinVector_span_top_of_linear_dual_separation
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageMellinVector_span_top_of_linear_dual_separation
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positive_interval_expanded_mellin_surjective_of_span_top
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positive_interval_expanded_mellin_surjective_of_linear_dual_separation
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positive_interval_node_value_image_mellin_surjective_of_span_top
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positive_interval_node_value_image_mellin_surjective_of_linear_dual_separation
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positive_interval_node_value_image_mellin_surjective_of_weighted_detection
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.linearFunctionalCoordinates
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.linearFunctional_apply_eq_sum_coordinates
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.linearFunctionalCoordinates_ne_zero
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.linear_dual_separation_of_weighted_expanded_mellin_detection
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageLinearFunctionalCoordinates
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageLinearFunctional_apply_eq_sum_coordinates
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageLinearFunctionalCoordinates_ne_zero
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.image_linear_dual_separation_of_weighted_mellin_detection
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.WeightedMellinKernelPositivePointSeparation
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.WeightedMellinKernelPositiveLineIndependence
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.WeightedMellinKernelLogLineIndependence
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.WeightedMellinKernelBumpSeparation
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.WeightedMellinKernelStrictPhaseBumpDetection
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.continuousAt_weightedMellinKernel_of_pos
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.exists_positive_interval_compact_test_real_bump
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_phase_re_positive_interval
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.integrableOn_weightedMellinKernel_mul_test
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_phase_integral_re_eq
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_strict_phase_bump_detection
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_positive_line_independence_of_log_line_independence
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_positive_point_separation_of_positive_line_independence
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_positive_point_separation_of_log_line_independence
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_bump_separation_of_strict_phase_detection
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.image_weighted_mellin_sum_eq_kernel_integral
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.image_weighted_mellin_detection_of_kernel_integral_detection
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.image_weighted_mellin_detection_of_kernel_point_and_bump_separation
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.ConcreteExpandedMellinRealizes
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.concreteExpandedMellinRealizes_of_node_value_image_mellin_surjective
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.concreteExpandedMellinRealizes_of_basis_matrix_det_ne_zero
  Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.concreteExpandedMellinRealizes_of_positive_interval_supported_basis
  Source.CC20YoshidaInterpolationNode.exists_concreteYoshidaMomentData_of_positive_interval_supported_basis
  Source.CC20YoshidaInterpolationNode.exists_concreteYoshidaMomentData_of_positive_interval_expanded_mellin_surjective
  Source.CC20YoshidaInterpolationNode.exists_concreteYoshidaMomentData_of_node_value_image_mellin_surjective
  Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_moment_data
  Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_positive_interval_supported_basis_provider
  Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_positive_interval_expanded_mellin_surjective
  Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_mellin_surjective
  Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_weighted_detection
  Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_kernel_separation
  Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence_and_bump
  Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence_and_phase_bump
  Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence
```

Known clean build from the earlier 05C finite-dual-coordinate work:

```text
WSL Ubuntu-24.04 main ext4 mirror, under /tmp/connes-weil-rh-lake.lock:
  lake build ConnesWeilRH.Source.CC20YoshidaConstruction
  lake build ConnesWeilRH

Result:
  passed
```

Known focused audit result for the new 05C construction declarations:

```text
[propext, Classical.choice, Quot.sound]
```

Current unbuilt pass:

```text
2026-07-07 latest edit did not run `lake` by Peter instruction:
  "别构建了，先打到闭合！"

Static scan only:
  rg -n "sorry|admit|axiom|constant|opaque|unsafe|Set\.univ|\bTrue\b" \
    ConnesWeilRH/Source/CC20YoshidaConstruction.lean

Result:
  no forbidden proof-shortcut hit in the added kernel separation chain.
```


## 8. Rejection Scans

Detector shortcut scan:

```text
rg -n "CC20YoshidaDetectorExists.*where|detectorExists|YoshidaDetectorExists :=|Nonempty\.intro|Classical\.choice|by_cases.*Nonempty|\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b|Set\.univ|\bTrue\b" ConnesWeilRH/Source/CC20YoshidaCriterion.lean ConnesWeilRH/Source/CC20YoshidaConstruction.lean
```

Expected allowed hit:

```text
normalizedCC20YoshidaDetectorExists_of_moment_data uses Nonempty.intro
```

That hit is allowed only because the theorem receives concrete moment data and
then packages the detector.

Four-node closure rejection scan:

```text
rg -n "four-node|four node|C\^4|M\(g,rho\) = 1|ConcreteMellinRealizesDesired.*05C.*closed|kronecker.*closed" plan/05C_2026-07-07_D1_cc20_yoshida_detector_plan.md ConnesWeilRH/Source/CC20YoshidaMellin.lean ConnesWeilRH/Source/CC20YoshidaConstruction.lean
```

Expected meaning:

```text
Any four-node hit must say prep-only, historical, or rejected as full 05C
closure.
```


## 9. WSL Build Gate

Smallest 05C build:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.CC20YoshidaCriterion ConnesWeilRH.Source.CC20YoshidaMellin ConnesWeilRH.Source.CC20YoshidaConstruction'
```

Top-level import gate after any Lean edit:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH'
```

Do not run `lake` from Windows or `/mnt/c`.


## 10. Focused Axiom Audit

Use an import-based scratch file in the WSL mirror.

```lean
import ConnesWeilRH.Source.CC20YoshidaConstruction

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.concreteExpandedMellinRealizes_of_basis_matrix_det_ne_zero
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.concreteExpandedMellinRealizes_of_basis_matrix_det_ne_zero

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.concreteExpandedMellinRealizes_of_positive_interval_supported_basis
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.concreteExpandedMellinRealizes_of_positive_interval_supported_basis

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.expandedMellinVector_span_top_of_linear_dual_separation
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.expandedMellinVector_span_top_of_linear_dual_separation

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positiveIntervalCompactTestCombination_compactSupportSmooth
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positiveIntervalCompactTestCombination_compactSupportSmooth

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positiveIntervalCompactTestCombination_support_subset
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positiveIntervalCompactTestCombination_support_subset

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.expandedMellinVector_positiveIntervalCompactTestCombination
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.expandedMellinVector_positiveIntervalCompactTestCombination

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positive_interval_expanded_mellin_surjective_of_span_top
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positive_interval_expanded_mellin_surjective_of_span_top

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positive_interval_expanded_mellin_surjective_of_linear_dual_separation
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positive_interval_expanded_mellin_surjective_of_linear_dual_separation

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.linearFunctionalCoordinates
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.linearFunctionalCoordinates

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.linearFunctional_apply_eq_sum_coordinates
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.linearFunctional_apply_eq_sum_coordinates

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.linearFunctionalCoordinates_ne_zero
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.linearFunctionalCoordinates_ne_zero

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.linear_dual_separation_of_weighted_expanded_mellin_detection
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.linear_dual_separation_of_weighted_expanded_mellin_detection

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.targetValue_eq_of_nodeValue_eq
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.targetValue_eq_of_nodeValue_eq

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.targetValueOnNodeValue_eq_targetValue
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.targetValueOnNodeValue_eq_targetValue

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageMellinVector_positiveIntervalCompactTestCombination
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageMellinVector_positiveIntervalCompactTestCombination

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageMellinVector_span_top_of_linear_dual_separation
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageMellinVector_span_top_of_linear_dual_separation

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positive_interval_node_value_image_mellin_surjective_of_linear_dual_separation
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positive_interval_node_value_image_mellin_surjective_of_linear_dual_separation

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageLinearFunctionalCoordinates
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageLinearFunctionalCoordinates

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageLinearFunctional_apply_eq_sum_coordinates
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageLinearFunctional_apply_eq_sum_coordinates

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageLinearFunctionalCoordinates_ne_zero
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.imageLinearFunctionalCoordinates_ne_zero

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.image_linear_dual_separation_of_weighted_mellin_detection
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.image_linear_dual_separation_of_weighted_mellin_detection

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_positive_line_independence_of_log_line_independence
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_positive_line_independence_of_log_line_independence

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_positive_point_separation_of_positive_line_independence
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_positive_point_separation_of_positive_line_independence

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_positive_point_separation_of_log_line_independence
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_positive_point_separation_of_log_line_independence

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_bump_separation_of_strict_phase_detection
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_bump_separation_of_strict_phase_detection

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.image_weighted_mellin_sum_eq_kernel_integral
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.image_weighted_mellin_sum_eq_kernel_integral

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.image_weighted_mellin_detection_of_kernel_integral_detection
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.image_weighted_mellin_detection_of_kernel_integral_detection

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.image_weighted_mellin_detection_of_kernel_point_and_bump_separation
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.image_weighted_mellin_detection_of_kernel_point_and_bump_separation

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.concreteExpandedMellinRealizes_of_node_value_image_mellin_surjective
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.concreteExpandedMellinRealizes_of_node_value_image_mellin_surjective

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.exists_concreteYoshidaMomentData_of_positive_interval_supported_basis
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.exists_concreteYoshidaMomentData_of_positive_interval_supported_basis

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.exists_concreteYoshidaMomentData_of_positive_interval_expanded_mellin_surjective
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.exists_concreteYoshidaMomentData_of_positive_interval_expanded_mellin_surjective

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.exists_concreteYoshidaMomentData_of_node_value_image_mellin_surjective
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.exists_concreteYoshidaMomentData_of_node_value_image_mellin_surjective

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_moment_data
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_moment_data

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_positive_interval_supported_basis_provider
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_positive_interval_supported_basis_provider

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_positive_interval_expanded_mellin_surjective
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_positive_interval_expanded_mellin_surjective

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_mellin_surjective
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_mellin_surjective

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_weighted_detection
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_weighted_detection

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_kernel_separation
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_kernel_separation

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence_and_bump
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence_and_bump

#check ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence_and_phase_bump
#print axioms ConnesWeilRH.Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence_and_phase_bump
```

Accepted output:

```text
[propext, Classical.choice, Quot.sound]
```

Rejected output:

```text
sorryAx
project-local axiom
constant
opaque
unsafe
raw Prop field carrying the target theorem
```


## 11. Next Safe Action

Execute B3b2A and B3b2B.  The image-level finite-dual socket, kernel integral
identity, log-line reduction, strict-phase reduction, and conditional detector
bridge are now in Lean, pending build/audit because Peter paused builds for
this pass:

```text
Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.linear_dual_separation_of_weighted_expanded_mellin_detection
Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.image_linear_dual_separation_of_weighted_mellin_detection
Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_positive_point_separation_of_log_line_independence
Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.weightedMellinKernel_bump_separation_of_strict_phase_detection
Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.image_weighted_mellin_sum_eq_kernel_integral
Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.image_weighted_mellin_detection_of_kernel_point_and_bump_separation
Source.CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.positive_interval_node_value_image_mellin_surjective_of_weighted_detection
Source.CC20YoshidaInterpolationNode.exists_concreteYoshidaMomentData_of_node_value_image_mellin_surjective
Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_kernel_separation
Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence_and_phase_bump
```

Current exact open theorem shapes:

```lean
theorem weighted_mellin_kernel_log_line_independence
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    CC20YoshidaExpandedMomentNode.
      WeightedMellinKernelLogLineIndependence rho

theorem weighted_mellin_kernel_strict_phase_bump_detection
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    CC20YoshidaExpandedMomentNode.
      WeightedMellinKernelStrictPhaseBumpDetection rho
```

Expanded, these mean:

```lean
∀ coeff : CC20YoshidaExpandedMomentNode.NodeValueImage rho → ℂ,
  (∀ u : ℝ,
    CC20YoshidaExpandedMomentNode.weightedMellinKernel rho coeff
      (Real.exp u) = 0) →
    coeff = 0

∀ (coeff : CC20YoshidaExpandedMomentNode.NodeValueImage rho → ℂ) (t : ℝ),
  0 < t →
    CC20YoshidaExpandedMomentNode.weightedMellinKernel rho coeff t ≠ 0 →
      ∃ (p : CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest)
          (phase : ℂ),
        0 <
          (phase *
            (∫ x : ℝ in Set.Ioi 0,
              CC20YoshidaExpandedMomentNode.weightedMellinKernel rho coeff x *
                normalizedCC20ConcreteTestAlgebra.legacy.encode
                  p.test x)).re
```

These theorems can have different final names, but they must prove the same
two lower analytic statements.  Do not replace them with:

```text
detector existence
raw Mellin rows
raw determinant rows
linear-dual separation as an input field
surjectivity as an input field
accepted-source analytic theorem
```

Current closed conditional route:

```text
WeightedMellinKernelLogLineIndependence
    -> positive-point separation
    -> bump separation via proved strict phase-bump detection
    -> image weighted Mellin detection
    -> image linear-dual separation
    -> image span = top
    -> image finite Mellin surjectivity
    -> ConcreteYoshidaMomentData
    -> normalizedCC20YoshidaDetectorExists
```

Old six-label weighted theorem shape:

```lean
theorem weighted_expanded_mellin_detection
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    ∀ coeff : CC20YoshidaExpandedMomentNode → ℂ,
      coeff ≠ 0 →
        ∃ p : CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest,
          (∑ i : CC20YoshidaExpandedMomentNode,
            CC20YoshidaExpandedMomentNode.expandedMellinVector rho p i *
              coeff i) ≠ 0
```

This old shape is compatibility-only unless a pairwise-distinctness hypothesis
for the six labels is added.

Current split route:

```text
B3b active:
  nonzero linear functional on C^6
    -> old six-label path                                [compatibility only]

  nonzero linear functional on the node-value image
    -> B3b0 finite image coordinate vector               [implemented]
    -> weightedMellinKernel                              [implemented]
    -> kernel integral identity                          [implemented]
    -> positive-point separation                         [open]
    -> bump separation                                   [open]
    -> imageMellinVector_span_top_of_linear_dual_separation

B3a + B3c already checked:
  linear-dual separation
    -> span = top
    -> finite Finsupp combination of PositiveIntervalCompactTest values
    -> one compact test by legacy.encode finite sum
    -> one positive interval containing the finite support union
    -> exact six-node target
```


## 12. 2026-07-07 Phase-Bump Execution Result

Result:

```text
Partial-good for 05C.  B3b2B is closed and audit-clean.  05C remains open
because B3b2A log-line finite power independence is still an input.
```

What changed:

```text
weightedMellinKernel_strict_phase_bump_detection :
  WeightedMellinKernelStrictPhaseBumpDetection rho

normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence :
  (forall rho, source zero and off-line hypotheses ->
    WeightedMellinKernelLogLineIndependence rho)
  ->
  CC20YoshidaDetectorExists normalizedCC20TestSpace
    cc20TripleFiniteVanishingSet
```

Proof route:

```text
K(t) != 0
  -> choose phase = star (K(t))
  -> Re(phase * K(t)) > 0
  -> continuity gives a positive interval around t
  -> build a real nonnegative compact bump supported in that interval
  -> rewrite Re(phase * integral K*bump) as a real set integral
  -> use nonnegative integral positivity from positive-measure support
```

Build:

```text
WSL Ubuntu-24.04 main ext4 mirror, under /tmp/connes-weil-rh-lake.lock:
  lake build \
    ConnesWeilRH.Source.CC20YoshidaCriterion \
    ConnesWeilRH.Source.CC20YoshidaMellin \
    ConnesWeilRH.Source.CC20YoshidaConstruction

Result:
  passed
```

Focused axiom audit:

```text
Targets:
  continuousAt_weightedMellinKernel_of_pos
  exists_positive_interval_compact_test_real_bump
  weightedMellinKernel_phase_re_positive_interval
  integrableOn_weightedMellinKernel_mul_test
  weightedMellinKernel_phase_integral_re_eq
  weightedMellinKernel_strict_phase_bump_detection
  weightedMellinKernel_bump_separation_of_strict_phase_detection
  normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence

Result:
  [propext, Classical.choice, Quot.sound]
  no sorryAx
```

Remaining hard leaf:

```text
WeightedMellinKernelLogLineIndependence rho

Equivalently:
  if the finite image-kernel power sum
    weightedMellinKernel rho coeff (Real.exp u)
  vanishes for every real u, then coeff = 0.
```


## 13. Acceptance Text

Use this text after the next 05C implementation step:

```text
Result:
  Good / partial / rejected.

05C status:
  <full detector closed, or exact remaining hard leaf>

Old weak path:
  <detector shortcut / four-node closure path removed or kept prep-only>

New active owner:
  <expanded six-node owner or lower analytic theorem>

Consumer:
  <exact declaration that now consumes the stronger owner>

Semantic sufficiency:
  <why this proves detector existence, or why it is still conditional>

Build:
  <WSL command and result>

Focused axiom audit:
  <targets and output>

Remaining black box:
  <exact theorem/type, if any>
```


## 14. 2026-07-07 Log-Line Execution Result

Result:

```text
Good.  05C detector existence is closed for the concrete normalized CC20 test
space and triple finite vanishing set.
```

What changed:

```text
weighted_mellin_kernel_log_line_independence :
  WeightedMellinKernelLogLineIndependence rho

normalizedCC20YoshidaDetectorExists :
  CC20YoshidaDetectorExists normalizedCC20TestSpace
    cc20TripleFiniteVanishingSet
```

Proof route:

```text
K(exp u) = 0 for every real u
  -> expMomentSum coeff 0 u = 0
  -> every derivative is zero
  -> expMomentSum coeff n 0 = 0 for every n
  -> sum_z coeff z * (z.1 - 1)^n = 0 for every n
  -> Vandermonde power-sum independence on NodeValueImage rho
  -> coeff = 0
```

Semantic sufficiency:

```text
WeightedMellinKernelLogLineIndependence
  -> positive-point separation
  -> strict phase-bump detection
  -> bump separation
  -> image weighted Mellin detection
  -> image linear-dual separation
  -> image span = top
  -> image finite Mellin surjectivity
  -> ConcreteYoshidaMomentData
  -> normalizedCC20YoshidaDetectorExists
```

Build:

```text
WSL Ubuntu-24.04 ext4 verification copy, under /tmp/connes-weil-rh-lake.lock:
  lake build \
    ConnesWeilRH.Source.CC20YoshidaCriterion \
    ConnesWeilRH.Source.CC20YoshidaMellin \
    ConnesWeilRH.Source.CC20YoshidaConstruction \
    ConnesWeilRH.Source.CC20PropositionC1 \
    ConnesWeilRH.Route.CC20RouteRealization

Result:
  passed
```

Focused axiom audit:

```text
Targets:
  weighted_mellin_kernel_log_line_independence
  weightedMellinKernel_strict_phase_bump_detection
  normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence
  normalizedCC20YoshidaDetectorExists
  normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence_and_phase_bump

Result:
  [propext, Classical.choice, Quot.sound]
  no sorryAx
```

Rejection scan:

```text
rg -n "sorry|admit|axiom|constant|opaque|accepted" \
  ConnesWeilRH/Source/CC20YoshidaConstruction.lean

Result:
  no matches for forbidden proof shortcuts.
```

Top-level build caveat:

```text
lake build ConnesWeilRH
  failed outside 05C at:
    ConnesWeilRH/Source/AnalyticCore.lean:7393

Error shape:
  unsolved goal involving
    Λ n = 0
    or n = 0
    or norm terms for encoded 0 summing to 0

This is not in the Yoshida detector module and does not block the 05C focused
closure result.
```

Remaining 05C black box:

```text
None for the concrete normalized Yoshida detector existence theorem.
```
