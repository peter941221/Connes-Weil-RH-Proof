# 1588 — the gate-residual bones land in Lean: the moment conversion becomes a
# per-vector (trace-summable) lemma, the nested split and the projection-pair
# ordering are machine-checked, and the sweep shows the "owed" hradial brick
# was half-committed and half-Mathlib (wave V CONT-12)

Date: 2026-09-17.

Status: LEAN LANDED + SWEEP FINDINGS. Nine declarations in
`ConnesWeilRH/Dev/C1G8R3GateResidualMomentBricks.lean` plus the paired axiom
audit `ConnesWeilRH/Dev/C1G8R3GateResidualMomentBricksAudit.lean`. One unified
acceptance build over both modules, green. No gate is closed here: the spectral
input of the conversion is a HYPOTHESIS of the lemma, not a claim of this file.
RH NOT claimed.

## 1. Result first

```text
+------------------------------------+---------------------------------------+
| acceptance item                    | value                                 |
+------------------------------------+---------------------------------------+
| targets                            | Dev.C1G8R3GateResidualMomentBricks    |
|                                    | Dev.C1G8R3GateResidualMomentBricksAudit|
| build footer                       | "Build completed successfully" x1     |
| lines matching "error:"            | 0                                     |
| lines matching "sorryAx"           | 0                                     |
| #print axioms outputs              | 9                                     |
| axiom sets printed                 | all nine = {propext,                  |
|                                    | Classical.choice, Quot.sound}         |
| warnings inside the new modules    | 0                                     |
| log                                | build-logs/1588_bricks.log            |
+------------------------------------+---------------------------------------+
```

The three module-external warnings in the log ("repository ... has local
changes") are pre-existing mirror state; the remaining 63 are replayed
warnings of already-committed modules. Neither is produced by this batch.

Build history of the batch (honest count): six rounds, three red and three
green. All three red rounds were mechanical, not mathematical — a missing
`open`, dropped glyph characters in the source text, and one stuck field
metavariable in a Cauchy-Schwarz call. The glyph-drop hazard is now recorded
in the project's Lean hazards list.

## 2. The nine declarations and the bone each one serves

```text
+----------------------------------------------------+-----------------------------+
| declaration                                        | serves                      |
+----------------------------------------------------+-----------------------------+
| sourceSoninProjection_le_radialSupportProjection   | the 1587 section 2.1 input  |
|                                                    | range(P) <= range(E)        |
+----------------------------------------------------+-----------------------------+
| sourceSoninProjection_le_sourceFourierSupport-     | the other half of           |
| Projection                                         | range(P) = range(E) & range(Q)|
+----------------------------------------------------+-----------------------------+
| radialSupportProjection_comp_sourceSoninProjection | E P = P, the order the      |
|                                                    | wide-radial absorption      |
|                                                    | lemmas consume              |
+----------------------------------------------------+-----------------------------+
| sourceSoninProjection_comp_radialSupportProjection | P E = P                     |
+----------------------------------------------------+-----------------------------+
| radialSupportProjection_fixes_of_support_subset    | the hradial bone: a.e.      |
|                                                    | support below               |
|                                                    | Real.log lambda - s makes   |
|                                                    | the wider projection fix    |
|                                                    | the vector                  |
+----------------------------------------------------+-----------------------------+
| norm_sq_sub_starProjection_eq_add                  | 1587 section 2.1 exactly:   |
|                                                    | ||x - P1 x||^2 =            |
|                                                    | ||x - P2 x||^2 +            |
|                                                    | ||P2 x - P1 x||^2           |
|                                                    | for P1 <= P2                |
+----------------------------------------------------+-----------------------------+
| norm_sq_sub_sourceSoninProjection_eq_add           | that split at the project's |
|                                                    | own pair (P, E)             |
+----------------------------------------------------+-----------------------------+
| starProjection_eq_self_of_re_inner_eq_normSq       | 1586 section 1's equality   |
|                                                    | case: <h, P h> = ||h||^2    |
|                                                    | forces P h = h              |
+----------------------------------------------------+-----------------------------+
| norm_sq_sub_starProjection_le_of_quadraticFormGap  | 1587 section 3 exactly:     |
|                                                    | ||x - P_W x||^2 <=          |
|                                                    | gap^-1 * <x, (1 - K) x>     |
|                                                    | on W^perp                   |
+----------------------------------------------------+-----------------------------+
```

## 3. Why the level of the moment brick is the point

The committed adapter (`normSq_le_of_spectralGap_of_norm_le`,
`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap.lean:47-58`) is a
WHOLE-SPACE operator-norm statement: its hypothesis is
`for all x, gap * ||x||^2 <= ||B x||^2` and its conclusion carries the
norm-ratio constant `(rawBound / sqrt gap)^2`. That shape cannot be summed
over a basis into a trace bound; 1587 section 4 already recorded that its
instantiation at `B = (1 - K)^{1/2} T` is unavailable.

The new brick buys exactly the two properties the gate needs:

```text
+-------------------------+---------------------------------------------------+
| property                | why it matters                                    |
+-------------------------+---------------------------------------------------+
| the gap hypothesis is   | the 1587 obstruction lives on the carrier         |
| COMPLEMENT-restricted   | (the fixed space); a whole-space lower bound is   |
| (hform acts on W^perp)  | impossible there by the committed                 |
|                         | approximate-kernel obstruction                    |
+-------------------------+---------------------------------------------------+
| the conclusion is a     | summing over an orthonormal family gives          |
| SCALAR per vector       | sum_i ||(1 - P) e_i||^2 <= gap^-1 * sum_i         |
| (a quadratic form)      | <e_i, (1 - K) e_i> = gap^-1 * Tr(1 - K),          |
|                         | i.e. the (star)-level statement, not a norm bound |
+-------------------------+---------------------------------------------------+
```

So the CONVERSION step is now machine-checked, and what stays open is exactly
the pair the 1587 erratum named: the trace/first-moment bound on `1 - K`
(the strip-mass object) and the gap itself. The bone is sharpened, not closed.

## 4. Sweep findings (law F8 / law F31 applied to shapes)

Three findings, all from the pre-spend sweep this wave ran before writing.

### 4.1 The "owed" hradial brick was already half-committed

Records 1585 and 1586 both called the hradial transport an owed Lean brick.
The committed file

```text
wideRadial_absorption_of_sourceRadialSupport
  (C1G8R3CompositeBoundaryEnergy.lean:175)
```

takes absorption at the NARROW scale
(`radialSupportProjection lambda o M o sourceInclusion lambda
 = M o sourceInclusion lambda`) and returns it at the WIDE scale
`wideRadialScale lambda s`. That is the absorption half, already proven. What
was genuinely missing is the pointwise-support half — turning an a.e. support
statement from the 1575/1576 transport ledger into the narrow-scale
membership the consumer consumes. That half is
`radialSupportProjection_fixes_of_support_subset`, and its hypothesis
`t < Real.log lambda - s -> v t = 0` is exactly what the ledger produces for
`M J N e_i`. The instantiation `lambda' := wideRadialScale lambda s` uses the
committed `realLog_wideRadialScale` (`:108-112`) as `hlog`.

### 4.2 A local duplicate of a Mathlib lemma is in the tree

```text
+---------------------------------------------------+----------------------------+
| local                                             | Mathlib                    |
+---------------------------------------------------+----------------------------+
| starProjection_comp_of_le                         | Submodule.starProjection_- |
| (Dev/ELambdaFamilyProjectorProbe.lean:48-61)      | comp_starProjection_of_le  |
| radialProjector_comp_of_le (:66-74)               | (Projection/Basic.lean:489)|
+---------------------------------------------------+----------------------------+
```

The Mathlib lemma states `U.starProjection o V.starProjection = U.starProjection`
for `U <= V` with no positivity or completeness side conditions. The new
concrete corollary `radialSupportProjection_comp_sourceSoninProjection` is the
project-level instance of it, so no third copy was introduced. The duplicate
is NOT removed in this wave: `ELambdaFamilyProjectorProbe.lean` has no built
olean and sits underneath the composite-boundary chain, so rewriting it would
force a rebuild of that chain for zero mathematical gain. Filed as a cleanup
candidate, not as a defect.

### 4.3 The nested Pythagorean split is genuinely absent from Mathlib

The sweep of `Projection/Basic.lean` (the full 60-lemma list) and
`Projection/Submodule.lean` finds only the ONE-projection Pythagoras
`norm_sq_eq_add_norm_sq_starProjection` and the orthogonal-complement version;
there is no two-nested-projections split. The tree had been deriving its
instances ad hoc by feeding two such identities plus `nlinarith`
(`C1G8R3PowerProjectionBridge.lean:302-303, :731`). So this brick is new
content, and the general two-line form replaces a repeated local derivation.

## 5. Law filed with this wave

**F32. The pre-spend sweep includes the MATHLIB layer, and it searches by
SHAPE.** Before writing a brick that the record chain calls "owed", grep
Mathlib for the shape (nested-projection composition, projection Pythagorean
splits, equality cases of projections) rather than for the name the record
chain invented. A standard lemma found is a cost avoided; a local duplicate
already in the tree is a cost already paid. This extends F8 (sweep the
project's own committed artifacts) and F31 (sweep premise shapes) to the
third layer.

## 6. Ledger

```text
+--------------------------------------+------------------------------------+
| item                                 | status after this record           |
+--------------------------------------+------------------------------------+
| nested split (1587 section 2.1)       | MACHINE-CHECKED, abstract + at     |
|                                      | the project pair                   |
| projection ordering P <= E, P <= Q    | MACHINE-CHECKED                    |
| equality case (1586 section 1)        | MACHINE-CHECKED                    |
| moment conversion (1587 section 3)    | MACHINE-CHECKED as a per-vector    |
|                                      | lemma with the gap as hypothesis   |
| hradial pointwise support half        | MACHINE-CHECKED                    |
| hradial absorption half               | WAS ALREADY COMMITTED (4.1)        |
| local projection-composition copies   | DUPLICATE OF MATHLIB (4.2), not    |
|                                      | refactored                         |
| StripDensity(Lambda)                  | OPEN (unchanged)                   |
| EndpointMass(epsilon)                 | OPEN (unchanged)                   |
| gap / (GAP)                           | OPEN, and now a hypothesis of a    |
|                                      | machine-checked conversion         |
| (star)/B4/rho5/R4/(OB)/W1             | OPEN                               |
| RH                                    | NOT claimed                        |
+--------------------------------------+------------------------------------+
```

## 7. Boundary

MOVED: the residual's linear-algebra skeleton is machine-checked on committed
objects (ordering, exact split, equality case, moment conversion, the
transport-to-wide-support interface), and three sweep findings are filed with
the law that generalizes them.

NOT MOVED: no trace bound, no density, no gap, no sign; the strip object and
the endpoint mass are untouched; nothing here feeds (star) by itself. The
conversion lemma is the interface through which a future trace bound on
`1 - K` would act — that bound does not exist in this wave.