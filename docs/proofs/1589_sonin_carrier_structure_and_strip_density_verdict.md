# 1589 — the Sonin carrier is pinned as the fixed space of the sandwich
# `E Q E` and is invariant under the Hardy--Titchmarsh involution; the 1587
# residual split and the trace-level moment conversion are machine-checked; the
# strip-density object is re-typed as a LOCAL TRACE whose finiteness is a new
# obligation, and the carrier's own nonemptiness turns out to be a HYPOTHESIS of
# the committed source layer, never a theorem (wave V CONT-13)

Date: 2026-09-17.

Status: LEAN LANDED + STRUCTURAL VERDICT + SWEEP. Ten declarations in
`ConnesWeilRH/Dev/C1G8R3SoninCarrierStructureBricks.lean` plus the paired axiom
audit `ConnesWeilRH/Dev/C1G8R3SoninCarrierStructureBricksAudit.lean`. One
unified acceptance build over both modules, green. Nothing in this record
closes the gate; the new finding of this wave is negative and load-bearing (see
section 5): the reduction chain that records 1586--1588 built stands on a
carrier whose nonemptiness is never proved anywhere in the tree. RH NOT claimed.

## 1. Result first

```text
+---------------------------------+-----------------------------------------------+
| item                            | value                                         |
+---------------------------------+-----------------------------------------------+
| targets                         | Dev.C1G8R3SoninCarrierStructureBricks +       |
|                                 | its paired axiom-audit module                 |
| build footer                    | "Build completed successfully" x1 (3161 jobs) |
| lines matching "error:"         | 0                                             |
| lines matching "sorryAx"        | 0                                             |
| #print axioms outputs           | 10                                            |
| axiom sets printed              | all ten = {propext, Classical.choice,         |
|                                 | Quot.sound}                                   |
| warnings inside the new modules | 0                                             |
| red rounds before the green one | 2, both mechanical (see below)                |
| log                             | build-logs/1589_carrier_structure.log         |
+---------------------------------+-----------------------------------------------+
```

Both red rounds were mechanical, not mathematical: one transposed `Eq.trans`
direction in the sandwich lemma, and one `rw` that could not unfold a `def`
(`ccm24ArchimedeanSoninClosedSubspace`) whose value is an infimum, replaced by a
`simpa only` with the `rfl`-level Mathlib lemma `ClosedSubmodule.toSubmodule_inf`
and by a defeq helper `fun v => Submodule.mem_inf`. The glyph-drop hazard struck
again (two bare `inner (...)` occurrences whose `ℂ` vanished in transit) and was
caught by the pre-build character audit, as in record 1588.

## 2. The ten declarations

```text
+----------------------------------------------------------+-------------------------------------------+
| declaration                                              | what it pins                              |
+----------------------------------------------------------+-------------------------------------------+
| starProjection_comp_apply_eq_self_iff                    | fixed space of the sandwich               |
|                                                          | E o Q o E = range E and range Q (1586 s1) |
| radialSupport_comp_fourierSupport_apply_eq_self_iff      | the same at the project pair              |
| sourceSoninProjection_eq_self_iff_mem_radial_and_fourier | the same with the inf projection          |
| sub_sourceSoninProjection_eq_add_defect                  | 1587 s2.1 vector identity                 |
| norm_sq_sub_sourceSoninProjection_eq_radial_add_defect   | 1587 s2.1 squared identity                |
| sum_norm_sq_sub_starProjection_le_of_quadraticFormGap    | (star)-level summed conversion            |
| radialSupportProjection_eq_self_of_mem_sonin             | 1581 s1 carrier vacuity, half 1           |
| sourceFourierSupportProjection_eq_self_of_mem_sonin      | 1581 s1 carrier vacuity, half 2           |
| radialSupportProjection_comp_apply_eq_of_mem_sonin       | 1581 s1 sandwiched consequence            |
| ccm24ArchimedeanHardyTitchmarsh_mem_sonin_iff            | carrier is H-invariant                    |
+----------------------------------------------------------+-------------------------------------------+
```

Three remarks on content.

`starProjection_comp_apply_eq_self_iff` is stated for two arbitrary orthogonal
projections and uses no relation between them. Read as an identity, it says the
carrier of the sandwich is `range(E) inf range(Q)` — the commutativity question
that record 1435 had raised at the level of norms disappears at the level of
ranges. The proof needs the equality case of the projection norm inequality,
which is the 1588 brick `starProjection_eq_self_of_re_inner_eq_normSq`; the two
waves therefore interlock.

`sub_sourceSoninProjection_eq_add_defect` and its squared twin are exact: no
error term, no hypothesis beyond the committed `P o E = P`. So the residual
column is *literally* the radial escape plus the carrier defect of the radially
projected vector, and the two are orthogonal.

`sum_norm_sq_sub_starProjection_le_of_quadraticFormGap` is the level change
that 1587 section 4 demanded: summed over any finite family (no orthonormality
needed — the per-vector bound is uniform), the squared distances are bounded by
`gap^-1` times the summed quadratic form of `1 - K`. That is exactly the `(star)`
level, and it is a scalar sum, so a future trace bound on `1 - K` acts through it
without passing through any operator-norm adapter.

## 3. Sweep findings (laws F8, F31, F32 applied by shape)

```text
+------------------------------------+-------------------------------------------------+
| layer swept                        | result                                          |
+------------------------------------+-------------------------------------------------+
| Mathlib Projection/*               | no fixed-space-of-sandwich lemma; only the      |
|                                    | orthogonal and the inclusion cases exist        |
| Mathlib (shape: projection comp)   | starProjection_comp_starProjection_of_le is the |
|                                    | only inclusion statement; no section/EQE form   |
| project tree (shape: fixed space)  | no statement identifying the fixed space of     |
|                                    | EQE with range E inf range Q                    |
| project tree (shape: H-invariance) | no statement that H preserves the carrier       |
| Dev/SoninWindowWitness.lean        | the carrier nontriviality IS filed, as an       |
|                                    | unproved Prop, and is called load-bearing       |
+------------------------------------+-------------------------------------------------+
```

The last two rows are the ones that matter, and they point in opposite
directions: the `Dev` tree has known since the Paley--Wiener lane that the
carrier's nonemptiness is the load-bearing analytic existence statement, while
the committed source layer — the layer the 1586--1588 reduction chain actually
consumes — carries it as a hypothesis and never proves it. That gap is the
subject of section 5.

The cleanup task carried over from 1588 (the local duplicate of
`Submodule.starProjection_comp_starProjection_of_le` in
`Dev/ELambdaFamilyProjectorProbe.lean`) is again NOT executed, and this time the
sweep produced the cost figure rather than the assertion: that file still has no
built olean, and it sits under the composite-boundary chain, so touching it
forces a rebuild of that chain for zero mathematical gain. Filed, not fixed.

## 4. What the carrier is, in two languages

```text
+------------------------+---------------------------------------------------+
| language               | statement                                         |
+------------------------+---------------------------------------------------+
| operator (this record) | carrier = range(E) inf range(Q)                   |
|                        | = fixed space of E Q E, and H maps it onto itself |
+------------------------+---------------------------------------------------+
| analytic (1586--1587)  | carrier = {g in H^2(C_-) : phi(-.) g in H^2(C_+)} |
|                        | a Toeplitz / Riemann--Hilbert kernel, where       |
|                        | phi = Factor/conj(Factor) is the archimedean      |
|                        | scattering multiplier                             |
+------------------------+---------------------------------------------------+
```

The right-hand analytic reading is the one that explains the difficulty. With
`phi = 1` the second condition degenerates into a support condition, and the
carrier collapses to `{0}`: the Paley--Wiener dictionary plus the F. and M.
Riesz uniqueness theorem for boundary values of `H^2` functions leaves no room.
So the multiplier is load-bearing: the carrier is NOT a support intersection,
it is a condition of analyticity after multiplication, and the naive
Wiener--Hopf factorization does not settle it — a unimodular boundary factor
has constant modulus and therefore is not in `L^2`. This is exactly the reason
`docs/paley_wiener/01_psp_projection_plan.md` still lists steps C, D, E as open.

## 5. The finding of this wave: the base of the chain is a hypothesis

Records 1586, 1587 and 1588 built a reduction of the gate residual onto the
carrier: the residual splits into a radial escape term and a carrier defect, and
the carrier is the fixed space of a sandwich. Every one of those statements is
about a subspace that may be `{0}`.

The sweep found where its nonemptiness lives:

```text
Dev/SoninWindowWitness.lean:44
  archimedeanSoninCarrier_nontrivial (lambda) : Prop :=
    exists u : sourceSoninCarrier lambda, u != 0
  -- doc: "the load-bearing analytic existence: every later step reduces to it"

CCM25Concrete/CCM24FiniteSFixedFullBoundaryInjectivityGuard.lean:103
  (hsource : exists y : sourceSoninCarrier lambda, y != 0)   -- a HYPOTHESIS
```

So the chain is not vacuous — it is conditional, in exactly the way that
matters. Every conclusion of the 1586--1588 form ("the residual equals the
carrier distance") is an identity, hence true when the carrier is `{0}`, where
it says nothing about the gate. The gate needs the carrier to be big enough to
carry mass, and that statement is not in the tree as a theorem.

**F33. A reduction chain must be checked for the existence of its base object,
not only for the correctness of its steps.** Before transporting an obligation
onto a subspace / fixed space / kernel, grep the tree for the `exists x, x != 0`
hypothesis that carries that object's nonemptiness. An identity whose two sides
both vanish is a valid theorem and a useless one; in a ledger it must be
recorded as conditional on the base object being nontrivial. The pre-spend sweep
of F8/F31/F32 checks statements and shapes; F33 adds the objects those
statements are about.

## 6. The strip-density object, re-typed

Task 1 of the wave was to decide what `StripDensity(Lambda) = Tr(P M_delta P)` is.
The typing is now settled at the level of the definition, but the decision
between "finite density" and "re-typed" cannot be made from the tree, because
neither side has a committed statement. What can be settled is the fork itself.

```text
+---------------------------------------------------+--------------------------------+
| reading of the local trace                        | consequence                    |
+---------------------------------------------------+--------------------------------+
| kernel of the carrier vanishes on the strip       | Tr = 0; the residual would be  |
|                                                   | priced entirely by the escape  |
| carrier kernel is a model-space / Toeplitz kernel | finite Poisson-type density;   |
| (H^2 minus theta H^2 shape)                       | StripDensity is a real number  |
| carrier kernel is full-Hardy-like                 | Tr = +inf; the object must be  |
|                                                   | re-typed before it can be used |
+---------------------------------------------------+--------------------------------+
```

The third row is not idle. For the orthonormal basis
`psi_n(z) = (z - i)^n / (z + i)^(n+1)` of `H^2`, the diagonal sum on the real
line is `sum_{n <= N} |psi_n(x)|^2 = (N + 1) / |x + i|^2`, which grows without
bound as `N` grows because `|x - i| = |x + i|` on the line. A carrier whose
kernel behaves like that has infinite local trace, and then
`Tr(P M_delta P) = ||M_delta P||_HS^2` is not a number to be bounded but a
statement that must be replaced. The two-sided evaluation of the archimedean
carrier kernel is therefore a prerequisite of task 1, not a corollary of it.

This is why the wave did not write a "finite density" declaration: writing one
would have been a guess dressed as a theorem. The bone list is unchanged in
kind — `StripDensity(Lambda)` stays open — but it now has a precise typing and a
precise prerequisite.

## 7. Why the chain has not reached RH (the structural answer)

Asked directly, the answer from this wave's evidence is a chain of three
statements, each of which is checked rather than asserted.

```text
+-----------------------------------------+--------------------------------------------+
| step                                    | evidence                                   |
+-----------------------------------------+--------------------------------------------+
| the gate is equivalent to the RH-level  | record 1343 (machine-checked iff)          |
| criterion, so closing the gate IS RH    |                                            |
| every wave since 1581 has reduced the   | 1581 carrier vacuity, 1586 residual        |
| residual onto the carrier and the strip | re-reduction, 1587 erratum + re-typing,    |
|                                         | 1588 + this record: the algebra is done    |
| the two remaining objects are analytic, | StripDensity: local trace of an unknown    |
| not algebraic, and neither has a        | kernel (section 6); carrier nonemptiness:  |
| committed statement in either direction | a hypothesis (section 5)                   |
+-----------------------------------------+--------------------------------------------+
```

In one sentence: the reduction has already consumed all of its algebraic
content — the linear algebra is machine-checked, the erratum cycle 1586 to 1587
retired its own angle premise, and what remains is two statements about a
specific analytic object, the archimedean scattering multiplier's Toeplitz
kernel, for which the tree contains no theorem in either direction. The gate is
not blocked by a missing technique; it is blocked by the fact that its residual
has been driven onto an object whose quantitative size nobody has ever computed,
and whose nonemptiness is currently assumed rather than proved.

## 8. Ledger

```text
+------------------------------------------+---------------------------------------------+
| object                                   | status after this record                    |
+------------------------------------------+---------------------------------------------+
| carrier = range E inf range Q            | MACHINE-CHECKED (general, no commutativity) |
| carrier is H-invariant                   | MACHINE-CHECKED                             |
| carrier nonemptiness                     | HYPOTHESIS in the source layer; NOT proved  |
| 1587 s2.1 residual split                 | MACHINE-CHECKED                             |
| (star)-level conversion                  | MACHINE-CHECKED as a finite sum             |
| rescaling eps-split of the zeroth moment | NOT machine-checked; needs the spectral     |
|                                          | measure of K, not algebraic                 |
| StripDensity(Lambda)                     | RE-TYPED: a local trace, finiteness is a    |
|                                          | NEW obligation; unchanged as a bone         |
| EndpointMass(epsilon)                    | OPEN (unchanged)                            |
| (star)/B4/rho5/R4/(OB)/W1                | OPEN                                        |
| RH                                       | NOT claimed                                 |
+------------------------------------------+---------------------------------------------+
```

Task 2 of the wave is therefore half-landed: the moment conversion is now
summed at the level the gate consumes (section 2), while the `eps`-window split
of the zeroth moment is NOT landed, because it needs the spectral measure of `K`
and is not an algebraic statement that can be written from the tree.

## 9. Boundary

MOVED: the carrier's operator-theoretic shape (fixed space of the sandwich,
invariance under `H`), the exact residual split at the project's own pair, the
trace-level form of the moment conversion, the two carrier-vacuity halves with
their sandwiched consequence, and the typing of the strip object together with
its test case.

NOT MOVED: no trace bound, no density value, no gap, no sign, and — the point of
section 5 — no proof that the carrier is anything other than `{0}`. Records
1586--1589 should be read as a conditional reduction: IF the carrier is
nontrivial, THEN the gate residual is priced by the strip trace and the gap.
That conditional is not RH, and this record does not claim it is closer to RH
than the previous wave: it is closer to knowing what RH would need here.
