# 1231 - NM Beat 0: finite-Mellin versus physical-evaluation separation

Date: 2026-09-09.

Status: `SCREENED-LIVE` at its deliberately raw scope after the formal proof
in section 4.  The separation brick was registered before any new Lean
declaration or numerical run.  RH is not claimed.

Authority: map record [`006`](../map/006_new_math_creation_workflow.md),
following G4's source/API stop in record
[`1230`](1230_nm_node_visible_profile_rank_preregistration.md).  Its sole
consumer is the healthy-`CompactLog`, selected-detector same-owner B5 direct
gate: it tests whether a proposed rho-node-only off-diagonal/profile identity
could possibly supply the missing P2 information.  It does not itself prove a
gate sign, positivity, or an RH consequence.

## 1. Generation Card G5

```text
candidate/id  G5: finite Mellin nodes do not determine a physical evaluation

TARGET
  For a fixed open residual log window I, finite S : Finset Complex, and an
  allowed physical coordinate x in I, construct a CompactLogTest h supported
  in I such that
      laplaceAt h s = 0  (s in S),       h.test x != 0.

INTERPRETATION
  This is a separation theorem for the raw interpolation layer.  It says that
  the finite raw Laplace equations alone cannot determine a physical test
  evaluation.  Since P2 reads bilateral physical values at log prime powers,
  a G1-style rho-node-only bridge must use additional same-owner structure.

NON-CLAIM
  h is not asserted to preserve the full selected orbit's tail estimates,
  closed-ball zero control, or detector health after insertion.  Thus G5 is
  not a perturbation of the complete orbit construction and cannot be used as
  the stronger G4 BARRIER without further legal-family work.

CHEAP FALSIFIER
  If the available compact-test API cannot state a point evaluation together
  with finite Mellin constraints on one support window, stop as NO-API.  If
  the proposed proof merely invokes arbitrary finite Mellin interpolation
  without a physical-evaluation nonvanishing argument, it fails.
```

## 2. Required formal shape

The target must make the support and point explicit and must prove the two
different kinds of condition separately:

```text
support(h.test) ⊆ I;
∀ s ∈ S, laplaceAt h s = 0;
h.test x ≠ 0.
```

An allowed proof may use a finite family of compactly supported local bumps,
their finite Mellin evaluation matrix, and a rank/nullspace argument, provided
the last nonzero physical coordinate is proved rather than selected as stored
data.  It may not use RH, `qw`, a B5 producer field, an unproved density
claim, or numerical rank evidence.

To touch the P2 profile later requires an additional, separately registered
composition lemma: the raw correction perturbation must survive convolution,
half-density shift, convolution square, and the actual finite visible-prime
owner.  G5 deliberately does not assert that lemma.

## 3. Branches and budget

```text
SEPARATED: prove the raw-layer theorem and record a formal Beat-3 guard:
           raw finite-node data alone cannot be cited as a profile identity.
NO-API:    record the exact absent compact-bump/point-evaluation API; do not
           simulate it numerically.
FAILED:    record a concrete counter-obstruction to the proposed construction,
           not a conclusion about all compact tests.
```

Budget: one source-interface audit, then at most one focused Lean source leaf
and its paired axiom audit.  No numerical run, endpoint work, or new owner is
authorized.

RH is not claimed.

## 4. Post-run addendum: formal raw-layer separation

Evidence level: FORMAL.  The `SEPARATED` branch is proved in
`C1FiniteMellinPhysicalSeparation.lean`:
`exists_laplace_vanishing_test_value_one` states that for every finite complex
node set and every `x > 0`, there is a `CompactLogTest h` supported in
`(-x, 2*x)` with

```text
laplaceAt h s = 0  for every registered node s,
h.test x = 1.
```

The proof uses exactly the preregistered construction.  A positive-variable
value-one bump supported around `exp x` becomes `h0`; the committed finite
Mellin interpolator supplies `h1` in `(-x/4, x/4)` with the same node values;
`h0 - h1` has zero node data and remains one at `x` because `h1` vanishes
there.  It is a symbolic support/interpolation proof, not a rank computation.

Focused WSL build:
`C1FiniteMellinPhysicalSeparation` plus its Audit, 3652 jobs, completed
successfully on 2026-09-09.  The audit prints exactly
`[propext, Classical.choice, Quot.sound]`; the build log contains zero
`error:` and zero `sorryAx`.

Formal consequence: a claimed P2 visible-profile identity cannot be justified
from the finite raw Laplace-node equations *alone*.  It must name additional
same-owner data that crosses from the raw correction to convolution,
half-density shift, convolution square, and the selected finite visible-prime
profile.  The result does not construct a perturbation preserving the full
orbit tail and zero-control package, so it is not the stronger G4 barrier and
does not alter the healthy detector or B5 route.

RH is not claimed.
