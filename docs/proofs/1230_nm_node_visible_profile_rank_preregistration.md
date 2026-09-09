# 1230 - NM Beat 0: orbit-node to visible-profile rank audit preregistration

Date: 2026-09-09.

Status: PREREGISTRATION.  This is a paper-and-formal-interface audit, committed
before any new Lean declaration, numerical run, or candidate survival claim.
RH is not claimed.

## 5. Post-run addendum: source/API audit

Evidence level: FORMAL interface audit.  Verdict: `NEEDS-ANALYSIS` (the
`NO-API` branch), not a barrier theorem and not a live Lean brick.

The audit identifies the genuine orbit-side finite data.  The target-node
object `healthyUnscaledTargetNodes rho` and its prescribed raw values are
defined in `C1HealthyYoshidaUnscaledOrbit.lean:31-43`; the selected owner is
assembled in
`exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner_with_raw_targets`
at lines 492-660.  Its raw correction does realize those values.  Thus G4.1
and the node portion of G4.2 are real formal interfaces, not an invented
ansatz.

But this theorem returns
`exists base, exists T, ... forall R, exists correction, exists C, exists n`.
It neither selects a correction as a function of `rho` nor exports an affine
source family, a difference action, or a node map whose kernel can be formed.
The lower interpolation supplier is likewise existential:
`exists_residualWindow_correction` in
`Source/CC20YoshidaConvolution.lean:295-319`, ultimately using finite Mellin
surjectivity in `Source/CC20YoshidaNearZeros.lean:1153-1180`.  That proves
that one may realize specified finite Mellin data, but gives no theorem about
two realizers' difference at a physical-space coordinate.

On the P2 side the required observable is explicitly a *physical* one:
`bilateralProfile F y = F.test y + F.test (-y)` in
`C1P2BilateralProfile.lean:34-35`, sampled at `y = log n` over the
detector-square's own finite `globalPrimeIndexSet`.  The orbit theorem supplies
a support bound and hence a cutoff, but no named vector-valued profile map and
no identity relating these physical evaluations to the finite Laplace-node
values.  Consequently G4.3 exists only as a scalar readback interface, while
G4.4 cannot be stated for a legal perturbation family.

No legal `N_rho`/`V_rho` pair is therefore available, so neither
`ker N_rho ⊆ ker V_rho` nor a node-preserving profile-changing perturbation is
currently a well-typed claim.  Constructing an arbitrary finite-dimensional
ansatz would violate this record's same-construction rule.  The exact next
admissible brick, if pursued, is narrower: expose a canonical or explicitly
parameterized correction family *together with* its physical-test evaluation
API, then repeat G4.  It still has no sign source, and no numerical work or
RH claim is authorized.

RH is not claimed.

Authority: map record [`006`](../map/006_new_math_creation_workflow.md), Beat
0, after the G1 audit in record
[`1229`](1229_nm_generate_direct_gate_preregistration.md).  The consumer is
the binding route ruling [`003`](../map/003_b1_b5_minimal_exit_route_selection.md):
the healthy-`CompactLog`, selected-detector, same-owner semi-local B5 exit.
It does not reopen B1, the normalized/additive owner, Line B, the prime-free
reference route, or a numerical campaign.

## 1. Generation Card G4

```text
candidate/id  G4: orbit-node to finite visible-profile factorization

TARGET QUESTION
  Does the rho-node/detection data used to construct the actual formal orbit
  detector g(rho) determine its bilateral values at the finite visible prime
  powers of that same detector owner?

NEEDED BRIDGE
  An explicit, noncircular factorization from the correction/orbit data fixed
  by the rho-node conditions to the actual finite visible-prime profile.  Only
  such a bridge could supply the rho-dependent off-diagonal information absent
  from G1 and potentially feed the direct gate
      ICgate (g(rho).convolutionSquare) <= 0.

SIGN SOURCE
  None is presumed.  G4 first decides information flow.  A factorization is
  useful only if a later independent identity supplies its sign; it is never
  permitted to assume qw >= 0, SourceRH, ICgate <= 0, or a same-g positivity
  field to obtain the factorization.

CHEAP FALSIFIER
  In an explicitly named affine correction family, exhibit a perturbation that
  preserves every registered rho node and detection equation but changes one
  actual visible prime-power bilateral value.  This disproves determination by
  those node data.  The first attempted restriction is one visible prime power,
  then two; arbitrary free matrices are not evidence.
```

## 2. Typed audit obligation

The audit first recovers the *actual* construction API: the source correction
data, its node/detection constraints, the orbit map to a healthy
`CompactLogTest`, and the finite visible-prime profile used by the direct P2
gate.  It must not silently replace the construction by an unrelated
interpolation space.

If the construction exposes an affine ambient correction family `A(rho)`, let
`N_rho` be its map to the full registered node/detection data and let `V_rho`
be its map to the bilateral values at the actual finite visible prime powers.
The only two conclusive outcomes are:

```text
BRIDGE:   ker N_rho ⊆ ker V_rho,
          together with an explicit construction/reason that V_rho factors
          through N_rho on A(rho).

BARRIER:  an explicitly legal d in A(rho) with N_rho(d) = 0 and
          V_rho(d) ≠ 0 at one actual visible coordinate.
```

`BRIDGE` is an information-flow result, not a gate inequality and not a B5
producer.  `BARRIER` kills only the claim that the registered node equations
alone determine that profile; it does not kill a later bridge using additional
orbit structure.  Both statements must retain the same rho, detector, support,
and finite-prime owner.

If no affine family or linear/affine node map belongs to the existing formal
construction, the permitted first result is instead `NEEDS-ANALYSIS`: document
the missing owner/API and stop.  Fabricating a parameter family after the fact
does not meet this card.

## 3. Exact screen checks

```text
G4.1  Name the formal orbit constructor and its correction source data.
G4.2  Name every rho-node and detector equation actually used to pin it.
G4.3  Name the finite visible-prime owner and the exact bilateral-profile map
      entering the same detector's ICgate.
G4.4  Establish that any proposed perturbation remains in the construction's
      legal source family and preserves health/support ownership; otherwise it
      is not a falsifier.
G4.5  Prove BRIDGE or BARRIER above, or stop as NEEDS-ANALYSIS with an exact
      missing-interface witness.
G4.6  Audit anti-circularity: no conclusion may use an RH-equivalent sign or
      read a stored positivity conclusion as source data.
```

The first audit is read-only source/interface inspection.  No numerical
evaluation is authorized: a float rank test could neither identify the actual
formal owner nor prove a kernel inclusion.  A Lean lemma may be opened only
after G4.1--G4.4 name concrete declarations and its consumer is the P2 direct
gate.

## 4. Branches and budget

```text
BRIDGE:      record the factorization and screen whether an independent,
             same-owner sign identity can consume it.
BARRIER:     append a Beat-3 kill-ledger row; do not retry node-only
             interpolation with a larger ansatz.
NO-API:      NEEDS-ANALYSIS; record the exact missing construction interface.
CIRCULAR:    SCREENED-DEAD; cite the circular premise precisely.
```

Budget: one source/API audit and, only if its terms already exist, one focused
formal interface proposition with its paired axiom audit.  No build is needed
for documentation-only results; no numerical or endpoint work is opened.

RH is not claimed.
