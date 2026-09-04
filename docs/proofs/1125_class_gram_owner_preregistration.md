# Record 1125 - class Gram owner and Hbox-G consumer socket

Status: PRE-REGISTRATION (committed before implementation).
Date: 2026-09-04.
Routing: the true-test bridge selected for the healthy-`CompactLog`, B5-shaped
mainline.  Consumer: `C1HboxRationalData.Hbox` as used by the class instances
of `C1HkerSpan.absolute_spanK_q28/q38/q48` and
`C1T2Assembly.exists_certified_classWindow_q28/q38/q48`.
RH NOT claimed.

## 0. Why this record exists

Record 1124 landed the Lean objects
`classWindowTest a ha i : CompactLogTest`.  The 1112 data pipeline's `G_TAB`
entry is the ordinary real Gram integral

    G[i,j] = ∫ x, phi_i(x) * phi_j(x),

but the current certificate chain still receives an abstract
`G_true : Matrix (Fin 8) (Fin 8) ℝ`.  This record supplies the same-owner
definition and its algebraic facts.  It does not silently turn the committed
floating-point/Arb enclosure into a theorem: the narrow inequalities
`GLo i j ≤ G_true i j ≤ GHi i j` remain a separately auditable analytic
certificate obligation.

## 1. Statement inventory

New module: `ConnesWeilRH/Dev/C1ClassGramOwner.lean`, namespace
`ConnesWeilRH.Source.C1ClassGramOwner`.

The module will provide:

1. `classWindowFun_contDiff` and a real-core compact-support lemma, making the
   integrability of every product `classWindowFun a i * classWindowFun a j`
   explicit rather than hidden inside the `CompactLogTest` constructor.
2. `classGramEntry a ha i j` and
   `classGramMatrix a ha : Matrix (Fin 8) (Fin 8) ℝ`, defined by the real
   Lebesgue integral of the two class-window cores.
3. A pointwise packaging bridge from `classWindowTest` back to its real core,
   plus the corresponding integral identity.  This pins the Gram owner to
   the same `phi_i` objects used by 1124 and by the 1112 convention probe.
4. Symmetry of `classGramMatrix` and the finite quadratic-form identity

       c ⬝ᵥ (classGramMatrix a ha *ᵥ c)
         = ∫ x, (∑ i, c i * classWindowFun a i x)^2,

   followed by nonnegativity of this quadratic form.  This is a generic Gram
   fact, not the missing `Hbox-G` numerical enclosure.
5. A consumer theorem which turns explicit entrywise bounds on
   `classGramMatrix a ha` (and the already separate M-side bounds) into the
   exact `Hbox` proposition consumed by the existing T-box chain.

No gate sign, detector contradiction, or RH statement is introduced.

## 2. Boundary and non-go

The formal owner is the real core, not the rejected normalized additive B5
owner.  The family is fixed at `Fin 8`, with class scales `a = 2, 3, 4`.
The record may expose a theorem of the form

    (∀ i j, GLo i j ≤ classGramMatrix a ha i j ∧
      classGramMatrix a ha i j ≤ GHi i j) → Hbox ...

but it must not prove that premise from a floating table, a quadrature rule,
or an unproved interval-arithmetic claim.  A later analytic certificate must
justify those 64 bounds with a validated integration/error argument and its
source provenance.

## 3. Mechanism

Smoothness and compact support come from 1124's `classBump_contDiff`,
`contDiff_legendreEval`, and support lemmas.  Products inherit compact support
and are integrable by continuous compact-support integrability.  The Gram
quadratic identity is finite-sum linearity of the Bochner integral followed
by ring normalization; its sign is `integral_nonneg` applied to a square.

The `Hbox` consumer is a structural projection: its G-half is exactly the
entrywise bound on `classGramMatrix`, while its M-half is passed separately.
No density lift, universal B1 theorem, or ROOT-window positivity theorem is
used.

## 4. Gates

G1. Focused resource-runner build of the module and paired audit module,
   with a success footer, zero `^error:` lines, and zero `sorryAx`.
G2. Every public declaration printed by the audit has exactly
   `[propext, Classical.choice, Quot.sound]`.
G3. Fidelity examples instantiate the `(2,8)` family, expose the real-core
   integral owner, and type-check the Hbox consumer socket.
G4. Staged-diff hygiene: no `sorry`, `admit`, private paths, or uncommitted
   generated artifacts.

## 5. Map consequence

Candidate bridge only, no route-map change.  If landed, 1125 makes the true
Gram matrix a named same-owner Lean object and reduces the Hbox-G blocker to
64 explicit analytic inequalities.  It does not close (iv), C2, detector
specific semi-local positivity, `SourceRH`, or RH.
