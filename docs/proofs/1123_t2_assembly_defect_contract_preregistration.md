# Record 1123 — T2 assembly: Hnorm discharge, the defect contract, and the one-window Stage-B instance

Status: PRE-REGISTRATION (committed before any build).
Date: 2026-09-04.
Predecessors: 1120 (span-level absolutes), 1121 (hrep generator), 1122
(generic archimedean legality).  Consumer: the T2 assembly of the D1-pinned
detector, per the 1120 s5 sequencing — this record closes item (ii) Hnorm,
fixes item (iv) as a ONE-inequality Lean contract, and supplies the
Stage-B instance template that consumes it.  RH NOT claimed; no map change
keyed.

## 0. Scope and motivation

After 1122 the T2 named-obligation set is exactly: (iv) real contraction
decay, C2 (true-table route only), Hnorm (bookkeeping).  This record:

  1. CLOSES Hnorm.  The 1120 span absolutes carry
       hnorm : K.mulVec y ⬝ᵥ (G_true *ᵥ (K.mulVec y)) = 1
     as a named hypothesis.  Because every quantity involved is homogeneous
     of degree 2 in y, normalization is WLOG: given
     s := K.mulVec y ⬝ᵥ (G_true *ᵥ (K.mulVec y)) > 0, the rescaled
     coefficient t • y with t = (sqrt s)^{-1} is normalized, and the
     certified bound lands on the rescaled span object.  Hbox does not
     mention y, so it is scale-invariant.  Landed as an EXISTENCE theorem:
     for every coefficient with positive G-norm there EXISTS a Stage-B
     window W with `ICgate W.convolutionSquare <= -mu` and the inherited
     support — no normalization hypothesis anywhere.

  2. FIXES the (iv) contract.  By the 1117 linearity layer, the Stage-B
     defect gate is EXACTLY a difference:
       ICgate (ICdefect gHead s W lam) = ICgate gHead - sum lam i * ICgate (W i),
     and by 1122 the legality hypotheses of `ICgate_ICdefect` are now
     discharged UNCONDITIONALLY.  For the one-window instance this reduces
     the whole Stage-B content to a single inequality on the true data:
       ICgate gHead - ICgate W <= epsilon.        (the 1116c contract)

  3. SUPPLIES the assembly template.  One literal `ICStageBContraction g`
     instance (iota = Unit, one window, lam = 1) consuming exactly:
     a certified window (slot supplied by item 1 above), the defect bound
     (slot = the 1116c contract of item 2), and the budget.  The bridge of
     1117 then produces the 1089 orbit gate.  After this record, the
     ENTIRE remaining content of (iv) is the numeric certificate for one
     inequality — a well-posed standalone task.

## 1. Statement inventory (the contract)

New module `ConnesWeilRH/Dev/C1T2Assembly.lean`, namespace
`ConnesWeilRH.Source.C1T2Assembly`.  Imports `C1HkerSpan` (1120 data +
absolutes), `C1ArchimedeanIntegrabilityGeneric` (1122),
`C1LocalConfigurationDomination` (1117), `C1GateMatrixRepresentation`
(1121), `C1OrbitWindowSemiLocalGate` (1089 gate, transitively).

Normalization layer:

  N1  qform_smul_homogeneous {n} (G : Matrix (Fin n) (Fin n) ℝ)
        (c : Fin n → ℝ) (t : ℝ) :
        (fun i => t * c i) ⬝ᵥ (G *ᵥ (fun i => t * c i))
          = t ^ 2 * (c ⬝ᵥ (G *ᵥ c))
  N2  qform_norm_representative {n} (G) (c)
        (hpos : 0 < c ⬝ᵥ (G *ᵥ c)) :
        ∃ t : ℝ, (fun i => t * c i) ⬝ᵥ (G *ᵥ (fun i => t * c i)) = 1
      (t = (Real.sqrt s)^{-1}, via Real.mul_self_sqrt)

Span layer:

  S0  spanObj_support {k} (w) (y) {B} (hw) :
        Function.support (spanObj w y).test ⊆ Ioo (-B) B
      (the union of the supports; needed by the assembly's hwsupp)
  S1  gate_span_smul_homogeneous {k} (w) (y) (t) {B} (hw) :
        ICgate ((spanObj w (fun i => t * y i)).convolutionSquare)
          = t ^ 2 * ICgate ((spanObj w y).convolutionSquare)
      (both sides expanded by 1121/1122 `gate_sum_span_free`, then
      Finset transport + ring)

Hnorm discharge (one per class; q28 shown, q38/q48 identical):

  C1  exists_certified_classWindow_q28 {w8 : Fin 8 → CompactLogTest}
        {G_true M_true : Matrix (Fin 8) (Fin 8) ℝ} {y : Fin 5 → ℝ}
        {B : ℝ} (hw8 : ∀ i, Function.support (w8 i).test ⊆ Ioo (-B) B)
        (hM : gateMatrix w8 = M_true)
        (hbox : Hbox GLo_q28 GHi_q28 MLo_q28 MHi_q28 G_true M_true)
        (hpos : 0 < Q28.K.mulVec y ⬝ᵥ (G_true *ᵥ (Q28.K.mulVec y))) :
        ∃ W : CompactLogTest, ICgate W.convolutionSquare ≤ -mu_q28
          ∧ Function.support W.test ⊆ Ioo (-B) B
      Proof: t := (Real.sqrt s)^{-1}; W := spanObj w8 (Q28.K.mulVec
      (fun i => t * y i)); feed `absolute_spanK_q28` at the rescaled
      coefficient with hnorm discharged by N1+N2 (K.mulVec rescales
      pointwise through `Matrix.mulVec`) and hrep supplied by
      `gate_qform_span_free` + hM.  The support slot is S0.

Defect contract layer:

  D1  defectGate_singleton_eq_sub (g W : CompactLogTest) :
        ICgate (ICdefect g.convolutionSquare {()}
          (fun _ => W.convolutionSquare) (fun _ => 1))
          = ICgate g.convolutionSquare - ICgate W.convolutionSquare
      (`ICgate_ICdefect` of 1117 with ALL legality from 1122
      `integrableOn_archimedeanIntegrand`; common window via
      convolutionSquare_support_subset_two_mul_Ioo at a radius built from
      `supportRadius g` / `supportRadius W` — small helper
      support_subset_Ioo_of_radius_lt)

Assembly layer:

  E1  stageBContraction_of_certifiedWindow (g W : CompactLogTest)
        {b a mu epsilon : ℝ}
        (hgsupp : Function.support g.test ⊆ Ioo (-b) b)
        (hWsupp : Function.support W.test ⊆ Ioo (-a) a)
        (hcert : ICgate W.convolutionSquare ≤ -mu)
        (hdec : ICgate (ICdefect g.convolutionSquare {()}
          (fun _ => W.convolutionSquare) (fun _ => 1)) ≤ epsilon)
        (hbudget : epsilon ≤ mu) :
        ICStageBContraction g
      (literal instance: iota = Unit, s = {()}, lam = fun _ => 1,
      mu = fun _ => mu)
  E2  orbitGate_of_certifiedWindow — same hypotheses as E1, conclusion
      `C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g`
      (E1 + the 1117 bridge; budget sum collapses by
      Finset.sum_singleton/mul_one)

Audit module `C1T2AssemblyAudit.lean`: `#print axioms` on every
declaration, plus G3 fidelity examples.

## 2. Mechanism and reuse

  - N1/N2: pure ℝ dotProduct/mulVec algebra + Real.sqrt; the
    dotProduct-over-literal-matrix idiom pinned by 1121.
  - S1: 1121 `gate_sum_span_free` at both coefficients (1122 removed the
    legality argument), Finset.sum_congr + ring.
  - C1: 1120 `absolute_spanK_q*` at the rescaled coefficient.  The point
    that makes hnorm dischargeable: hbox does not mention y, and hrep at
    the rescaled coefficient is re-supplied by the 1121 generator (the
    hrep of an arbitrary w tied to the ORIGINAL y is NOT needed — the
    existential CHOOSES the rescaled span object as its witness).
  - D1: 1117 `ICgate_ICdefect`; 1122 makes its integrability arguments
    unconditional for the first time.
  - E1/E2: 1117 structure + bridge.

Zero numeric content: no probe, no data, no thresholds.

## 3. Risks / pre-registered deviation policy

  R1  `Matrix.mulVec` rescaling: a pointwise helper (mulVec over
      `fun i => t * v i` = scaled mulVec) is proved if no ready-made
      `Matrix.mulVec_smul` form matches; PROOF-side only.
  R2  E1 structure-literal eta-shapes (`fun _ => W.convolutionSquare` vs
      projection paths): if the literal does not typecheck against the
      1117 field, the assembly is stated with an explicit
      `ICStageBContraction.mk` application; statement shapes above are
      the contract.
  R3  Scope does not shrink below C1(q28,q38,q48) + D1 + E1 + E2.  If any
      step cannot close, the addendum registers the root cause and the
      fix batch.

## 4. Gates and protocol

  G1  (build) focused `lake build ConnesWeilRH.Dev.C1T2Assembly
      ConnesWeilRH.Dev.C1T2AssemblyAudit` on the ext4 build mirror via
      the resource runner: footer "Build completed successfully (N jobs)"
      AND zero `^error:` lines AND zero `sorry`.  Acceptance = log
      content, not exit code.
  G2  (axioms) every `#print axioms` in the audit prints exactly
      `[propext, Classical.choice, Quot.sound]`.
  G3  (fidelity) audit examples: (a) E1 applied at abstract data yields a
      term of `ICStageBContraction g`; (b) C1(q28) applied at an abstract
      coefficient with positive G-norm yields a certified window with the
      inherited support; (c) D1 reproduces the difference form.
  G4  (hygiene) staged-diff grep on EVERY commit: no `sorry`/`admit`/
      `sorryAx`, no private artifacts, no local paths.

Protocol: preregistration commits BEFORE the first build; one root-caused
fix commit per failing build; zero threshold changes (no thresholds);
post-run addendum after the gates.

## 5. Map consequence (post-landing, to be confirmed by the addendum)

T2 named obligations after this record: EXACTLY (iv) — now a single named
inequality `ICgate gHead - ICgate W <= epsilon` on the TRUE correction
data (the 1116c contract, fixed in Lean by D1+E1) — plus C2 on the
true-table route only.  Hnorm CLOSED.  The numeric side receives a
precise, standalone target.  RH NOT claimed; no map change keyed.

## 6. Post-run addendum (2026-09-04, after builds 1-5)

VERDICT: LANDED.  Chain: prereg `cbd184a` committed BEFORE any build ->
module draft `69fa680` -> build 1 FAILED -> fix batch `1bb1a2e` -> build 2
FAILED -> fix batch `9d7d69b` -> build 3 FAILED -> fix batch `472559e` ->
build 4 FAILED (audit only) -> fix `141d510` -> build 5 FULL GREEN.

Build 1 root causes (7 sites, 6 mechanisms, one batch):
  (a)  missing `open C1WindowRationalIngest` - Q28/Q38/Q48 live inside
       that namespace (file C1WindowRationalIngestQ28.lean); 12 unknown-
       identifier sites are ONE root cause;
  (b)  `field_simp` on the sqrt normalization leaves the residual goal
       `s = Real.sqrt s ^ 2` (pow form vs mul form of Real.mul_self_sqrt);
  (c)  the span-homogeneity chain needs `Finset.mul_sum` BEFORE
       sum_congr - the RHS is still wrapped in `t ^ 2 * sum`;
  (d)  `support_subset_Icc F hx` returns an opaque Set-membership atom;
       `simp only [Set.mem_Icc] at hcc` before linarith;
  (e)  `ICgate_ICdefect _ _ _ _` leaves s/lam as metavars - they appear
       in no elaborated argument and `exact` does not back-propagate
       them through the expected type; supply them explicitly;
  (f)  `ICStageBContraction g` is a STRUCTURE, not a Prop - the E1
       assembly is a `noncomputable def`, not a theorem ("type ... is
       not a proposition").

Build 2 root causes (7 sites, 4 mechanisms):
  (a)  the sqrt chain: `rw [pow_two]` leaves a LEFT-associated product;
       `rw [← mul_assoc]` looks for a RIGHT-associated one;
  (b)  `absolute_spanK_q*`'s implicit `y` appears in NO conclusion
       (only in hrep/hnorm), so `refine` cannot synthesize it; pin
       `(y := fun i => t * y i)` explicitly - 3 sites;
  (c)  the E1 budget slot is unused in the body (contract-only) ->
       `_hbudget` (zero new warnings);
  (d)  `simpa using hbudget` cannot reduce projections of an APPLIED
       def without its equation lemmas: `simpa [def-name] using h`.

Build 3 root causes (5 sites, 2 mechanisms):
  (a)  `rw [← hsq]` rewrites EVERY occurrence of the dot product -
       including the copies inside the two `Real.sqrt` applications -
       nesting the square roots; `nth_rewrite 2 [← hsq]` targets only
       the standalone multiply - 2 sites;
  (b)  `mulVec_smul_pointwise` was specialized to SQUARE matrices but
       `Q28/Q38/Q48.K : Matrix (Fin 8) (Fin 5) ℝ` is RECTANGULAR
       (8 window tests, 5-dim class space); generalized to
       `{m n}` - 3 sites.  Preregistered under R1 (proof-side helper).

Build 4 root cause (1 site): the audit E1 fidelity `example` RETURNS
the noncomputable def's output, so the example itself must be
`noncomputable example`.

Build 5: FULL GREEN - "Build completed successfully (3657 jobs)", zero
`^error:` lines, zero `sorry`.  G1 PASS.  G2 PASS: 13/13 `#print axioms`
records exactly `[propext, Classical.choice, Quot.sound]` (lines
rejoined across wraps; 13 unique declarations, none missing, zero
sorryAx).  G3 PASS: all three fidelity examples compile - (a) E1 applied
at abstract data yields a literal `ICStageBContraction g` term, (b) C1
(q28) yields a certified window with inherited support from a positive
G-norm coefficient, (c) D1 reproduces the difference form.  G4 PASS:
staged-diff hygiene grep on all six commits of this record, clean.
Warnings: the pre-existing old-module warning set only; ZERO warnings
on the two new modules.

Deviations: NONE on the preregistered statement shapes.  Two
preregistered-rule applications: R1 fired (the pointwise mulVec helper
was proved in-house AND generalized to rectangular matrices), R2 did
not fire (the `where`-literal typed fine once def-typed).  One
additional generalization: N1-helper `mulVec_smul_pointwise` carries
`{m n : ℕ}` instead of `{n}` - strictly more general, statement shapes
above unchanged.

Consequence: Hnorm CLOSED for all three certified classes - the 1120
absolute headline now fires for EVERY coefficient with positive G-norm,
with the window existential absorbing the normalization.  The 1116c
consumption contract is FIXED in Lean as a single inequality:
`ICgate gHead - ICgate W <= epsilon` (D1 gives the equality, E1
consumes the inequality, the 1117 bridge returns the 1089 orbit gate).
T2 named-obligation set after this record: EXACTLY
  (iv)  the numeric certificate for `ICgate gHead - ICgate W <= epsilon`
        on the TRUE correction data - a well-posed standalone task,
  C2    drift bound on the TRUE moment table (true-table route only).
RH NOT claimed; no map change keyed.
