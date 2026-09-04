# Record 1124 - bridge phase 1: the class window-test family as Lean objects

Status: PRE-REGISTRATION (committed before any build).
Date: 2026-09-04.
Routing: Peter selected (alpha) the true-test bridge over (beta) mp-grade
true-correction, (gamma) E1 literature reconstruction, (delta) consolidate.
This is phase 1 of the bridge: the OBJECTS only.  It certifies no number,
installs no box, and asserts no sign.  RH NOT claimed; no map change keyed.

## 0. Why this record exists

After 1123 the T2 named obligations are exactly (iv) the defect certificate
on TRUE data and C2 (true-table route).  Both are CONSUMER-BLOCKED by the
same missing layer: the certified-class window tests

    phi_i(u) = P_i(u/a) * exp(-1/(1-(u/a)^2)),   |u| < a;  0 otherwise
    (i = 0..7, P_i the standard Legendre polynomial, a the class scale)

exist only in the Python pipeline (1112_true_interval_whitened_probe.py:69,
K = 8; convention verified this window), so `Hbox` has no Lean-side true
instance, `gateMatrix w8 = M_true` cannot be instantiated, and C2's drift
box has no Lean consumer.  The bridge program is:

    1124 (this)  the objects: phi_i as CompactLogTest, supports, smoothness
    1125         Gram enclosures int phi_i phi_j (the Hbox-G half)
    1126         gate-matrix enclosures (the Hbox-M half, hrep instance)
    1127         C2 drift box + the data-grounded certified window
                 (1123's exists_certified_classWindow_q28 instantiated)

The point that makes 1124 cheap: Mathlib ALREADY proves the hard analytic
fact.  `expNegInvGlue x = if x <= 0 then 0 else exp (-x⁻¹)` carries
`expNegInvGlue.contDiff : ContDiff ℝ n expNegInvGlue`
(Mathlib Analysis/SpecialFunctions/SmoothTransition.lean:139), and on
x > 0 it is LITERALLY exp(-1/x).  Therefore the class bump

    classBump x = expNegInvGlue (1 - x^2)

agrees with the Python bump pointwise EVERYWHERE (both are exp(-1/(1-x^2))
for |x| < 1 and 0 for |x| >= 1) and is ContDiff-infinite by one composition.
The object layer is pure bookkeeping over landed Mathlib facts.

## 1. Statement inventory (the contract)

New module `ConnesWeilRH/Dev/C1ClassWindowObjects.lean`, namespace
`ConnesWeilRH.Source.C1ClassWindowObjects`.

Object layer:

  O1  classBump (x : ℝ) : ℝ := expNegInvGlue (1 - x^2)
      with `classBump_eq_exp` (|x| < 1 -> classBump x = exp (-1/(1-x^2))),
      `classBump_eq_zero` (1 <= |x| -> classBump x = 0),
      `classBump_contDiff : ContDiff ℝ ∞ classBump`.
  O2  legendrePoly : ℕ -> ℝ[X] by the standard recurrence
      P0 = 1, P1 = X, (n+1) P_{n+1} = (2n+1) X P_n - n P_{n-1}
      (no literal tables - the recurrence IS the convention; the Python
      probe asserts its tables satisfy the same recurrence in Fraction
      arithmetic, so both sides are standard Legendre by construction).
  O3  classWindowFun (a : ℝ) (i : ℕ) (u : ℝ) : ℝ :=
        Polynomial.eval (u / a) (legendrePoly i) * classBump (u / a)
      - the REAL-valued core of phi_i, matching
        1112 phi_iv(u_iv, i, A_R) (0-based i in range(K), K = 8).
  O4  classWindowTest (a : ℝ) (ha : 0 < a) (i : ℕ) : CompactLogTest :=
        { test := hcompact.toSchwartzMap hsmooth, compactSupport := ... }
      - the house packaging (C1HealthyDetectorArchRescue:57-63 idiom),
        ℂ-valued via the real core coerced; hsmooth by fun_prop over
        O1-O3 (polynomial eval + expNegInvGlue composition + scalar mul).
  O5  classWindowTest_support (a) (ha) (i) :
        Function.support (classWindowTest a ha i).test ⊆ Ioo (-a) a
      and the closed twin ⊆ Icc (-a) a (downstream consumers use both;
        support_subset_Icc shape matches CompactLogTest helpers).
  O6  classTestFamily (a : ℝ) (ha : 0 < a) : Fin 8 -> CompactLogTest :=
        fun i => classWindowTest a ha i
      - THE family object the certified-class chain consumes; the (a, 8)
        naming (q28/q38/q48) uses a in {2, 3, 4} downstream.

Audit module `C1ClassWindowObjectsAudit.lean`: `#print axioms` on every
public declaration + fidelity `example`s: (a) classWindowTest applied at
(a = 2, i = 3) types as a CompactLogTest with the O5 support; (b) the
family at a = 4 types as `Fin 8 -> CompactLogTest`; (c) O1's pointwise
identity at a concrete |x| < 1 rational.

Probe `docs/proofs/1124_class_window_probe.py` (exact Fraction only,
report-class): re-derives the Legendre monomial tables from the recurrence
in Fraction arithmetic and asserts the 1112 LEG tables satisfy it
(convention fidelity, falsifies the O2 recurrence reading); prints the
phi_i sample-value table at u in {0, +-a/2, +-a} (float, report-only).
NO enclosure, NO box, NO gate value - phases 2+ own those.

## 2. Mechanism and reuse

  - O1: expNegInvGlue.contDiff (Mathlib) + ContDiff.comp with
    (fun x => 1 - x^2); the pointwise lemmas are simp on the def
    (`if x <= 0 then 0 else exp (-x⁻¹)`) applied at 1 - x^2 with the
    sign arithmetic of 1 - x^2.
  - O2: Polynomial over ℝ; the recurrence with Polynomial.smul/monomial
    algebra only.  No Mathlib Legendre exists (only the number-theoretic
    Legendre symbol) - hence the in-repo definition.
  - O4: fun_prop for the ContDiff; `HasCompactSupport.toSchwartzMap`
    idiom verbatim from C1HealthyDetectorArchRescue.lean:57-63.
  - O5: support of a product lies in the support of the bump factor;
    the bump is nonzero exactly on |x| < 1 (expNegInvGlue.zero_iff_nonpos).

Zero numeric content: no probe thresholds, no boxes, no gates.  Pure
object construction over already-landed Mathlib smoothness.

## 3. Risks / pre-registered deviation policy

  R1  `fun_prop` may refuse the exact O3/O4 composition (Polynomial.eval
      smoothness shape).  Fallback: cite `Polynomial.contDiff` style
      lemmas explicitly / build the ContDiff chain by hand.  PROOF-side
      only; statement shapes above are the contract.
  R2  The ℂ-coercion idiom for toSchwartzMap may need `Complex.ofRealCLM`
      composition instead of a bare coercion.  PROOF-side only.
  R3  If the O5 support needs the boundary value (classBump 1 = 0 by
      expNegInvGlue.zero_of_nonpos at 1 - 1^2 = 0) the support lemma
      carries that as a simp step - not a deviation.
  R4  Scope floor: O1-O6 + audit + probe.  If any step cannot close, the
      addendum registers the root cause; scope does not shrink below O1
      + O4 + O5 (the family is phases 2+ input and may not be dropped).

## 4. Gates and protocol

  G1  (build) focused `lake build ConnesWeilRH.Dev.C1ClassWindowObjects
      ConnesWeilRH.Dev.C1ClassWindowObjectsAudit` on the ext4 build mirror
      via the resource runner: footer "Build completed successfully (N
      jobs)" AND zero `^error:` lines AND zero `sorry`.  Acceptance =
      log content, not exit code.
  G2  (axioms) every `#print axioms` in the audit prints exactly
      [propext, Classical.choice, Quot.sound].
  G3  (fidelity) the three audit examples compile with the literal shapes
      of section 1.
  G4  (hygiene) staged-diff grep on EVERY commit: no sorry/admit/sorryAx,
      no private artifacts, no local paths.

Protocol: this preregistration commits BEFORE the first build; one
root-caused fix commit per failing build; zero threshold changes (no
thresholds exist); post-run addendum appended after the gates.

## 5. Map consequence (post-landing, to be confirmed by the addendum)

Phase 1 of the true-test bridge lands.  The certified-class chain gains
its Lean-side object substrate: 1125 (Gram enclosures) consumes O4-O6
directly; the hrep instance (gateMatrix w8 = M_true) becomes a provable
statement for the first time.  T2 named obligations UNCHANGED ((iv) + C2)
- this record shrinks their BLOCKERS, not the obligations.  RH NOT
claimed; no map change keyed.

## 6. Post-run addendum (2026-09-04, after builds 1-4 and the probe)

VERDICT: LANDED.

The preregistration was committed as `dbd3177` before the first build.  The
object and audit modules landed as `295031b`.  Three root-caused fix batches
were required: `dd4b9b2` adapts the v4.30 polynomial and compact-support APIs,
`0a3aeb1` corrects the scaled boundary inequality, and `15c399e` makes the
audit fidelity examples elaborate.  The final focused build (`1124_build4`)
has footer `Build completed successfully (2918 jobs)`, zero `^error:` lines,
and zero `sorryAx` lines.  The audit contains 14 axiom records, all exactly
`[propext, Classical.choice, Quot.sound]`; the only warning is the existing
warning in the imported convolution source, with no warning from the new
1124 modules.

The preregistered exact convention probe was added as `9cf9c64` and run under
the resource scheduler.  Its log reports
`1124 exact convention check: PASS (P0..P7 recurrence tables)` and prints the
report-only samples for `a = 2, 3, 4`, `i = 0..7`, at `0, ±a/2, ±a`.  It
installs no enclosure, threshold, gate value, or sign claim.

This record lands only the Lean-side class-window objects, their open/closed
support lemmas, smoothness packaging, and convention fidelity.  T2 obligations
((iv) and C2) remain unchanged; the true-data consumer is now unblocked at
the object layer.  RH is not claimed and no route-map conclusion changes.
