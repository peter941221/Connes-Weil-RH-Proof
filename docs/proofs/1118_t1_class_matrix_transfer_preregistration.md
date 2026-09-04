# 1118 - T1 class==>matrix transfer (the transcendental half): pre-registration

Date: 2026-09-04. Status: PRE-REGISTRATION committed BEFORE any probe/
build. Consumer (record 1117 s1(3), `ConnesWeilRH/Dev/
C1LocalConfigurationDomination.lean:861`): the per-window-class gate upper
bounds are consumed as the field

    hcert i : ICgate ((w i).convolutionSquare) <= -mu i   (i in s)

of `ICStageBContraction`, and the bridge at :867
(`orbitWindowSemiLocalGate_of_contraction`) composes with record 1089's
one-line gate-to-qw bridge into the RH reduction exactly as booked. RH NOT
claimed; no map change keyed.

## 0. What is owed, quoted verbatim

Record 1115 s2 (still-out clause):

    STILL OUT (unchanged, as registered ss2): the transcendental half -
    true Gram data inside the outward boxes, and ker R_true vs ker R_mid -
    remains the law-34 chain's own obligation (consumed by 1114's I-C
    framing).

Record 1117 s2:

    - (T1, transcendental half): gate-level bounds per window class - the
      1115 instances give matrix-level `isTopBound` on the quotient models;
      the class ==> matrix analysis (the 3 registered axioms) is the
      existing open transfer, unchanged by this record.

The algebraic half landed in 1115: per class a in {2,3,4} at fixed shape
n = 8, m = 3, k = 5,

    Q{28,38,48}.top : E0SlemmaBridge.isTopBound U G M R
(`ConnesWeilRH/Dev/C1WindowRationalIngestQ*.lean:268`), i.e. for every real
c in ker R (the exact rationalized vanishing matrix):

    dotProduct c (M *v c) <= U * dotProduct c (G *v c),   U < 0 named rat.

with the certified U values of record 1115 s3d:

    class   U (rational upper of the bundle)
    (2,8)   -1231802638776891/1180591620717411303424
    (3,8)   -3669237615059765/302231454903654240776192
    (4,8)   -193419435787029/1208925819614629174706176

This record transfers that matrix certificate into the gate-level shape
consumed as `hcert`, and names exactly which parts remain transcendental.

## 1. The transfer, in three sub-obligations

### (a) T-box: the box-robust ingestion theorem [ALGEBRAIC - landed here]

Record 1115 s3c registered TWO theorems per class and closed with "Both are
proved". Code inspection of this window (2026-09-04, full-tree grep for the
box machinery: `Dred_rad|whiten|slack|InBox` - only comment hits in
C1WindowRationalIngest.lean:27,90 and C1OrbitWindowExitComposition.lean:16):
only T-center (the exact closed-form SOS at the MID data) landed as `Q*.top`.
The box theorem -

    for all real Gt/Mt with G_lo <=entrywise Gt <=entrywise G_hi and
    M_lo <=entrywise Mt <=entrywise M_hi:
      forall c, R.mulVec c = 0 ->
        dotProduct c (Mt *v c) <= U * dotProduct c (Gt *v c)

- exists in NO module. It is exactly the statement a true-data consumer
needs, because the true data only knows it lies INSIDE the box. Mechanism:
the whitened-corner diagonal dominance of record 1115 s0/s3c - L1 (strict DD
with positive diagonal => PSD) applied to the five exact slacks committed in
`docs/proofs/1115_qchain.json`. FALSIFIER: any class whose five exact slacks
are not all strictly positive -> report that class T-box-unlandable, shrink
this record's claim to the remaining classes; booked alternatives are 1112
ss2 (i)-(iii) unchanged.

### (b) True Gram data inside the outward boxes [TRANS-ALGEBRAIC]

The committed bundles already carry the enclosures: `1112_cert.json` /
`1113_cert.json` keys G_lo/G_hi/M_lo/M_hi are EXACT FRACTION STRINGS of
center +/- width, entrywise (probe origin
`docs/proofs/1112_true_interval_whitened_probe.py:387-398`: `G_lo = frac_out
(G - wG_box)`, likewise G_hi; the widths are arb interval half-widths under
the certified remainder budget of law 34, record 1101, via the dependency-
safe true-interval mechanism of records 1112/1113). What THIS record lands
in Lean: per class, the rational matrices G_lo/G_hi/M_lo/M_hi as committed
data + entrywise containment theorems (norm_num) tying them to 1115's MID/rad
decomposition. What remains law-34's OWN obligation (named, not claimed):
that the TRUE values

    G_true[i,j] = int phi_i(t) * phi_j(t) dt,
    M_true      = arch-cross + prime-cross bilinear form (the 1101 machine),

are entrywise inside those boxes. The Lean statement is written with a named
hypothesis `Hbox` so the transfer composes WITHOUT trusting any float object;
discharging Hbox from first principles is a separate law-34 brick. FALSIFIER:
a committed endpoint violates the containment chain against 1115's MID/rad
decomposition -> report, do not patch (booked alternative: recompute that
entry at escalated arb bits).

### (c) ker R_true vs ker R_mid [TRANS - decision rule pre-registered]

The certificate holds on ker R of the rationalized matrix. A window test
g = sum_k c_k * phi_k satisfies true triple vanishing iff R_true . c = 0 with
R_true[s,j] = int phi_j(t) e^{s t} dt over s in VANISH_S (transcendental
integrals). Two pre-registered mechanisms, tried IN ORDER:

    C1. Exact annihilation: for the concrete coefficient vectors of window
        tests actually used by a Stage-B instance, verify R . c = 0 as
        rational identities (norm_num) whenever those coefficients are
        themselves committed rationals. Cheap; closes per-instance.
    C2. Drift bound: |R_true - R| entrywise inside a committed rational drift
        box + slack-margin argument moving ker R_true into the T-box domain,
        the residual absorbed by `epsilon` (the hD slot of
        ICStageBContraction). Requires law-34 enclosures on the moment
        integrals - remains that chain's obligation if invoked.

Decision rule: C1 first; C2 only where C1 is inapplicable, and then this
record lands the SKELETON with `Hker` named (as with Hbox) rather than
silently assuming it. FALSIFIER: neither mechanism applies to a class ->
declare T1 partial for that class (a+b landed), no threshold weakening.

## 2. The gate-level headline shape (what hcert consumes)

Per class a in {2,3,4}, with mu_a := -U_{class(a)} the named positive
rational of s0:

    RATIO form   (unconditional from (a)+(b), Hbox + matrix-representation):
      ICgate (w.convolutionSquare) <= U_a * dotProduct c G_true c
    ABSOLUTE form  (adds Hnorm : dotProduct c G_true c = 1, i.e. the window
                   test is L2-normalized on the class - a law-34-side fact):
      ICgate (w.convolutionSquare) <= -mu_a

The matrix-representation identity feeding these headlines - for g in
span{phi_k}, GATE(g) = dotProduct c M_true c with M_true the true arch+prime
bilinear form; bilinearity follows from the star-convolution square being
bilinear in (conj c, c) and the gate functionals linear on a common support
bound (record 1117 s0 linearity layer) - lands as a named lemma over the
abstract matrix data. `ICStageBContraction` accepts any named real mu i, so
T2's bookkeeping chooses which form to feed it. This record claims neither
that a window family exists for the D1-pinned g (that is T2, record 1117 s2)
nor RH.

## 3. Gates (assertions), registered BEFORE the build

G1 (build): `lake build` of the new module + its audit module on the Linux-
   side mirror; acceptance = LOG CONTENT: "Build completed successfully"
   footer AND zero `^error:` lines.
G2 (no sorry, no axiom drift): the build log carries no sorry warning; the
   audit module runs `#print axioms` on every public declaration - allowed
   set exactly {propext, Classical.choice, Quot.sound} (choice inherited from
   the supportRadius/globalIndexBound machinery upstream, not introduced).
G3 (fidelity): the ratio-form headline must elaborate with LHS literally
   `ICgate ((w).convolutionSquare)` where ICgate is 1117's functional at
   C1LocalConfigurationDomination.lean:73, and RHS `U_a * dotProduct c G_true
   c`; the absolute form's RHS is `-mu_a` with mu_a the s0 rational -
   checked by definitional/`Iff.rfl` verification where applicable, else by
   printed-pp diff against 1117:861.
G4 (hygiene): staged-file grep of the forbidden local-path / private-artifact
   patterns before every commit; require 0 matches.

## 4. Artifacts and run protocol

- docs/proofs/1118_t1_class_matrix_transfer_preregistration.md (this file)
- ConnesWeilRH/Dev/C1GateLevelTransfer.lean (+ Audit module)
No probe is scheduled at registration: the data already exists in committed
JSON bundles. If obligation (c) requires mechanism C2, a probe
`1118_kerdrift_probe.py` gets its own pre-registered section BEFORE running.
Run protocol: commit artifacts BEFORE the first build (house law); every
build error gets a root-caused fix batch committed before rerun; post-run
addendum lands after G1-G4 are evaluated. RH NOT claimed; no map change keyed.

## 5. Post-run addendum (2026-09-04, kernel green; record stays OPEN)

Scope landed this window: sub-obligation (a)'s GENERIC kernel -
`ConnesWeilRH/Dev/C1GateLevelTransfer.lean`, five declarations, all proved
with zero `sorry`:

    two_abs_mul_le_sq_add_sq (a b : ℝ)     AM-GM cross-term bound
    qformDoubleSum                         x ⬝ᵥ (A *ᵥ x) = full double sum
    sumUnivSplit                           univ-sum = diagonal + off-diagonal tail
    lbCollect                              per-pair bound collects to sum c_i x_i^2,
                                           c_i = d_i - rad i i - (sum j≠i)(rad i j + rad j i)/2
    qform_nonneg_whitenedBox               0 <= x ⬝ᵥ ((diagonal d + E) *ᵥ x) for EVERY
                                           entrywise-bounded E (|E i j| <= rad i j) when each
                                           slack rad i i + (sum j≠i)(rad i j + rad j i)/2 < d i

The headline theorem is box-robust exactly as registered in (a): E is
universally quantified over the entrywise box, so a true-data consumer needs
only `Hbox` to instantiate it. Verification state (build 9, Linux-side
mirror, focused build): `RESOURCE_RESULT exit=0`, footer `Build completed
successfully (1773 jobs).`, zero `^error:` lines, zero warnings, zero
`sorry` in the log. Fix-batch chain, one commit per root-caused failure:
938ffa2 (kernel draft) -> 760743b (header form: house files open with a
plain `/-` comment, not a module docstring) -> ebee19e (abs_le) -> 4d7949d
(draft had written big-sigma as U+2213 with subscript braces; all sums
rebuilt as explicit ASCII `Finset.sum` over the `uK` abbrev) -> ea0852f
(bare-`fun` sums swallow a following `=`/`<` making the summand a Prop;
`show T, by tac` not term syntax; v4.30 `pow_two` is stated `a ^ 2 = a * a`;
the hO off-diagonal collection proved in full - restricted sums become
if-zeroed full sums, `Finset.sum_comm` swaps them, row/column shares merge
via sum_add_distrib + sum_neg_distrib) -> f8b4393 (calc steps need
monotonic/flat indentation; `zero_add` not `add_zero` for `0 + s`;
sum_sub_distrib consumes a subtraction, routed via `← sub_eq_add_neg`) ->
f0f2fb4 (implicit leading arguments: call sites must be `lbCollect rad x`
/ `qformDoubleSum x`; `heb i j` itself is the needed bound, not an
abs_le.mp projection; `intro i` must also intro the membership) -> f1c50d7
(nlinarith cannot see |x i * x j| = |x i| * |x j|; feed abs_mul) -> d1d5964
(hdpos dropped: slack subsumes diagonal positivity).

Honest gate status: G1 partially met - the KERNEL builds green, but the
registered artifact list includes the Audit module, which is NOT yet
written; G2's `#print axioms` sweep has therefore not run (no sorry in the
log is satisfied, the axiom-set check is not). G3/G4: hygiene held at 0
matches on every batch; the fidelity headline of s2 is not yet instantiated.
Still owed for THIS record before any verdict: (i) the Audit module over
the five declarations; (ii) per-class instantiation feeding the five exact
slacks of `docs/proofs/1115_qchain.json` as `hslack` (falsifier as booked
in (a)); (iii) the s2 headline composition (ratio/absolute forms).
Obligations (b) and (c) unchanged and unstarted. RH NOT claimed; no map
change keyed.

## 6. Post-run addendum (2026-09-04, owed list (i)-(iii) DISCHARGED)

Scope landed this window, closing the section-5 owed list:

(i) AUDIT: `ConnesWeilRH/Dev/C1GateLevelTransferAudit.lean` - the focused
`#print axioms` sweep over the five kernel declarations plus all 17 new
record headlines (22 prints total).

(ii) PER-CLASS INSTANTIATION (falsifier check): generator
`docs/proofs/1118_generate_classes.py` (committed; asserts at generation
time, over exact `Fraction`s: `Lam*Dred*Lam^T = diag(Ldl_d)`, the
kernel-form slack identity, all-slacks-positive, radp >= 0, and U equality
against the committed `Q*.lean` literals) emits
`ConnesWeilRH/Dev/C1GateLevelTransferClasses.lean` (220 KB). Per class
a in {28, 38, 48}: committed data `radp_a` / `dd_a = Ldl_d` (the five LDL
pivots; the whitened center `Lam Dred Lam^T` is EXACTLY diagonal), then
`hradpos_a` (norm_num), `hslack_a` (norm_num over ~10^4-digit rational
sums - the five committed slacks ARE these differences, all strictly
positive: min slacks +1.8512872832557472e-08 / +3.468136203356025e-10 /
+1.3305376776557043e-11; FALSIFIER FIRED NOWHERE), and the box-robust
instance `whitenedBox_a : for EVERY E with |E i j| <= radp_a i j,
0 <= x . ((diagonal dd_a + E) . x)`.

(iii) S2 HEADLINE COMPOSITION: general `ratio_headline` /
`absolute_headline` with the record-1117 `ICgate` literally on the LHS
(the 1089 gate body via `orbitWindowSemiLocalGate_iff : Iff.rfl`), plus
per-class Tier-1 corollaries `ratio_a` / `absolute_a` consuming the
committed `Q*.top` certificates (no hypothesis beyond the representation
slot `hrep` and, for the absolute form, the L2-normalization slot
`hnorm`) and named margins `mu_a := -Q*.U` with `mu_a_pos` proved.

Build ledger: tactic-shape probe `_1118probe.lean` (2 runs; pins the hKV
idiom - plain `simp` evaluates a univ-sum with a VARIABLE binder over a
literal matrix - the `sdiff_sum_eq` route via the kernel `sumUnivSplit`,
the full hslack chain, the mu-positivity pattern, and a Tier-1 headline
against the real Q28 data). Official build 1: classes module GREEN FIRST
TRY (37 s); audit failed on a missing `open Matrix` (vec notation without
its open elaborates as a raw subscript token - "elaboration function for
`Mathlib.Tactic.subscriptTerm` has not been implemented" at each notation
site - with a knock-on PHANTOM `isDefEq` heartbeat timeout at the first
example; gotcha banked in AGENTS 7b). Fix commit, build 2 FULL GREEN:
`Build completed successfully (3650 jobs).`, `RESOURCE_RESULT exit=0`,
zero `^error:` lines, zero warnings, zero `sorry`.

GATES: G1 PASS (footer + exit 0). G2 PASS - 22/22 `#print axioms` lists
exactly `[propext, Classical.choice, Quot.sound]` (regex-extracted across
log line wraps; NON-STANDARD: none), 0 sorry. G3 PASS - the headline LHS
elaborates as `ICgate w.convolutionSquare` with the 1117:73 functional,
RHS `U * c . (G * . c)` resp. `-mu_a`; the audit re-prints both shapes as
`example`s over `G_true`/`M_true` binder names. G4 PASS - staged-file
hygiene greps 0 matches on every commit.

Provenance erratum: the (3,8) `U` denominator printed in section 0 above
is a transcription typo; the committed `C1WindowRationalIngestQ38.lean`
literal `-3669237615059765/302231454903657293676544` (used here) matches
`1115_qchain.json`.

Honest status after closure: the REGISTERED owed list (i)-(iii) is
discharged, so this record's verdict fires as booked - all three classes
T-box-landable at the whitened level. Sub-obligations (b) and (c) of
section 1 remain UNSTARTED as registered: nothing yet certifies that the
TRUE Gram data lies inside the outward boxes ((b) `Hbox`; the §1b
data+containment landing is part of that open obligation), and the
whitened-to-(Gt, Mt) pull-through plus the matrix representation remain
named-hypothesis slots (`ratio_headline`'s `hcert`/`hrep`). T2 (a Stage-B
instance for the D1-pinned g) unchanged and open. RH NOT claimed; no map
change keyed.
