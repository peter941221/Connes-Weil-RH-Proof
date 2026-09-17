# MEMORY.MD

Project narrative ledger — CURRENT FRONTIER + wave digest + archive
pointers. Compressed 2026-09-17: per-record narratives live in the committed
records `docs/proofs/<record>_*.md` (each file's `#` title line IS the
verdict); this file keeps only what steers future work. Full pre-compression
text: `_precompress_backup_2026-09-17/` (this file, AGENTS.md, all auto-memory
cards) and `_precompress_backup_2026-08-27/`. Also mirrored (hooks) in the
auto-memory index.

2026-09-17 C1G8R3WideHardyBoundaryConsumer.lean + Audit : added and verified
the B4 wide-radial/Hardy-wide-radial support-certificate consumer; it reduces
the complete boundary energy to the two actual support identities plus the
already-open survivor IN leg, without asserting either analytic estimate.

2026-09-17 C1G8R3GapFreeEndpointMoment.lean + Audit : formally verified the
finite-spectral gap-free endpoint-moment inequality used by S3; it converts
the zeroth moment into a first-moment term plus explicit endpoint mass, with
no Friedrichs-gap premise. This is an interface brick only: the actual Sonin
spectral measure, strip-density bound, and endpoint-mass estimate remain open.

2026-09-17 C1G8R3ApproximateHardySupportConsumer.lean + Audit : formally
verified the B4 truncation consumer `A = H E_w H A + (A - H E_w H A)`.
The wide-supported Hardy component uses the existing composite gap theorem;
the only new producer input is square-summability of the explicit Hardy tail.
This replaces the over-strong exact-support premise without closing that tail.

2026-09-17 C1G8R3ApproximateHardyBoundaryConsumer.lean + Audit : formally
assembled the approximate Hardy-tail gap leg with the radial leg for the full
G8 visible boundary energy.  B4 is now exposed at the actual ledger boundary
as per-output Hardy-tail square summability; no analytic tail estimate is
claimed.

2026-09-18 C1G8R3ApproximateHardySupportConsumer.lean + BoundaryConsumer :
normalized the B4 tail consumer to the exact reflected-radial operator
`H (I - E_w) H A` and rewired the boundary consumer to that interface;
formal acceptance is record 1598, with the reflected radial-complement
square-sum still open.

2026-09-18 B4 route audit : established from committed definitions that
`I - E_w` is an unbounded lower-half-line complement, not a finite window;
the Hardy--prolate Gram identity also forbids splitting its Hardy and prolate
pieces into standalone HS estimates.  Record 1599 marks the resulting
analytic stop rule: B4 needs half-line decay/cancellation, while S3 needs
source-compressed cancellation.

2026-09-17 GapFreeEndpointMoment : extended the finite endpoint-moment bound
to a countable `tsum` under explicit summability of the zeroth moment, first
defect, and endpoint-mass sequence. The Lean audit is green; this is the
limit-exchange interface for S3, not an actual Sonin spectral-measure estimate.

2026-09-17 GapFreeEndpointMoment : formally reduced endpoint-mass summability
to convergence of the endpoint diagonal values to zero; the threshold
indicator is eventually zero. The actual Sonin spectral-tail convergence
remains the open S3 producer.

2026-09-18 C1G8R3ApproximateHardySupportConsumer : formally normalized the
B4 Hardy tail as `A - H E_w H A = H (I - E_w) H A` using Hardy involutivity.
The remaining analytic task is now a reflected radial-complement estimate for
the actual Schur columns; no square-summability claim is made here.

2026-09-18 C1G8R3ApproximateHardySupportConsumer : formally normalized the
B4 Hardy tail as `A - H E_w H A = H (I - E_w) H A` using Hardy involutivity.
The remaining analytic task is now a reflected radial-complement estimate for
the actual Schur columns; no square-summability claim is made here.

## CURRENT FRONTIER (2026-09-17, record 1590)

Tower: off-line zero ⇒ qw(g)<0 [formal] ⇒ 0≤qw(g) [THE open gate = classical
Weil criterion, machine-checked iff SourceRH] ⇒ RH. Live face: MAINLINE G8
(map 012), gate = one square-sum (★)  P C P HS. As of 1589 the 1586 residual
is re-typed and machine-checked through the (★)-level conversion, and its
angle-gap branch is retired. EXACT, no gap:
`residual² = StripDensity(Λ) + Σ_i dist(h_i, carrier)²`,
`h_i = E T_{−Λ}e_i = T_{−Λ}(e_i·1_{[L+Λ,∞)})` — the radial half IS the strip
mass. The remaining half is the ZEROTH spectral moment of `K = EQE`
(`ν'_{h_i}([0,1))`); 1586's strip bound is its FIRST moment
(`Σ‖(1−Q)h_i‖² ≤ StripDensity`). Converting moments costs `1/δ` = exactly the
angle gap, and that gap IS the already-ruled Friedrichs shape
(`‖EQE − R_S‖ < 1` = record 1435's `‖p_b q_1 p_b − r_b‖ < 1`, ruled out by map
016 §3.1 as "not an available premise"; same shape machine-checked to fail in
the sibling reduction, record 590). Gap-free replacement:
`residual² ≤ (1+1/ε)·StripDensity(Λ) + EndpointMass(ε)`,
`EndpointMass(ε) = Σ_i ν'_{h_i}([1−ε,1))` — the map-016 weight object. Bones:
**StripDensity(Λ) = Tr(P M_{1_[L,L+Λ)}P)** (local trace / local (★); no
committed kernel-diagonal or point-evaluation statement exists for the Sonin
carrier), **EndpointMass(ε)** (near-endpoint mass), **T1 transport** (identify
(E,Q) with the doubled-shift (p_b,q) to reuse R3 endpoint machinery). The
**hradial** bone is CLOSED AT THE INTERFACE LEVEL (1588), and as of 1589 the
residual chain 1586→1587 is ALGEBRAICALLY COMPLETE and machine-checked: the
carrier IS `range E ⊓ range Q` = fixed space of `EQE` (no commutativity) and IS
H-invariant; the 1587 §2.1 split is exact in vector and squared form; the
moment conversion is machine-checked at the (★) TRACE level
(`Σ_i ‖(1−P)e_i‖² ≤ δ⁻¹ Σ_i (e_i,(1−K)e_i)`, summed, no orthonormality
needed), the gap being a HYPOTHESIS. **StripDensity(Λ)** is RE-TYPED (1589 §6)
as a LOCAL TRACE `‖M_Δ P‖²_HS = ∫_Δ K_P(u,u)du`: finiteness is a NEW
obligation with a three-way fork (zero / Poisson-finite / +∞), and the H²
diagonal test `Σ_{n≤N}|ψ_n(x)|² = (N+1)/|x+i|² → ∞` shows the infinite branch
is not idle — no committed kernel-diagonal statement exists. **EndpointMass(ε)**
and **T1 transport** unchanged. NEW NEGATIVE FINDING (1589 §5, law F33): the
CARRIER'S NONEMPTINESS IS A HYPOTHESIS, never a theorem —
`Dev/SoninWindowWitness.lean:44` files `archimedeanSoninCarrier_nontrivial` as
an unproved Prop ("the load-bearing analytic existence"), and the committed
source layer consumes `(hsource : ∃ y : sourceSoninCarrier λ, y ≠ 0)`
(`CCM24FiniteSFixedFullBoundaryInjectivityGuard.lean:103`), so 1586–1589 are a
CONDITIONAL reduction: identities are true and useless at `{0}`. The carrier is
a Toeplitz/Riemann–Hilbert kernel `{g ∈ H²(ℂ₋) : φ(−·)g ∈ H²(₊)}` whose
nonemptiness is the project's standing open existence statement (naive
Wiener–Hopf fails: a unimodular factor is not in L²). Laws F31, F32, **F33**
filed (F32: sweep the Mathlib layer by shape; F33: check the EXISTENCE of the
base object). Gates (★)/B4/ρ5/R4/(OB)/W1 OPEN. RH NOT claimed. Stop word =
gate certificate.

BASE-OBJECT ATTACK (1590, paper + numerics cross-check, zero Lean bricks): the
base of the carrier face is NOT refuted and NOT proved; both cheap routes are
closed with computable reasons. CORRECTED (erratum on 1331 §2.1): with
`φ = A/B`, `A = Γ_ℝ(1/2−2πiz)`, `B = Γ_ℝ(1/2+2πiz)`, φ has a ZERO at
`+i/(4π) ∈ ℂ₊` and a POLE at `−i/(4π) ∈ ℂ` (hand + mpmath); the statement that
carries the weight is **`1/φ` analytic in `ℂ₋`** (B's poles sit in `ℂ`, `1/A` is
ENTIRE because Γ_ℝ has no zeros) — that is the correct reason for 1331 §2.2's
"w is entire", whose conclusion stands and whose stated reason is replaced.
BLOCKED TRIVIALITY: the two-sided rigidity `H²(ℂ₊) ∩ H²(ℂ₋) = {0}` would refute
nonemptiness, but it needs `|1/φ|` bounded on the horizontal lines of `ℂ₋`, and
the weight is `(1+|x|)^{2πη}` — numerically confirmed against the committed
factor (ratio → 1 at η = 0.0796 and 0.1592); analyticity plus L² boundary values
does NOT imply H², and entire functions CAN lie in `H²(ℂ)` (witness
`((sin z)/z)²·e^{2Iz}`: boundary `sin²x/x² ∈ L²`, line mass `→ 0`), so no
Liouville-type shortcut replaces the rigidity. RE-TYPED: the base obligation is
a nonzero ENTIRE `w` with `w ∈ H²(ℂ₊)` and `φw ∈ H²(₋)` — a de Branges space
element, classically the Sonin/Weil model space
`W = {w ∈ H²(ℂ₊) : φw ∈ H²(ℂ₋)}`, whose classical nonzero witnesses are products
of two Weil Λ factors; the productive route is T4 of `docs/proofs/1003`
(prolate / Connes–Moscovici negative eigenfunction), every step of which is an
unformalized theorem. **Law F34**: a rigidity identity does not survive a
multiplier — compute the horizontal-line growth of `1/φ` before invoking it.
Guard fired mid-session: a full triviality argument was drafted and then
SELF-REFUTED at the weighted-L² step. Bones unchanged: StripDensity(Λ) (still a
local trace with open finiteness), EndpointMass(ε), T1 OPEN;
(★)/B4/ρ5/R4/(OB)/W1 OPEN. RH NOT claimed.

## WAVE V (current, 2026-09-17)

2026-09-17 record 1590, WAVE V CONT-14 (paper + numerics, ZERO Lean bricks, zero new
declarations; commit `6c54b1b`), **THE CARRIER BASE IS ATTACKED HEAD-ON: NOT REFUTED,
NOT PROVED, BOTH CHEAP ROUTES CLOSED, OBLIGATION RE-TYPED.** (1) ERRATUM to 1331 §2.1:
its claim that φ is "analytic and nonvanishing in the interior of each half-plane"
contradicts its own pole placement in the same section; computed by hand and with
mpmath, φ = A/B (A = Γ_ℝ(1/2−2πiz), B = Γ_ℝ(1/2+2πiz)) has a ZERO at `+i/(4π) ∈ ₊`
and a POLE at `−i/(4π) ∈ ₋` (zeros at `+i(4k+1)/(4π)`, poles at `−i(4k+1)/(4π)`), so
φ is analytic in `ℂ₊` WITH zeros there and carries its poles in `ℂ₋`; the useful
statement is **`1/φ = B/A` analytic in `₋`** (B's poles are in `ℂ`; `1/A` is ENTIRE
because Γ_ℝ has no zeros). 1331 §2.2's conclusion "w is entire" STANDS; its stated
reason is replaced, and that conclusion is the first structural fact the whole face
rests on (EVERY carrier element is an entire function). (2) BLOCKED TRIVIALITY: the
cheapest refutation of `W ≠ {0}` is the two-sided rigidity `H²(ℂ₊) ∩ H²(ℂ) = {0}`
(available in the committed model: `P⁺ + P⁻ = id`, `PP⁻ = 0`), applied to
`W := (1/φ)(φw)`. It dies at the last step and the reason is quantitative: on the
horizontal lines of `₋`, `|1/φ(x−iη)| ~ (1+|x|)^{2πη}` — POLYNOMIAL GROWTH, matched
numerically against the committed factor to ratio 1 (rows at η = 0.0796, 0.1592 and
x = 5, 500) — so boundary values stay in `L²` while the shifted-line `L²` masses can
diverge; analyticity + `L²` boundary values does NOT imply `H²` (witness `exp(−z²)`),
and a second check killed the Liouville escape: ENTIRE functions CAN lie in `H²(ℂ₊)`
(witness `((sin z)/z)²·e^{2Iz}`: boundary `sin²x/x² ∈ L²`, line mass
`~ π/(2y³)(sinh²y·e^{−2y})² → 0`). (3) RE-TYPED: the base obligation is a nonzero
ENTIRE `w` with `w ∈ H²(₊)`, `φw ∈ H²(ℂ₋)` — a de Branges space element, classically
the Sonin/Weil model space (1331 §2.5), classical nonzero witnesses = products of two
Weil Λ factors; the productive route is T4 of `docs/proofs/1003` (prolate /
Connes–Moscovici negative eigenfunction), every intermediate step an unformalized
theorem. A full triviality argument was drafted and then SELF-REFUTED at the
weighted-`L²` step (this is why the counterexample family is in the record).
**Law F34**: a rigidity identity does not survive a multiplier — compute the
horizontal-line growth of `1/φ` before invoking it. Bones unchanged:
StripDensity(Λ) / EndpointMass(ε) / T1 OPEN; (★)/B4/ρ5/R4/(OB)/W1 OPEN. RH NOT claimed.

2026-09-17 record 1589, WAVE V CONT-13 (Landed Lean + structural verdict + sweep; commit `ec2a42e`),
**THE CARRIER IS PINNED AND THE CHAIN'S BASE TURNS OUT TO BE A HYPOTHESIS.**
Ten declarations in `Dev/C1G8R3SoninCarrierStructureBricks.lean` (+ paired
Audit) in ONE acceptance build: footer ✓, zero `error:`, zero `sorryAx`, ten
`#print axioms` all = {propext, Classical.choice, Quot.sound}, zero warnings in
the new modules (log `build-logs/1589_carrier_structure.log`; two red rounds,
both mechanical — a transposed `Eq.trans` direction and a `rw` that could not
unfold an infimum-`def`, fixed by `simpa only` with the `rfl`-level
`ClosedSubmodule.toSubmodule_inf` plus a defeq `fun v => Submodule.mem_inf`
helper; the glyph-drop hazard struck again, caught by the pre-build audit).
Content: (a) `starProjection_comp_apply_eq_self_iff` — the fixed space of the
sandwich `E∘Q∘E` is exactly `range E ⊓ range Q`, for ARBITRARY orthogonal
projections, no commutativity (1586 §1 in general form; its proof consumes the
1588 equality-case brick, so the two waves interlock); (b) the same at the
project pair and in `⊓`-projection membership form; (c) `sub_sourceSonin_
Projection_eq_add_defect` + squared twin — 1587 §2.1 EXACT,
`g − Pg = (g − Eg) + (Eg − P(Eg))`, only input the committed `P∘E = P`;
(d) `sum_norm_sq_sub_starProjection_le_of_quadraticFormGap` — the (★)/TRACE
level conversion, SUMMED over any finite family with no orthonormality needed
(1587 §4's demanded level change); (e) the two carrier-vacuity halves (1581 §1)
plus the sandwiched `J†XEJ = J†XJ` consequence; (f)
`ccm24ArchimedeanHardyTitchmarsh_mem_sonin_iff` — `H` maps the carrier ONTO
itself (preimage-of-radial commutant + committed involutivity). SWEEP
(F8/F31/F32 by shape): Mathlib has no fixed-space-of-sandwich lemma and no
section-form projection product; the tree had neither the fixed-space nor the
H-invariance statement; `Dev/ELambdaFamilyProjectorProbe.lean` still has no
olean ⇒ the 1588 duplicate cleanup is deferred AGAIN, now with a cost figure
rather than an assertion. **NEGATIVE FINDING (§5)**: the carrier's nonemptiness
is nowhere a theorem — `Dev/SoninWindowWitness.lean:44` files
`archimedeanSoninCarrier_nontrivial` as an unproved Prop ("the load-bearing
analytic existence: every later step reduces to it"), and the committed source
layer consumes `(hsource : ∃ y : sourceSoninCarrier λ, y ≠ 0)` as a HYPOTHESIS
(`CCM24FiniteSFixedFullBoundaryInjectivityGuard.lean:103`; same pattern at
`…OldCarrierSpectralGapObstruction.lean:59,120`), so 1586–1589 are a
CONDITIONAL reduction. §6: StripDensity RE-TYPED as a local trace
`‖M_Δ P‖²_HS = ∫_Δ K_P(u,u)du` with a three-way fork and the H² diagonal test
`Σ_{n≤N}|ψ_n(x)|² = (N+1)/|x+i|² → ∞`; no "finite density" declaration was
written, because that would be a guess dressed as a theorem. §7: the one-line
structural answer to "why not RH yet". **Law F33**: a reduction chain must be
checked for the EXISTENCE of its base object, not only for the correctness of
its steps. Bones unchanged in kind: StripDensity(Λ) (re-typed),
EndpointMass(ε), T1 OPEN; (★)/B4/ρ5/R4/(OB)/W1 OPEN. RH NOT claimed.

2026-09-17 record 1588, WAVE V CONT-12 (Landed Lean + sweep; commit `deae24c`, table-alignment fixup `90bfbcd`),
**THE GATE-RESIDUAL BRICKS ARE MACHINE-CHECKED AT THE INTERFACE LEVEL, AND
THREE "OWED" ITEMS TURN OUT TO BE ALREADY-OWNED.** Nine declarations in
`Dev/C1G8R3GateResidualMomentBricks.lean` (+ paired Audit) in ONE acceptance
build: footer ✓, zero `error:`, nine `#print axioms` all = {propext,
Classical.choice, Quot.sound}, zero `sorryAx`, zero warnings in the new
modules (log `build-logs/1588_bricks.log`). Content: (a) projection ordering
`P ≤ E` (`inf_le_left`) and `P ≤ Q` (`inf_le_right`); (b) `E P = P` and
`P E = P` (the latter through Mathlib's `Submodule.starProjection_comp_
starProjection_of_le`); (c) `radialSupportProjection_fixes_of_support_subset`
— the POINTWISE transport⇒wide-support interface: a.e. support below
`log λ − s` fixes the wider projection (its `hlog` instance is the committed
`realLog_wideRadialScale`, `C1G8R3CompositeBoundaryEnergy.lean:108-112`);
(d) `norm_sq_sub_starProjection_eq_add` — the EXACT nested split
`‖x−P₁x‖² = ‖x−P₂x‖² + ‖P₂x−P₁x‖²` for `P₁ ≤ P₂` (1587 §2.1) plus its
concrete instance at (P, E); (e) `starProjection_eq_self_of_re_inner_eq_
normSq` (1586 §1's equality case); (f) `norm_sq_sub_starProjection_le_of_
quadraticFormGap` — the moment conversion `‖x−P_W x‖² ≤ gap⁻¹·(x,(1−K)x)`
with the gap a HYPOTHESIS on the complement `Wᗮ` only. LEVEL POINT: the
committed adapter is whole-space/operator-norm (unsummable over a basis); this
one is per-vector and complement-restricted, so summing a basis gives
`Σ‖(1−P)e‖² ≤ gap⁻¹·Tr(1−K)` — the (★)-level shape. SWEEP (F8/F31
extended): (i) hradial was HALF-COMMITTED —
`wideRadial_absorption_of_sourceRadialSupport` (:175) already turns
narrow-scale absorption into wide-scale absorption; only the pointwise-support
half was missing; (ii) `starProjection_comp_of_le` / `radialProjector_comp_
of_le` (`Dev/ELambdaFamilyProjectorProbe.lean:48-61, :66-74`) DUPLICATE
Mathlib's `Submodule.starProjection_comp_starProjection_of_le`
(`Projection/Basic.lean:489`) — not refactored (missing olean under the
composite chain), filed as cleanup; (iii) the nested split is genuinely ABSENT
from Mathlib (full sweep of Projection/Basic + Projection/Submodule), and the
tree had re-derived its instances ad hoc by `nlinarith`
(`C1G8R3PowerProjectionBridge.lean:302-303, :731`). Law F32 filed: the
pre-spend sweep includes the MATHLIB layer and searches by SHAPE. Bones
unchanged: StripDensity(Λ), EndpointMass(ε), T1 transport OPEN;
(★)/B4/ρ5/R4/(OB)/W1 OPEN. RH NOT claimed.

2026-09-17 record 1587, WAVE V CONT-11 (paper-only, zero Lean, zero digits),
**ERRATUM + RE-TYPING: the angle gap is a retired shape, and 1586 priced the
wrong moment.** (1) ERRATUM to 1586 §4, two independent defects: (a) the
committed adapter `normSq_le_of_spectralGap_of_norm_le` needs a WHOLE-SPACE
lower bound `∀x, gap‖x‖² ≤ ‖Bx‖²`; at `B = (1−K)^{1/2}T_{−Λ}` it fails on
carrier directions vanishing on the strip (those give `T_{−Λ}x ∈ range E ∩
range Q = carrier ⟹ Bx = 0`), so 1586 §7 Brick 2 is WITHDRAWN; the same SHAPE
is machine-checked to fail in the sibling reduction — record 590 /
`…SpectralGapObstruction.lean:118-126` proves `¬∃ gap, Nonempty
(SuffixRawOldCarrierUniformSpectralGapData λ gap)` for every nonzero source
column (approximate kernel `y_p = newSuffixFrame λ [] x`, `‖W_p y_p‖ → 0`).
(b) (GAP) itself: `spec(EQE) ⊆ {1} ∪ [0,1−δ] ⟺ ‖K − R_S‖ < 1  Friedrichs
angle of (range E, range Q) positive ⟺ range E + range Q closed` — in the
project's own notation this is record 1435's "exact remaining obligation"
`‖p_b q_1 p_b − r_b‖ < 1`, and map 016 §3.1 (2026-09-14, three days BEFORE
1586) rules: "It is not an available premise. Near-extremal prolate
directions make a uniform angle gap an unsuitable default target"; map 015 §6
card: "Do not assume a Friedrichs-angle gap…endpoint filter trace-summable";
record 1435: "forces the next proof to use an angle-free weighted spectral
estimate". (2) EXACT SPLIT (new): `(1−P)g = (1−E)g + A(Eg)` orthogonal for
`g ∈ range Q`, `A(E) = A`, `A(1−E) = 0` ⇒ `residual² = StripDensity(Λ) +
Σ_i dist(h_i, carrier)²`. (3) MOMENT ACCOUNTING (new): the strip bound is the
FIRST moment `∫(1−λ)dν'_{h_i} = ‖(1−Q)h_i‖²` (1586 §3.2 read spectrally);
the open term is the ZEROTH `ν'_{h_i}([0,1))`; conversion costs `1/δ` = the
retired gap. Gap-free: `residual² ≤ (1+1/ε)StripDensity(Λ) + EndpointMass(ε)`
with `EndpointMass(ε) = Σ_i ν'_{h_i}([1−ε,1))`, i.e. the map-016 weight shape
`∫w d tr(C E_b(dt)C†)` with the derived vanishing weight `(1−λ)`. (4) Law
**F31 filed**: the pre-spend sweep applies to PREMISE SHAPES, not only to
named cards (1586 swept for names and re-derived a shape retired 3 days
earlier). StripDensity status: no committed kernel-diagonal / point-evaluation
statement exists for the Sonin carrier (sufficient condition named: locally
integrable reproducing-kernel diagonal = the local (★)). Nothing
machine-checked. RH NOT claimed. Commit da31544.

2026-09-17 record 1586, WAVE V CONT-10 (paper-only, zero Lean, zero digits),
**RESIDUAL RE-REDUCED: the angle remainder is gone as an independent object —
everything is strip mass plus one gap constant.** (1) `range(R_S) = ker(1−EQE)`
(exact, classical; proof by the quadratic-form equality) ⇒ `K^n → R_S`
strongly ⇒ `dist(g,R_S)² = lim_n⟨g,(1−K^n)g⟩`. (2) The residual column is
exactly `(E−R_S)T_{−Λ}e_i = A h_i` with `h_i = E T_{−Λ}e_i =
T_{−Λ}(e_i·1_{[L+Λ,∞)}) ∈ range E` (uses 1585's left-transport Q-invariance);
for `h ∈ range E`: `dist(h,R_S)² = ‖(1−Q)h‖² + ‖(Q−R_S)h‖²`. (3) **TWO EXACT
BOUNDS, both = strip mass**: (a) `‖(1−E)T_{−Λ}e_i‖² = ‖e_i·1_{[L,L+Λ)}‖²`
EXACT; (b) NEW — `‖(1−Q)h_i‖ = ‖(1−E_{>L−Λ})H(e_i·1_{[L,L+Λ)})‖ ≤
‖e_i·1_{[L,L+Λ)}‖` (because `He_i ∈ E` is annihilated and `H` is unitary on
the strip part) ⇒ `⟨T_{−Λ}e_i,(1−K)T_{−Λ}e_i⟩ ≤ 2‖e_i·1_strip‖²` ⇒ first-order
≤ `2·StripDensity(Λ)`. (4) Single remaining interface: **(GAP)** —
`spec(EQE) ⊆ {1} ∪ [0,1−δ]` (no approximate carrier) ⇒
`residual ≤ (2/δ)‖D‖²‖N‖²·StripDensity(Λ)`; the committed adapter
`normSq_le_of_spectralGap_of_norm_le` (old-carrier spectral-gap file :47-92)
does the conversion verbatim; the tree explicitly asserts NO source-specific
gap, and its sibling obstruction `noExistsUniformOldCarrierDomination_of_
approximateKernel` (:220-238) shows the warning shape if (GAP) fails.
`StripDensity(Λ) = Tr(P M_{1_[L,L+Λ)}P)` is the ONLY carrier-geometry input;
Mellin-row density machinery (`GlobalLogMellinCompleteness.lean:151-252`) is
the natural tool. Two Lean bricks SPECIFIED (1586 §7: transport⇒hwide; the
(GAP) adapter instantiation) — neither written/compiled. Nothing
machine-checked. RH NOT claimed. Commit 886e767.

2026-09-17 record 1585, WAVE V CONT-9 (paper-only, zero Lean, zero digits, no
sentinel), **ERRATUM + STRIP-ESCAPE IDENTITY — the gate's residual re-priced
onto a finite strip.** (1) ERRATUM to 1584 §4/§5: "multiplication by the
compact-window indicator IS Hilbert–Schmidt with ‖M‖²_HS = Λ" is VOID — on
L²(ℝ), multiplication by a positive-finite-measure indicator is an orthogonal
projection of INFINITE RANK, hence not compact, hence not HS; composing with
the source inclusion `J` does not repair it (`‖M_χ∘J‖²_HS` = the carrier's
diagonal density integrated over the strip, finite only if the carrier is
thin). Same error class as the 1583 §3 |W|-bound that 1584 itself retracted.
Consequences: 1584 §4's constant-Λ bound and §5's 2Λ angle-compact bound are
WITHDRAWN (angle-compact part NOT closed); §5's tail bound
`Tr_carrier(E_{>L+2Λ})` is the compression of an infinite-rank projection ⇒
vacuous. (2) WHAT ACTUALLY CLOSES hradial (committed, quoted): the
`ContinuousKernelHilbertSchmidt` mechanism on COMPACT windows — continuous
kernel on a product of compact intervals ⇒ L² kernel ⇒ HS
(`C1G8R3CompositeBoundaryEnergy.lean:841-898`), with bounded pre/post
composition preserving column summability
(`PositiveTrace.summable_normSq_precomp/postcomp`) — plus the committed
`compositeRadialLeg_sourceBasis_normSq_summable` (:911-922) which consumes
`hwide`, which the transport ledger DELIVERS at λ′ = λe^{−Λ}. hradial status
UNCHANGED (CLOSED-PENDING-ONE-BRICK), mechanism corrected; no density input
needed there. (3) NEW EXACT STRUCTURE: left transports preserve the
Fourier-support class — `H(T_{−c}g) = T_c(Hg) ∈ E` for `Hg ∈ E`, `c ≥ 0`, so
`g ∈ range Q ⇒ T_{−c}g ∈ range Q`; escape from the carrier is purely RADIAL.
Hence `(1−P)T_{−Λ}f = (1−E)T_{−Λ}f + A E T_{−Λ}f` exactly (orthogonal terms),
with `(1−E)T_{−Λ}f = T_{−Λ}(f·1_{[L,L+Λ)})` — an exact STRIP identity of width
Λ, replacing 1584's infinite tail. (4) Re-priced residual = CARRIER THINNESS
FUNCTIONAL `Thin(Λ) = ∫_{[L,L+Λ)}K_P(u,u)du + Σ_i‖A E T_{−Λ}e_i‖²`; decisive
fork (F30): finite density ⇒ priced ⇒ hgap closes ⇒ (★) for the physical
factors; infinite ⇒ the compression route is structurally re-typed. Checked:
NO committed dimension/rank/density/localisation statement about
`ccm24ArchimedeanSoninClosedSubspace` exists — the thinness input is genuinely
new mathematics. Bonus committed anchor: `K_S = (E−R_S)∘Q∘(E−R_S)` (:168-183).
Nothing machine-checked. RH NOT claimed. Commit 89dc765.

2026-09-17 record 1584, WAVE V CONT-8 (paper-only, zero Lean, zero digits, no
sentinel — all constants structural), **CARRIER-DEFECT BRICK LANDED — the
gate is reduced to ONE named functional**. (1) WINDOW PINNED: W =
[log λ, ∞) is a committed HALF-LINE (`ccm24LogRadialLowerRegion = Iio
(log λ)`, subspace = restriction kernel) ⇒ 1583 §3 ERRATUM: the
`|W|·‖K‖₂²` mechanism is void (W infinite); correct model pricing =
`∫_{2L}^∞ (w−2L)|K(w)|²dw` — finite via compact band + compact-η parts tail
+ IN-ZONE positive-ray saddle (η*=e^w ≥ 2 ⟺ w ≥ log 2; the 1571 β₊=5/2 row
is F30-valid) — **verdict FINITE stands, mechanism corrected**. Model-object
note: the 1582 K is the frequency-cut single-H object; the true defect is
the two-H u-cut composite — model is indicative, the exact pricing is the
decomposition. (2) EXACT DECOMPOSITION (committed names): `E(1−Q)E =
(E−R_S) − K_S` ⇒ hgap = angle-excursion term − prolate term. (3) Prolate
term CLOSED (committed K_S all-scale HS + ideal transfer). (4) **hradial
CLOSED-PENDING-ONE-BRICK**: strip-confinement + `T_{−Λ}∘M_{1_{[L,L+Λ)}}`
factorization, `‖(1−E)MJN‖² ≤ ‖D‖²Λ‖N‖²` (compact-window multiplication is
HS with HS² = Λ) — quantitatively REPLACES the wide-window premise hwide at
scale λe^{−Λ}; owes one Lean brick (transport ⇒ propagation budget ⇒
hwide). (5) Angle term: compact part closed (same trick, 2Λ); residual =
ONE named object — **the carrier tail-trace functional**
`Tr_carrier(M†E_{>L+Λ}M)`, the Halmos two-projection form of Sonin
thinness; attack vehicle = the all-scale prolate machinery; both outcomes
decisive. Gate content: two defect columns → one thinness theorem. Nothing
machine-checked. RH NOT claimed. Commit e0f53f9.

2026-09-17 record 1583, WAVE V CONT-7 (paper-only, zero Lean, zero new
digits), **P2 EXECUTED — the gate's restriction functional is pinned on
committed definitions, and the model verdict FLIPS to finite**. The
functional of 1581 §6 is NOT a new object: the committed reduction chain
(1531 two-column split → 1532 prolate discharge → 1533/1534 Hardy split →
1536 normal form) identifies it EXACTLY with the pair of committed premises
hradial (`Sum ‖D(1−E)MJN e_i‖²`) + hgap (`Sum ‖DE(1−Q)EMJN e_i‖²` = the B4
chain `DEH(I−E)HEMJ` of 1573, verbatim), with hfactor already discharged.
STRUCTURAL FINDING: the committed factorization H = F∘reflection∘multiplier∘F⁻¹
(CCM24HardyTitchmarsh.lean:331-336) forces `H T_c = T_{−c} H` — H does NOT
commute with log translations, it REFLECTS them (the :976
translation-conjugation lemma carries an explicit commuting hypothesis,
satisfied by rootConvolution, not by H) ⇒ H's kernel is ANTI-difference,
function of `u+u′` = multiplicative inversion r↦1/r. The 1571 model kernel's
variable is therefore u+u′, not u−u′; the 1582 envelope applies unchanged.
MODEL PRICING: `‖EHΠHE‖²_HS ≤ |W|·‖K‖²₂` (Jacobian-1 substitution), K ∈
L²∩L^∞ from 1582 ⇒ finite for ALL bounded D,M,N by the committed HS ideal
lemmas ⇒ the pre-correction DIVERGENT reading (β₋=1/2 vs "2β>2") is
superseded in substance — the negative ray is permanently off the obstruction
list. ADJUDICATION: the committed prolate absorption closes ONLY the prolate
column; the model does NOT close hgap/hradial; the remaining content is ONE
carrier-defect family — sharp-cut counter-term (third manifestation) +
physical M-transport (≤ log q per Euler transport) — i.e. a CARRIER-GEOMETRY
problem, not a phase problem. The 1576 stop scope narrowed accordingly
(multiplier-phase class superseded IN KIND). (★)/B4/ρ5/R4/(OB)/W1 OPEN.
RH NOT claimed. Commit 3c4392b.

2026-09-17 record 1582 (CONT-6): **P1 PAID** — T0c/T0d paid with signed
cross-validation (C₃=2.928/π<0.933, C₄=23.67/π<7.54; the chain check caught
a real Im(1/z⁵) sign slip); compact caps B₁≤61.8/B₂≤340/B₃≤8.03e3/B₄≤3.00e5;
threshold U₀≤20.7; full-line even-fold model correction; N=2 no-saddle parts
lemma |K(u)| ≤ 43(1+|u|)⁻² for u ≤ −U₀ ⇒ every polynomial-weighted L²
functional converges at model level. Sentinel d34 exact-rational PASS 16/16,
no stored constants (EM off-by-one hazard: ζ shifted by exactly 1·N⁻³, caught
at m=16). Commit 584eb1b.

2026-09-17 record 1581 (CONT-5): NEGATIVE-RAY LEDGER CORRECTION — 1571's
β₋=1/2 row invalid twice (zone violation; smooth compact zone ⇒ no saddle ⇒
parts decay); 1576 stop's driving premise withdrawn; threshold prose never
satisfiable; CARRIER VACUITY (E=Q=I on the Sonin carrier) ⇒ modulation void
at the gate; law F30; P1/P2 two-brick program (both now paid).

## WAVE DIGEST (older; one block per era — details in docs/proofs/)

+---------------+----------------------------------------------------------+
| era           | verdict                                                  |
+---------------+----------------------------------------------------------+
| 1580          | W1 OPENED: escape-form equivalence hand-verified; two    |
|               | naive attacks typed dead; prime-free ceiling = hardest   |
|               | window; W1→W1a/b/c; ψ(¼) Gauss = contract, not theorem.  |
| 1579          | G8 survivor queue exhausted at paper level (phantom      |
|               | support-propagation; F29 born: HS-ness needs a source).  |
| 1577-1578     | Owner card from source: B3 PHANTOM, hradial CAPPED, W0   |
|               | LANDED (Φ, r₀); counter-term = NON-LOCAL (3rd defect);   |
|               | (OB) = CONSTRAINED extremum; laws F26/F27/F28.           |
| 1572-1576     | B4 = ONE square-sum; fixed-scale hM FAILS (support moves |
|               | ≤ log q per Euler transport); strip-confinement; ρ5      |
|               | producer interface GREEN; 1576 TYPED STOP (premise       |
|               | later withdrawn by 1581); law F25; AGENTS §7b N–R.       |
| 1568-1571     | WAVE V entry: P2 connector GREEN; T0/T0b paid (sentinel  |
|               | 8/8); stage-1 ledger β₊=5/2, β₋=1/2 (row later killed).  |
| 1510-1567     | B4 → ONE Fourier-gap Hardy tail; ρ5 pinned; T0           |
|               | groundwork + committed phase transcription (1511).       |
| 1508-1509     | Gate normal form + route W strip GREEN — (★) = "P C P    |
|               | is HS on the ambient".                                   |
| 1502-1507     | GATE COLLAPSED TO (★); ρ4 GIVEN (★); ρ5 iff FORMAL;      |
|               | gate typed PHASE-level (map 012 live face opened).       |
| 1498-1501     | S1/S2+B1/B2 GREEN (3958 jobs); gate = ρ5 not remainder   |
|               | convergence; 1498 audit: both diagonal gates OPEN (F24). |
| 1417          | CATEGORY CHANGE: gate is PHASE-level, inputs DENSITY-    |
|               | level (F21/F22); map 011 tracks A/W; 1418: track A       |
|               | does not reach RH as written.                            |
| 1412-1416     | F2 campaign 51 decls GREEN (kill (a) machine-checked);   |
|               | C1MinimalWeilCriterion GREEN (side-condition-free iff,   |
|               | F20); 1415: brick 4 phantom, wall = proof idea.          |
| 1405-1411     | CHUK sealed; dictionary PLUS_ONE; radius-shrink closed   |
|               | (archive card); F1 freeze / F2 bridge fork.              |
| 1400-1404     | ROUTE-BETA CLOSED: 107/107 negatives, one mechanism;     |
|               | F14 (taper-dead) + F15.                                  |
| 1391-1399     | 009 contract closed; rung-3 rigs: A(g) Hermitian         |
|               | quadratic, all NEG; 0/41 kills nothing (sup-law);        |
|               | F10-F13.                                                 |
| 1375-1390     | N0' ladder CLOSED; F3 UNCONDITIONAL (hypothesis-free B5  |
|               | producer); (J1) regime; shape layer FORMAL.              |
| 1342-1374     | A1b critical-pinning; B0b Weil-iff brick; H2 corridor;   |
|               | placement audit kills count→energy.                      |
| 1318-1341     | P1 two-channel; 1341 family surface DISSOLVES (gate =    |
|               | SourceRH both ways); 1343 B0b: gate MACHINE-CHECKED      |
|               | Weil criterion.                                          |
| 1140-1227     | Probe H2 (FP = −3.321·qw); RANK-3 sealed; Cand-B         |
|               | withdrawn; signed-tail DEAD; 1214/1216 M-side fracture   |
|               | (see m-side card).                                       |
| 1050-1139     | P2 producer freeze frontier; 1087 closes root-window     |
|               | carrier search; 1063 F1 crux (F1' survives).             |
+---------------+----------------------------------------------------------+

## ARCHIVE POINTERS

- Committed records: `docs/proofs/` (numbered; title line = verdict).
- Route maps: `docs/map/` (README + binding rulings; read before new bricks).
- Pre-compression full text: `_precompress_backup_2026-09-17/` (newest) and
  `_precompress_backup_2026-08-27/`.
- Auto-memory cards: frontier = rh-mainline-freeze; dead routes =
  archive-dead-routes; conventions = m-side-convention-fracture-1214,
  numerics-last-read-source-first, readme-progress-dashboard,
  wsl-windows-toolbox, lean-mathlib-gotchas; grants = push-authorization;
  dormant = external-ai-prompt-packs; historical verdicts =
  probe-1213-verdict-h2, f1-crux-verdict-1063, rh-direct-attack-charter-1358.
2026-09-18 ConnesWeilRH/Dev/C1G8R3JointHardySubIdConsumer.lean : added and audited a generic Hardy-sub-identity consumer; the arbitrary finite-S factor D plus the existing prolate square-sum now imply the source-Sonin commutator square-sum used jointly by S3/B4. The analytic Hardy producer remains open; accepted by build log 1606.
2026-09-18 ConnesWeilRH/Dev/C1G8R3WideHardyFourierSupportBridge.lean : formalized the exact equivalence between wide Hardy radial support and same-scale Fourier support, giving B4 a shorter Fourier-defect producer interface; accepted by build log 1609.
2026-09-18 ConnesWeilRH/Dev/C1G8R3WideHardyFourierSupportBridge.lean : added the source-column form of the wide Hardy/Fourier support equivalence, matching the actual B4 column type; the producer estimate remains open, accepted by build log 1612.
2026-09-18 ConnesWeilRH/Dev/C1G8R3FourierGapConsumer.lean : rewired the generic B4 internal-gap consumer to accept the exact same-scale Fourier support certificate through the source-column Hardy/Fourier bridge; the actual Fourier producer remains open, accepted by build log 1613.
2026-09-18 docs/proofs/1614_s3_operator_target_boundary.md : audited the exact distinction between the ambient S3 right-leg consumer C ∘ E ∘ (I - Q) ∘ E and the source-compressed J† C J survivor gate; the ambient non-Hilbert--Schmidt obstruction blocks only the shortcut, accepted as a formal route audit.
2026-09-18 ConnesWeilRH/Dev/C1G8R3SourceCompressedRootKernel.lean : added the direct source-carrier operator J† C J and exact ambient matrix-coefficient readback, with no ambient HS premise; accepted with paired audit in build log 1615_source_compressed_kernel_retry3.
