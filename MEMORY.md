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
2026-09-18 ConnesWeilRH/Dev/C1G8R3SourceCompressedRootKernel.lean : formally split the source-compressed root kernel into the central Hardy corner plus the three prolate-remainder terms using P = E Q E - R; accepted with paired audit in build log 1616_source_compressed_kernel_split_retry13.
2026-09-18 ConnesWeilRH/Dev/C1G8R3SourceCompressedRootKernel.lean : added the sharper one-sided identity J† C J = J† (E Q E) C J - J† R C J, removing the unnecessary right Hardy corner and isolating the central energy target; accepted with paired audit in build log 1617_source_compressed_kernel_one_sided_retry3.
2026-09-18 docs/proofs/1618_route_rereview_s3_b4_carrier.md : wave preflight - the registered S3 brick is already landed (zero S3 spend, law F8), the B4 strip identity of 1575 section 3.3 was never landed, and the carrier base is a def consumed as hsource (law F33); the healthy-CompactLog B5 consumer and the three guardrails are re-named before any spend.
2026-09-18 ConnesWeilRH/Dev/C1G8R3StripConfinement.lean + Audit : landed record 1575 section 3.3 as support algebra - the radial defect of any wide-certified operator is the translated finite strip projection on [log lambda - s, log lambda), with additive scale composition (wideRadialScale_add, wideRadial_support_comp) and no caller premise for suffixEulerFrameAmbientLossColumn / suffixEulerFrameSchurStep.boundaryDagger at width exactly log p; the signed corollary hardyColumn_radialDefect_eq_strip_of_wideHardySupport collapses the 1599 unbounded tail to that strip under the wide Hardy certificate. Support algebra only (law F29): no estimate, B4 producer and hgap OPEN, accepted by build log 1618.
2026-09-18 docs/proofs/1620_s3_reduction_layer_complete.md : route record - the S3 reduction layer is complete (C1G8R3GateAmbientNormalForm links 1-5 plus 1614-1617), so the single open estimate is filed in five equivalent forms (ambient P C P, source gate J† C J, source input C J, Hardy-compressed E Q E C J, source projection P C J) and any further rearrangement is a rename; S3 stays OPEN.
2026-09-18 ConnesWeilRH/Dev/SoninCarrierEigenvectorBridge.lean + Audit : machine-checked that carrier nonemptiness is exactly the existence of a nonzero radial ±1 eigenvector of the committed Hardy--Titchmarsh involution H; the paper-level half-phase unitary U = F^-1 M_{m^{-1/2}} F gives U H U^-1 = R, so the fixed-point condition is evenness and the base is the 1590 de Branges existence W != {0} (T4 of docs/proofs/1003 the productive route); the base stays a def, not a theorem (F33), no witness, RH not claimed; accepted by build log 1618.
2026-09-18 ConnesWeilRH/Dev/SoninCarrierMultiplierConjugate.lean + Audit : machine-checked the factorization H = R ∘L U_m with U_m = F ∘L M_m ∘L F⁻¹ (free, from the committed covariance F⁻¹ = R ∘L F at CCM24ArchimedeanCarrier.lean:863), ten declarations including the fixed/anti-fixed forms U_m u = ± R u, U_m u = R (H u), the carrier characterization as radial u with U_m u in the reflected radial subspace, and the closed eigenvector bridge U_m u = ±R u; the same record (docs/proofs/1622) carries the erratum withdrawing 1621's "covariance not committed" caveat and its half-phase square root m^{1/2}; no witness for the carrier, base stays a def (law F33), RH not claimed; accepted by build log 1622.
2026-09-18 docs/proofs/1623_t4_prolate_attack_four_obligations_and_two_mismatches.md : route record - T4 typed as four independent obligations (domain / spectral sign / carrier transport / window restriction) against the source (PNAS 2022, PMC9295779, Corollary 2.2, semiclassical counting on the sign leg); the tree's "prolate" naming is the finite-S strict-angle band-crossing layer (ProlateTraceReduction.lean), not the CCM prolate operator; two mismatches filed (one-sided committed carrier vs two-sided CCM Sonin space; bounded multiplier would force an empty carrier), Mathlib has no Bessel/Paley-Wiener/Hardy/de Branges/Sturm-Liouville layer; T4 OPEN, no Lean beyond the 1621/1622 interface.
2026-09-18 docs/proofs/1624_b4_certificate_and_carrier_are_one_toeplitz_condition.md : route record - the B4 wide certificate and the carrier base are the same Toeplitz condition P_+(e^{2πi c xi} m · R(F v)) = 0 (1003's kernel statement), so WO-B's producer premise and the base of both WO legs are one analytic object; the difficulty is entirely the multiplier's half-plane growth (πx)^{2πy} (paper-level, unformalized PW/H² dictionary); m ≡ 1 forces H = R and an empty carrier, so no bounded-multiplier witness can exist; nothing proved or refuted, B4 OPEN.
2026-09-18 docs/proofs/1625_s3_form_selection_and_strip_density_bound.md : route record - S3 attack surface selected as form v P ∘L C ∘L J (fewest layers after 1616/1617, carrier-visible, same Toeplitz object as 1624); the 1589 section 6 StripDensity finiteness fork is closed at the trivial bound Tr(P M_Δ P) ≤ Λ from the committed P ≤ E (1588) and radialSupportProjection_coeFn_indicator (C1G8P1HeadWindowEnergyLowerBound.lean:81), with the Lean brick specified (missing layer: basis-to-measure trace identity); S3 OPEN in form v.
2026-09-18 ConnesWeilRH/Dev/SoninScaleMonotonicity.lean + Audit : machine-checked the scale monotonicity of the carrier layer (five declarations): Radial, FourierSupport and the archimedean Sonin subspace are antitone in the scale lambda (the vanishing region Iio(log lambda) grows), so carrier nonemptiness propagates DOWNWARD in the scale (a witness at a larger scale witnesses every smaller one) and triviality propagates UPWARD (triviality at a scale forces triviality at every larger scale) - the base obligation is a sharp-threshold statement; the m = 1 sanity check becomes structural: the model carrier is {0} at lambda = 1 and hence for all lambda >= 1; accepted by build log sonin_scale_monotonicity2 (3319 jobs, zero error, zero sorryAx, five standard axiom prints, no warning in the new modules); no witness, base stays a def (law F33), RH not claimed.
2026-09-18 ConnesWeilRH/Dev/SoninWindowTransport.lean + Audit : machine-checked window transport into the one-sided carrier (four declarations): IsWindowWitness T u (u nonzero, u and H u vanishing outside the window (-T,T)) and carrier_nontrivial_of_window_witness (log lambda <= -T => archimedeanSoninCarrier_nontrivial lambda), plus the two membership helpers mem_radialSupport_of_window / mem_fourierSupport_of_window; this makes the direction of the 1623 one-sided vs two-sided mismatch formal - any bounded-window Sonin witness transports into the tree for free and then spreads downward by the 1626 monotonicity; the proof uses only the window's lower edge, no window witness is constructed, base stays a def (law F33), RH not claimed; accepted by build log sonin_window_transport.
2026-09-18 docs/proofs/1631_base_weapon_inventory_and_erratum_c.md + scripts/dvi_extract.py + scripts/phase_budget_1631.py : analytic record, no Lean brick - (the inventory) item 1 of the 1630 next steps executed: the carrier base's "wall 1 = no criterion in class" turned into a 15-row checklist in three groups (A phase-decomposition, B density-completeness, C structure/class/spectral), each row carrying statement + source + hypothesis-vs-m + the one named failing hypothesis + what it buys; verdicts: three tools apply at our question (MP 2010 Thm A(ii)+Corollary at p < 1/2; section 4.1's little-multiplier proposition subject to the d = 0 transfer gap; the maximal-vector structure theorem of Camara-Partington arXiv:1711.04511), one applies only to the strictly weaker finite-type question (Krasichkov-Tumarkin, statement committed in 1628), six are out of class with a named failing hypothesis (Theorem B needs J inner; section 5.1's big multiplier as stated needs gamma of bounded variation and gamma' bounded below; the "crucial part" sub-problem needs h~' <~ 1; the BM density criterion Prop 8.6 needs a meromorphic-inner symbol, law F40; the classical |Psi'| <~ 1 multiplier; de Branges' classical machinery, dead because A is not Hermite-Biehler), three are dictionaries or parallel lanes (Smirnov identity N^+ cap L^2 = H^2; model spaces; CCM prolate = the T4 lane, not a base tool), one is the target (MP 2010 (1.6)'s Hardy clause at p = 2) and one is a phase-choice tool (section 6 Krein-shift approximation by inner functions); (phase budget, rig) the committed phase is gamma(xi) = -2 pi xi log|xi| + 2 pi xi + pi/4 - 6.631e-3/xi + O(xi^-3) with gamma'(xi) = -2 pi log|xi| + O(xi^-2) and gamma odd (30-digit check over five decades, residual after pi/4 decays exactly like 1/xi), so the criterion's phase psi = -gamma - a xi is super-linear with exponent 1 + o(1) (x log x) and its derivative is BELOW every polynomial: inside the survey's generalized power-law form, outside the classical |Psi'| <~ 1 form; (two budgets) for model data of exponent beta, h in L^1(dPi) needs beta < 1 (density) while inner-function arguments (measures) need beta < 2, and our phase sits at 1 + o(1): strictly inside the measure budget and strictly outside the density budget, so in any decomposition psi = arg Theta + h~ the super-linear part must be carried by Theta (the measure side) - the criterion is not obstructed by a crude growth count, and the obstruction, if any, is the joint density/atoms constraint Q3; (five questions with sources) Q1 inner-vs-meromorphic Theta (extract says "inner function", the survey's prose says "meromorphic inner function"), Q2 e^h in L^1(R) vs L^2(R) (the survey states both in different sentences; the extract prints L^2), Q3 the joint h~ ceiling ([23] section 2 / MP 2010 section 2 Lemmas 1-5), Q4 transfer of the section 4.1 machine to d = 0 intervals, Q5 removability of the eps-gap plus MP 2010 section 5.1's exact hypothesis list; five retrieval targets R1-R5 filed; (source pin) the (1.6) criterion's reference [23] identified as Makarov-Poltoratski, "Meromorphic inner functions, Toeplitz kernels and the Uncertainty Principle", Perspectives in Analysis (Springer 2005) 185-252, full text retrieved as DVI (prose extract by the new committed scripts/dvi_extract.py; DVI version-2 opcode table established from the post amble: bop = 139, eop = 140, push = 141, pop = 142); (Erratum C) 1630 section 8's two-tap form w(.-a_tilde/(2 pi)) * h = w * g is replaced by w(-.) * h(. + c) = w * g with c = 2 log lambda <= 0 - the frequency shift acts on the SIGNAL, and after clearing denominators the coefficient of H is A(-xi), whose inverse transform is the flipped tap - with three checks: at lambda = 1 the printed form gives h^ = g^ hence h = 0 (an empty base at lambda = 1 for every symbol), at m = 1 the two forms agree because delta is even (why 1630's own model check missed it), and on the shifted-tap model m(xi) = e^{2 pi i mu xi} the printed form's threshold is mu-independent (lambda < 1) while the corrected form gives mu > c = 2 log lambda, the true answer; (flag, not erratum) 1630 section 4's audit line "power-law hypotheses of B/C and section 5.1 FAIL" is NOT re-verified and is likely wrong for section 5.1 (there the power-law slot belongs to the theorem's own free multiplier psi, and our gamma' grows only logarithmically): the line must not be cited until R2 closes; (laws) F45 an inventory row IS its hypotheses (a row without a retrieved statement is a pointer and carries no verdict), F46 class + exponent + eps-gap are part of a statement ("short" drives nontriviality in N_p for p < 1/2, representability up to eps x in N^+, and triviality of the PERTURBED symbol in H^2), F47 a re-typing must be tested at the degenerate parameter and on an asymmetric model (a symmetric test cannot discriminate a symmetric error); map 043 updated (inventory pointer, the five questions, Erratum C, F45-F47); carrier base/T4/B4/S3/WO legs unchanged and OPEN, RH not claimed.
2026-09-18 docs/proofs/1630_mp2010_primary_source_bm_interval_and_shortness_direction.md : route record plus one Lean brick with audit - (item 1, primary source) MP 2010 Invent. Math. 180 full text retrieved and quoted: BM-interval definition, the (beta)-almost-decreasing shortness sum over intervals with d >= 1, Theorem A (short => N_p != {0} for p < 1/2), the corollary p < 1/3, Theorems B/C (J meromorphic inner), the (1.6) criteria, section 4.1's little multiplier proposition, section 4.2's construction and section 5.1's multiplier theorem with proof skeleton, plus the roadmap items (1)-(6) and the exact statement of the still-missing Thm 8.5; (BM computation) for the tree's phase gamma + a xi the Beurling-Malliavin components are ONE interval (x*_a, R_a) containing the origin with R_a = e^{a/(2 pi)} = lambda^{-2} and d = 0, so the shortness sum is VACUOUS for every beta >= 0 and every lambda <= 1; (Erratum A) 1629 section 3 recorded the shortness direction backwards (short => NONTRIVIAL kernel) and carried a vacuous "H^2 \ N^+" phrase (H^p subset N^+; N^+ cap L^2 = H^2 by Smirnov makes p = 2 exactly the Hardy kernel) - the surviving content is that the base is the p = 2 endpoint of the N_p scale; (class audit) our phase satisfies the one-sided (1.4) hypothesis for every beta > 0 but is not of power-law type (|gamma'| ~ 2 pi log|x|), m is not inner, and the transfer gap is the p-range (criterion p < 1/2 vs ours p = 2) plus section 4.2's l >~ d against our d = 0; (base at p = 2) the criterion form becomes a decomposition psi = arg Theta + h-tilde with Theta inner and e^h in L^1, convention flags pinned; (section 8) the tap identity A = 2F(w), B = 2F(w(-.)), w(u) = e^{u/2} e^{-pi e^{2u}}, with the numerical check INT w = 1.3616441040 against Gamma_R(1/2)/2 = 1.3616441082, and the base rewritten as the two-tap convolution equation w(.-a/(2 pi)) * h = w * g with h in L^2((-inf,0]), g in L^2([0,inf)) (model m = 1 degenerates to h(.+c) = g and reproduces nontrivial iff lambda < 1); (B3, item 5) STRUCK - no provably nonempty substitute: strictly inside is the base in disguise (F33), strictly larger destroys the distance terms, a different skeleton is a rename (1620's five forms); (item 3) brick Dev/StripDensityTraceLedger + audit Dev/StripDensityTraceLedgerAudit: re_ordinaryTraceAlong_eq_tsum_re, ordinaryTraceAlong_re_nonneg, re_inner_self_le_of_le, ordinaryTraceAlong_re_mono, the named StripDensityCompressionObligation and stripDensity_trace_le_of_compression, plus the refutation rankOne_compression_not_le / rankOne_compression_counterexample (explicit C^2 witness, re <w,(M-PMP)w> = -1 < 0) of 1625 section 2's operator-level sandwich P M P <= M (Erratum B; the trace-level conclusion of 1625 is unaffected), accepted by build log 1630_strip_density_trace_ledger_audit.log (Build completed successfully (2662 jobs), zero error, zero sorryAx, zero warnings in the new modules, all six axiom prints standard); (item 2) B4-scalar tested literally on three explicit column classes by the slice definition of H^2(C_+): the premise FAILS for all three, mechanism |m(x+Iy)|/|x|^{2 pi y} -> 1 (measured, deviation < 3e-3 at y = 1) against the column's decay - the algebraic columns keep every slice in L^2 exactly up to y < 1/(4 pi) (G500/G20 = 1.01 below, 1.27-1.30 at the threshold, 86 at y = 0.3, 1.2e8 at y = 1) and the entire column's slice norms grow 0.698 -> 0.930 -> 8.27 -> 2.28e9 - and the literal line is additionally DEGENERATE by support algebra (K and the columns on the committed half-line give K*v on that same half-line, so only Psi = 0 satisfies it); orientation flag filed for the next source read of 1622's U_m against 1626 section 2's dictionary, no erratum claimed; (item 4) Toeplitz finite-section probe scripts/toeplitz_probe_1630.py on the translate family of one bump: sigma_min(K) saturates by K ~ 16 (drift < 0.5%) and depends only on lambda - 0.4124768 (lambda = 1), 0.068243 (1/2), 0.026005 (1/e), 2.9905e-6 (0.1, resolved five orders above floor), <= 1.8e-11 (0.01, at the floor) - so no finite-type witness at any lambda (1627 confirmed numerically) and the distance to the base decays steadily in lambda: the base is approximable by finite-type data but never attained by it; floor calibrated on the exactly-solvable model (lambda = 1/2, exact answer 0): 4.146e-8 at |xi| <= 64 and 1.8208e-11 at |xi| <= 128, i.e. xi-window-edge leakage (the grid-aligned witness c = -2 reads 3.6e-16), so every reading is quoted against it; (laws) F41 direction and p-range come from the primary source, F42 name the kernel class and exponent (H^p subset N^+, N^+ cap L^2 = H^2), F43 a numeric floor is a property of the rig - calibrate on a known-exact case, F44 check a committed formula's own support algebra before treating its failure as evidence; map 043 updated (all five rows executed, next spend rows added); carrier base/T4/B4/S3/WO legs unchanged and OPEN, RH not claimed.
2026-09-18 docs/proofs/1629_mp_class_audit_normalization_resolved_b4_support_correction.md + docs/map/043_route_map_to_rh_after_1629.md : route record, no Lean brick - (class audit, law F40) the exact Prop 8.6 of Hartmann-Mitkovski arXiv:1511.08326 section 8 retrieved (Theta must be a meromorphic INNER function with INCREASING argument; inf{a >= 0 : Ker T_{conj(S)^a Theta} != {0}} = D^+_BM(Lambda); radius-of-completeness reading) and audited against m: m is not inner (unbounded in C_+), its argument gamma is not increasing (gamma' < 0 for |xi| > 1), and m is NOT in the Nevanlinna class (if f in N with |f*| = 1 a.e. then f = Theta_1/Theta_2, so gamma = C x + O(log|x|) by the Herglotz representation of the positive harmonic -log|Theta|, contradicting the super-linear gamma), hence 1628's redirect "the WO base is governed by D^+_BM(Lambda(m))" is WITHDRAWN as a class misapplication - a node sequence is not a symbol; the computed value D^+_BM(Lambda(m)) = infinity (counting n(R) ~ 4 R log R from 2 pi |lambda_n| log|lambda_n| ~ n pi) stands only as a statement about completeness of {e^{i lambda_n x}}; (normalization RESOLVED) from the committed 1622/1624 facts the carrier base is exactly the Toeplitz kernel with the CONJUGATE multiplier: carrier(lambda) != {0} <=> exists H in H^2(C_+)\{0} with e^{4 pi I (log lambda) xi} m(-xi) H(xi) in H^2(C_-), shift a-tilde = 4 pi log(1/lambda), matching Prop 8.6(ii)'s T_{conj(S)^a Theta} shape and model-checked with m = 1 by the explicit witness H = -F(1_{[2a,0]}) (nontrivial iff log lambda < 0 iff lambda < 1, threshold 0 = D^+_BM(empty)), closing 1628's normalization caveat; the base is therefore a HARDY-ONLY phenomenon (H^2 \ N^+), the Smirnov-Nevanlinna kernel of our symbol being expected trivial (gamma = decreasing + one compact bump, which is short); (B4 correction) the kernel K = F^{-1}(m) sits on (-inf, 0] (m holomorphic in C_+, poles in C_-; model m = e^{iaz} gives K = delta at -a/(2 pi)), so supp(U_m v) is contained in (-inf, sup supp v] - the UPPER edge is inherited and no lower edge is created, correcting 1628 section 3's "(K on [0,inf), lower edge controlled by upper edge)" while keeping its conclusion (B4's premise is a cancellation, not a support condition); retrieval gap filed (definition of Sigma(gamma) and I_n in 8.2, full statement of the big multiplier Theorem 8.5, not retrieved); route map 043 redraws the tower, the gate anatomy, the five open bones, the base's four equivalent forms, the B1/B2/B3/B4 decision tree and the ordered attack plan; carrier base/T4/B4/S3/WO legs unchanged and OPEN, RH not claimed.
2026-09-18 docs/proofs/1628_mp_criterion_shortness_b4_scalar_form_transport_brick_ledger_erratum.md : route record - (N5) the Makarov-Poltoratski criterion's real form located and quoted (shortness condition on Sigma(gamma), failure form SUM |I_n|^2/(1+dist^2) = infinity; little multiplier theorem 8.4 of Hartmann-Mitkovski arXiv:1511.08326 section 8; Smirnov-Nevanlinna form Ker^+ T_U trivial <=> gamma = d + h-tilde; BM threshold form inf{a : Ker T_{conj(S)^a Theta} != {0}} = D^+_BM(Lambda)), our m identified as a meromorphic inner function (MP's own class) with two-term phase asymptotics gamma(xi) = -2 pi xi log|xi| + 2 pi xi + (pi/4) sgn(xi) + O(1/|xi|) and gamma' = -2 pi log|xi| + O(1/|xi|), hypothesis audit showing BOTH stated hypotheses fail (gamma' not bounded below, gamma not of bounded variation), and the redirect to the single number D^+_BM of the node sequence Lambda(m) = {gamma in pi Z} with counting ~ 4 R log R and both branches mapped to route consequences; (N6) Krasichkov-Tumarkin criterion (exists entire of type tau below M on R iff INT (log M - tau|x|)/(1+x^2) > -infinity) independently re-proves the 1627 finite-type obstruction, no infinite-type construction available; (B4) the premise in single-column scalar form xi -> e^{2 pi I (log lambda'') xi} m psi in H^2(C_+) with psi = F^{-1} v, plus the proof that support algebra cannot deliver it (kernel K = F^{-1}(m) on [0,inf) so the lower edge of U_m v is controlled by the upper edge of v - cancellation, not support); erratum (numerically confirmed, mpmath): the line-growth ledger's pi factors are spurious - |A(x+Iy)| ~ sqrt(2)|x|^{pi y - 1/4} e^{-pi^2|x|/2} and |m(x+Iy)| ~ |x|^{2 pi y} (not (pi x)^{2 pi y}), because the pi^{-s/2} prefactor contributes pi^{-pi y} cancelling the pi^{pi y} of Stirling; no qualitative conclusion of 1626/1627 changes; carrier base OPEN, T4/B4/S3 unchanged and OPEN.
2026-09-18 docs/proofs/1627_entire_w_obligations_two_corrections.md : route record - the elementary L2 face of the carrier base (T'): one nonzero g in L2 with supp g in [0,inf) and supp (U_m g) in (-inf,0], exactly V_arch(1) != {0}, stated in committed vocabulary (Radial, H, U_m) with no H2/PW layer; ONE PROVED OBSTRUCTION: no witness W can have finite exponential type (from W/A in H2(C_+) the weighted boundary L2 bound plus subharmonicity gives |W(x)| <= C e^{-pi^2|x|/2}|x|^{pi-1/4} on R, and a finite-type entire function with exponential decay on R has compactly supported transform analytic across the real axis, hence is zero), so every band-limited / Paley-Wiener / finite-type candidate is excluded and the witness must be infinite type (the Gamma-factor/prolate class of 1590); TWO CORRECTIONS: (i) the carrier is a conjunction of two half-line support conditions on the same vector and is genuinely scale-dependent - in the model m = 1, V_arch(lambda) != {0} exactly for lambda < 1 and no single translation maps it to lambda = 1 (the two endpoints must move in opposite directions), so 1624 section 4's unification of the B4 premise with the carrier base is withdrawn in its equivalence form (they share the symbol m only); (ii) a closed form drafted this round, A*B = pi^{1/2}/sin(pi/4 - pi^2 I z), is FALSE - counterexample Gamma_R(1/2)^2 = 7.4163 vs sqrt(2 pi) = 2.5066, the slip being Gamma((1-s)/2) != Gamma(1-s/2); the correct statements are A*B = pi^{-1/2} Gamma(1/4 - pi I z) Gamma(1/4 + pi I z) (hence 1/(A B) entire, zeros exactly at the poles of A and B, the "product of two Weil factors" object, which is too large: its quotient by A has modulus rho^{-3}) and Gamma_R(s) Gamma_R(-s) = -2 pi/(s sin(pi s / 2)) verified at s = 1/2 to 5 digits; MP criterion still not explicitized (precise statement in the 2005 paper, not retrieved; the surveys state the structural results only); carrier base OPEN, T4/B4/S3 unchanged and OPEN, no witness, RH not claimed.
2026-09-18 docs/proofs/1626_infrastructure_verdict_toeplitz_form_and_scale_monotonicity.md : route record - infrastructure verdict (the committed carrier layer is stateable without any H2/Paley-Wiener layer; the missing layer is needed only to prove), the explicit symbol form m(xi) = Gamma_R(1/2 - 2 pi I xi)/Gamma_R(1/2 + 2 pi I xi) = A/B with the zero/pole ledger (A analytic and zero-free on C_+, poles in C_-; B = A(-.) the mirror; m analytic on C_+ with zeros at +I(4n+1)/(4 pi), poles in C_-, |m| = 1 on R, |m(x+Iy)| ~ (pi x)^{2 pi y}), the carrier base re-typed as the de Branges-pattern obligation (W entire != 0 with W/A in H2(C_+), W/B in H2(C_-); W = A phi = B psi, no pointwise cancellation conditions at all - the content is a pair of line-norm bounds), the obstruction that A is NOT Hermite-Biehler (m vanishes at I/(4 pi)) and that A's poles are too dense to clear (SUM 1/|z_n| = infinity), and the WITHDRAWAL of 1624 section 5's cheap scalar test (the symbol's argument gamma ~ -2 pi xi log|xi| has no limit at infinity so the continuous-symbol index theory is unavailable; the applicable criterion is Makarov-Poltoratski for real-analytic unimodular symbols, arXiv:1711.04511 section 2.3, which lands in model-space/uniqueness-set territory; model tests m = affine phase and m = 1 both give trivial kernels); also records the self-correction that entire functions CAN lie in H2(C_+) (witness W(z) = (e^{2 pi I a z} - 1)/(2 pi I z), exponential type a, line norms <= a on C_+ and growing on C_-), so 1590's claim is right and its example wrong; carrier base (now in Toeplitz/de Branges form) OPEN, T4/B4/S3 unchanged and OPEN.
