# 1141 - P2 scalar witness: zero-configuration design

Date: 2026-09-05.

Status: attack-plan registry. This record proves no new theorem, closes no
obligation, and claims no sign. RH is not claimed.

Map role: supporting design record under the binding ruling
[`003`](003_b1_b5_minimal_exit_route_selection.md). It registers the
producer-side design for the single open C3 obligation P2 (obligation table
of [`004`](004_endpoint_literature_interface_audit.md) section 4) after
record 1140 isolated the exit contract. It changes no route selection and
no endpoint authority.

## 1. The producer contract (FORMAL, landed)

The exit is fully wired. The chain is:

```text
P2ScalarOneWindowBudgetWitness g                      [C1P2DefectControl.lean:1288]
        |
        |  orbitGate_of_p2ScalarOneWindowBudgetWitness
        v
orbitWindowSemiLocalGate g                            [record 1089 gate]
        |
        |  qw_nonneg_of_healthyDetectorData_of_orbitWindowSemiLocalGate
        v
0 <= qw g  -- contradicts the detector branch qw g < 0
        |
        |  healthy_sourceRH_of_right_detector_specific_qw_nonneg
        v
SourceRH
```

The producer obligation is the single universal statement consumed by
`sourceRH_of_pinnedOrbitDetector_p2ScalarOneWindowBudgetWitness`
(`C1P2DefectControl.lean:1352`): for every right-oriented off-line zero,
the pinned detector `g` with its formal support and visible-prime package
admits a witness. The witness fields are:

```lean
structure P2ScalarOneWindowBudgetWitness (g : CompactLogTest) where
  W : CompactLogTest
  mu epsilon b a Bsupport Carch : Real
  hgsupp : Function.support g.test ⊆ Set.Ioo (-b) b
  hWsupp : Function.support W.test ⊆ Set.Ioo (-a) a
  hcert : ICgate W.convolutionSquare ≤ -mu                    -- window certificate
  hpoint : ∀ y > 0, ‖archimedeanIntegrand (ICdefect ...) y‖ ≤
             Carch * Real.exp (-y)                            -- arch envelope
  hgsquareSupp / hWsquareSupp : ... ⊆ Set.Ioo (-Bsupport) Bsupport
  hbudget : (|log (4π) + γ| * s0 (defect) + Carch)
            + N * log N * 2 * (s0 g.convSq + s0 W.convSq) ≤ epsilon
            -- N = ceil (exp Bsupport) + 1                    -- scalar budget
  hmargin : epsilon ≤ mu                                      -- margin
```

Two analytically loaded groups remain:

```text
+------+--------------------------------------------+---------------------------+
| Field group                                        | Feeding route             |
+------+--------------------------------------------+---------------------------+
| hcert | window certificate ICgate W.convSq ≤ -mu  | Hbox: records 1118-1123,  |
|       |                                            | the 1126-1139 moment      |
|       |                                            | campaign, G2 repair,      |
|       |                                            | M-side true intervals     |
+------+--------------------------------------------+---------------------------+
| hpoint, | defect envelope + scalar budget + margin | THE zero-configuration   |
| hbudget,                                           | producer (this record)    |
| hmargin                                            |                           |
+------+--------------------------------------------+---------------------------+
```

The `hcert` group is the already-registered window campaign; nothing in
this record touches it. This record designs the second group.

## 2. Design constraints

Any candidate producer must clear three constraints. Each is stated with
its evidence level.

### 2.1 The admission no-go (FORMAL)

```lean
theorem no_stageB_budget_of_qw_negative
    (g W : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (hnegative : C1SameOwnerWeil.qw g < 0)
    {mu epsilon : ℝ}
    (hcert : ICgate W.convolutionSquare ≤ -mu)
    (hdec : ICgate (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1)) ≤ epsilon)
    (hbudget : epsilon ≤ mu) : False
```

(`C1T2Assembly.lean:293`.) Since the detector branch proves
`0 < ICgate g.convolutionSquare` unconditionally and
`defectGate_singleton_eq_sub` gives the exact identity
`gate(defect) = gate(g) - gate(W)`, the conjunction
`{hcert, hdec, hbudget}` is refutable on every actual off-line zero.

Design rules derived from it:

```text
DR1  Bookkeeping closure is dead.  The defect bound cannot follow from
     detector negativity, window certificate, and budget arithmetic.

DR2  Honest-envelope smallness is dead.  In the hypothetical off-line-zero
     world gate(defect) >= gate(g) + mu > mu >= epsilon.  A producer that
     sizes Carch or the seminorm products by the defect's TRUE magnitude
     computes a budget above mu and cannot satisfy hmargin.  The rho-dependent
     derivation must reach hbudget through identities (cancellation), never
     through triangle estimates of the actual defect.
```

### 2.2 The scale wall (QUANTIFIED, record 1142)

Pre-brick B2 has landed as
[`record 1142`](../proofs/1142_p2_scale_table.md); its exact table
supersedes the sketch numbers this section first carried (which erred by
using the test radius `n+2` instead of the square radius `2(n+2)` for
`Bsupport`). The corrected floor:

```text
N = ceil (exp Bsupport) + 1,  Bsupport = 2(n+2) for the detector square
  n = 0:  N = 56,   2 N log N ≈ 450.8
  n = 1:  N = 405,  2 N log N ≈ 4863.1
operative margins (committed exact rationals):
  mu_q28 = 1.0434e-06, mu_q38 = 1.2140e-08, mu_q48 = 1.5999e-10
required uniform-square-seminorm scale (n = 1):
  q28 2.15e-10, q38 2.50e-12, q48 3.29e-14
```

The two comparison scales are those margins and the detector's positive
gate mass (record 1116 model twin: `GATE / f0 = +0.45698` at the true
`delta = 0` configuration). The wall is worth 6 to 13 orders of
magnitude depending on the cell: no estimate-based mechanism can cross
it, and the honest-envelope route DR2 is killed quantitatively, not by
slogan. Class selection is forced to q28; orbit selection prefers the
smallest `n` the pinned export admits.

### 2.3 Logical status: the construction is RH-equivalent (FORMAL reading)

In every model with a right off-line zero the witness is unsatisfiable for
the pinned detector (section 2.1). Hence the universal producer statement
is provable only together with `SourceRH`. This is the map-level form of
the 1124-era finding that P2 is the exit itself, not a brick. Consequence
for scheduling: the three lines of section 4 are attack lines on RH-level
mathematics; they are registered with falsifiers and are NOT expected to
close independently. The schedulable work is the pre-brick list of
section 6, all of which is honest regardless of the core.

## 3. Zero-configuration inventory

What rho-dependent data the pinned construction actually carries:

```text
+----+---------------------------------------------------+-------------------------+
| ID | Data                                              | Owner                   |
+----+---------------------------------------------------+-------------------------+
| Z1 | Triple vanishing lap g = 0 on {0, 1/2, 1} and    | HealthyYoshidaDetector- |
|    | detection value at rho (nonzero, pinned ±1 in    | Data (Source tree)      |
|    | the D1 replay)                                    |                         |
+----+---------------------------------------------------+-------------------------+
| Z2 | Unconditional spectral negativity qw g < 0 with   | C1HealthyYoshidaSpectral|
|    | explicit -m(rho) vs dyadic tail margin           | Negativity              |
+----+---------------------------------------------------+-------------------------+
| Z3 | Arithmetic-spectral identity psi F = spectralWeil | centerTwo_arithmetic_   |
|    | Value F for EVERY CompactLogTest (Gauss half-     | eq_spectral             |
|    | anchor contract)                                  | (C1XiCenterTwoArithmetic|
|    |                                                   | Assembly.lean:232)      |
+----+---------------------------------------------------+-------------------------+
| Z4 | The D1 fixed-window orbit construction: g(rho)    | exists_healthyDetector- |
|    | built from rho via empty routeNodes, ±1 windows,  | Data_with_pinned_support|
|    | dyadic tail budget; support Ioo (-(n+2)) (n+2),   | (record 1140)           |
|    | visible q < exp (2(n+2))                          |                         |
+----+---------------------------------------------------+-------------------------+
| Z5 | Window-side machinery: hrep generator (gate =     | records 1121/1122,      |
|    | y ⬝ᵥ (M y)), T-box transport, hker, certified     | 1118/1119/1120, 1123;   |
|    | class windows once Hbox lands                      | moment campaign         |
|    |                                                   | 1126-1139 + G2 + M-side |
+----+---------------------------------------------------+-------------------------+
```

Design reading: Z1+Z3 are the levers (values at the nodes
`{0, 1/2, 1, rho, rho-conjugate}`), Z4 fixes the arithmetic, Z5 supplies
the window side. A producer must connect Z1/Z3 to the `hbudget`
arithmetic of section 1.

## 4. Attack lines

All three are PROJECT CANDIDATE level unless a line says otherwise. None
may be scheduled without passing section 5.

### 4.1 Line S - spectral accounting on the defect

VERDICT (2026-09-05): REFUTED as stated, at identity level, armchair -
[`record 1144`](../proofs/1144_line_s_verdict.md), backed by the landed
record-1143 identity brick.  The defect gate is exactly the spectral
difference `SW W.convSq - SW g.convSq` (one number; every channel
decomposition sums to it), and on any negative detector the window
certificate plus detector positivity force it above `mu >= epsilon`
(`defectGate_gt_add_mu_of_qw_negative`, `no_stageB_budget_of_qw_negative`).
No rearrangement can change the truth value of `hdec`; the registered
falsifier resolves negatively without a probe.  Lines B/C below are
unaffected.

Mechanism (as registered, now historical). Rewrite `ICgate (defect)`
through Z3 into its zero-sum form.
The rho-term carries the detection mass, the on-line zero background is
termwise nonnegative (record 1070 Weil-test dictionary:
`f~(rho) = g~(rho) g~(1-rho)`, on-line terms are squares), the pole terms
vanish on the Z1 nodes, and the producer must show the window cross-terms
absorb the detection mass. This is a Weil-criterion-shaped inequality on
explicit data with the class data fixing W's Mellin profile.

Zero-configuration entry: Z1 detection + node vanishing + Z4 coefficient
structure.

Falsifier (register before any Lean): model-level channel decomposition of
the defect on the record-1116 twin at the true `delta = 0` configuration.
If no admissible window cross-term covers the detection channel, Line S
dies as stated.

Shared sub-brick: B1 (identity audit) is FORMAL-izable with no RH content.

### 4.2 Line B - Bombieri eigensystem port

Mechanism. The landed Wirtinger chain (map record
[`001`](001_first_cut_window_architecture.md) sections 6y slices 7a-12i)
proves boundary-controlled quadratic signs from zero-configured
exponential sums; its remaining steps formalize Theorem 8's sign count
(`#negative eigenvalues of H(Gamma;t) = #distinct complex-conjugate pairs
in Gamma`), the quantitative detector statement. The design question is
whether the eigensystem shape `w = Lambda * H(Gamma;t) *v w` can be ported
into the P2 interface: the window family plays the H-matrix role, the
detector coefficients play `w`, and the boundary correction carries the
sign.

Zero-configuration entry: the Gamma-indexed node equations (Bombieri
section 6, equation (6.4); transcription certified in map 001 section 6y).

Prerequisite: pre-brick B3 (exponential independence + sign count) is
honest detector-branch work regardless of Line B's fate.

Formal bridge brick (record 1147): `C1BombieriP2Bridge` now packages the
finite eigen-relation, reciprocal identity, nonzero mass, and the explicit
same-owner equality `qw g = lam * bombieriWMass gamma z`.  The existing
Bombieri Wirtinger chain then supplies `0 ≤ qw g`, and
`sourceRH_of_right_bombieriP2BridgeData` consumes the contract at `SourceRH`.
No producer currently constructs this data for the pinned orbit detector;
the owner equality and per-zero finite eigensystem remain OPEN.

Falsifier: the fake-zero rig (Bombieri section 13, `N` up to 160). Measure
whether the unique negative eigenvalue's magnitude at the window scale
`t ~ log 2 / 2` is compatible with the `hmargin` scale required by the
class margins `mu_q*`. If the scales are separated by orders of magnitude
with no tunable parameter, Line B dies as a P2 producer (B3 still stands
for the detector branch).

### 4.3 Line C - correction-remainder route (the 1116c contract)

Mechanism. `g(rho)` is itself the fixed-window construction with
node-restoring correction (records 1078/1079 lineage; D1 replay in 1089
and 1140). The defect `g.convSq - W.convSq` is a correction remainder
whose defining relations are the node equations; the `hbudget` derivation
would run through the correction's algebra (its coefficients solve a
linear system against the node values), not through norm estimates.

Zero-configuration entry: the correction's node equations
`{0, 1/2, 1} ∪ {rho, rho-conjugate}`.

Shared obligation: the true-correction mp-grade numerics is the SAME debt
as the M-side/C2 gap of the moment campaign (record 1140 work order item
1; the record-1116 abort finding named it "not scheduled"). Line C and the
M-side route share this producer; building it serves both.

Formal owner/gate boundary audit (record 1148): the existing selected-owner
construction supplies finite raw `laplaceAt` node equations, support, square
zeros, and tails, while `ICgate` is evaluated from the full archimedean and
visible-prime test values. No current declaration transports those node
equations into a gate sign or `hbudget`. Line C therefore needs a new
gate-level cancellation identity on the same owner; interpolation alone is
not a producer.

The first exact sub-target is now formal (record 1149):
`finitePrimeSum_eq_of_primePairMatch` cancels the complete visible-prime sum
when the two square owners match in the bilateral sum at `± log q` on the
union of their visible sets. This is a genuine Line-C consumer, not a
positivity premise. The open producer task is to obtain those real point
sums from the correction (or to replace them with an equivalent low-rank
residual identity); the existing finite Mellin interpolation does not do so
automatically.

Falsifier: record 1116's structural finding is the standing guard - the
model-class sign is configuration-local, and any candidate derivation must
reproduce the 13-constraint collision structure at `delta = 0` exactly
(numeric-probe law 65: build at the TRUE collision-resolved node set, not
a perturbed surrogate).

## 5. Producer admission checklist (anti-circularity gate)

A proposed producer statement is schedulable only if all five hold:

```text
+----+------------------------------------------------------------------------+
| A1 | Interface: output stated as P2ScalarOneWindowBudgetWitness fields     |
|    | (or a named refinement) on the pinned g(rho), n owner.                |
+----+------------------------------------------------------------------------+
| A2 | Zero-configuration use: the proof cites at least one rho-specific     |
|    | fact (node vanishing, detection value, D1 coefficient identity) that  |
|    | is unavailable for generic tests.                                     |
+----+------------------------------------------------------------------------+
| A3 | No smuggled conclusion: does not assume qw >= 0, any gate <= 0, RH,   |
|    | or an equivalent statement (record 1140 work order item 3).           |
+----+------------------------------------------------------------------------+
| A4 | No honest-envelope smallness: does not size the budget by triangle    |
|    | or norm estimates of the actual defect (section 2.1 DR2).             |
+----+------------------------------------------------------------------------+
| A5 | Pre-registered falsifier: a model-level instantiation with named      |
|    | direction (1116 rig or fake-zero rig) committed before the Lean       |
|    | attempt.                                                              |
+----+------------------------------------------------------------------------+
```

## 6. Schedulable pre-bricks

```text
+----+---------------------------+---------+---------------------------------+
| ID | Brick                     | Level   | Consumer                        |
+----+---------------------------+---------+---------------------------------+
| B1 | Identity audit: exact     | FORMAL  | Line S. DONE as record 1143     |
|    | statement chain from      | LANDED  | (module                         |
|    | ICgate(defect) to the     |         | C1P2DefectZeroSumIdentity,      |
|    | spectral/zero-sum form    |         | 5 declarations, standard        |
|    |                           |         | axiom audit): the zero-sum      |
|    |                           |         | form S3 and the positive-form   |
|    |                           |         | wall S5 are named theorems.     |
|    |                           |         | Fed the record-1144 Line-S      |
|    |                           |         | REFUTED verdict.                |
+----+---------------------------+---------+---------------------------------+
| B2 | Scale table: exact        | NUMERIC | All lines (feasibility datum).   |
|    | mu_q28/q38/q48 from       | LANDED  | DONE as record 1142: operative   |
|    | committed data; hbudget   |         | margins, corrected N floor at    |
|    | floor at n = 1; the       |         | n = 0/1, 6-13-order wall.        |
|    | detection-mass gap        |         |                                  |
+----+---------------------------+---------+---------------------------------+
| B3 | Bombieri chain completion | FORMAL  | Line B + detector branch (freeze |
|    | (exponential independence |         | item 3): slices 12i -> Theorem 8 |
|    | + Theorem-8 sign count)   |         | sign count.                     |
+----+---------------------------+---------+---------------------------------+
| B4 | True-correction mp-grade  | OPEN    | Line C + M-side/C2 (shared       |
|    | numerics, pre-registered  |         | producer; the 1116c contract).  |
+----+---------------------------+---------+---------------------------------+
```

B1 and B2 have landed and consumed the Line-S falsifier (record 1144:
REFUTED as stated).  B4 is already owed by the window campaign; B3 is
independent detector-branch strengthening and now carries the Line-B
falsifier's formal side alone.

Record 1147 lands the Line-B same-owner bridge contract and its `SourceRH`
consumer.  This is a FORMAL narrowing of the producer obligation, not a sign
theorem: the Bombieri-to-`qw` equality and finite per-zero eigensystem data
are still OPEN.

Record 1150 adds a FORMAL bilateral-observable reduction.  For a same-owner
formula test, both the finite-prime terms and the archimedean numerator see
`F.test y + F.test (-y)`; the archimedean term additionally sees `F.test 0`.
Thus bilateral profile equality gives the weaker `PrimePairMatch` needed for
finite cancellation, while full profile equality plus the origin value makes
the archimedean terms equal as well.  The resulting defect-gate theorem says
that complete profile matching yields exact zero, not a sign.  This sharpens
the live Line-C producer target to finite bilateral samples with a genuine
archimedean/low-rank residual estimate on the healthy owner; P2 remains OPEN.
The same brick now exposes the residual identity itself: the numerator
difference is the weighted bilateral-profile difference minus the origin
difference, and profile matching only on the visible-point image already
implies finite-prime cancellation.  These are FORMAL interface facts; they do
not provide the missing envelope or sign.
The local-match theorem is now wired directly to the defect gate, so a future
producer can state its finite arithmetic obligation as a profile condition
without reopening the prime-index bookkeeping.
The same module also reads each finite-prime term as the real weight
`Λ(n)/√n` times the real bilateral profile and provides the corresponding
nonnegative-sum adapter.  This is a FORMAL sign primitive only; the orbit
detector has not been shown to satisfy its profile-positivity premise.
The odd-profile corollary is also FORMAL: an odd correction has zero bilateral
profile and contributes zero to every finite-prime term and to the full
finite-prime sum.  This identifies a genuine arithmetic-blind direction in
the even/odd correction family, while leaving its archimedean anchor sign
open.
Record 1151 strengthens this to a FORMAL full-gate decomposition: finite-prime
additivity holds for arbitrary compact-log sums after unioning visible-index
sets, and for an even/odd pair the polarized cross is odd and disappears from
both gate channels.  Hence `ICgate((f+g)□) = ICgate(f□) + ICgate(g□)`; the odd
correction's own square remains arithmetic-visible, so the diagonal sign
problem is not solved.
The same FORMAL brick now feeds back through the vanishing identity:
`qw(f+g) = -(ICgate(f□) + ICgate(g□))`.  Its paired consumer shows that two
nonpositive diagonal gates suffice for the desired `qw ≥ 0`; no such two-gate
sign theorem is currently available for the pinned orbit detector.
The B5 consumer is now explicit: the two diagonal inequalities imply the
healthy summed-owner `orbitWindowSemiLocalGate`, and healthy detector data then
feeds the existing `qw_nonneg` consumer.  This remains a producer contract;
the diagonal inequalities for the pinned orbit detector are still OPEN.

Record 1152 adds a FORMAL narrow sufficient condition for those diagonal
inequalities.  If each square test has support in `(-R,R)` with `0 < R < 1`
and `R < log 2`, then the visible-prime sum vanishes; the existing narrow
archimedean budget theorem therefore gives each diagonal `ICgate ≤ 0`.  The
even/odd consumer then yields `qw ≥ 0` for the summed healthy owner.  This is
only a conditional interface: no result identifies the pinned orbit detector
with either narrow-support class, so P2 remains OPEN and the route authority is
unchanged.
The same FORMAL brick now derives `CC20VanishesOn` directly from oddness plus
the three nodal equations, so future pair producers need not restate the
vanishing predicate; this is bookkeeping/interface compression only, with no
new detector sign.
It also proves a FORMAL no-go: under prime-free square supports, a positive
sum of the two archimedean diagonal terms rules out simultaneous
`ICgate ≤ 0`.  Thus the ROOT-side positive-anchor pair cannot be silently
reused as the P2 nonpositive-diagonal witness.

Record 1153 adds a direct FORMAL same-owner consumer: archimedean nonpositivity
plus nonpositivity of the real bilateral profile at every visible prime power
forces the finite-prime sum nonpositive and hence `qw ≥ 0`.  The sign direction
is material—profile nonnegativity would contribute with the opposite sign in
`qw = -arch - finitePrimeSum`.  The pinned orbit detector is not yet shown to
satisfy either premise, so P2 remains OPEN.

Record 1154 packages those two signs as `P2BilateralProfileSignWitness` and
composes it with the existing healthy-detector contradiction to `SourceRH`.
This fixes the exact B5 producer quantifier: one witness on the same healthy
detector owner for every right-oriented off-line zero.  Constructing that
witness for the pinned orbit remains the sole open analytic task in this
subroute.

Record 1155 supplies a FORMAL fixed reference window for the scalar witness:
the existing `narrowArchRoot` has strict negative `ICgate` because its square
is prime-free and its archimedean term is strict negative.  Thus the window
certificate and its positive margin can be instantiated exactly; the remaining
P2 producer obligation is the detector-to-window defect budget (or an
alternative direct profile sign), not construction of a negative reference
gate.

Record 1156 adds a FORMAL fixed-window adapter.  The new
`P2NarrowReferenceCanonicalWitness` expands to the existing canonical P2
witness with `W = narrowArchRoot`, while the root support, gate certificate,
and square-owner seminorm bounds are supplied by the shared owner.  The
producer payload is therefore reduced to detector support, the same-owner
`ICdefect` budget, and its margin comparison.  This is contract compression,
not a detector-to-window estimate; P2 remains OPEN and route authority is
unchanged.
The adapter also exposes the exact same-owner `SourceRH` exit, so this fixed
window is now a complete producer socket: only the detector-side budget and
margin need an analytic construction.

Record 1157 now gives the decisive FORMAL no-go for that scalar socket.  For
any `HealthyYoshidaDetectorData rho g`, a
`P2NarrowReferenceCanonicalWitness g` implies the defect gate bound through
the canonical budget consumer; together with the fixed root certificate and
margin, `no_stageB_budget_of_qw_negative` derives `False` from the detector's
strictly negative `qw`.  Therefore this fixed-window triangle-budget contract
cannot be a producer for the live detector.  The active P2 targets are the
direct bilateral-profile sign witness or a genuinely signed semi-local trace
comparison; the route authority is unchanged.

Record 1158 strengthens the no-go to the full formal `P2OneWindowBudgetWitness`
contract, with arbitrary `W`, `mu`, and support radius.  Its own consumer
would produce `orbitWindowSemiLocalGate` and hence `qw(g) ≥ 0`, contradicting
the strict negative value carried by `HealthyYoshidaDetectorData`.  Therefore
changing the reference window cannot rescue the absolute-value Stage-B
budget; further scalar-budget variants are frozen.  Work now targets the
signed bilateral-profile route or a genuinely new semi-local trace theorem.

Record 1159 sharpens the signed route with a FORMAL aggregate socket.  The
finite-prime sum is exactly the weighted sum of the real bilateral profile,
so a producer need only prove one same-owner inequality
`archimedeanTerm + weightedProfileSum ≤ 0`; pointwise signs at individual
prime powers are optional.  This is a genuine weakening of the producer
premise, not a stored `qw` conclusion, and its B5 `SourceRH` consumer is
landed.  Constructing the aggregate inequality for the orbit detector remains
OPEN.

Record 1160 proves the aggregate socket is exact: under triple vanishing,
`qw(g) ≥ 0` is equivalent to
`archimedeanTerm(g²) + Σ Λ(n)/√n·Re(profile(log n)) ≤ 0`.  The former
pointwise profile witness is formally mapped into the aggregate witness, so
the aggregate formulation is a true weakening of the producer interface and
not a change of mathematical owner.  The orbit-detector inequality itself is
still OPEN.

Record 1161 formally identifies the existing `orbitWindowSemiLocalGate` with
the aggregate profile witness: after the exact finite-prime readback, a gate
for `g` constructs `P2BilateralProfileAggregateWitness g`.  This is an
interface composition only; the Stage-B contraction fields and the
detector-specific gate inequality remain unconstructed.

Record 1162 adds the Hermitian real-value adapter: for every convolution
square, `bilateralProfile(y) = 2 * Re(g²(y))`.  A producer may therefore
submit the aggregate estimate using only real evaluations of the square; the
formal exit converts it to the existing profile witness.  This is still an
interface reduction, not the missing detector-specific sign estimate.

Record 1163 also composes the Stage-3 positive-trace route with this socket:
an actual `PositiveTracePairLimitFamily` on the same `CompactLogTest` yields
the aggregate witness through the exact `qw` equivalence.  Thus Stage-3 and
direct profile estimation are two producer interfaces for the same P2 owner;
neither is populated for the pinned orbit detector yet.

Record 1164 closes the interface audit with an `iff`: the aggregate witness
and `orbitWindowSemiLocalGate` are exactly the same proposition after finite
prime readback.  The live P2 obligation is therefore one gate producer, not a
choice among inequivalent formulations.

Record 1165 adds the support-controlled real readback: when the square is
supported in `(-B,B)`, the aggregate finite-prime term is exactly a sum over
`range (ceil(exp B)+1)`.  This exposes the detector's finite arithmetic owner
as an explicit cutoff for the next analytic estimate; it proves no sign.

Record 1166 packages the explicit-cutoff producer contract
`P2BilateralProfileRangeWitness`.  Given the detector square's support in
`(-B,B)`, its range inequality converts exactly to the aggregate/gate socket.
For the pinned orbit, `B = 2(n+2)` is already exported by the support
construction; only the signed range estimate remains analytic.

Record 1167 wires that explicit-range contract into the pinned B5 exit
quantifier.  For every right-oriented off-line zero, a same-owner detector
with source support radius `n+2` and the range witness now yields `SourceRH`
formally: source support gives square support `B = 2(n+2)`, then the range
adapter gives the aggregate witness and the existing `qw ≥ 0` consumer.  The
only remaining producer content is the signed finite-range inequality itself;
P2/RH remain open.

Record 1168 adds the parallel positive-operator producer adapter.  A
same-owner `PositiveTraceOperatorLimitFamily` (positive trace-class operators,
vanishing remainder, and `qw` readback) now yields the identical aggregate P2
witness as the already wired self-pair family.  This broadens the producer
socket without changing the owner or the quantifier: constructing either trace
family for the pinned orbit is still open.

Record 1170 gives the matching quantifier-level exit for the self-pair trace
route.  A fixed-basis `PositiveTracePairLimitFamily` for each right-oriented
off-line detector now implies `SourceRH` through the same aggregate socket.
The pair/operator distinction is therefore purely a producer-construction
choice; neither construction is presently available for the pinned orbit.

Record 1171 wires the Bombieri Line-B finite-chain bridge into the same P2
socket.  Once `BombieriP2BridgeData` proves its owner equality
`qw = lam * mass`, the existing finite Wirtinger positivity yields the P2
aggregate witness and a direct healthy-B5 `SourceRH` exit.  The owner equality
and per-zero finite data remain the open Line-B producer obligations.

Record 1172 is superseded by the formal bare-convolution obstruction.  The
Stage-3 factor used there is the whole-line translation-invariant convolution;
`C1Stage3BareHSObstruction.bareHS_iff_zero_test` proves its Hilbert--Schmidt
premise holds iff the test is zero.  Since a healthy detector is nontrivial,
that FRONTIER-HS contract cannot be a P2 producer.  Any surviving Stage-3
route must use a genuinely windowed or renormalized factor.

Record 1174 wires the viable `ProjectionCutoffLimitContracts` owner into P2.
The cutoff operator `C_n† K C_n` is already positive and trace-class; its two
remaining fields are exactly remainder convergence and same-owner `qw` readback.
Supplying those contracts for the pinned detector now gives the aggregate
witness and `SourceRH` formally.  This is the live Stage-3 positive route; it
does not reuse the refuted bare Hilbert--Schmidt premise.

Record 1175 makes the first of those analytic obligations consumable without
unfolding it: the formal theorem
`tendsto_norm_cutoffKernelInsertionSandwich_zero_of_kernelCompatibility`
maps `kernelCompatibilityAlongCutoffs` to `D₁,n → 0` in operator norm.  This is
an interface-only implication; neither the compressed-kernel estimate nor the
same-owner trace readback is proved.  The second defect remains subject to the
existing unbounded-trace no-go for a fixed response.

Record 1176 strengthens the Bombieri finite-certificate lane without changing
the P2 owner.  The readback leaf now proves exact conjugation compatibility and
evenness of the normalized sinc, then uses the paired correction terms to prove
that `K* x y t` is self-conjugate for real parameters.  Consequently every
finite entry `H x y t` is self-conjugate, and the Gamma matrix is Hermitian for
arbitrary finite maps `gamma : Fin n → Real`, including repeated ordinates.
This is FORMAL algebra and makes the finite spectral/Gram route honest; it does
not supply the same-owner equality `qw = λ · mass`, a per-zero finite
certificate, or the detector-specific P2 sign.  Those remain OPEN producer
obligations.

Record 1177 adds the next finite consumer interface: from the Hermitian matrix
 theorem, `bombieriHMatrix_quadraticForm_im_zero` proves that
 `star z ⬝ᵥ (H Γ;t *ᵥ z)` has zero imaginary part for every finite vector `z`.
This is FORMAL and makes “finite quadratic form is real” available to a future
positivity certificate.  It asserts no nonnegativity, no spectral lower bound,
and no same-owner `qw` readback; the detector-specific P2 producer remains
OPEN.

Record 1178 completes that finite consumer step.  The new formal identity
`bombieriHMatrix_quadraticForm_eq_KstarGram` rewrites the weighted finite
`H(Γ;t)` quadratic form exactly as `bombieriKstarGram`; composing it with the
existing 8.11–Wirtinger theorem yields
`bombieriHMatrix_quadraticForm_eq_ofReal_nonneg` for `t > 0`.  This is genuine
finite positivity and allows repeated ordinates, but it still does not identify
the form with `qw g`, construct the per-zero detector certificate, or close the
healthy `CompactLog` P2 gate.  Those producer obligations remain OPEN.

Record 1179 makes the finite eigenvalue readback speak directly in the new
matrix owner: `lambda_mass_eq_bombieriHMatrix_quadraticForm` identifies
`(lam : Complex) * ofReal (bombieriWMass gamma z)` with the weighted Hermitian
`H` quadratic form under the finite eigen-relation and reciprocal identity.
This is FORMAL and removes an unnecessary detour through the raw Gram name.
It still leaves the owner-changing equality `qw g = lam * mass` and the
per-zero finite data as OPEN producer obligations.

Record 1180 exposes a direct alternative producer contract,
`BombieriQuadraticP2BridgeData`, whose sole owner-changing field is the
explicit equality `qw g = Re⟨w,H(Γ;t)w⟩`.  The finite positivity theorem from
records 1178–1179 then supplies `qw ≥ 0`; the contract is wired through the
healthy B5 aggregate and `SourceRH` exits.  This is FORMAL interface work, not
a new sign assumption: constructing the same-owner equality and the finite
data for each pinned orbit detector remains OPEN.

Record 1181 corrects the status of record 1180.  The direct quadratic socket is
formally incompatible with the healthy detector branch: the finite theorem
forces the matrix form, and hence `qw` under its equality field, to be
nonnegative, while `HealthyYoshidaDetectorData` forces the same `qw` strictly
negative.  The new negative guards
`not_bombieriQuadraticP2BridgeData_of_healthyDetectorData` and
`not_nonempty_bombieriQuadraticP2BridgeData_of_healthyDetectorData` therefore
show that the socket cannot coexist with a healthy detector.  Record 1182
corrects the resulting over-strong NO-GO wording: this is the expected
conditional contradiction consumer for any successful P2 producer, not an
independent route refutation.  Its conditional exits remain auditable
interfaces, and active work may use them alongside the signed
semi-local/profile or genuine renormalized trace routes.

The record-1182 adapter
`BombieriQuadraticP2BridgeData.of_bombieriP2BridgeData` transports any existing
Line-B finite eigen/mass producer to the direct quadratic spelling by taking
real parts of `lambda_mass_eq_bombieriHMatrix_quadraticForm`.  The direct socket
therefore remains a valid conditional interface; constructing its
same-owner equality from the pinned detector is still OPEN.

Record 1183 adds the pinned direct-quadratic exit
`sourceRH_of_pinnedOrbitDetector_p2BombieriQuadraticP2BridgeData`.  Its
producer must return one `g,n` carrying healthy detector data, the exported
`n+2` support interval, the strict finite visible-prime cutoff, and the direct
Hermitian contract on that same `g`.  This is FORMAL quantifier tightening;
the same-owner matrix equality remains the open analytic obligation.

Record 1184 adds the residual-aware direct-form socket
`BombieriQuadraticResidualP2BridgeData`.  It replaces an exact finite-form
equality by an explicit real residual and the inequalities
`|residual| ≤ tailBound ≤ Re⟨w,Hw⟩`; finite positivity then proves the desired
`qw ≥ 0` without storing that conclusion.  The socket is wired to both the
aggregate profile owner and the pinned detector exit.  This is the preferred
finite-form interface if the spectral tail cannot be eliminated exactly; the
residual readback and its domination remain OPEN analytic producer fields.

Record 1185 makes the residual owner explicit.  The new theorem
`spectralHeightShellTail_abs_re_le_normTail` gives a two-sided bound for the
high-shell tail of the same `g.convolutionSquare`; the new
`BombieriQuadraticSpectralTailP2BridgeData` sets the Bombieri residual to that
tail and derives the generic residual socket without an arbitrary residual
field.  Its same-owner decomposition and tail-to-main-term domination remain
OPEN producer obligations, so this is a formal interface tightening, not a
P2 closure.

Record 1186 adds the FORMAL lemma
`bombieriHMatrix_quadraticForm_pos_of_eigen`: in the nonzero reciprocal
eigenvector branch, the finite Hermitian main term is strictly positive.  It
provides the margin that a future same-owner spectral-tail producer must
beat, but it does not select a cutoff or prove the Bombieri-to-`qw` residual
identity.  P2 remains OPEN on those producer obligations.

Record 1187 combines the strict finite-form margin with the exact shell-tail
cutoff theorem.  `exists_spectralTail_normTail_lt_bombieriQuadraticForm_of_eigen`
now supplies a cutoff whose same-owner spectral norm tail is below the finite
main term.  Thus residual domination is no longer an independent producer
field; the remaining Bombieri bottleneck is the exact `qw`–finite-form–tail
decomposition at the chosen cutoff.

Record 1188 packages that cutoff canonically.  The new
`BombieriQuadraticCanonicalSpectralTailP2BridgeData` carries the finite
eigen/reciprocal data and asks only for the same-owner `qw` decomposition at
the cutoff selected from the proved positive main-term margin.  Its residual,
aggregate, and pinned `SourceRH` consumers are FORMAL; the decomposition
itself remains OPEN.

Record 1189 corrects the sign/interface shape of that decomposition.  The
formal shell identity is additive:
`qw = finite spectral prefix + high-shell tail`.  The spectral-tail contracts
therefore now expose `qw = quadratic + tail`; only the generic residual adapter
negates the tail when using its subtractive convention.  A new split-prefix
contract asks for the narrower producer equation that the finite spectral
prefix at the canonical cutoff equals the Bombieri Hermitian quadratic form.
The conversion to the canonical tail socket, its positivity consumer, and a
pinned `SourceRH` exit are FORMAL.  The prefix-to-Bombieri identification is
still OPEN; no sign conclusion or RH claim is added.

Record 1190 aligns the remaining prefix socket with Bombieri's native
`qIntegrand` owner.  The new
`BombieriQuadraticCanonicalQIntegrandPrefixP2BridgeData` asks for equality of
the finite same-owner spectral prefix with the `qIntegrand` interval integral
minus `endpointCorrection`.  Existing formal readbacks then convert this to
the `KstarGram` and Hermitian quadratic forms, and the aggregate/pinned B5
consumers remain available.  This is FORMAL owner alignment only; the
finite-prefix-to-qIntegrand equality for the selected healthy detector is
still OPEN.

Record 1169 closes the quantifier-level exit for the general positive-operator
route as well.  With one fixed Hilbert basis, a producer supplying a healthy
detector and a `PositiveTraceOperatorLimitFamily` for every right-oriented
off-line zero now implies `SourceRH` by the same-owner consumer.  This is only
an exit theorem: no such family has been constructed for the pinned orbit.

The G2 repair of the 1139 concrete q28 moment checkpoint has now landed as
record 1145/RED-10.  The Rat certificate was split into four isolated value
modules plus the bridge/prefix consumer; the certificate and audit builds
are green, with only the standard three axioms and no `sorryAx`.  This
unblocks the concrete q28 `hcert` input mechanically; it does not prove the
M-side true-table interval or the detector-specific P2 budget.

## 7. Scope guards

1. No route-selection change: [`003`](003_b1_b5_minimal_exit_route_selection.md)
   rules; P2 remains the single open C3 obligation per
   [`004`](004_endpoint_literature_interface_audit.md) section 4.
2. This record registers designs and guards; it does not close, retire, or
   unfreeze anything, and no B1/B5 boundary is moved.
3. Evidence labels follow 004 section 1. Raw or unresolved numerical
   observations belong in `docs/proofs/` and do not by themselves change a
   map conclusion.
4. Record 1145 closes only the G2 mechanical checkpoint. Record 1146 is a
   FORMAL interface audit confirming that the M-side true-table interval is
   still an independent producer obligation; the shared point with Line C is
   B4.
5. RH is not claimed.
