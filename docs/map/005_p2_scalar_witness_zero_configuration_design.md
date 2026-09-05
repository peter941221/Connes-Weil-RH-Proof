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

### 2.2 The scale wall (NUMERICAL, design audit)

The `hbudget` left side has an explicit floor once the support radius is
pinned. At the `n = 1` orbit (support `Ioo (-(n+2)) (n+2) = Ioo (-3) 3`):

```text
N = ceil (exp 3) + 1 = 21,   N * log N ≈ 64
prime-side floor ≈ 64 * 2 * (s0 g.convSq + s0 W.convSq)
arch side        = |log (4π) + γ| * s0 (defect) + Carch
```

The two comparison scales are the committed window margins
`mu_q* = -Q*.U` (record 1118 whitened class data) and the detector's
positive gate mass (record 1116 model twin: `GATE / f0 = +0.45698` at the
true `delta = 0` configuration). Pre-brick B2 (section 6) tabulates the
exact gap; the design-relevant fact is that the gap is expected to span
several orders of magnitude, which no estimate-based mechanism can cross.
This is the quantitative face of DR2.

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

Mechanism. Rewrite `ICgate (defect)` through Z3 into its zero-sum form.
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
| B1 | Identity audit: exact     | FORMAL  | Line S. Verify the statement-   |
|    | statement chain from      |         | level chain ICgate(defect) ->   |
|    | ICgate(defect) to the     |         | zero-sum form via Z3 +          |
|    | spectral/zero-sum form    |         | defectGate_singleton_eq_sub;    |
|    |                           |         | pin sign and normalization.     |
+----+---------------------------+---------+---------------------------------+
| B2 | Scale table: exact        | NUMERIC | All lines (feasibility datum).   |
|    | mu_q28/q38/q48 from       |         | Pull -Q*.U from committed data; |
|    | committed data; hbudget   |         | compute the section-2.2 floor   |
|    | floor at n = 1; the       |         | at the pinned orbit; tabulate   |
|    | detection-mass gap        |         | the detection-mass gap.         |
+----+---------------------------+---------+---------------------------------+
| B3 | Bombieri chain completion | FORMAL  | Line B + detector branch (freeze |
|    | (exponential independence |         | item 3): slices 12i -> Theorem 8 |
|    | + Theorem-8 sign count)   |         | sign count.                     |
+----+---------------------------+---------+---------------------------------+
| B4 | True-correction mp-grade  | PREREG  | Line C + M-side/C2 (shared       |
|    | numerics, pre-registered  |         | producer; the 1116c contract).  |
+----+---------------------------+---------+---------------------------------+
```

B1 and B2 are cheap and unblock the falsifiers of section 4; B4 is already
owed by the window campaign; B3 is independent detector-branch
strengthening.

## 7. Scope guards

1. No route-selection change: [`003`](003_b1_b5_minimal_exit_route_selection.md)
   rules; P2 remains the single open C3 obligation per
   [`004`](004_endpoint_literature_interface_audit.md) section 4.
2. This record registers designs and guards; it does not close, retire, or
   unfreeze anything, and no B1/B5 boundary is moved.
3. Evidence labels follow 004 section 1. Raw or unresolved numerical
   observations belong in `docs/proofs/` and do not by themselves change a
   map conclusion.
4. The G2 repair of record 1139 and the M-side interval work are
   unaffected by and independent of this record; the shared point is B4.
5. RH is not claimed.
