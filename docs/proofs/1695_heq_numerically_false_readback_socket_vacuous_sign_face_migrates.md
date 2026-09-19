# 1695 — the G8 readback socket is formally vacuous (the A1 pattern inside the lane, now a brick); rig: the shear-channel trace reads +0.021 vs qw −0.913 at the detector test; Erratum on map 045's sign face — no single positive trace can carry the sign, the carrier must be a signed four-channel book

Date: 2026-09-19.

Status: one F52-calibrated numeric rig (`scripts/heq_trace_check_1695.py`,
run in WSL2; results `results/1695_heq_trace_check.json`) + one new Lean
brick with Audit (`ConnesWeilRH/Dev/C1G8P4ReadbackSocketVacuity.lean`,
machine-checked).  RH is not claimed.

This record executes map 043/045's pending de-risk item — "check `heq`
before betting the lane on it" — and the answer is decisive in the wrong
direction: the aggregate equality is numerically false at the canonical
test, and the formal reason was already sitting in the committed tree.
Three findings: the rig verdict (§1); the structural explanation and its
formalization — the readback socket cannot be filled at any healthy-detector
test, so the R5 sign-face route is closed by a two-line composition (§2);
the map correction — the sign face was placed on the wrong operator class,
and the annular-Gram migration (1635–1674) is confirmed as the only live
sign carrier (§3).

## 1. The rig verdict: `Re tr_carrier(A_end) = qw(g)` is FALSE at the test

Instance (all committed definitions, hand-derived per F27/F28): `lambda* =
e^{-1}` (`a = -1`), `g` = even real `C_c^inf` bump with `supp g ⊆
[-0.42, 0.42]`, `family = {(2,1)}`.  Operator stack pinned from committed
defs: `C` = convolution by `h = conj g(-·)`; `W = C†C`; `N = E⁻¹P_targetE −
P_source` with `E = E_2 = id − (1/√2)T_{−log 2}`; `P_source` = meet of
`{supp u ⊆ [a,∞)}` and `{Hu ∈ [a,∞)}` read through the Hardy–Titchmarsh
readback `(Tu)^ = m(ξ)(Fu)(−ξ)`; `P_target` = `radial ⊓ E(archFourier)`;
`H_grid[f,k] = (1/N)Σ_j m(ξ_j)e^{+2πiξ_j(t_f+t_k)}` (= the 1694 v4 matrix;
Mathlib FT convention `e^{−2πixξ}`, `Gammaℝ s = π^{−s/2}Γ(s/2)` verbatim).

Results (`results/1695_heq_trace_check.json`):

```text
+------------+------+----------------------+-------------+--------------+-----------+----------+
| m-slot     |    N | dims (meet/archF/tgt)|         LHS |           qw |     ratio |    hcore |
+------------+------+----------------------+-------------+--------------+-----------+----------+
| m (comm.)  | 1024 | 117/544/64           | +0.02117170 | -0.91262846  | -0.023199 | 0.885784 |
| m (comm.)  | 2048 | 281/1088/128         | +0.02082372 | -0.91262846  | -0.022817 | 0.873495 |
| conj m     | 1024 | 64/544/64            | +0.99750549 | -0.91262846  | -1.093003 | 2.948368 |
| conj m     | 2048 | 159/1088/132         | +0.42323316 | -0.91262846  | -0.463752 | 2.451288 |
+------------+------+----------------------+-------------+--------------+-----------+----------+
  qw = pole - arch - finite = +1.252931 - +2.163934 - +0.001626 = -0.912628
  (g even real => F even; finite = (log2/sqrt2)*2F(log2), only n=2 in supp F)
```

Verdicts:

- **The measured aggregate is nowhere near `qw`.**  LHS reads `+0.021`
  while `qw = -0.913`: the sign demanded by the equality is not even
  present.  The gap is `O(1)` and does not close under refinement (drift
  `1.7%` from N=1024 to N=2048 — grid convergence, not a finite-size
  artifact).
- **F66 reconfirmed numerically.**  The committed `m̃(+ξ)` orientation is
  N-stable (0.0212 → 0.0208); the conj orientation is N-unstable (0.9975 →
  0.4232, dims drift, hcore drifts 0.5) — the discriminator from 1694 §3
  reproduces on a different rig shape.
- **The failure is structural, not a bug** (§2): no correct implementation
  of this socket could have read a negative number.

**Correction (operator object).**  The rig's `A_end` was assembled with
`Nop = E⁻¹P_targetE − P_source` (the reduction-side difference,
`CCM24FiniteSGatePhysicalObliqueShearReduction.lean:92`).  On the carrier
columns `P_source` acts as the identity (`Q_c` spans the meet), so
`(I + Nop)|carrier = S|carrier` and the rig's LHS is the FOURTH CHANNEL
`C† S W S†|carrier` alone — NOT the committed endpoint operator, which
sandwiches the shear ALONE: `g8AdjointShearGram = (id + S†)† ∘ D ∘
(id + S†)` (`C1G8AdjointShearGram.lean:59-66`), whose carrier trace is
`hcore + cross + adjoint-cross + fourth ≈ 0.886 + (cross book) + 0.021`.
The committed `heq` names THAT object.  The brick of §2 — not the rig —
is therefore the authoritative closure of `heq`: it covers every readback
data at once, hence the committed sandwiched object too.  What the rig
establishes is the channel datum: the fourth channel books `+0.021`, so
for the committed `heq` to hold at the test the cross channels would have
to book `≈ -1.82` — and §2 proves they cannot (any successful book gives
`qw ≥ 0`).

## 2. The structural finding: the readback socket forces `qw ≥ 0`, already in the tree

The de-risk found the reason the equality cannot hold, and the reason is
not analytic — it is the sign of a positive operator, and it is ALREADY
FORMAL:

- every source cutoff trace is nonnegative:
  `g8SourceCutoffPairData_trace_re_nonnegative`
  (`C1G8AdjointShearGram.lean:558`);
- hence ANY `G8SameOwnerReadbackData` — whose readback limit is `qw` up to
  a vanishing remainder — forces `0 ≤ qw`:
  `qw_nonnegative_of_g8SameOwnerReadbackData`
  (`C1G8AdjointShearGram.lean:1056`, through the committed
  `PositiveTraceOperatorLimitFamily` engine);
- the healthy-detector bridge chain forces `qw < 0` at every detector test
  (`weilSquareSumPositive_iff_spectralWeilValue_neg` +
  `qw_eq_spectralWeilValue_centerTwo`);
- and the committed P3 capstone's OWN PROOF BODY
  (`C1G8P3Contradiction.lean:38-48`) is exactly this contradiction:
  `qw ≥ 0` from the readback hypothesis, `qw < 0` from the detector,
  `False`.  P3 was never a capstone "waiting for two inputs"; it is the
  theorem that its two inputs are JOINTLY UNSATISFIABLE — the A1 pattern
  (records 1225/1226, Bombieri aggregate socket) inside the G8 lane.

New brick (`C1G8P4ReadbackSocketVacuity.lean`): the R5 route closes in one
composition — `g8R5ZeroRemainderReadbackData` turns `hcore + heq` into
readback data (`C1G8R3SameOwnerGateNormalForm.lean:142`), P3 then kills it:

```lean
theorem false_of_survivorCore_aggregateEq_and_healthyDetector
    (rho) (owner) (lambda) (family) (globalBasis) (sourceBasis)
    (hcore : Summable fun i : ρ => ‖((sourceInclusion lambda).adjoint ∘L
      rootConvolution owner ∘L sourceInclusion lambda) (sourceBasis i)‖ ^ 2)
    (heq : (ordinaryTraceAlong sourceBasis
      (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
      = C1SameOwnerWeil.qw owner.sourceTest)
    (hdetector : HealthyYoshidaDetectorData rho owner.sourceTest) : False
```

Reading: **the aggregate equality is provably false at every
healthy-detector test** (detector existence is unconditional,
`CC20YoshidaConstruction.lean:2690`).  §1's numeric failure of `heq` was
therefore not an accident of the test — it is the theorem, measured.

Consequences, precisely:

- `qw_nonnegative_of_g8_survivorCore_and_aggregate_eq`
  (`C1G8R5AggregateExpansion.lean:318`) can never fire where it matters:
  its `heq` hypothesis is false at every test with `qw < 0`, and `qw ≥ 0`
  for all g IS RH.  The G8 positive-trace consumption chain is not
  "one theorem short"; it is complete and its completion proves the chain
  cannot start.
- This is not wasted machinery: the mass face (survivor core), the
  cutoff-pair ledger, and the four-term factorization are operator facts
  independent of the sign, and the annular-Gram lane consumes them (§3).

Erratum on 1694 §5 (map 045): the "sign face = heq" placement is retracted
as a ROUTE (it remains the true logical content of the gate, but there is
no proof route through it — the object whose trace would have to equal qw
is positive, so the equality is anti-sandwiched: LHS ≥ 0 always, RHS < 0
at tests).  Erratum on 1694 §1's closing caveat: "even a proof that the
carrier is {0} would not reach the gate" — sharpened to: no proof of heq
exists at detector tests, proved, not conjectured.

## 3. Map 046 — the sign must ride a DIFFERENCE of positive objects, not any single positive trace

The diagnosis generalizes: any identification of the form
`qw = Re tr(T)` with `T` POSITIVE is dead on arrival — LHS ≥ 0
unconditionally, so it can only ever prove RH to itself.  Two concrete
corpses, both committed vocabulary:

- the G8 endpoint operator is `D†D` (four-term form, `:273`, positive by
  `:112`) — closed as a sign carrier, with the brick above as the seal;
- the annular Gram is `W_ann† ∘L W_ann`
  (`C1G8R3SourceRootFiniteWindowCriterion.lean:68-72`), and its trace is
  the column-energy sum `∑' i, ‖W_ann(basis i)‖²` (committed at `:95-108`)
  — positive BY CONSTRUCTION.  Map 046's originally drafted "sign de-risk
  on the annular Gram" is therefore resolved analytically before any rig:
  the annular Gram is a MASS producer (the 1659 equivalence with the
  survivor core is exactly this), never a sign carrier.  The 1635–1694
  lane's `0 ≤ Re tr Gram ≤ B` content is an upper-bound statement about a
  positive quantity; it cannot read negative.

Where can a negative number legitimately appear?  Only in a SIGNED SUM —
a difference of positive traces.  The committed vocabulary already has
the container: the four-channel finite-window ledger
(`C1G8AdjointShearGram.lean:1067`, cutoff base/cross/adjoint-cross/N†WN
channels).  The §1 rig supplies first numeric content, with one caution:
its LHS is the UNCUTOFF four-term aggregate

```text
  hcore  = Re tr JWJ|_carrier    ≈ +0.886   (mass face; the W-channel)
  LHS    = Re tr A_end|_carrier  ≈ +0.021   (uncutoff signed 4-channel sum)
  qw                           = -0.913
  gap = qw - LHS               ≈ -0.934     (what a correct carrier must book)
```

The committed ledger is NOT this uncutoff aggregate: its channels carry
their own windows (`cutoffLower/cutoffUpper ... n`) and the readback is
the n → ∞ limit of the WINDOWED signed sum.  Whether the limit books
`qw` is untested — the rig tested only the uncutoff object.

1. **Four-channel ledger rig (1696)**: at the same test instance, compute
   the four WINDOWED channels of the COMMITTED object (shear-alone
   sandwich: base = `J†B†DB`, cross = `J†B†SDB`, adjoint-cross =
   `J†B†DS†B`, fourth = `J†B†S†DS B`, with `B` the kernel window) for
   growing window, and read the book: the §2 brick predicts the total
   stays `≥ 0` and misses `qw` — the rig locates WHICH channel would
   have had to book the missing `≈ -1.8` and confirms it does not.
   Outcome either way closes the "maybe the cross channels carry the
   sign" escape hatch with data.
2. Formalize the channelwise trace identity the rig verifies
   (machine-checkable where the estimates are limit-algebra; the
   analytic channel estimates are the real work).
3. Mass face and its annular-Gram producer: unchanged (the 1659
   equivalence, the 1640 Laguerre obligations, B4 at 1673 — all feed the
   carrier side, which both routes need).

Stop word for this lane is unchanged: gate certificate.

## 4. Lessons

- Read the PROOF BODY, not just the statement, before building on a
  socket: P3's body already contained the vacuity argument; a statement
  read (`:28-48` summary) said "capstone", the body said "joint
  unsatisfiability".
- v4.30 name notes: `Set.Iio_mem_nhds` is not a valid constant (v4.30
  renamed the neighborhood-of-a-point bounds to
  `eventually_lt_nhds (hab : a < b) : ∀ᶠ x in 𝓝 a, x < b` /
  `eventually_gt_nhds`, to_dual-generated in
  `Mathlib/Topology/Order/OrderClosed.lean:227`); `ge_of_tendsto` remains
  absent.  For "limit of a nonnegative sequence is nonnegative", the
  shortest v4.30 route in this tree is the committed
  `qw_nonnegative_of_positiveTraceOperatorLimitFamily` engine, not limit
  calculus.
- An even-real test `g` makes `F` even and the finite sum a single prime
  power (`n=2`): the cleanest rig shape for sign checks.
