# 1693 — The Kolmogorov ceiling is machine-checked; Erratum G (1682's carrier conflation); map 044 redrawn; Laguerre re-scoped; the completion map

Date: 2026-09-19.

Status: proof record (paper level, hand-derived) + one machine-checked
engine brick (`ConnesWeilRH/Dev/C1G9R2KolmogorovCeiling.lean` + Audit;
build `build-logs/1693_kolmogorov_ceiling_build.log`, 8476 jobs, the
three standard axioms, zero sorryAx, zero warnings in new modules).
No uniform bound is proved and RH is not claimed.

This record executes the four next steps of 1692: the engine brick
(§1), Erratum G on 1682 (§2), the mass-face reformulation and attack
plan (§3), the Laguerre re-scope (§4), and the redrawn map with the
completion diagram (§5).

## 1. The Kolmogorov ceiling brick

Record 1692's Theorem D (carrier empty) used three inputs: the MP 2010
basic criterion (paper), the paper's Kolmogorov estimate for the
conjugate function (`Pi{|h~| > A} = o(1/A)`, `dPi = dt/(1+t^2)`, paper),
and one pure real-analysis engine — now machine-checked.

Brick contents (`C1G9R2KolmogorovCeiling`):

```text
poissonDensity t = ofReal (1/(1+t^2))          -- dPi = dt/(1+t^2)
poissonMass s   = ∫⁻ x in s, poissonDensity x ∂volume
KolmogorovAdmissible u  :  ∃ A₀ > 0, ∀ A ≥ A₀,
  poissonMass {x | A ≤ |u x|} ≤ ofReal (1/A)   -- the (kol) property
poissonMass_Ioc_ge (hY : 1 ≤ Y) :
  ofReal (1/(5Y)) ≤ poissonMass (Ioc (-2Y) (-Y))
kolmogorov_ceiling (hc : 0 < c) (hmono : Monotone α)
  (hrep : ∀ x, γ x = u x - α x) (hkol : KolmogorovAdmissible u)
  (htail : ∃ X₀, ∀ x ≤ -X₀, γ x ≤ -c|x| log|x|) : False
```

The engine's mechanism, exactly as designed pre-build: on
`(-2Y, -Y]` with `Y = A/10` chosen deep in the tail, monotonicity of α
enters only through the constant `α(-1)`, so `u = γ + α` satisfies
`|u| ≥ A` on the whole interval; `Pi((-2Y,-Y]) ≥ 1/(5Y) = 2/A`
(density floor `1/(1+4Y^2)` times Lebesgue length `Y`); the `1/A`
ceiling then reads `2/A ≤ 1/A`.  No regularity of γ beyond the tail
bound is used; no principal-value technicality appears anywhere.

What remains paper-level for Theorem D (unchanged from 1692): the MP
basic criterion's representation (criterion face) and the Stirling tail
growth `γ x ≤ -c|x|log|x|` for the committed phase `m(ξ) =
Gamma_R(1/2-2πiξ)/Gamma_R(1/2+2πiξ)` (on the left tail c → 2π; the
phase is odd, exact, `γ(0) = 0`).

## 2. Erratum G — 1682's §1 carrier identification is refuted

1682 stated (its §1, lines 17–18, 27): with `J = sourceInclusion λ`,
`core = Σ_i ‖C J e_i‖² = tr(P₀ M_φ P₀)`, where `P₀ = carrier
projection (range E ⊓ range Q, 1589 pin)` — the MP carrier meet.

That identification is FALSE.  The machine-checked gate iff
(`g8EndpointGate_iff_survivorCore`,
`C1G8R3ActualEndpointTraceLimit.lean:336`) sums the survivor core over
`sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier λ)` — the SONIN
carrier, not the meet.  The reductio: if 1682's identity held with the
meet projection, then Theorem D (meet = {0}, 1692) would give
`core = 0`, and the 1680 no-slack iff would give the gate — hence RH —
unconditionally, contradicting the openness of every committed leg.
The two projections agree only if the Sonin carrier equals the meet,
which Theorem D just destroyed.

Correct form (supersedes 1682 §1):

```text
core = ‖C ∘ J‖²_HS = tr(P_J M_φ P_J),
P_J = projection onto range(sourceInclusion λ)  -- the Sonin carrier
```

Consequences: (a) the mass face is now stated on the Sonin source side:
the gate is equivalent to `P_J M_φ P_J` being trace-class — a concrete
operator on a concrete (nontrivial, infinite-dimensional) space;
(b) 1682 §3's two-sided-measure framework retires as the STATEMENT of
the gate — the "global two-sided finite-mass statement" of 1691 §3
becomes the Sonin-side statement above; (c) 1682 §2's Clark-formula
material and 1683's local analysis survive as DESCRIPTION of the
fold's continuous concentration (F63: no atom, no gap), not as the
gate's carrier; (d) 1636's compactness upgrade can never fire — its
input was the meet-carrier.

Consistency audit (all pre-1692 observations agree with Theorem D +
Erratum G): 1630's σ_min > 0 always (0 in spectrum, no kernel vector);
1633's focusing (`m(-ξ)` reads below the free-shift floor); 1634's
`D_real/D_model = 0.080 < 1`; Thm C injectivity; F63 no-atom; 1683's
surrogate atoms = inner-model artifact.  No committed numeric result
is invalidated; only 1682's §1 projection label was wrong.

## 3. The mass face after Erratum G, and the attack plan

The single open object, in its final committed form:

```text
GATE  ⟺  P_J M_φ P_J is trace-class
(J = sourceInclusion λ, φ the committed weight; 1680 no-slack iff)
```

Attack plan (race-rate first, F61-compliant fixed-ansatz self-checks):

1. Kernel-diagonal route: compute the diagonal of `P_J M_φ P_J`
   against the Sonin carrier's natural frame; the trace-class question
   becomes summability of the diagonal against the race-rate depth
   profile of 1690 Thm B.
2. The fold's continuous concentration (F63) must be integrable
   against φ along the Sonin source side — the race rate is the depth
   profile, the Kolmogorov ceiling (§1) is the rigidity that already
   killed the exact face; the same ceiling bounds any candidate
   concentration kernel from the superlinear side.
3. Finite-section hygiene: any partial trace `tr(P_J M_φ P_J)` used
   numerically must be bracketed between explicit truncation error
   bars (F52/F54 discipline; 1637's stage-2 bias stays quarantined).

## 4. Laguerre program re-scoped (1640 obligations rewritten)

1640 defined four obligations reading the carrier base as an
"existence" problem pushing toward the empty limit.  After Theorem D
the existence reading is void (the meet is empty — there is nothing to
approximate).  Re-scoped obligations, effective immediately:

```text
+------------------------------------------------------------------+
| 1640 obligation | old reading          | new reading (1693)      |
+-----------------+----------------------+-------------------------+
| 1 (core object) | carrier witness      | P_J M_φ P_J trace-class |
| 2               | basis → measure push | race analysis of the    |
|                 |                      | Sonin-side diagonal     |
| 3               | attain the ε-gap     | finite-section hygiene  |
|                 |                      | (F52/F54 brackets)      |
| 4               | compactness upgrade  | RETIRED (1636 upgrade   |
|                 |                      | can never fire)         |
+------------------------------------------------------------------+
```

Future sessions must not push Laguerre work toward the empty limit
problem; the target is the Sonin-side trace-class statement of §3.

## 5. Map 044 redrawn — and the completion map

Front B is REMOVED from the route map entirely: the exact face
(carrier nonemptiness, F33's "witness to construct") is now a theorem
in the negative direction (Theorem D, 1692), and its engine is
machine-checked (1693 §1).  Lane 1 = the bound; one obstruction, three
faces; the face that blocked the criterion tools is the same face the
engine brick now enforces mechanically.

Completion map — how much remains:

```text
+------------------------------------------------------------------+
|                       THE TOWER (fixed)                          |
|                                                                  |
|   off-line zero ⟹ qw(g) < 0   [formal, machine-checked]          |
|        |                                                         |
|        v         1680 NO-SLACK IFF  [machine-checked]            |
|   (∃B, ∀n≥N, Re tr Gram(N,n) ≤ B)  ⟺  Σ_i ‖C J e_i‖² < ∞         |
|        |                               |                         |
|        v                               v                         |
|   GATE ⟺ RH (F20)              survivor core = ‖C∘J‖²_HS        |
|                                        = tr(P_J M_φ P_J)         |
|                                        [Erratum G: Sonin side]   |
+------------------------------------------------------------------+
                    ^                    ^
                    |                    |
  +-----------------+----+     +---------+------------------------+
  | LOCAL / FOLD LAYER   |     | GLOBAL LAYER (THE ONE OBJECT)    |
  | COMPLETE             |     | OPEN — irreducible               |
  | 1690 Thm A normal    |     |                                  |
  |   form; Thm B race;  |     | P_J M_φ P_J trace-class?         |
  | 1691 Thm C injective |     |                                  |
  | F63 no atom, no gap  |     | attack = §3 plan                 |
  | 1693 brick: Kolmog-  |     | (kernel diagonal vs race rate,   |
  |   orov ceiling [MC]  |     |  ceiling-bracketed, F52 hygiene) |
  +----------------------+     +----------------------------------+
                    ^                    ^
                    |                    |
  +-----------------+--------------------+--------------------------+
  | CLOSED LANDS (do not revisit)                                 |
  |  Thm D carrier EMPTY [engine MC] · front B removed            |
  |  F51 / F64: one obstruction, three faces (factorization,      |
  |    p=2 Hardy clause, Kolmogorov ceiling)                      |
  |  F62 no index · F40/F43 inner-model dead · 1627 finite-type   |
  |    dead · F33 resolved (nonemptiness FALSE) · canonical-      |
  |    system transfer void (no de Branges realization)           |
  +---------------------------------------------------------------+

  legend: [MC] = machine-checked; ⟸ the gate iff has NO slack, so
  nothing between Σ_i ‖C J e_i‖² and RH is formalizable for free.
```

Reading: every reducible layer is closed and machine-checked; the
remaining work is the single global object, and it is irreducible
because it is machine-checkably equivalent to RH.  The proportion of
the program that is now formal or theorem-closed versus open:

```text
+---------------------------------------------+--------+---------+
| layer                                       | share  | status  |
+---------------------------------------------+--------+---------+
| formal chain (iff, monotone, endpoint)      | done   | MC      |
| local/fold layer (normal form → injectivity)| done   | thm+MC  |
| exact face of the front (carrier)           | done   | thm+MC  |
| global bound (P_J M_φ P_J trace-class)      | open   | 1 object|
+---------------------------------------------+--------+---------+
```

## 6. Boundary

No uniform annular bound, no trace-class statement, no RH.  New laws:
none beyond 1692's F64/F65 (this record's new content is the Erratum G
correction, the re-scope, and the brick).  The deliverables: the
machine-checked Kolmogorov ceiling engine, the corrected mass-face
statement, the re-scoped Laguerre program, and the completion map
above.
