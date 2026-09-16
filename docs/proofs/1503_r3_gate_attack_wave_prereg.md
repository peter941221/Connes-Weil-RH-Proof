# 1503 — the four-gate attack wave: preregistration and new structural findings

**Status: PREREG + PAPER (zero new Lean beyond record 1502).** This record
preregisters the attack on the one square-sum that record 1502 showed gates
both the survivor energy and the endpoint channel limit, plus the B3/B4
composite-window program and the ρ5 sub-split. The typed guards come first;
no estimate is claimed; RH is not claimed.

## 1. The committed carrier geometry (read, not assumed)

Quoted from committed definitions:

```text
ccm24ArchimedeanSoninClosedSubspace λ
  = ccm24LogRadialSupportClosedSubspace λ
      ⊓ ccm24ArchimedeanFourierSupportClosedSubspace λ
      (CCM24HardyTitchmarsh.lean:376-380)

ccm24ArchimedeanFourierSupportClosedSubspace λ
  = comap (Hardy–Titchmarsh HT) (ccm24LogRadialSupportClosedSubspace λ)
      (CCM24HardyTitchmarsh.lean:361-366)   -- "HT u vanishes below log λ"

HT = F⁻¹ ∘ (mult by (m∘neg) ∘ (·∘neg)) ∘ F ,  HT ∘ HT = id
      (CCM24HardyTitchmarsh.lean:331-357),
m = ccm24ArchimedeanScatteringMultiplier (the modulus-phase multiplier).
```

So the Sonin carrier is an intersection of a position half-line condition
and a Hardy–Titchmarsh-image half-line condition — a **two-sided
(time-band) limiting configuration** of infinite measure, on the global log
carrier. The finite-window collapse (`HS² ≤ ‖k‖²·|S|`) is therefore NOT
available, and the openness of the gate is structural, not technical.

## 2. Sharp normal forms of the gate (paper)

Let `C` be the root convolution (`convolution by the involuted compactly
supported root`), `P` the Sonin projection, `J` the inclusion, and

```text
(★)   Summable i, ‖(J† ∘L C ∘L J)(e_i)‖² .
```

* **(★) ⟺ P C P is Hilbert–Schmidt on the ambient.** `{J e_i}` is an
  orthonormal basis of `range P`; `P C P` kills the complementary columns;
  and `‖P w‖ = ‖J† w‖` for all ambient `w` (P = J J†, J is an isometry).
  Hence the full ambient column sum of `P C P` equals (★). [Formalizable:
  needs ambient-basis column-sum surgery; no analysis.]
* **Conjugation gives no free lunch.** `HT` is a reflection-plus-multiplier
  sandwich, and multiplication operators conjugate reflections into
  reflections; hence `HT ∘ C ∘ HT⁻¹` is again a CONVOLUTION operator (by
  the reflected kernel), never a window. Under `HT`, `P C P` becomes the
  compression of a convolution to `Ṙ ⊓ R` with `Ṙ = HT(R HT⁻¹)` — the same
  problem in the dual picture. **No conjugation in the committed algebra
  turns the gate into a finite-window form.**
* **Hardy-pressure structural finding (new).** At the classical limit
  (multiplier phase absent, `m` constant), the two-sided condition
  `supp u ⊆ half-line ∧ supp HT u ⊆ half-line` is the Hardy-uniqueness
  regime — the carrier collapses toward `{0}` and the gate is vacuous.
  The entire nontriviality of `S_λ ≠ {0}` — and therefore of (★) — is
  carried by the scattering multiplier `m`. Corollary: **any proof of (★)
  must read the phase of `m`**; a decay-only (density-level) argument
  cannot conclude it. This is the mechanism behind the phase/density
  typing of record 1417 (law F21), now derived rather than observed.

## 3. Attack routes for (★) [WO-S3]

Guard first (typed): before any tail estimate, check the family
`{P C P_{>N} e_i}` for a record-1488-style non-summable orthonormal orbit;
records 1421 (pointwise antiresonance) and 1490 (source projection of the
ambient orbit decays pointwise) supply only the pointwise layer.

* **Route W (window strip, formalizable).** Split the radial half-line at a
  window `W_N`: the compressed operator `P C P_{W_N}` has kernel supported
  in the bounded strip `W_N + supp(root)` × `W_N`, hence is Hilbert–Schmidt
  with `‖·‖²_HS ≤ M²·|W_N + supp|·|W_N|` (M = kernel sup). This is the
  record-1495 finite-window mechanism in compressed form. Deliverable: a
  compressed strip-HS lemma. Cost: L²-kernel bookkeeping on the committed
  interval carriers; no new analysis.
* **Route T (collective tail, the open mathematics).** Show the tail term
  `Σ_i ‖P C P_{>N} e_i‖²` tends to 0 fast enough, using the two-sided
  condition: the position half-line localizes `C P_{>N} e_i` near the tail
  (compact root support), and the HT half-line must then suppress the
  projected mass **through the phase of `m`** (finding of §2). Candidate
  engines: Hardy–Titchmarsh covariance (committed, 1421's engine) with the
  multiplier phase as the quantitative input; almost-orthogonality
  (Cotlar-type) for the compressed tail family, with cross terms killed by
  the two-sided support and SIZED by the phase. Stop rule: any route that
  reads only |m|-decay or support facts is typed-dead by §2.
* **Route AO (almost-orthogonality, alternate).** If the compressed family
  `{Q_N e_i}` (Q_N = compressed tail operators) is almost orthogonal with
  summable cross-structure, the collective energy is bounded by the
  Cotlar–Knapp argument. The §2 finding requires the almost-orthogonality
  constants to be phase-derived.

## 4. Attack routes for B3/B4 [WO-B, M_p-adapted]

* **B3 (composite radial-boundary estimate `(I−E) C M_p J`).** The visible
  prime transports act by log-shifts; the composite window is
  `supp(root) ∪ (shift range)` — still COMPACT (record 1464 exports the
  visible-prime cutoff data). Preregister the composite window identity as
  the record-1495 identity with the shift-set union; the algebraic support
  calculus is formalizable cheaply, and the analytic transfer (record-1496
  pattern) is unchanged because the composite window remains compact.
* **B4 (composite internal-gap estimate `(E−P) E C M_p J`).** The
  record-1497 prolate absorption with `M_p` kept ambient-side. Guard:
  record 1491 — any route factoring through
  `J† ∘L sourceProlateFactor ∘L J` is identically zero and dead; `M_p`
  must stay on the ambient side of the sandwich.

## 5. ρ5 sub-split [the substantive gate]

State the identification `B + 2·X + L = qw(owner.sourceTest)` as ONE Lean
theorem with record-1464 raw-geometry inputs only (audit A1 of record
1501). Preregistered sub-split of `L`'s limit object (record 1480): prime
window residual (the P2 sub-limit) + compressed response, so the Euler
content of ρ5 is exposed term by term. Typed guard: if the only available
input for the identification is a `qw` sign, the route is circular and
stops (record 012 stop rules).

## 6. Order of battle

```text
1. Route W strip-HS lemma          formal, next session
2. (★) ⟺ P C P HS normal form      formal, next session
3. Route T/AO phase mechanism      paper first, then brick
4. B3 composite window identity    formal support calculus
5. B4 prolate absorption w/ M_p    brick after 4
6. ρ5 one-theorem statement + P2 sub-limit split
```
