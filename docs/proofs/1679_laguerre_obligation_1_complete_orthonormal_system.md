# 1679 — Laguerre obligation 1: the shifted log-pulled-back Laguerre system is a complete orthonormal system of the committed half-line

Date: 2026-09-19.

Status: paper-level record (obligation 1 of the 1636–1642 carrier-base
program), with a self-consistency rig.  Classical content, exact transport.
Obligations 2–4 and the base itself remain OPEN; RH is not claimed.

## 1. The obligation, exactly

The constructive base program (1636 compact-observable interface; 1639–1642
Laguerre finite sections; corrected numerics 1640) needs, as its first
brick, an explicit complete orthonormal system of the committed half-line
subspace on the E-side — the ansatz family inside which the Q-side defect
minimization (obligations 2–3) is run.  In committed vocabulary:

```text
space      finiteSCarrier = L²(R, du), u = log variable
half-line  E = M_{1_{[log λ, ∞)}},  log λ = −a,  a = log(1/λ) > 0
obligation 1:  exhibit {χ_n}_{n≥0} ⊂ L²(log λ, ∞) with
               ⟨χ_m, χ_n⟩_du = δ_mn   and   span closure = L²(log λ, ∞).
```

## 2. The system and the exact transport chain

Classical input: the Laguerre polynomials L_n (standard normalization
L_n(0) = 1) are orthogonal and complete in L²((0,∞), e^{−x}dx) with

```text
∫_0^∞ L_m(x) L_n(x) e^{−x} dx = δ_mn ,
```

so the Laguerre functions φ_n(x) := e^{−x/2} L_n(x) form a complete
orthonormal system of L²((0,∞), dx) (classical; standard
orthogonal-polynomial completeness).

The geometry: the u-half-line (log λ, ∞) maps by x = e^u onto the
x-half-line (λ, ∞) — NOT onto (0, ∞).  So the transport needs the
TRANSLATED Laguerre system on (λ, ∞) (translation by λ preserves Lebesgue
orthonormality; scaling would not), then the log pull-back:

```text
(T1) translation    η_n(x) := φ_n(x − λ)        ONB of L²((λ, ∞), dx)
     ∫_λ^∞ φ_m(x−λ) φ_n(x−λ) dx = ∫_0^∞ φ_m φ_n dx = δ_mn.

(T2) log pull-back  (U f)(u) := e^{u/2} f(e^u)   L²((λ,∞),dx) → L²((logλ,∞),du)
     unitary: ∫_{logλ}^∞ e^u |f(e^u)|² du = ∫_λ^∞ |f(x)|² dx.
```

Composed:

```text
χ_n(u) = e^{u/2} · φ_n(e^u − λ)
       = e^{u/2} · e^{−(e^u − λ)/2} · L_n(e^u − λ),    u ≥ log λ,
       n = 0, 1, 2, …
```

Norm check by hand: x = e^u gives
∫_{logλ}^∞ |χ_n|² du = ∫_λ^∞ |φ_n(x−λ)|² dx = ∫_0^∞ |φ_n|² dx = 1.

ERRATUM NOTE (caught by the section-3 rig on the first run, law F27/F28
doing its job): a first draft used the PURE log pull-back
e^{u−logλ}·e^{−e^{u−logλ}/2}·L_n(e^{u−logλ}) — that system is an ONB of
the FULL line L²(R, du) (it transports L²((0,∞),dx)), and its restriction
to the half-line is neither orthonormal nor complete there; the rig read
max|G−I| = 1.8e+01 and growing residuals.  The translated system above
fixed both readings.

**Obligation 1 is discharged at paper level**: {χ_n} is a complete
orthonormal system of L²(log λ, ∞) — the composition of a translation and
a unitary pull-back preserves orthonormality and completeness, and the
classical Laguerre theorem supplies both at the source.  Normalization is
exactly ‖χ_n‖² = 1 in the committed du-measure.

## 3. Self-consistency rig (F61-permitted: inside the fixed ansatz)

`scripts/laguerre_hardy_side_check_1679.py`
(log `build-logs/1679_laguerre_hardy_side.log`), final run at λ = e⁻¹,
M = 16384 du-quadrature points on (−a, 40), sections n < 30:

```text
Gram:      max |G − I| = 4.380e−04          (quadrature floor, all 30 sections)
residual:  K = 4: 2.263e−01   K = 8: 3.646e−02   K = 12: 8.693e−03
           K = 20: 9.280e−04  K = 30: 1.081e−04  (smooth bump, out of span;
                                                 clean monotone decay)
```

Rig notes, two transcription hazards caught on the way (F27/F28):

```text
(i)   the first draft used the PURE log pull-back
      e^{s} e^{−e^s/2} L_n(e^s), s = u − logλ — the ONB of the FULL line
      L²(R, du), not of the half-line; the rig read max|G−I| = 1.8e+01
      and growing residuals.  Fixed by the translated system of section 2.
(ii)  eval_laguerre overflows at y = e^u ~ 1e17 for n ~ 30 (nan readback);
      χ_n is masked at y > 400 where e^{−y/2} has already underflowed.
```

The rig guards transcription only; the evidence for obligation 1 is the
paper transport of section 2.

## 4. Boundary

Obligation 1 was the classical prerequisite; the base still owes the hard
parts: (2) finite-section defect → 0 for the meet-minimizing vectors,
(3) a positive limiting lower bound for the compact observable, (4) removal
of FFT truncation — and, above the program, the base existence itself is
hypothesis-grade (F33).  No Lean brick (transporting unitary chains into
the tree is a separate project; the consumers consume the base as a
hypothesis today).  RH NOT claimed.
