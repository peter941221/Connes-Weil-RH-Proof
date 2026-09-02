# Yoshida-shaped finite-matrix interval certificates — generator scaffold

Status: ENGINE ONLY, 2026-08-27. No Yoshida matrix data has been encoded,
because none is available from an accessible primary source. This file states
exactly what was checked and what remains open, so a future contributor does
not mistake the scaffold for evidence.

## Provenance findings (checked 2026-08-27)

The Gate-1 numerical route in this repository cites:

> H. Yoshida, *On Hermitian forms attached to zeta functions*,
> Zeta functions in geometry (Tokyo, 1990),
> Advanced Studies in Pure Mathematics 21, Kinokuniya, Tokyo, 1992, 281–325.

* The Connes–Consani paper (arXiv:2006.13771) lists exactly this reference in
  its bibliography; its own §6 uses Hermitian Toeplitz matrices and equation
  (114)'s trigonometric approximation rather than quoting Yoshida's matrices.
* The chapter is hosted by Project Euclid, DOI `10.2969/aspm/02110281`
  (<https://projecteuclid.org/proceedings/advanced-studies-in-pure-mathematics/Zeta-Functions-in-Geometry/Chapter/On-Hermitian-Forms-attached-to-Zeta-Functions/10.2969/aspm/02110281>).
  Only page 1 (the introduction) previews. From that page we verified, quoted
  verbatim from the OCR: Yoshida works with test functions `F ∈ C_c^∞(ℝ)` and
  the class `C(a) = { φ | supp φ ⊆ [−a, a] }`, i.e. **the SQUARE support form**,
  and reduces R.H. to positive definiteness of the hermitian form restricted to
  every `C(a)`.
* The matrix entry formulas (and any role of the digamma function `psi`) live
  behind the access wall and were **NOT obtained**. Per repository integrity
  repository source-data rules, no formula is fabricated here.

Consequence for the plan (updated 2026-08-27 evening): route (a) is now
satisfied by a different open primary source. Bombieri 2000, section 7
(53-page scan `~/bombieri_weil_qf.pdf`, kept out of the repository) supplies
a certified elementary entry-formula system: the sinc kernel `K*`, the
symmetry law (7.1), the eigen system (7.2)-(7.5), and the completed Lemma-10
Gram identity -- visual read plus numerical triangle closure, worst deviation
8.9e-16, recorded in `docs/proofs/1043` §6y (including a sign erratum found
in the lossy text layer of (7.1)). The "odd 10×10 / even 200×200 digamma
LDLᵀ" description of Yoshida's own matrices remains *unconfirmed* behind the
access wall. The engine's digamma brackets stay available for the CC20 gamma
lane. Transcription starts from the Bombieri section-7 formulas; nothing
consumes this scaffold until those value nodes land.

## What the engine provides today

`yoshida_interval_gen.py`, pure Python 3 stdlib (no dependencies):

* **Rigorous digamma brackets at positive rationals**, from the series
  `psi(x) = −gamma + Σ_{k≥0} (1/(k+1) − 1/(k+x))`:
  every partial-sum term is an exact `Fraction`; the tail obeys the
  elementary bound `|tail(N)| ≤ |x−1|/N` because `k + x > k` makes
  `1/((k+x)(k+1)) ≤ 1/(k(k+1))` telescope. The Euler–Mascheroni constant is
  carried as an explicit bracketing pair of rationals whose digit source is
  recorded (published expansion, OEIS A002852 tier — re-derive or import via a
  proof-carrying route before Lean consumption).
* **Exact interval algebra**: add / scale / multiply / join of `[lo, hi]`
  Fraction pairs, with directed results (no floating point anywhere).
* **Rigorous elementary brackets on interval arguments**
  (`elementary_bracket(kind, theta_iv)` for `kind ∈ {sin, cos, sinh, cosh}`):
  the defining Taylor series evaluated in exact Fraction interval arithmetic,
  truncated at degree `E` with the Lagrange remainder
  `sup|θ|^(E+1)/(E+1)! · M` added back (`M = 1` for sin/cos,
  `M = exp(sup|θ)|` via an in-file proven rational upper bound — no stored
  digits). The term count doubles until the remainder meets `width_target`.
  Unlike `psi_bracket`, ZERO pre-stored digits are consumed, so these brackets
  are already proof-carrying: they need only be transcribed as rational pairs.

* **Exact symmetric-matrix Cholesky/LDLᵀ inspection** for positive-definite
  rational matrices: pivots `d_i` and factors `L` come out as exact
  Fractions, mirroring the shape already certified in Lean by
  `Dev/C1YoshidaLdlCertificate.lean`.
* **Lean emitters**: interval lines and LDLᵀ witness skeletons formatted as
  transcribable snippets matching that leaf's conventions.
* **Anti-fabrication mechanics**: every value node carries a mandatory
  `source` string; the engine refuses empty sources, so the encoder cannot
  silently invent an entry.

## Usage

```bash
cd scripts/yoshida_intervals
python3 yoshida_interval_gen.py --self-test          # stdlib only
uv run --with mpmath python3 yoshida_interval_gen.py --self-test --mpmath
```

Self-tests cross-check the LDLᵀ engine against the synthetic witness already
landed in Lean (`witnessL` subdiagonals 1/2, 1/3, 1/4 with `D = diag(4,9,1)`),
verify `psi(1) = −gamma` inside its bracket, verify `psi(1/2) = −gamma − 2·log 2`
against independently published digit expansions, and optionally compare both
the digamma bracket and the four elementary brackets to high-precision
`mpmath` values (modulo explicit parsing slack). The elementary suite also
checks the exact removable values at zero and the Pythagorean containment
`sin²θ + cos²θ ∋ 1` as a set identity on interval outputs.

## Integration path (when real data exists)

1. Transcribe entry formulas from the certified Bombieri section-7 system
   (`docs/proofs/1043` §6y) into value nodes, one `source` per node; each
   source string names the equation and the scan page it came from.
2. Emit per-entry rational intervals `[lo_q, hi_q]`.
3. Extend a Dev leaf consuming those pairs through the existing
   `C1YoshidaLdlCertificate` reading identity; keep floats on the generator
   side only — Lean verifies exact identities.
