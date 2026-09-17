# 1575 — the M_p support ledger: exact leak, the hM' scale, and the strip confinement of the radial defect

Date: 2026-09-17.

Status: PAPER RECON over committed definitions. Zero Lean, zero digits. This
record executes the item registered at the end of record 1574 section 3.2
("scale-adapted hM' candidate") by reading EVERY factor of the actual
ambient factor `M_p` against its committed definition and summing the
support shifts. It (1) re-confirms 1574's orientation verdict from the
primitive lemmas, (2) pins the exact failing scale and the exact escape, and
(3) converts 1534's vague warning ("does not cover arbitrary actual M") into
a quantitative statement: the radial defect is confined to a finite strip of
explicit width. B4's status is NOT changed (still two premises); its two
premises are now both precisely typed. RH not claimed.

## 1. The primitives, verbatim

Coordinate convention (`GlobalLogCrossing.lean:145-150`):

```text
(cc20GlobalLogTranslation b u) t =ᵐ u (t + b)          [the ONLY shift lemma]
ccm24LogRadialLowerRegion lambda = Set.Iio (log lambda)     :30-32  (FORBIDDEN set)
radial subspace = ker restrict-to-Iio = {u : u = 0 a.e. on t < log lambda}
   docstring :46-47 "functions that vanish below `log lambda`"
=> carrier columns: supp u ⊆ [tau, ∞),  tau := log lambda
=> E_lambda = multiplication by indicator of [tau, ∞)
```

Support arithmetic on lower-bounded supports (`[sigma, ∞)` notation):

```text
Trans(-log q):  u(t - log q)   nonzero iff t >= sigma + log q   TIGHTENS by log q
Trans(+log q):  u(t + log q)   nonzero iff t >= sigma - log q   LEAKS by log q
Trans(b)† = Trans(-b)           (measure-preserving conjugation)
scalars (p^{-1/2}, (1+c_p)^{-1} in R) : support-neutral
```

## 2. The M_p chain, factor by factor (application order right to left)

Source: `Bridge:74-79` (the witness of
`suffixEulerBoundaryOutputMaps_cons_head_factorization`), input columns
`sourceInclusion lambda o N x` with supp ⊆ [tau, ∞):

```text
(1) parameterizedFiniteEulerFactor 1 (p::S)
      = prod_{q in p::S} (1 - c_q Trans(-log q))       [EulerProduct :32-37]
      identity part keeps [sigma,∞); contraction parts tighten.
      SUPPORT-PRESERVING.   leak 0
(2) (normalizedPrimeEulerFrameTransport p)†
      = scalar • (1 - c_p Trans(-log p))†
      = scalar • (1 - c_p Trans(+log p))               [Transport :81-90 + §1]
      worst term LEAKS by log p.
(3) (I - F o F†),  F = newSuffixFrame lambda S
      F = Eprod_S o subtypeL o GramInvSqrt             [FrameGram :113-118,
                                                       FixedSourcePolar :230-235]
      range F ⊆ Eprod(carrier columns) ⊆ supp [tau,∞) by (1) => frame term
      lands INSIDE the strip-free zone.  SUPPORT-PRESERVING.   leak 0
(4) (suffixEulerAmbientProduct S)†
      = reverse product of |S| adjoint transports      [SchurPolar :52-56]
      each LEAKS <= log q; total leak Σ_{q in S} log q.
```

Total: every leak is an adjoint-Euler advance; no other factor moves
support. The composition cannot cancel the worst term (the identity
component of each leaking factor keeps the pre-leak boundary).

## 3. The verdicts

### 3.1 Fixed-scale hM: FAILS, and we know by how much

```text
Lambda(p :: S)  :=  Σ_{q in p::S} log q  =  log ∏_{q in p::S} q

supp (M_p o sourceInclusion lambda o N) x  ⊆  [tau − Lambda, ∞)
(I − E_lambda) o M_p o sourceInclusion o N  ≠  0   in general   (1574 confirmed)
```

1574's mechanism note stands; the placeholder "λ' = λ/p^k" of 1574 §3.2 is
hereby REPLACED by the exact value `lambda' = lambda / prod_{q in p::S} q`.

### 3.2 Scale-adapted hM': HOLDS as pure support identity - but is not slot (3)

`E_{lambda'} o M_p o sourceInclusion = M_p o sourceInclusion` at the coarser
`lambda'` above: the columns' image is already supported in
`[log lambda', ∞)`, and nothing in the ledger depends on estimates - this is
all indicator arithmetic from §1-§2.

BUT the 1535 shortcut consumer is SCALE-FAITHFUL: slot (1)'s decomposition
`(E Q E − M)J = −(I−E)MJ − E(I−Q)E MJ` lives at the bundle scale lambda, and
the B4 tail square-sum is written with `E_lambda`, `Q_lambda`. Running the
consumer at `lambda'` changes the operator family, not the obligation. So:

```text
hM' true  =/>  B4 collapses to one column.        (1574 §3.1 RE-CONFIRMED,
                                                   now from the full ledger)
```

### 3.3 The real prize: the radial defect is STRIP-CONFINED

What hM' DOES buy is the exact SHAPE of the first (hradial) premise:

```text
D o (I − E_lambda) o M_p o J o N
  = D o 1_{[tau − Lambda, tau)} o M_p o J o N
```

- a bounded operator whose radial-defect range is confined to a finite
  interval of length `Lambda = log prod(q in p::S) q`;
- for the canonical family with primes up to X: `Lambda = theta(X) ~ X`
  (Chebyshev) - FINITE per bundle, growing linearly in the cutoff. Any
  uniform-in-cutoff argument on hradial must therefore carry the strip
  width; per-bundle, it is one explicit constant.
- this refines 1534's warning from "arbitrary M uncovered" to: "the
  uncovered defect is exactly the strip [tau − Lambda, tau)".

## 4. Registered next actions (no spend taken)

1. **Strip-confinement brick (Lean, candidate)**: the identity of §3.3 is
   pointwise-a.e. indicator arithmetic through `cc20GlobalLogTranslation_coeFn`,
   the transport apply lemmas and the factorization witness - all committed,
   no estimates. Cheap leaf; schedule AFTER the T2 verdict unless the owner
   orders the both-columns route now (it only feeds route B).
2. **T2 Cotlar paper wave** stays the next registered item (1568/1572):
   the gap column `E H (I−E) H E M_p J N` is untouched by this ledger (the
   strip confinement is about the OTHER premise), and the (★)/B4 shared-fate
   pricing (1572 §1.2) still stands.
3. Honest caveat kept visible: nothing here is a formal no-go of hM - the
   failure claim (§3.1 "in general") is a support-arithmetic worst-case
   statement, and a family-specific cancellation would show up as a
   support-shrink lemma nobody has proved; the strip identity (§3.3) is the
   constructive replacement regardless.

## 5. Boundary

MOVED: hM/hM' fully adjudicated at the ledger level; hradial precisely
typed (finite-strip, width log prod q, theta(X) for the canonical family);
1574's placeholders replaced by exact values. NOT MOVED: no summability,
no estimate, no scale-faithful shortcut; B4 keeps both premises; (★), rho5,
transport, R4 OPEN. WO-S/WO-B unchanged. RH not claimed.
