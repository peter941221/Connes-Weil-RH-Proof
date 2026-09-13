# 1405 — Chuk arXiv:2608.24827 as a pillar-B supplier? Recon, and a prereg for the one-cell cross-term dictionary probe

Date: 2026-09-14. Zero-digit record: literature re-screen + paper audit
+ a locked probe specification. NO measurement is reported here; the
outcome is 1406. No Lean was written. RH not claimed.

## 1. Why this exists (register correction, law F15 applied to myself)

1404 declared the campaign queue empty by construction. The 004
endpoint audit had, all along, kept an OPEN external obligation:
Marcus Chuk, arXiv:2608.24827 (submitted 2026-08-25, unrefereed),
Corollary 9 / Theorem 1.2, certified for every complex
`f in L^2(R)` with `supp f subset [-0.8, 0.8]`:

    Q(f) >= 8.9e-18 * ||f||_2^2,

where Q is the geometric side of the Riemann-Weil explicit formula
evaluated on the autocorrelation `g = f star f~`. Our root-base
owners have support radius `log2/2 = 0.3466 < 0.8`, so on its face
the theorem sits strictly under the window our pinning uses. If our
`psi(g.convolutionSquare)` were that Q, then unconditional positivity
would hold on every chain owner, and the machine-checked chain
(exit 1081: off-line zero forces `qw < 0`) would refute its own
hypothesis. The paper itself cannot settle this: it positions a
fixed-L certificate as "a finite fragment of RH" (section 1), proves
a barrier showing the fixed-window route closes doubly-exponentially
(`T_1(L) = 2*pi*e^{A_L}`, `A_L ~ 4e^L`, section 7), and explicitly
declines to rely on or compare against unrefereed claims beyond
log 2. So 1405 prices the bridge from its hypotheses (F15), not from
novelty feeling.

## 2. Paper facts (read this session, arXiv HTML, quoted for the audit)

* Classical baseline (their line, section 1): Yoshida [Adv. Stud.
  Pure Math. 21 (1992), 281-325] proved `Q >= 0` for `2L <= log 2`;
  Connes-Consani reproved by trace-formula methods. Our convSq
  radius 0.6928 < log 2 sits INSIDE the classical range.
* Their certificate machinery: pointwise envelope of the Weil symbol
  Psi_L, one-stroke reduction to a 200x200 Legendre matrix, verified
  Cholesky residual at shift 8.9e-18; independent run at
  T^sharp = 150; error budget closes by 24 orders. Ingredients
  declared "elementary and fully explicit; there are no anonymous
  constants".
* Support 2.38 CLAIM RETRACTED (section 7): per-prime envelope
  sharpening bounded the comb in the wrong direction; the corrected
  true threshold needs T^sharp ~ 1.2e4 and N ~ 1.4-2e4 modes at 90
  digits. Their own barrier: no pointwise comb bound lowers T_1.
* Lemma 6.1 (parity splitting) and Corollary 6.3, the hinge:
  for REAL f, `Q(f) = Q(f_e) + Q(f_o)` with the pole term
  `+2c^2 - 2s^2` (c = int f_e cosh(x/2), s = int f_o sinh(x/2));
  proof uses `g^(z) = f^(z) f^(-z)`, "no cross term". Then,
  verbatim: "Moreover, for complex f, Q(f) = Q(Re f) + Q(Im f)"
  and Corollary 6.3: "for every complex f ... no parity or reality
  restriction".

## 3. The structural finding (why the bridge is NOT free)

For a REAL f the autocorrelation is `(f~ star f)(x) = int f(u-x) f(u) du`
and its transform factors as `f^(z) f^(-z)` — this is where their
cross-term cancellation lives. For a genuinely COMPLEX owner
`h = r + i*m` the Hermitian autocorrelation instead satisfies

    (h~ star h)(x) = (r~ star r)(x) + (m~ star m)(x) + i*(cross terms),

and the cross terms are NOT zero in general: they vanish sectorwise
only when the two summands are each REAL and the transform factors
with the conjugation symmetry `conj(f^(conj z)) = f^(z)` — a real-
valuedness statement, not an identity for complex r, m separately
mixed. The register's owners ARE genuinely complex: the 1083/1403
node set `{rho, -rho, 0, +-1/2, +-1}` is not conjugation-symmetric
(rho = 0.99 + 14.13i has rho-bar outside the set), which 1397
already flagged as the untapped structure. Consequence: their
"complex case" is a DEFINITION-BY-SECTORS
`Q(Re) + Q(Im)`, an inequality on sector sums, not on the full
Hermitian autocorrelation. Whether our `psi(h~ star h)` can be
bounded by their certificate is therefore exactly the question
whether the cross-term contribution to `psi` vanishes. That is a
single-cell computable question — and it is the whole M2 bridge for
the root base, so it is priced as one probe, not as a campaign.

## 4. Local definitions the probe must respect (read this session)

* `C1SameOwnerWeil` (Dev/C1SameOwnerWeil.lean:31-70):
  `poleTerm F = Re(laplaceAt F (1/2) + laplaceAt F (-1/2))`;
  `archimedeanTerm F = Re((log 4pi + gamma) F(0) + int_0^inf F-part
  /(2 sinh) )`; `finitePrimeTerm` visible iff `|log n| <=
  supportRadius F`; and (:193-200) `psi F = poleTerm F -
  archimedeanTerm F - finitePrimeSum F`.
* `C1SpectralWeil.lean:592-610`: `spectralWeilValue F = Re tsum
  (spectralTerm F)`, `spectralTerm F rho = xiMultiplicity rho *
  laplaceAt F (centeredXiCoordinate rho)`; and `gate2ExplicitFormula`
  (psi = spectralWeilValue) is a DEF (a Prop) — this is the
  UNDISCHARGED hJ1 obligation. The probe is model-level and does not
  touch it.
* `psi` is LINEAR in the test function F (all three terms read F
  linearly). Hence `psi(h~ star h) = psi(r~ star r) + psi(m~ star m)
  + psi(i*cross)` holds identically; the probe measures the last
  summand.
* Instruments: `scripts/run_1403_rig.py` (tier-1 solve, owner
  evaluator, `gd_lap`-fixed panel integrator), imported;
  `scripts/run_1398_rig.py` (`_S_np`, `_panels`, `compute_A`) imported.
  No reimplementation of the solve or the A-functional.

## 5. PREREG — the cross-term dictionary probe (model; one cell)

Cell: tier-1 beta owner (rr, im) = (0.99, 14.134725), eps = 0.01,
window log2/2, solve/owner VERBATIM 1403. All integrals mp
prec=200 with the 1403 `gd_lap` panel rule (density
max(|im target|, |im rho|)+2), float64 mirror for the G1 gate.

Quantities (F = Hermitian autocorrelation, computed as
int conj h(u - x) h(u) du over panels; sectors a_r, a_m with real f):

    P_h   = psi(F_h)    [expect = -A_h ~= +17.3431099 since pole,
                          primes ~ 0 at tier-1; reference 1403 values]
    P_r   = psi(a_r),  P_m = psi(a_m)
    P_x   = P_h - P_r - P_m        (= psi of the cross part)

Gates:

| id | statement | class |
|----|-----------|-------|
| G0 | import + solve sanity: P_h reproduces the 1403 tier-1 A to tie class: `|P_h + 17.3431099115819| <= 2e-4` (quadrature budget of nested autocorrelation, float-vs-mp measured at G1) | 2e-4 |
| G1 | mp/float agreement for each of P_h, P_r, P_m, P_x (float64 panels npw 24, freq rule as `gd_lap`) | 1e-6 relative |
| G2 | linearity self-check: `|P_h - P_r - P_m - P_x| <= 1e-9` (identity by construction; detects evaluator aliasing, F12 recurrence-5 style) | 1e-9 |
| G3 | sector magnitudes printed; NO sign class locked (their convention dictionary is exactly what is at issue) | report |
| G4 | cross decisiveness: verdict fires only if `|P_x| >= 1e-3` (their certified floors are <= 2.35e-14 per sector; a cross term of model O(1) dwarfs the entire certified margin) | 1e-3 |

Sentinels:
`DONE gates=G0:...,G1:...,G2:...,G4:...,` and
`VERDICT chukBridge=EXCLUDES_OWNER|COVERS_OWNER|INCONCLUSIVE P_h=... P_r=... P_m=... P_x=...`

Reading: EXCLUDES_OWNER (|P_x| >= 1e-3) — the Hermitian
autocorrelation value is not reachable from any sum of sector
positivities; Chuk's certificate does not bound our owner class; the
species closes as a pillar-B supplier, and the chain's negative
witness coexists with their theorem by construction. COVERS_OWNER
(|P_x| < 1e-6) — their theorem would bound `psi` on our owner: the
register then has a genuine chain-vs-preprint collision to escalate
(highest-priority red flag, no silent fix). INCONCLUSIVE between.
Pre-run conditioning (F12, including recurrence 4: the NEW gate is
audited): the nested quadrature touches smooth exp-sum integrands at
frequency ~ im*2 = 28 rad over a window of length 2*log2/2 ~ 0.7 —
panel count at npw 24 with that rule gives float64 error ~1e-12
(1403 measured the same integrator class end-to-end at 7.4e-14); the
tie margins are 9 and 11 orders above the expected noise. P_x is an
O(1)-scale difference of O(10) terms — no cancellation trap.

Kill scope (law 65 + sup-law stated up front): one model cell. It
CANNOT falsify their theorem (their class is real/sector-real) and
cannot falsify the chain. It decides ONE dictionary question about
whether an external certificate reaches the register's complex
owner class. No Lean, no gate, no RH claim in any branch.

## 6. Literature re-screen ledger (this wave, cheap)

* arXiv:2608.24827 Chuk — audited above; bridge = probe 1405/1406.
* arXiv:2608.10121 Vedana, "Classification of Fourier summation
  formulas on a horizontal strip" (v2 2026-09-10): framework/
  classification of summation identities with Selberg-class
  application; no positivity certificate on any test-function class;
  NOT a gate species (same grading as 1352's K-convexity close).
* arXiv:2607.02828 (finite Guinand-Weil dictionary) — ALREADY
  screened: 041 section ("accepted as exact coordinate evidence");
  not a supplier. arXiv:2606.09096 (screw-function Weil form) —
  ALREADY screened: 125 route screen. arXiv:2602.04022 — survey,
  no mechanism (multiple ledger entries). 2408.15135, 1703.03827,
  2608.13637 — closed by 1348/1352/1355, untouched here.
* No new positivity species found beyond Chuk in a one-round screen
  (search_arxiv, tbs=qdr:y, three queries, 2026-09-14).

## 7. Next steps

1. Write `scripts/run_1405_probe.py` importing the 1403/1398
   instruments VERBATIM; commit BEFORE any digit (law 42).
2. Sync to the Linux-side verification environment; run; write 1406
   outcome record with the sentinels quoted verbatim.
3. Register closing pass (README item, memory cards, and — if
   EXCLUDES — law F16 candidate: "preprint complex extensions stated
   as sector sums do not cover Hermitian autocorrelations with
   cross terms; measure the cross term before consuming the
   theorem").
