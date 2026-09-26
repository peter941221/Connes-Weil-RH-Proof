# Record 1995 — Route C audit: the Velez stabilization claim

Date: 2026-09-26.

Status: literature/line audit of an external preprint. No Lean brick, no
producer theorem, no RH claim. This record answers the five promotion
questions of `route/000_rh_mainline/003_route_c_trace_formula/001_literature_audit.md`
for the Velez lead and fixes the verdict.

## Source

```text
Velez, Simon. "A proof of the Riemann Hypothesis."
Zenodo record 21184595, version v5, published 2026-07-04.
https://zenodo.org/records/21184595  (paper.pdf, 6 pages, 288.6 kB)
```

Claim chain of the paper:

```text
Weil criterion: RH <=> Q_arith(F) >= 0 for all F in A_0 = C_c^inf(R; R)
Q_arith(F) = D(F) - P_prime(F) = <L_arith, C_F>          (Def 3.1-3.3, s4)
Lemma 5.1: q_X(F,G) = <L_arith, C_{F,G}> once X > e^R    (support exhaustion)
Prop 6.1:   q_X(F,G) = <Phi_X(F), Phi_X(G)>_{H_X}        (Hilbert norm)
Thm 7.1:    Q_arith(F) = ||Phi_X(F)||^2 >= 0
Thm 8.1:    RH
```

The classical parts (the coordinate dictionary, Definitions 3.1-3.3, the
explicit-formula bookkeeping of Appendices A-C, and Lemma 5.1) are routine
and correct: Lemma 5.1 is a finiteness statement (prime terms with
`k log p > R` vanish on the test autocorrelation), nothing more.

## The load-bearing step

Everything rests on Proposition 6.1: for `X > e^R` there are a semilocal
Hilbert space `H_X = L^2(C_X, d*u) (+) H_X^{0,1}` with
`C_X = A^{S_X}/Q*_{S_X}`, a scaling representation `U_X`, a
"cutoff-renormalized completed vacuum" `Xi_X`, and `Phi_X(F) = U_X(g_F) Xi_X`
such that the cutoff Weil form equals the Gram norm. Its entire proof is
Appendix D, equation (D.1), whose derivation is:

```text
Tr(R_U(h)) = 2 h(1) log(...) + PV integral + o(1)      [quoted from Connes]
  -- applied to h_{F,G}, then "passing to the compressed
     coefficient", gives (D.1):  <U_X(g_F) Xi_X, U_X(g_G) Xi_X>
                                = P_pole - W - 2 sum_{(p,k) in P_X} ...
```

Two steps in that derivation are not proved:

1. The `o(1)` remainder of the quoted trace formula is never shown to
   vanish. It is a local-cutoff asymptotic remainder on Connes' side; the
   paper's support hypothesis on the GLOBAL autocorrelation has no bearing
   on it. An exact identity is extracted from an asymptotic one.
2. The passage from a trace (a representation-level distributional
   statement) to a single matrix coefficient of a fixed vector requires an
   explicit covariance computation for `Xi_X` across the finitely many
   places plus the pole projection. In Connes-Consani's archimedean paper
   this compression is the main content, carried out for ONE place with
   prolate/Toeplitz machinery and explicit constants. Here it is one
   sentence with no computation.

## The five questions

**Q1 — where is the full semi-local Weil form shown equal to the Hilbert
norm?** In Proposition 6.1's display, via (D.1). Not proved; see the two
gaps above.

**Q2 — what gives positivity uniformly after removing the cutoff?**
Nothing independent. Positivity enters only through the Gram representation
itself; the paper's own Remark 6.2 concedes no positivity before support
exhaustion, and exhaustion is per-test finiteness, not a uniform estimate.
If Prop 6.1 is granted, positivity for every `X > e^R` at once IS global
Weil positivity — the claim is the theorem, packaged as an identity.

**Q3 — what controls the archimedean, prime, and zero-side limits
simultaneously?** Nothing: the zero side never appears. `Q_arith` equals
the zero sum on the spectral side (their own Appendix B quotes the explicit
formula); a Gram representation of `Q_arith` is a representation of the
zero sum's positivity, which is RH-equivalent content. The missing primes
are invisible only through per-test support exhaustion on the prime side;
the zero side has no exhaustion at all.

**Q4 — does it apply to this repository's owner and support?** The test
class `A_0 = C_c^inf(R; R)` (complexified) is shape-compatible with the
committed CompactLog class (same log-coordinate picture as the 1922
readback). Not the obstruction; Q1-Q3 are.

**Q5 — can the stabilization be formalized without hiding positivity in an
input?** No. The formalizable skeleton splits into (a) the dictionary and
Definitions 3.1-3.3 (routine), (b) Lemma 5.1 (routine), and (c) Prop 6.1,
which needs as hypotheses exactly the two missing items — vanishing of the
trace remainder on the test class and the compression covariance identity.
Item (c)'s hypothesis is a Gram-norm identity for the global Weil form,
i.e. an RH-equivalent input. This is the repo's law F67 shape: a positivity
engine (an inner product) that forces the target sign by construction, with
the entire content sitting in an unproved identity.

## Citation audit (primary sources)

- Connes, Selecta Math. (N.S.) 5 (1999), 29-106 [the paper's ref [3]]: the
  semilocal trace formula. The paper's own Appendix D quotation contains
  the `o(1)`. The theorem equates a regularized trace with a sum of local
  terms; it does not supply a rank-one Gram representation of the global
  Weil form. If it did, RH would have been settled in 1999.
- Connes-Consani, arXiv:2006.13771 [ref [4]]: the abstract states verbatim
  "We provide a potential conceptual reason for the positivity of the Weil
  functional using the Hilbert space framework of the semi-local trace
  formula" — scoped by title and content to the ARCHIMEDEAN place. Their
  Corollary 2.3(i) (the compressed scaling vector) is an archimedean-place
  construction; extending it to the multi-prime quotient with pole
  projection is new, unproved content, not an import.

## Cross-checks against committed repo facts

- Corollary 7.2 (a positive measure with density `L_arith^`) is equivalent
  to Weil positivity. The repo has already measured this kernel:
  record 1919's `K(xi) = sigma(2 pi xi) + 2 sum Lambda(n)/sqrt(n)
  cos(2 pi xi log n)`, and record 1920's finding that the kernel's negative
  mass is created by the visible prime sum inside the sigma-positive zone.
  The object is a delicate signed book; its positivity is exactly the
  map-047 P2 core, not an evident density.
- Zhu, arXiv:2608.24827 (per the route-003 audit table): compact-window
  positivity certificates hit a doubly-exponential resolution barrier.
  Lemma 5.1 does not engage this: support exhaustion is per-test, not
  uniform in the test.

## Verdict

```text
Route C / Velez: FAILS the five-question promotion audit.

The single load-bearing step (Prop 6.1 / (D.1)) is asserted, not proved;
the cited sources do not contain it; as a hypothesis it is RH-equivalent
and cannot be imported as a lemma.

Route C remains audit-only. No promotion. No change to any Route A or
Route B obligation.
```

Note on scope: this audit is of proof validity, not of the truth of RH or
of Weil positivity — the claimed statements are RH-equivalent and therefore
not numerically falsifiable; only the proof can be audited, and it fails.

Audit artifacts: the PDF was retrieved from the Zenodo record and read in
full (6 pages); quotations above are from that text.
