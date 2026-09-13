# 1397 — Rung-3 recon: the archimedean sign is a closed-form quadratic functional, the old scan was real-slice and one-sided, and the route-alpha owner is complex — what the next rig can and cannot decide

Date: 2026-09-13. Follows
[1395](1395_009_contract_closed_ledger_state.md) section 3 (the rung table)
and its section 4 pointer. This is a SOURCE-ONLY reconnaissance: no digit of
the sign functional is computed here, no Lean was written, no build was run
(the 1389 section 8 discipline, re-used verbatim). Its purpose is the 1373
protocol's precondition: know the exact register before locking a prereg.
RH not claimed.

## 1. What rung 3 asks, from source

1389 section 3's collapse: on a ROOT-pinned triple-vanishing test the whole
`HealthyYoshidaDetectorData rho g` package is equivalent to ONE scalar:

```text
healthyDetectorData_of_routeAlphaOwner        (1391, formal, conditional)
healthyDetectorData_iff_selectedDetectorArchimedeanGate   (1389)
        package(rho, g)   <==>   0 < archimedeanTerm g.convolutionSquare
```

and the functional is fully explicit
(`C1SameOwnerWeil.lean:48-64`;
`CCM25Concrete/SelectedWeilFormula.lean:103`;
`CCM25Concrete/CompactLogConvolution.lean:114-120`):

```text
F(x)  = (g~ * g)(x) = integral t, conj (g(-t)) * g(x - t)          (Hermitian)
A(g)  = ( (log 4pi + gamma) * F(0)
          + integral y in (0,oo),
              [ e^(y/2) * (F(y) + F(-y)) - 2 * F(0) ]
              / (e^y - e^(-y))  dy ).re
gate  :  0 < A(g)
```

Regularity (for a future quadrature): the numerator vanishes at `y = 0`
(`archimedeanNumerator_zero`, machine-checked; `F(y)+F(-y) = 2 re F(y)` by the
Hermitian law `convolutionSquare_neg`), the denominator is `2 sinh y ~ 2y`,
so the integrand is proper at 0; for `y > 2 Rg'` (twice the owner's open
support radius) `F = 0` and the tail is `-2 F(0) / (e^y - e^(-y))`,
exponentially integrable. Every locked cell of the 1393 grid has
`2 (Ru + Rf) <= 0.6928 < log 2 = 0.69315`, so `F` is supported strictly
inside `(-log 2, log 2)` and the finite-prime sum of `g~ * g` is EMPTY —
`A(g)` alone decides the sign of `qw` on the owner class
(`qw = -A` on root-pinned triple-vanishing tests, 1087 section 1 reading of
the formal chain).

## 2. The owner whose sign is asked

`g = u.convolution f` from the 1391 leaf, with (1385's explicit shape,
`C1WindowTaperLift.lean:391-425`):

```text
f(x) = tau_f(x) * sum_j  c_j  e^{conj(s_j) x}    c solves the tapered Gram, target y = (0,0,0,-1)
u(x) = tau_u(x) * sum_j  b_j  e^{conj(s_j) x}    b solves the tapered Gram, target v = (1,1,1,1)
g    = u * f   (pointwise integral convolution, CompactLogConvolution:108-111)
```

Three structural facts the scan history never exploited:

1. **The owner is genuinely complex.** The solve target `-1` at `rho = r +
   14.13i` (or any height) feeds complex exponentials; `A` is a REAL
   quadratic form on a COMPLEX space `V_a^C`. The classical real-slice
   intuition (section 3) does not transfer without the cross terms.
2. **1083 already put complex pairs on the table.**
   `laplaceAt_reflection : lap f.reflection s = lap f (-s)` and the
   even/odd decomposition `evenPart h = h + h.reflection`,
   `oddPart h = h - h.reflection` with the 7-node symmetric interpolation
   realized at the exact root window
   (`1083` sections 1-5). The reflection identity is the algebraic handle
   for the real-vs-imaginary split of the owner family.
3. **Scale invariance survives** (1389 section 6): `A(c*g) = c^2 A(g)` for
   real `c` — amplitude cannot fix a wrong sign; only shape (tapers, radii
   ratio, and the imaginary-to-real content of the solve) can.

## 3. What the 1080-1087 wave actually established (inventory, before any
   new rig misreads it)

```text
1080  gate introduced: archimedeanTerm > 0 "NOT proven for any specific
      test"; branch conditional.
1082  arch-rescue algebra: the gate promotes a pinned test to strict-
      negative detector data (formal).
1083  even/odd pair + reflection identity: complex-structure machinery
      landed formal, unused by numerics since.
1085  the branch reduced to ONE inequality on ONE explicit object.
1086  first direct measurement of the gate quantity on an explicit real
      carrier: NEGATIVE (carrier slice frozen; -1.294-class values;
      normalization cannot affect the sign - quadratic form).
1087  Galerkin scan, 168 configurations, real basis profiles (enveloped
      Legendre + sine), three moment constraints imposed approximately:
      "every computed matrix had a negative largest eigenvalue".
```

The inference lock from 1087 section 2, quoted because it is the single most
load-bearing line for rig design:

```text
lambda_{a,K} = sup { A(h) : h in V_{a,K}, ||h||_2 = 1 }
             <= sup { A(h) : h in V_a,  ||h||_2 = 1 }.
... its maximum is a lower bound for the full supremum. A negative value
cannot prove that the full supremum is nonpositive.
```

So the correct verdict-history sentence is: **A has never been observed
positive, and nothing in the 1080-1087 evidence says it cannot be.** The
observed domain was the real slice with approximate constraint nullspaces;
the owner family of section 2 — complex, exactly vanishing by the solved
system (1385's realization theorem, not a penalized SVD nullspace) — has
never been evaluated. That is the gap the rung-3 rig fills.

## 4. What the next rig (1398 prereg) can and cannot decide — pre-committed scope

DECIDES (one-sided, constructively):
```text
JOINT WITNESS  find cells with BOTH (J1) (1394 band PASS) and A(g) > 0.
               Such a cell is MODEL evidence that rung 3 and rung 2 are
               simultaneously satisfiable on ONE owner — the analog of
               1394's role for rung 2. Kill-power: NONE on the route if
               negative (sup-lower-bound law above); a FAIL is NOT a
               falsifier of route alpha, and the prereg must say so in
               its kill-scope section with the same verbosity as 1393
               section 6.
```
CANNOT decide, no matter what it outputs:
```text
- 0 < A on ALL admissible owners, or on none (no finite grid bounds the
  sup from above; a certified upper bound would need an analytic
  complement estimate, i.e. C3-class work);
- the Weil criterion (rung 5) — orthogonal object;
- detector data (rung 4) — needs the sign on the FORMAL owner term, not on
  a model formula;
- RH, in either direction.
```
Design commitments locked here for 1398 (F10/F11 law from 1393): precision
class with residual/imag tolerance numbers; at least one gate a plausible
bug cannot fake (candidates: `A` must be exactly scale-invariant under
`g -> c*g` real — a mis-wired normalization breaks it; `A` of the
pure-real sub-family must reproduce a 1086-class value within tolerance —
cross-instrument continuity check; Gram-solve residual class as in 1393
G3).

## 5. Open design questions 1398 must resolve before commit (no digits)

1. Taper closed forms: 1385 takes `tau` as a `ContDiffBump` parameter; the
   rig must fix an explicit family (candidate: the classical `exp(-1/(1-
   t^2))` bump rescaled to `(-R', R')`, plus the plateau/spline alternative
   already used in 1373's detector rig) and lock it as model content.
2. Grid: subset of the 1393 grid restricted to the 1394 PASS region (reuse
   VERBATIM — same grids = auditable joint condition; no new parameters
   except taper shape).
3. The convolution `g = u * f` and autocorrelation `F = g~ * g` need
   certified quadrature (two nested 1D integrals per evaluation point);
   discretization error must enter the G3-class tolerance budget, unlike
   1393 where every quantity was a closed form.
4. Whether to also impose the detector value `laplaceAt g rho = -1` as a
   CHECK (it is built into the family) — recommended: yes, as a gate, cheap.

## 6. Boundary

No Lean. No run. No sign value computed at any shape — not even a smoke
evaluation, because ANY digit here would be an unpreregistered rung-3
measurement and the 1373 protocol exists exactly to prevent designing grids
around peeked signs. The numbers quoted from 1086/1087 are that wave's own
recorded (real-slice) telemetry, cited, not reused as evidence. Every
hypothetical `rho` remains a hypothetical off-line zero. RH not claimed.
