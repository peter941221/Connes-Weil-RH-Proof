# Plan 018: Screw-Norm Defect Feasibility Experiment

Date: 2026-07-11

Status: rejected at Gate D1. No guaranteed RH proof route has been identified.
The exact integral defect exists unconditionally, but the required absolutely
convergent zero-pair expansion and sign mechanism do not follow.

## 1. Meaning Of A Guaranteed Route

The project may call a route guaranteed only after it has all of the following:

```text
an axiom-clean final implication to _root_.RiemannHypothesis;
explicit source objects rather than stored spectral or zero conclusions;
uniform error bounds for every limit and every quantifier;
no RH-equivalent positivity, zero-location, or compact-open convergence input;
at least one lower theorem with a strict quantitative margin beneath the
  final RH-closing step.
```

Logical validity alone is insufficient. A theorem of the form `X -> RH` does
not give a guaranteed route when `X` is equivalent to RH or lacks a lower
producer.

## 2. Candidate Audit

```text
+----------------------+--------------------------+-----------------------------+
| candidate            | unconditional part       | rejection / remaining root  |
+----------------------+--------------------------+-----------------------------+
| QW--prolate 017      | real-zero theorem;       | critical Herglotz ordering; |
|                      | proxy transform -> Xi    | ground/proxy transfer       |
+----------------------+--------------------------+-----------------------------+
| Suzuki W(a,theta;z)  | entire function with     | conjectural compact-open    |
|                      | only real zeros           | limit; motivation uses RH   |
+----------------------+--------------------------+-----------------------------+
| Jensen polynomials   | each fixed degree is     | RH needs every degree and   |
|                      | eventually hyperbolic    | every shift                  |
+----------------------+--------------------------+-----------------------------+
| de Bruijn--Newman    | Lambda >= 0              | RH is the missing Lambda<=0 |
+----------------------+--------------------------+-----------------------------+
| Xi-kernel PF route   | low-order positivity     | certified PF5 counterexample|
+----------------------+--------------------------+-----------------------------+
| Volterra/Weyl/KLM    | normalized quotient      | quotient lift, uniform      |
|                      | certificate              | omega, de Branges bridge    |
+----------------------+--------------------------+-----------------------------+
| screw Gram identity  | S_t is explicit and L2  | norm equality is equivalent |
|                      | without RH               | to RH                       |
+----------------------+--------------------------+-----------------------------+
```

Primary evidence:

```text
Suzuki, Weil's quadratic form via the screw function
https://arxiv.org/abs/2606.09096
screwzelf_7.tex:538-664,2677-2681,3054-3073

Suzuki, On the Hilbert space derived from the Weil distribution
https://arxiv.org/abs/2301.00421
screwzse_11.tex:321-430,741-1015,1182-1268

Griffin--Ono--Rolen--Zagier, Jensen polynomials...
https://arxiv.org/abs/1902.07321

Rodgers--Tao, The de Bruijn--Newman constant is non-negative
https://arxiv.org/abs/1801.05914

Michałowski, On the Polya Frequency Order...
https://arxiv.org/abs/2602.20313

Finite-core Volterra reductions...
https://arxiv.org/abs/2606.29555
```

## 3. Selected Research Object

Let `S_t(z)` be Suzuki's explicit function from zeta, gamma, prime, and
Hurwitz--Lerch terms, defined without RH. Let `g(t)` be the explicit Riemann
screw function. Define the real defect

```text
Delta(t) := (1/(2*pi)) * integral_R |S_t(z)|^2 dz + g(t).
```

Suzuki proves

```text
RH <=> Delta(t)=0 for every t >= t0, for some t0 >= 0.
```

Source: arXiv:2301.00421, `screwzse_11.tex:1250-1268`.

This is the narrowest located RH criterion with all objects defined
unconditionally. It uses one real parameter and no choice of a ground state,
parity sector, Galerkin cutoff, or compact-open normalization.

## 4. Why This Is Not Yet A Producer

The zero expansion is

```text
S_t(z)
  = sum_gamma sqrt(pi*m_gamma)
      * (exp(-i*gamma*t)-1)/gamma
      * F_gamma_sharp(z).
```

Source: `screwzse_11.tex:1021-1034`.

Under RH, the functions `F_gamma` form an orthonormal basis and Parseval turns
the norm square into the screw kernel. Without RH, they do not have that
orthogonality theorem. Expanding the norm produces the Gram matrix

```text
G_(gamma,rho) := <F_gamma,F_rho>.
```

The diagonal terms reproduce the target screw expression; the off-diagonal
Gram terms form `Delta(t)`. An off-critical zero yields a negative Weil
direction by the Yoshida separation argument (`screwzse_11.tex:1303-1337`).
Therefore no sign-definite error term has been found that can be discarded by
a soft inequality.

## 5. Rejection-First Gates

### Gate D1. Exact unconditional defect formula

Derive `Delta(t)` as an absolutely convergent zero-pair or contour expression.
The formula must preserve quadruples

```text
gamma, -gamma, conjugate(gamma), -conjugate(gamma)
```

and must not assume `gamma` real.

Pass only if the result separates diagonal and off-diagonal contributions with
an explicit summable majorant.

### Gate D2. Defect sign or coercive evolution

Find one of:

```text
Delta(t) has a fixed sign and vanishes at one controlled endpoint;
Delta satisfies an ODE/Volterra equation with unique zero solution;
integral w(t)|Delta(t)|^2 dt equals an explicitly vanishing arithmetic term;
Delta is analytic and vanishes on an unconditional uniqueness set.
```

Reject any argument that assumes Weil positivity, `E_xi` Hermite--Biehler,
`F_gamma` orthogonal, or all zeros real.

### Gate D3. Quantifier closure

Suzuki's criterion needs every sufficiently large real `t`. A proof on a
sequence, a bounded interval, or a density-one set does not count unless a
named uniqueness theorem upgrades it to the full half-line.

### Gate D4. Formal bridge

Only after D1--D3 pass, formalize:

```text
Delta(t)=0 on a half-line
  -> -g(t)>=0 on that half-line
  -> source RH
  -> _root_.RiemannHypothesis.
```

The first Lean target must be the explicit scalar identity, not a structure
field storing half-line vanishing.

## 6. Success And Rejection

```text
accepted guaranteed route:
  D1--D3 have unconditional proofs with no RH-equivalent premise, and the
  source-to-Mathlib bridge is explicit.

partial:
  an exact defect formula is proved but no sign, evolution, or uniqueness
  mechanism forces its vanishing.

rejected:
  the defect has an explicit nonzero term with no forced cancellation, or the
  proposed vanishing mechanism is equivalent to RH.
```

Current verdict: rejected at D1 under the stated pass criterion. The detailed
derivation is `docs/proofs/018_screw_norm_d1_verdict.md`. A finite symmetric
truncation splits into a `K_R-I` Gram correction and a separate off-critical
conjugation correction. The source proves local absolute convergence of the
partial-fraction series and global `L2` membership of the completed function,
but not an absolutely convergent zero-pair norm expansion or a summable pair
majorant. Since positivity of `K_R` gives no sign for `K_R-I`, D2 is inactive
for this representation. Do not create Lean route APIs from plan 018.
