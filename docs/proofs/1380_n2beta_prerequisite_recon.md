# 1380 — N2β prerequisite recon: the correction engine has no norm control, and the budget producer is a quantitative interpolation theorem

Date: 2026-09-13. Commissioned as the branch-A prerequisite of [1379]
(1379_n1c_joint_feasibility.md): determine whether the register's
existing construction can supply the norm budget `||g||^2 <= delta /
(2*C_min)`, and specify what a producer must look like if not.
Evidence class: SOURCE READBACK (all claims below are read off committed
files, with line citations) + PAPER design spec. No digits; no Lean
build in this record. RH NOT claimed.

## 1. What the register's construction actually does (source verdict)

The chain behind every detector constant:

```text
exists_residualWindow_correction_with_quadratic_decay
    (ConnesWeilRH/Source/CC20YoshidaConvolution.lean:323-354)
  |  returns: correction + support + exact node values + EXISTENTIAL C
  |           (uniform quadratic strip decay :331-333)
  v
fixed_window_finite_mellin_surjective
    (ConnesWeilRH/Source/CC20YoshidaNearZeros.lean:1153-1182)
  |  proves: the Mellin evaluation vectors SPAN the target space
  |          (windowedFiniteMellinVector_span_top)
  v
span/separation argument
    (CC20YoshidaNearZeros.lean:1120-1149)
  |  a proper subspace of the value space is contained in a hyperplane
  |  kernel; a test with nonzero kernel integral separates
  |  (Submodule.exists_le_ker_of_lt_top)
  v
g := windowedPositiveIntervalCompactTestCombination c
     (a finite linear combination with Finsupp coefficients c)
```

```text
VERDICT V1.  The mechanism proves SURJECTIVITY, not boundedness.
The separating-functional argument controls nothing about the
coefficients c, hence nothing about ||g||.  The constants C_b, C_c
consumed by the F1/F2/F3 chain are existential decay constants, and
NO norm of the constructed detector exists anywhere in the interface.
```

Consequences:

```text
(a) The [1379] norm budget is NOT extractable from the current
    mechanism — verified at source, closing the recon question.
(b) F3 is unaffected: its late-N choice consumes C_b only through the
    decay antecedent, which needs existence, not size.
(c) Any budget producer must be a NEW quantitative construction.
```

## 2. Coordinate facts: the budget is norm-invariant

```text
laplaceAt_compactLogTestOfWindow_eq_mellin
    (CC20YoshidaConvolution.lean:60-71):
    laplaceAt (compact-log pullback of h) s = mellin h s   — NO shift:
    Mellin's u^(s-1) du and the log Jacobian cancel exactly.
```

The compact-log pullback is an exact isometry between the Mellin-side
and bridge-side norms:

```text
Integral |h(e^x)|^2 dx = Integral |h(u)|^2 du/u      (u = e^{±x}),
```

so `||g||_2` in [1377]-[1379] IS the Mellin-side `L^2(du/u)` norm of
the register test — no conversion constant enters the budget. (The
orientation `e^{±x}` in the source is immaterial; both are isometric.)

## 3. The budget producer is a quantitative interpolation theorem (N2β spec)

Work on the positive window `(A, B)` with `0 < A < 1 < B` (register
class; `x`-window `(a, b) = (log A, log B)`). The Gram of the
evaluation functionals has the elementary entries

```text
Gamma(w_i, w_j) = Integral[A..B] u^(w_i + conj(w_j)) du/u
                = (B^(w_i + conj(w_j)) - A^(w_i + conj(w_j)))
                  / (w_i + conj(w_j)),
```

positive definite on distinct nodes, and `[1379]` Lemma E gives the
minimal interpolation norm `K_loc = y* Gamma^(-1) y`.

```text
Theorem shape (N2beta).  For every eps > 0 and every value pattern y
on distinct nodes w_1..w_N, there is a smooth compactly supported test
h (in the register class) with

  mellin h (w_j) = y_j  for all j,            and
  ||h||_{L^2(du/u)} <= (1 + eps) * sqrt(y* Gamma^(-1) y).
```

Construction (paper): `c := Gamma^(-1) y`; taper `eta_eps` in
`C_c^oo(A, B)` with `eta_eps -> 1` pointwise; take
`h_eps := (Sum_j c_j u^(conj(w_j))) * eta_eps`. Exact values: solve
`Gamma(eps) c' = y` with `Gamma(eps)` the tapered Gram
(`Gamma(eps) -> Gamma` entrywise, inversion stable for small eps);
norm: `||h_eps||^2 = y* Gamma(eps)^(-1) y -> y* Gamma^(-1) y`. This is
the [1377] Lemma A-prime extremizer logic upgraded from one evaluation
to finitely many.

Assembly budget. The detector is `base * correction` in the register's
convolution (`laplaceAt_convolution`, values multiply), so by Young

```text
||g_det||_2 <= ||base||_2 * ||corr||_1,
||f * g||_1 <= ||f||_1 * ||g||_1,
```

and `L^1` norms of kernel combinations are bounded by
`Sum_j |c_j| * ||u^(conj(w_j)) eta_eps||_1 <= Sum_j |c_j| * C(w_j)`,
`C(w) := Integral[A..B] u^(Re w) du/u` — all explicit. The producer's
output is a detector with EXACT node data and a fully explicit norm
budget `(1 + eps) * B(y_targets, y_zeros)`.

Closure observation (the point of the recon):

```text
(J1) of [1379] reads  x* > 2 C_min / delta  with  x* = 1 / K_loc,
i.e. exactly  K_loc < delta / (2 C_min).
```

The ratio condition and the budget condition are THE SAME inequality
on the two sides of the interpolation theorem. Branch A's entire
content is therefore: realize `K_loc` up to `(1 + eps)` — one
quantitative interpolation theorem, well-posed, with the theorem
shape above.

## 4. Formalization ledger (the N2beta Lean campaign, componentized)

1. L^2 interface export (shared prerequisite with N1d): a `||.||_2`
   accessor on the test class + the §2 isometry lemma.
2. Gram machinery: `Gamma` as a matrix over the node Finset; positive
   definiteness / inversion for distinct nodes (the existing span
   machinery of CC20YoshidaNearZeros.lean:1120-1149 supplies the
   independence).
3. Taper construction: `eta_eps` in the register class, dominated
   convergence for `Gamma(eps) -> Gamma`, eps-loss bookkeeping.
4. Young convolution bounds against the register's convolution
   (support additivity already present,
   CC20YoshidaConvolution.lean:386-399).
5. Recast of F1/F2 with the quantitative interpolant: the existential
   constants become `(1 + eps)`-quantified ones. Backward
   compatibility: F3 remains valid as the unconditional existence
   entry point; the quantitative entry point is an ADDITION, not a
   replacement.

## 5. What this record does NOT do

- No digits: `K_loc` is not evaluated numerically for the register's
  node list; the budget fit `(1+eps) K_loc < delta/(2 C_min)` in the
  near-line band stays symbolic. That fit question is the natural
  N1e-with-prereg target (rig, 1373 amendment protocol) — its answer,
  not this recon, decides the practical health of branch A.
- Branch A vs B remains owner-facing ([1379] §4); this record
  establishes that A is well-posed and formally reachable, not that
  it closes cells.
- `C_min` remains the global-window worst case of [1378]; moment
  control can only shrink it.

## 6. Honesty ledger

- SOURCE READBACK + PAPER design; no Lean statement, no numerical
  claim. RH NOT claimed; stop word unchanged (gate Lean certificate,
  1358).
