# 017 QW--Prolate Feasibility Plan

Date: 2026-07-11

Status: active rejection-first mathematical feasibility experiment. This is
not yet an RH implementation plan. Plan 016 remains rejected. No route consumer
is to be rewired and no new Lean interface is to be built until the spectral
selection gates below have a proved mathematical producer.

AI session start:

```text
owner:              primary Codex session
cwd:                Windows project repository
lane:               QW_lambda low-spectrum / prolate feasibility
old weak path:      numerical or graphical QW/prolate agreement
files allowed:      this plan, MEMORY.md, new 017 proof notes, later isolated
                    source/audit modules owned by this lane
files forbidden:    current 016 dirty Lean files, UnconditionalSkeleton.lean,
                    RouteTheorem.lean, old route consumers, README.md
smallest WSL build: none before a theorem-grade mathematical gate exists
focused axiom audit: none before a Lean theorem is introduced
expected output:    a proof or rejection of each spectral bridge, starting
                    with the lowest even QW cluster
```

## 1. Result First

### Hard feasibility gate

Plan 017 becomes an executable RH route only if one proves, without RH or an
equivalent global Weil-positivity input, that there is a sequence
`lambda_j -> infinity` and normalized lowest eigenvectors `xi_j` of the genuine
closed Weil form operators `A_(lambda_j)` such that:

```text
1. the spectral bottom of A_(lambda_j) is a simple isolated eigenvalue;
2. xi_j is even under u |-> u^-1;
3. nonzero scalars c_j exist for which
     c_j * FourierMellin(xi_j) -> Xi
   uniformly on compact subsets of |Im z| < 1/2.
```

The lane is rejected if a named counterexample or asymptotic obstruction shows
that no such sequence can satisfy one of these statements. It remains partial,
not accepted, if it proves only finite-cutoff numerics, small Rayleigh
quotients, proximity to the whole near-radical subspace, or convergence of the
explicit proxy `k_lambda` without identifying the genuine lowest eigenvector.

### Logical consequence

The three statements above are sufficient for an unconditional proof of RH:

```text
simple-even lowest state
  -> every FourierMellin(xi_j) has only real zeros
  -> compact-open convergence to Xi in |Im z| < 1/2
  -> Hurwitz excludes every nonreal Xi zero in that strip
  -> every nontrivial zeta zero has real part 1/2
  -> _root_.RiemannHypothesis.
```

This implication is a route-legitimacy result. It does not assert that the
three spectral statements are true.

## 2. What Counts As Solved

Feasibility is accepted only after all of the following have theorem-grade
proofs with one consistent normalization of `QW_lambda`, `A_lambda`, the
prolate functions, the summation map `E`, and the Xi Fourier--Mellin transform:

```text
F0  genuine QW_lambda owner and parity decomposition
F1  quantitative low-cluster comparison with a prolate model
F2  selection of the first even state inside that cluster
F3  strict separation from the odd spectral bottom
F4  compact-open convergence of the selected state transform to Xi
F5  Hurwitz/RH bridge with no hidden premise
```

A useful F1 theorem must control spectral projections or an effective
low-cluster matrix. A typical acceptable shape is:

```text
P_low A_lambda P_low = M_lambda + E_lambda
||E_lambda|| = o(gap_1(M_lambda)),
```

where `P_low` is tied to the genuine QW low spectral cluster and `M_lambda` has
an explicitly simple first even eigenvalue. Equivalent resolvent, Riesz
projection, or quadratic-form estimates are allowed.

## 3. What Does Not Count

Reject the following as insufficient:

```text
QW_lambda(k_lambda) -> 0
||(A_lambda - mu_lambda) k_lambda|| -> 0 without a relative gap
overlap observed in finite Galerkin matrices
agreement of plotted eigenfunctions
Gram--Schmidt candidates without a uniform error theorem
prolate eigenvalue asymptotics without transport to QW_lambda
finite-N simple-even without an infinite-dimensional stability theorem
convergence of zero lists without compact-open convergence of holomorphic maps
any proof using RH, global QW positivity, SourceRH, detector coverage, or an
RH-conditioned Weil Hilbert-space factorization
```

The first two statements locate a vector near a low spectral cluster. The
known cluster has dimension approximately `2 * lambda^2`; they do not select
its first eigenvector.

## 4. Current Evidence

### 4.1 Local code evidence

The project already has lower Xi and strip facts that can serve F5 later:

```text
ConnesWeilRH/Source/CC20YoshidaNearZeros.lean:41
  sourceNontrivialZero_re_lt_one

ConnesWeilRH/Source/CC20YoshidaNearZeros.lean:145
  sourceNontrivialZero_zero_lt_re

ConnesWeilRH/Source/CC20ZetaCounting.lean:298
  completedRiemannXi_eq_mul_completedRiemannZeta

ConnesWeilRH/Source/CC20ZetaCounting.lean:320
  completedRiemannXi_eq_zero_of_sourceNontrivialZero
```

No current project declaration constructs `A_lambda`, its form domain,
compact resolvent, parity restrictions, or its lowest eigenprojection. The
selected CCM25 owner is a scalar explicit-formula foundation, not this
operator.

### 4.2 Primary source evidence

Connes--Consani--Moscovici define the genuine restricted Weil form and prove
the associated operator exists with discrete lower-bounded spectrum:

```text
Zeta Spectral Triples
https://arxiv.org/abs/2511.22755
mc2arXiv.tex:530-575   QW_lambda and form core
mc2arXiv.tex:578-613   A_lambda and discrete spectrum
```

Connes--van Suijlekom prove the unconditional real-zero theorem from a simple,
isolated, even lowest eigenvector:

```text
Quadratic Forms, Real Zeros and Echoes of the Spectral Action
https://arxiv.org/abs/2511.23257
Araki-final-oct25.tex:1366-1391
```

The explicit prolate proxy has the required transform limit:

```text
Zeta Spectral Triples
mc2arXiv.tex:1352-1383
FourierMellin(k_lambda) -> Xi uniformly on closed substrips of
|Im z| < 1/2.
```

The same source names the two missing theorems:

```text
mc2arXiv.tex:1389-1396
  simple-even spectral bottom
  k_lambda approximates a scalar multiple of xi_lambda
```

The earlier prolate construction supplies only candidate vectors and numerical
comparison:

```text
Spectral Triples and Zeta-Cycles
https://arxiv.org/abs/2106.01715
Spectraltriples.tex:181-193  near-radical mechanism and about 2*lambda^2 modes
Spectraltriples.tex:741-760  approximate parity, Gram--Schmidt candidates,
                            and graphical coincidence
```

The 2024 semilocal paper repeats the qualitative mechanism and does not give a
QW/prolate operator-norm or spectral-projection comparison:

```text
Zeta Zeros and Prolate Wave Operators
https://arxiv.org/abs/2310.18423
mainc2m24fine.tex:187-198
```

## 5. First-Principles Dependency Chain

```text
explicit QW_lambda quadratic form
  |
  +-- closed lower-semibounded form
  |     -> selfadjoint A_lambda with compact resolvent
  |
  +-- inversion symmetry
  |     -> H_even (+) H_odd
  |     -> A_lambda^even (+) A_lambda^odd
  |
  +-- time/frequency near-intersection
        -> prolate modes
        -> E(prolate modes)
        -> a growing QW near-radical cluster
              |
              +-- cluster comparison theorem
              +-- first-state effective matrix
              +-- even/odd bottom comparison
              |
              v
        genuine simple-even xi_lambda
              |
              +-- compare xi_lambda with k_lambda in a weighted norm
              |     strong enough for compact-open transform convergence
              |
              v
        FourierMellin(xi_lambda) -> Xi
              |
              v
        Hurwitz -> RH
```

The central unknown is the vertical arrow from the growing cluster to one
selected first state. Smallness alone cannot supply it.

## 6. Rejection-First Research Order

Attack the most likely failure first. Do not advance to a later gate while an
earlier gate lacks either a proof or an explicit surviving hypothesis.

### Gate R1. Lowest even cluster selection

Question:

```text
Can the first two even QW eigenvalues be asymptotically separated inside the
prolate near-radical cluster with an error strictly smaller than their gap?
```

First experiment:

```text
choose the first two normalized even prolate-derived candidates e0_lambda,
e1_lambda;

compute the exact 2 x 2 compression
  B_lambda(i,j) = QW_lambda(ei_lambda, ej_lambda),
splitting every entry into
  archimedean + pole + finite-prime;

derive a remainder bound for coupling to the orthogonal complement;

compare that remainder with the eigenvalue gap of B_lambda.
```

Pass:

```text
one eigenvalue of the effective block has a provably simple main term and
the total block/complement error is little-o of the first gap along an
explicit sequence lambda_j -> infinity.
```

Partial:

```text
the compression is explicit but the complement coupling or relative error is
not smaller than the proposed gap.
```

Reject the proposed two-mode selection mechanism:

```text
the leading block is degenerate, the error is necessarily of the same or
larger order than the gap, or higher near-radical modes contribute at leading
order.
```

If two modes are insufficient but a structured finite or growing effective
matrix is visible, replace R1 by that exact model. Do not call this a pass.

R1 selects only inside the proposed low even cluster. It cannot by itself show
that the selected positive minuscule state is the bottom of the full operator.

### Gate R1B. Full-bottom ownership

Question:

```text
Is the state selected inside the even prolate cluster actually below every
other even mode, every odd mode, and every possible negative QW direction?
```

This is a separate RH-sensitive gate. If the selected eigenvalue is proved
positive and is the full spectral bottom along a cofinal sequence
`lambda_j -> infinity`, then `QW_(lambda_j)` is positive on every vector in
those intervals. Every fixed compactly supported test eventually belongs to
one such interval, so this yields global Weil positivity and hence RH. That is
a legitimate proof route, but it is the main arithmetic theorem, not a routine
spectral-perturbation corollary.

Pass only with an unconditional lower bound on the orthogonal complement of
the selected state. A finite-mode computation, an even-sector result, or
absence of negative eigenvalues in Galerkin numerics does not count.

### Gate R2. Full low-cluster transport

Prove a Riesz-projection, resolvent, or min--max theorem identifying the low
QW cluster with the prolate-derived subspace. The target must remain uniform
as the cluster dimension grows like `2 * lambda^2`.

Reject any proof whose constants grow faster than the relative gap it needs to
protect.

### Gate R3. Even/odd bottom order

Prove along the same sequence:

```text
lambda_1(A_lambda^even) < lambda_1(A_lambda^odd).
```

Parity invariance alone does not count. Perron--Frobenius/Krein--Rutman can be
used only after proving a genuine positivity-improving realization of the
relevant shifted or transformed operator; the explicit prime translations do
not make this automatic.

### Gate R4. Selected-state transform convergence

After R1--R3, prove a weighted estimate strong enough to imply compact-open
convergence on each closed substrip. A sufficient shape is, for every
`alpha < 1/2`,

```text
integral exp(alpha * |x|) * |c_lambda xi_lambda(x) - k_lambda(x)| dx -> 0.
```

Ordinary `L2` convergence on expanding intervals is insufficient.

### Gate R5. Hurwitz and Mathlib RH bridge

Only after R1--R4 survive, formalize the lowest-risk final theorem:

```text
existence of a compact-open convergent sequence of nonzero holomorphic
functions with real zero sets, limiting to Xi
  -> Xi has only real zeros
  -> _root_.RiemannHypothesis.
```

## 7. Static Rejection Scans

Before accepting any 017 theorem or note, scan its dependencies and prose for:

```text
SourceRH
RiemannHypothesis as an input
global QW positivity
no-off-line source-zero
detector criterion coverage
"assume RH"
"under RH"
stored simple-even or convergence fields
finite Galerkin numerics presented as an infinite-dimensional theorem
```

Representative code scan:

```text
rg -n "SourceRH|RiemannHypothesis|NoOffLine|DetectorCriterion|Assume RH|under RH|fullWeilPositivity" \
  ConnesWeilRH/Source ConnesWeilRH/Dev -g "*.lean"
```

## 8. Implementation And Verification Policy

Phase R1 begins as mathematics and exact computation, not route code.

Allowed before R1 passes:

```text
source-line audits
symbolic derivations
certified finite-dimensional experiments used to discover a theorem
isolated proof notes under docs/proofs
small standalone Lean lemmas for exact identities or counterexamples
```

Forbidden before R1 passes:

```text
new RouteCertificate fields
new source interfaces that store the desired spectral theorem
UnconditionalSkeleton rewiring
full repository builds
claims that numerics establish asymptotic separation
```

When a theorem-grade Lean target exists, author on Windows, sync one way to a
clean WSL ext4 mirror, and use the repository lock. The initial expected narrow
targets are new 017 source/audit modules only. Route and Dev builds begin after
R4, not before.

Focused audits must include:

```lean
#check @declaration_name
#print declaration_name
#print axioms declaration_name
```

No accepted theorem may contain `sorryAx`, a project axiom, or a theorem-valued
premise that states the spectral selection or convergence conclusion.

## 9. Outcomes

```text
accepted feasibility:
  R1--R4 have unconditional theorem-grade producers; create the 017 RH
  implementation plan and then formalize R5.

partial:
  an exact effective matrix or cluster theorem is proved, but relative
  separation or weighted convergence remains open.

blocked:
  use only after the same external-data or user-input blocker repeats under
  the project blocked threshold; mathematical difficulty alone is not blocked.

rejected:
  a named theorem/counterexample disproves the required sequence, or a proved
  asymptotic shows the proposed error cannot be smaller than the selecting gap.
```

## 10. Immediate Work Item

Start Gate R1. Produce a source-normalized formula ledger for

```text
QW_lambda(e0_lambda,e0_lambda)
QW_lambda(e0_lambda,e1_lambda)
QW_lambda(e1_lambda,e1_lambda)
```

where `e0_lambda,e1_lambda` are the first two even Gram--Schmidt vectors built
from the corrected prolate functions satisfying the two Poisson conditions.
The ledger must state which equalities are exact, which are asymptotic, and
which constants are uniform in `lambda`. The first decision is whether a
two-mode effective gap exists at a scale larger than every uncontrolled term.

### 2026-07-11 R1 first result

Status: partial; R1 survives the first algebraic rejection test.

The source-normalized `h_0,h_4` combination with zero integral has exact point
defect proportional to `chi_0-chi_2`, and its out-of-band Fourier leakage has
an exact squared norm expressed through `1-chi_0^2` and `1-chi_2^2`. The full
Poisson formula turns the lower support tail into the sum of that Fourier
leakage and the point-defect term. See:

```text
docs/proofs/017_qw_prolate_r1_first_verdict.md
```

This does not yet identify the QW ground state. The next gate is a uniform
bound transporting the exact tail defects into the QW low spectral projection
with loss smaller than the first relative gap.

### 2026-07-11 R1 tail and R1B refinement

Status: partial. The Poisson-tail mechanism survives as a research target, but
the implication from `L2` leakage to a `QW_lambda` estimate is invalid because
`QW_lambda` is an unbounded closed form. See:

```text
docs/proofs/017_qw_prolate_tail_and_bottom_verdict.md
```

The formal identity

```text
QW(P g_lambda,P g_lambda) = QW((1-P)g_lambda,(1-P)g_lambda)
```

requires `g_lambda=E(h_lambda)` to be a radical vector in a common extended
form domain. The source radical theorem assumes both `h(0)=0` and
`integral h=0`, while the exact finite-`lambda` proxy has a nonzero point
defect. The next R1 theorem must prove this larger-domain identity and an
explicit logarithmic form-norm bound; it may not infer either from the `L2`
leakage norm.

R1B is now split into two gates:

```text
R1B-owner: selected simple even state is the full spectral bottom;
R1B-sign:  its lowest eigenvalue is nonnegative.
```

The owner statement alone does not imply RH. Owner plus sign along a cofinal
sequence implies global Weil positivity by support exhaustion and is therefore
the RH-level arithmetic theorem. Qualitative high-frequency coercivity from
the archimedean `log |t|` symbol does not close the owner gate because no
uniform complement bound relative to the growing prolate cluster is known.

### 2026-07-11 final feasibility decision

Status: rejected as a guaranteed executable RH route. See:

```text
docs/proofs/017_final_feasibility_verdict.md
```

The logical real-zero/Hurwitz implication remains valid. The rejection is at
the producer level. General-support even-simplicity has now been reduced to a
critically tight scalar Herglotz resolvent inequality but not proved. The
margin is of the same order as the minuscule even/odd bottom gap, so the exact
Poisson `L2` leakage and qualitative complement coercivity do not decide it.
The required ground-state/proxy compact-open convergence is itself the
RH-closing assertion and has no lower relative spectral-projection theorem.

Do not implement R2--R5 or add route certificates under plan 017. A future
route may reuse the valid real-zero theorem, the exact Poisson defects, and the
rank-one Herglotz reduction only after a new arithmetic theorem proves the
near-resonant inequality with an explicit uniform margin or replaces it with
another genuinely lower producer.
