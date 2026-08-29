# 1049 - The non-paper Bessel branch and the (delta) reconnaissance

Date: 2026-08-29.  Follows 1048.  Two deliverables: (A) the GATE 1 T-side
payload is discharged from the assembly by a new accepted leaf, shrinking the
conditional chain; (B) the archimedean-comparison payload (delta) is pinned
to named CC20 displays from a verbatim HTML sweep.

Paper-scale correction, same date: part A is a specialized `lam < 1` branch,
not a discharge of the paper-facing payload.  CC20's reported scale is near
`1.05158 > 1`, so the general GATE 1 chain still needs its exceptional-vector,
complement-spectrum, and rank-one-repair certificate.  Proof 1050 supersedes
the earlier route-status interpretation while preserving the valid theorem.

## A. The non-paper Bessel branch (accepted under `lam < 1`)

`ConnesWeilRH/Dev/C1CC20Gate1BesselDischarge(+Audit).lean` exhibits concrete
gap data and discharges the `hT` premise of the GATE 1 assembly.  The
exhibit is the order-structure choice

    a := 1,  epsilon1 := (1 - lam)/2,  epsilon2 := 1 - lam,  ePrime free,

so `h_gap : epsilon1 < epsilon2` is exactly `0 < 1 - lam` and the flagship
premise `epsilon2 <= 1 - lam` holds by `le_refl`.  It is NOT the paper's
numeric scale (`a ~ 0.064`, `epsilon2 ~ 0.00441`); that stays tied to
payload (delta).  Accepted declarations:

| Declaration | Content |
| --- | --- |
| `cc20Eq115Gate1GapData` | the exhibit (proof fields discharged by `linarith`) |
| `cc20Eq115_exhibitedGapData_gamma_eq` | `gamma = 2 * ePrime` at the exhibit |
| `cc20Eq115_exhibitedGapData_band_iff` | paper band `294/100 < gamma < 2944/1000` iff `147/100 < ePrime < 1472/1000` |
| `cc20Eq115_gate1hT_exhibited` | the flagship `hT` at the exhibit, `ell := 0` |
| `cc20Eq115_negativeForm_le_rankOne_of_uniformGrid_bessel` | Lemma-`second` rank-one bound with NO `hT` premise: `-(2 ePrime) * q(K_I) <= 0` |
| `cc20Eq115_kf_defect_nonneg_of_uniformGrid` | at `ePrime := 1`: plain `0 <= q(K_I)` from the grid table alone |
| `cc20Eq115_gate1Residual_nonpositive_of_uniformGrid_bessel` | GATE 1 flagship residual `trace <= 0` with NO `hT` premise |

Net effect on the specialized conditional chain: at the concrete extracted table, the
`K_I`-side defect form is nonnegative - and the eq-(100)-identified endpoint
residual is nonpositive - from (i) a uniform-grid Fact-1 table for the
extracted profile, (ii) `ContinuousOn` of the endpoint displacement profile,
(iii) the endpoint kernel `MemLp` premise, and (iv) `lam in [0, 1)`.  The
T-side spectral block is gone only from the new `lam < 1` consumers.  The
paper-facing GATE 1 assembly still needs payload (alpha), the dependent grid
table (beta), paper-scale payload (gamma), and payload (delta).  The algebraic
`ePrime` interval does not bridge the incompatible `lam` regimes.

GATE 1 payload table after this batch:

| Payload | Status |
| --- | --- |
| alpha endpoint enclosure | OPEN (interval-ODE project; feeds the grid table) |
| beta joint grid table | OPEN (blocked by alpha) |
| gamma T-side coercivity | OPEN at the paper scale; Bessel accepted only for `lam < 1` |
| delta archimedean comparison | OPEN (pinned below) |
| gapData choice | CLOSED only inside the non-paper Bessel branch |

## B. (delta) reconnaissance: the CC20 comparison chain

Verbatim sweep of `arxiv.org/html/2006.13771` (2026-08-29).  The
archimedean side is organized by the following named displays:

1. eq (53): `W_infinity(f) = -integral f(rho^-1) tau(rho) d*rho` - the
   definition of the archimedean term; eq (54) is the double vanishing
   `integral f(rho) rho^{+-1/2} d*rho = 0`.
2. Theorem 7, eq (83): `Tr(theta(f) S) = W_infinity(f) +
   integral f(rho^-1) epsilon(rho) d*rho >= 0` - the trace functional on
   Sonin's space is positive; this is the comparison engine between the
   spectral side and `W_infinity`.
3. eq (101)-(102): `E_+(f) := integral f(x) epsilon(exp|x|) dx` and
   `E_+(Q_+ f) = -2 epsilon'(1_+) f(0) +
   integral_0^infty (f(x) + f(-x)) (Q epsilon)(exp x) dx`.
4. Proposition 5, eq (103)-(104): `N_I` is the bounded operator
   `<eta | N_I xi> = E_+(Q_+ f)`, `f = eta^* * xi`, and
   `N_I = -2 epsilon'(1_+) (Id - K_I)` with the `K_I` kernel normalized by
   `1/(2 epsilon'(1_+))` against `(Q epsilon)(exp|v|)`.
5. Remark 6: `Q epsilon(1) = 0`, so the diagonal integral of the `K_I`
   kernel vanishes - its trace is 0 for ANY window size.
6. Numerics (section 6.1-6.2): at the symmetric ROOT window
   `I = [-log 2/2, log 2/2]` the largest eigenvalue of
   `(2 epsilon'(1_+))^{-1} omega T_q` is `lambda_1 ~ 1.05177 > 1` (a SINGLE
   bad eigenvector), while the next eigenvalue is
   `lambda_2 ~ 0.687925`, and Lemma 8(iii) pins the residual spectrum
   inside `{lambda_max} cup [-2, lambda_2]` with `lambda_2 <= 0.772216`.
   The Lemma-`first` determinant condition appears verbatim as
   `a((c + b)|<zeta|xi_0>|^2 - b) >= bc` with `b = lambda_max - 1`,
   `c = 1 - lambda_2`, and `c > b` makes `a + c >= b` automatic.
7. Fact 1 (115), Lemma 3 (119), and (120)-(121) confirm the extracted
   table's provenance and the `epsilon_1 ~ 0.00122` gap.

RECON VERDICT: payload (delta) is the composition of Theorem-7 positivity
(83) with the Proposition-5 normalization (104): the archimedean comparison
must bound the eq-(100) residual `trace - (4 a / log 2) rank` of the GATE 1
flagship by `W_infinity(g^2)` evaluated at the convolution square.  In the
operator language of the repo: `E_+(Q_+ f) = -2 epsilon'(1_+) q(K_I)(xi)`
(eq 104), so the discharged brick's `0 <= q(K_I)` conclusion is exactly the
statement that `E_+(Q_+ f) <= 0` on ROOT-class tests - one W_infinity
comparison away from the Weil inequality `W_infinity(f) >= 0`.  The
remaining transcription obligations: eq (99)-(100) verbatim (the slope
identity behind `trace = -(4/log 2) q(K_I)`), and the verbatim blocks of
Lemma (first)/(second) and Theorem 8 (the HTML passage extraction does not
surface their display blocks; the b/c determinant text above is confirmed).

## Build evidence

Round 1: 1 root error - the implicit `{ell}` of the assembly consumers was
still a metavariable when the supplied `hT` term was checked; higher-order
unification of `?ell y` against the beta-reduced zero filler failed
("0 has type Real ... expected Prop").  Fix: pin `ell` with a NAMED argument
`(ell := fun _ => (0 : Real))` BEFORE `hT`.

An attempted large Round 2 is not acceptance evidence: its Lake child was
found compiling through the Windows-side checkout rather than the required
ext4 mirror, so it was terminated before completion.  Round 3 is the
acceptance run: a forced build from the ext4 mirror with an explicit
shell-level project `cd`, 3644 jobs, zero `error:` lines, the success footer,
zero `sorryAx`, and seven `#print axioms` reports containing exactly
`[propext, Classical.choice, Quot.sound]`.

New mechanics for AGENTS.md 7e: when feeding a term with a beta-reducible
function argument into an implicit-argument slot, instantiate the implicit
FIRST via named arguments; do not rely on higher-order pattern unification
to guess a constant function.
