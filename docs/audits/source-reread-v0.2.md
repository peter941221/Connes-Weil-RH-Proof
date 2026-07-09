# Source Reread Audit For Lean Readiness

Status: v0.2 Lean-preparation audit.

This audit checks whether the manuscript's external source dependencies are
clear enough to become Lean boundary declarations. It does not independently
prove the cited source theorems. It records the source locations that must be
treated as imported theorem interfaces when Lean work begins.

Official source packages checked:

| label | arXiv source endpoint | source file |
|---|---|---|
| CCM24 | https://arxiv.org/e-print/2310.18423 | `mainc2m24fine.tex` |
| CCM25 | https://arxiv.org/e-print/2511.22755 | `mc2arXiv.tex` |
| CC20 | https://arxiv.org/e-print/2006.13771 | `weil-compo.tex` |

## Result

The result is good for Lean preparation.

The critical source-line ranges cited by the manuscript are present in the
official arXiv source packages, and the checked ranges support a clean split
between:

```text
external source theorem interfaces
  |
  v
project transport / ledger lemmas
  |
  v
route theorem
```

This means the next Lean phase can start with axiomatized source theorem
interfaces instead of trying to formalize all analytic source papers at once.

## Critical Dependency Checks

| dependency | source lines checked | manuscript role | Lean boundary |
|---|---|---|---|
| CCM24 canonical semilocal model | `mainc2m24fine.tex:237-253`, `786-804` | defines `U_S`, `M_S`, `V_S=M_S U_S`, and the Fourier grading as reflection | imported source theorem |
| CCM24 support and Fourier transport | `mainc2m24fine.tex:761-771`, `983-1003` | supports Lemmas A and B for support/Fourier-support movement | imported source theorem plus project wrapper |
| CCM24 bounded comparison map | `mainc2m24fine.tex:806-823` | supports bounded comparison between source Hilbert models | imported source theorem |
| CCM24 Sonin-space comparison | `mainc2m24fine.tex:1050-1060` | supports fixed support-window comparison used by exhaustion | imported source theorem |
| CCM25 finite-prime, archimedean, and pole signs | `mc2arXiv.tex:445-470` | fixes `W_p`, `W_R=-W_infty`, `QW`, `Psi`, and `W_(0,2)` | imported source theorem |
| CCM25 restricted quadratic form | `mc2arXiv.tex:530-540` | supplies `QW_lambda` and the prime-power operator pairing | imported source theorem |
| CC20 archimedean support-square trace | `weil-compo.tex:378-387` | supplies the support-square trace template and `traceequa` | imported source theorem |
| CC20 trace-class verification | `weil-compo.tex:448-464` | supports the trace-class part of Lemma 2 | imported source theorem plus project smoothing wrapper |
| CC20 Mellin and half-density convention | `weil-compo.tex:2014-2030` | fixes the transform convention used in the final RH exit | imported source theorem |
| CC20 positivity criterion | `weil-compo.tex:2072-2085` | supplies Proposition C.1, the final RH exit | imported source theorem |
| CC20 quantized calculus trace ideal | `weil-compo.tex:2106-2121` | supplies the trace-ideal template used by Lemma 2 | imported source theorem plus project wrapper |
| CC20 signs and normalizations | `weil-compo.tex:2131-2165` | fixes `u_infty`, `qd u`, and the archimedean sign | imported source theorem |

## Lean Impact

The first Lean milestone should not attempt to formalize the full analytic
content of CCM24, CCM25, or CC20.

Instead, the formalization should introduce a source-interface layer:

```text
ConnesWeilRH/Source/CCM24.lean
ConnesWeilRH/Source/CCM25.lean
ConnesWeilRH/Source/CC20.lean
```

Each file should declare the imported theorem statements needed by the route
proof, with names and hypotheses matching the manuscript. The project-owned
Lean work should then prove the route composition from those interfaces.

## First Lean Axiom Interfaces

The following names are recommended as the initial imported theorem interface.
They are intentionally manuscript-facing names, not source-paper notation:

| Lean-facing name | source | content |
|---|---|---|
| `ccm24_canonical_semilocal_model` | CCM24 | canonical fixed-`S` Hilbert model and grading transport |
| `ccm24_support_transport` | CCM24 | support and Fourier-support transport through `eta_S` / `theta_S` |
| `ccm24_bounded_comparison` | CCM24 | bounded comparison map with bounded inverse |
| `ccm25_qw_definition` | CCM25 | `QW(f,g)=Psi(f^* * g)` and sign decomposition |
| `ccm25_qw_lambda_formula` | CCM25 | restricted `QW_lambda` formula and `T(n)` pairing |
| `cc20_archimedean_trace_square` | CC20 | archimedean support-square trace template |
| `cc20_trace_class_template` | CC20 | trace-class and quantized-calculus trace ideal template |
| `cc20_mellin_half_density` | CC20 | Mellin/Fourier/half-density convention |
| `cc20_finite_vanishing_rh_exit` | CC20 | finite-vanishing Weil positivity criterion implying RH |

## Residual Checks Before Lean Code

These checks are not new mathematical ingredients. They are packaging checks
needed before opening `lakefile.toml`.

| gate | why it matters | status |
|---|---|---|
| Convert manuscript theorem names into stable Lean-facing names | Lean names become expensive to rename after dependencies form | ready |
| Freeze source theorem hypotheses | route proof must not rely on hidden assumptions | ready for first pass |
| Split external theorems from project lemmas | prevents circular formalization | ready |
| Record trace-class terms as explicit hypotheses or theorem outputs | Lean cannot infer analytic domain legality from prose | ready for interface design |
| Decide how much analytic content remains axiomatized in phase 1 | first Lean phase should certify route composition, not all source papers | ready |

## Verification Commands Run

```text
git status --short
git diff --check
official arXiv source package download from the three e-print endpoints above
line-range extraction from the three source files listed above
```
