# Connes-Weil RH Proof

This repository records a source-conditional Connes-Weil route to the Riemann
Hypothesis.

External reviewers should be able to judge the project from this README. The
supporting audit and proof-package files are cited so a reviewer can check the
rows that need source verification.

## Status

```text
route-evidence composition: closed
local pre-Lean proof-package matrix: complete
accepted-source certification: open
external referee certification: open
Lean proof status: open
public proof status: source-conditional
```

Here `closed` means every row needed by the route has a named local
proof-package or audit artifact. It does not mean that an outside referee has
accepted the analytic row, that a source paper contains the exact imported
theorem, or that Lean has checked the row.

The repository does not claim journal acceptance, Clay acceptance, community
acceptance, or completed Lean verification. It gives a route whose outside
analytic inputs stay visible.

## Short Verdict

The route is a conditional composition theorem:

```text
If the named CCM24, CCM25, and CC20 source-facing rows are accepted with the
normalizations used here, then the fixed-S positive-compression route gives RH.
```

The route does not import RH. It also does not import the CCM25 finite-operator
spectral convergence program. It tries to avoid that program by using a
fixed-test scalar restriction bridge:

```text
QW_lambda(g,g) = QW(g,g)
```

for the same fixed source test once the support lies in the restricted interval.

The hard mathematical questions for reviewers are narrow:

```text
1. Does the ordinary positive trace have the same scalar normalization and
   lambda-scale as the CCM QW_lambda read-off plus named ledgers and Cdef?

2. Does the project correctly identify every positive-trace defect as either a
   killed rank/pole ledger or endpoint-strip Cdef, with no hidden fourth
   positive defect?

3. Does the fixed-test choice of S(g) return the same global QW(g,g) and the
   same CC20 Weil sum needed by Proposition C.1?

4. Do the CCM25 finite-prime atoms, weights, pairings, and signs match the
   source formula pointwise before any sum is formed?

5. Does the final sign bridge give
   QW(g,g) = - sum_v W_v(F_g), with the same F_g used in the trace read-off?
```

If questions 1 and 2 fail, the route fails at the positive-trace-to-Weil
read-off. If questions 3 through 5 fail, the route may still have a fixed-S
calculation, but it cannot feed CC20 Proposition C.1.

## Primary Sources

| source | arXiv | role in the route |
|---|---|---|
| Connes--Consani--Moscovici 2024 | https://arxiv.org/abs/2310.18423 | fixed-`S` semilocal Hilbert model, support transport, Fourier compatibility, Sonin comparison |
| Connes--Consani--Moscovici 2025 | https://arxiv.org/abs/2511.22755 | Weil form `QW`, restricted form `QW_lambda`, pole and finite-prime normalizations |
| Connes--Consani 2020 | https://arxiv.org/abs/2006.13771 | archimedean support-square trace, trace-class legality, Mellin convention, finite-vanishing RH criterion |

The source-line map is `docs/audits/source-reread-v0.2.md`.

The source-import legitimacy audit is
`docs/audits/source-import-legitimacy-audit.md`.

The accepted-source review checklist is
`docs/audits/accepted-source-certification-audit.md`.

The second external-opinion audit is
`docs/audits/second-external-opinion-audit.md`.

The accepted-source theorem upgrade ledger is
`docs/audits/accepted-source-theorem-upgrade-ledger.md`.

The accepted-source packet completion audit is
`docs/audits/accepted-source-packet-completion-audit.md`.

The CCM24 source-interface accepted-source packet is
`docs/audits/ccm24-source-interface-accepted-source-packet.md`.

The CCM25 source-interface accepted-source packet is
`docs/audits/ccm25-source-interface-accepted-source-packet.md`.

The CC20 trace source-interface accepted-source packet is
`docs/audits/cc20-trace-source-interface-accepted-source-packet.md`.

The first S2-B1 source-term certification packet is
`docs/audits/trace-scale-source-term-ledger.md`.

The sign/defect accepted-source packet is
`docs/audits/sign-defect-accepted-source-packet.md`.

The restricted-to-full accepted-source packet is
`docs/audits/restricted-to-full-accepted-source-packet.md`.

The final sign accepted-source packet is
`docs/audits/final-sign-accepted-source-packet.md`.

The CC20 exit accepted-source packet is
`docs/audits/cc20-exit-accepted-source-packet.md`.

The RH definition accepted-source packet is
`docs/audits/rh-definition-accepted-source-packet.md`.

The local pre-Lean completion gate is
`docs/audits/pre-lean-completion-audit.md`.

## Evidence Classes

Reviewers should separate four levels of evidence.

| class | meaning | current status |
|---|---|---|
| Source line located | The cited source file contains the object, formula, or theorem shape. | many rows |
| Project proof package | This repository gives a manuscript-level derivation from cited source inputs. | all local pre-Lean rows |
| Accepted-source row | A source theorem, external referee, or accepted proof confirms the exact statement and hypotheses. | open |
| Lean theorem | Lean proves the row and `#print axioms` leaves only approved source interfaces and foundations. | open |

The current repository reaches the second class for the full route. It does not
reach the third or fourth class for any source-interface row.

## Self-Review After The First External Opinion

The first external opinion identified four attack points. The repository now
answers each at route-evidence level, with explicit failure conditions.

| item | local answer | strongest remaining attack |
|---|---|---|
| B1 trace-scale compatibility | `PositiveTrace`, support-square trace, no-defect source trace, and `QW_lambda` are tied to one finite-lambda scalar; no untracked bulk term is allowed outside rank, pole, or endpoint-strip `Cdef`. | A referee can find a source-owned bulk or finite-part term not present in the named ledgers or `Cdef`. |
| B2 Sonin-projection repair | The route rejects replacing `Tr(A^*A)` by `Tr(S_lambda theta_S(F_g))`; any future replacement must prove a new trace-scale theorem and a nontrivial limit. | Someone can prove a normalized Sonin-projection scalar with positivity, same-scale read-off, and nonzero fixed-test limit. |
| B3 semilocal fourth defect | The Rows 1-7 ledger gives every possible cross-term a slot: source post-`Q`, fixed-S transport, rank, pole, or endpoint-strip `Cdef`. | A reviewer can exhibit a source term produced by fixed-S transport that is neither no-strip rank/pole nor endpoint-strip `Cdef`. |
| B4 dynamic `S(g)` | The route uses `S(g)` only as a fixed-test witness; after restricted-to-full, the output is global `QW(g,g)` and then the CC20 global Weil sum for the same `F_g`. | CC20 Proposition C.1 or another route step can be shown to require constants uniform in `g`, or the bridge can be shown to retain an `S`-dependent scalar. |

The project should not hide those attacks behind the phrase
`source-conditional`. A source-conditional route still needs exact imported
statements. If an imported statement is weaker than the row above, the route
stops at that row.

## Self-Review After The Second External Opinion

The second external opinion sharpened the same attack surface. It added a
stronger divergent-bulk model and two spectral-route cautions.

| item | local answer | strongest remaining attack |
|---|---|---|
| S2-B1 divergent bulk | The route keeps the B1 no-missing-bulk row as source-critical: `PositiveTrace = QW_lambda + Rank + Pole + CdefRemainder` must hold at one finite-lambda scale. | A referee can locate a source-owned `BulkScaleTerm ~ C log(lambda) ||g||^2` outside `QW_lambda`, rank, pole, and `Cdef`. |
| S2-B2 spectral pollution | The route does not use finite-dimensional spectral positivity to pass from `QW_lambda` to `QW`; it uses a fixed-test restriction-definition bridge. | A reviewer can point to a route step that imports spectral convergence, determinant convergence, or eigenvalue convergence. |
| S2-B3 even-sector assumption | The even-sector minimum-eigenvector claim belongs to the CCM25 spectral program and is not an accepted input here. | An accepted-source row can be shown to depend on that even-sector conjecture. |
| S2-B4 semilocal `S(g)` non-uniformity | The route uses `S(g)` as a fixed-test witness and returns the global scalar `QW(g,g)` for the same `F_g`. | A reviewer can show that CC20 or another route step needs constants uniform in `g`, or that the final scalar remains `S`-local. |

The second-opinion audit is:

```text
docs/audits/second-external-opinion-audit.md
```

## Accepted-Source Upgrade Work

The next phase is not more route packaging. It is accepted-source theorem
review.

The row-level ledger is:

```text
docs/audits/accepted-source-theorem-upgrade-ledger.md
```

It does not mark any row accepted-source. It states exact theorem candidates,
source anchors, current evidence, and blockers for external review.

The packet completion audit is:

```text
docs/audits/accepted-source-packet-completion-audit.md
```

It records that every source-facing row now has a review packet. It also records
that no row has yet become accepted-source by external referee, accepted proof,
or Lean theorem.

The three base source-interface packets are:

```text
docs/audits/ccm24-source-interface-accepted-source-packet.md
docs/audits/ccm25-source-interface-accepted-source-packet.md
docs/audits/cc20-trace-source-interface-accepted-source-packet.md
```

They cover the fixed-S model, CCM25 Weil objects, and CC20 trace legality
front end consumed by the later packets.

The first certification packet attacks S2-B1:

```text
docs/audits/trace-scale-source-term-ledger.md
```

That packet asks a referee to classify each source-owned scalar in the
positive-trace read-off as `QW_lambda`, rank, pole, or endpoint-strip `Cdef`.
If a source-owned scalar remains outside those classes, it becomes a new
`BulkScaleTerm` obstruction and the route stops at the positive-trace read-off.

The next two certification packets are:

```text
docs/audits/sign-defect-accepted-source-packet.md
docs/audits/restricted-to-full-accepted-source-packet.md
```

The first packet asks a referee to accept the Rows 1-7 sign/defect chain as a
single source-owned classification theorem. The second packet asks a referee to
accept `QW_lambda(g,g)=QW(g,g)` from the CCM25 restriction definition and
fixed-test support, with no spectral convergence input.

The final-exit packets are:

```text
docs/audits/final-sign-accepted-source-packet.md
docs/audits/cc20-exit-accepted-source-packet.md
docs/audits/rh-definition-accepted-source-packet.md
```

They cover the sign equality `QW(g,g)=-sum_v W_v(F_g)`, the CC20
finite-vanishing exit, and the transport from the CC20 source RH conclusion to
the standard RH predicate.

## Falsification Tests For Reviewers

A reviewer can reject the route by finding one of these concrete failures:

| test | failure mechanism | file to inspect first |
|---|---|---|
| ordinary trace scale | `Tr(A^*A)` contains a lambda-growing bulk term not included in rank, pole, or endpoint-strip `Cdef` | `docs/proofs/trace-scale-compatibility-proof-package.md` |
| source convention conversion | the no-defect source trace uses a finite-part convention that loses positive-trace nonnegativity | `docs/proofs/trace-scale-compatibility-theorem-contract.md` |
| spectral shortcut import | `QW_lambda -> QW` uses finite-operator spectra instead of the CCM25 restriction definition plus fixed-test support | `docs/audits/restricted-to-full-qw-source-readiness-audit.md` |
| even-sector assumption import | a route source row relies on the even-sector minimum-eigenvector conjecture | `docs/audits/source-import-legitimacy-audit.md` |
| hidden fourth defect | fixed-S semilocal transport creates a cross-term outside the Rows 1-7 classification | `docs/audits/semilocal-fourth-defect-ledger.md` |
| finite-prime support | a visible prime-power atom of `F_g` is omitted, duplicated, or assigned the wrong `Lambda(n)<g|T(n)g>` term | `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md` |
| dynamic `S(g)` | the fixed-S read-off returns an `S`-local scalar rather than global `QW(g,g)` | `docs/audits/s-local-global-quantifier-audit.md` |
| final sign | `QW(g,g)` equals the CC20 Weil sum with the opposite sign or for a different test object | `docs/proofs/final-sign-bridge-proof-package.md` |
| RH definition bridge | the CC20 source zero predicate does not match Mathlib's `riemannZeta s = 0`, trivial-zero exclusion, pole exclusion, and `s.re=1/2` target | `docs/proofs/rh-definition-bridge-proof-package.md` |

A reviewer should reject the route if one test fails with a source-backed
counterexample.

## Proof Spine

```text
  One compact test g
        |
        v
  F_g = g^* * g
        |
        v
  +--------------------------------------------------+
  | CCM24 fixed-S coordinate                         |
  | V_S = M_S U_S                                    |
  | one support window, one Fourier window           |
  +--------------------------------------------------+
        |
        v
  +--------------------------------------------------+
  | CC20 trace legality                              |
  | Hilbert-Schmidt -> trace-class -> cyclicity      |
  +--------------------------------------------------+
        |
        v
  +--------------------------------------------------+
  | Positive fixed-S trace                           |
  | Tr(A_(S,lambda,g)^* A_(S,lambda,g)) >= 0         |
  +--------------------------------------------------+
        |
        v
  +--------------------------------------------------+
  | Source read-off                                  |
  | positive trace = QW_lambda(g,g)                  |
  |                  + rank ledger                   |
  |                  + pole ledger                   |
  |                  + endpoint-strip Cdef remainder |
  +--------------------------------------------------+
        |
        v
  +--------------------------------------------------+
  | Triple vanishing                                 |
  | hat g(0)=hat g(i/2)=hat g(-i/2)=0                |
  | kills rank and pole ledgers                      |
  +--------------------------------------------------+
        |
        v
  +--------------------------------------------------+
  | Fixed-test exhaustion                            |
  | Cdef(lambda,g) -> 0                              |
  | QW_lambda(g,g) = QW(g,g) for fixed g             |
  +--------------------------------------------------+
        |
        v
  +--------------------------------------------------+
  | Final sign bridge                                |
  | QW(g,g) = - sum_v W_v(F_g)                       |
  | QW(g,g) >= 0 -> sum_v W_v(F_g) <= 0              |
  +--------------------------------------------------+
        |
        v
  +--------------------------------------------------+
  | CC20 Proposition C.1                             |
  | finite vanishing set F={0,1/2,1}                 |
  +--------------------------------------------------+
        |
        v
  Mathlib-style Riemann Hypothesis target
```

## Core Objects

The route fixes a finite set `S` of places containing the archimedean place.
CCM24 supplies the semilocal transform:

```text
V_S = M_S U_S.
```

For `lambda > 1`, the route uses the transported projection:

```text
P_(S,G)(lambda) = V_S P_S(lambda) V_S^(-1).
```

For a compactly supported test function `g`, the route sets:

```text
F_g = g^* * g.
```

The route uses only admissible tuples:

```text
supp(g) subset I,
I subset [lambda^(-1), lambda],
S contains every finite prime visible to F_g.
```

This keeps the positive trace, the restricted Weil form, and the endpoint-strip
exhaustion on the same test object.

The finite set `S` may depend on the fixed test `g`. The route uses it only as
an auxiliary witness for that fixed test. After the restricted-to-full bridge,
the output is the global scalar `QW(g,g)`, and the final sign bridge gives the
CC20 global Weil sum for the same `F_g`. The route does not use a uniform
finite `S` or constants uniform over all tests.

Relevant files:

```text
docs/proofs/source-test-convolution-compatibility.md
docs/proofs/source-object-definition-spine-discharge.md
docs/proofs/source-common-test-tuple-theorem-contract.md
docs/audits/source-object-theorem-discharge-ledger.md
docs/audits/s-local-global-quantifier-audit.md
```

## Step 1: Fixed-S Model

The fixed-`S` model prevents drift between source objects. The route needs the
same `g`, `F_g`, window, Fourier window, comparison map, and Sonin coordinate
through the trace and Weil-form read-off.

Review target:

```text
Do the CCM24 source hypotheses give the exact fixed S, support window,
Fourier window, bounded comparison, and Sonin comparison used by this route?
```

Relevant files:

```text
docs/proofs/ccm24-support-window-transport-discharge.md
docs/proofs/ccm24-semilocal-object-normalization-discharge.md
docs/audits/source-interface-discharge-completion-audit.md
```

## Step 2: Trace Legality

The positive trace may be used only after the analytic gates are in place:

```text
operator identity
        |
        v
Hilbert-Schmidt witness
        |
        v
trace-class witness for A^* A
        |
        v
cyclicity witnesses for each trace move
        |
        v
ordinary positive trace
```

The positive operator is:

```text
A_(S,lambda,g)
  =
P_hat_(S,G)(lambda) P_(S,G)(lambda) theta_S(g).
```

After those gates:

```text
PositiveTrace^G_(S,lambda)(g)
  =
Tr(A_(S,lambda,g)^* A_(S,lambda,g))
  >= 0.
```

Review target:

```text
Do the CC20 trace-class, cyclicity, Mellin, and sign conventions apply to the
exact transported source object used here?
```

Relevant files:

```text
docs/proofs/cc20-trace-legality-mellin-discharge.md
docs/proofs/cc20-analytic-trace-legality-spine-discharge.md
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md
docs/proofs/trace-scale-compatibility-theorem-contract.md
docs/proofs/trace-scale-compatibility-proof-package.md
```

## Step 3: Positive Trace Read-Off

The route does not use:

```text
Tr(A^* A) >= 0
        |
        v
QW_lambda(g,g) >= 0
```

That implication is false without a defect analysis.

The route instead claims the source read-off:

```text
PositiveTrace^G_(S,lambda)(g)
  =
QW_lambda(g,g)
  +
Rank_(S,I)(g)
  +
PoleJetExtra_(S,I)(g)
  +
R_(S,I,lambda)(g),

|R_(S,I,lambda)(g)|
  <=
C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

The sign/defect bridge is the main obstruction. The local project answer is a
Rows 1-7 proof chain:

```text
Rows 1-2:
  CC20 source remainder object,
  sign orientation,
  post-Q image.

Rows 3-7:
  fixed-S post-Q transport,
  projection-defect split,
  rank/pole identification,
  endpoint-strip Cdef domination,
  no hidden positive defect.
```

Review target:

```text
Does the Rows 1-7 chain classify every CC20 post-Q remainder term as killed
rank/pole ledger or endpoint-strip Cdef, with no fourth positive defect?
```

Relevant files:

```text
docs/audits/sign-defect-blocker-audit.md
docs/audits/sonin-prolate-defect-discharge-ledger.md
docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md
docs/proofs/sonin-prolate-defect-referee-discharge.md
```

## Step 4: Killing The Ledgers

The route imposes:

```text
hat g(0) = hat g(+i/2) = hat g(-i/2) = 0.
```

Then the rank and pole ledgers vanish:

```text
Rank_(S,I)(g) = 0,
PoleJetExtra_(S,I)(g) = 0.
```

The positive-trace identity gives the finite-lambda lower bound:

```text
QW_lambda(g,g)
  >=
-C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

This is weaker than finite-lambda positivity. It becomes useful only after the
fixed-test endpoint-strip remainder tends to zero.

Relevant files:

```text
docs/proofs/source-rank-pole-ledger-identification-proof-package.md
docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md
docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md
```

## Step 5: Fixed-Test Exhaustion

The route sends `lambda` to infinity while keeping `g`, `I`, and the finite
prime visibility set fixed.

The route needs:

```text
Cdef_(S_A,I,lambda,J)(g) -> 0.
```

Then it uses the fixed-test bridge:

```text
for lambda large enough,
QW_lambda(g,g) = QW(g,g).
```

This step does not import finite-operator spectral convergence or determinant
convergence. It uses the CCM25 restriction definition for the same fixed test
object.

Review target:

```text
Does fixed-test QW_lambda(g,g)=QW(g,g) follow from the CCM25 restriction
definition plus common-test, window, and finite-prime support stabilization,
without spectral convergence?
```

Relevant files:

```text
docs/audits/restricted-to-full-qw-source-readiness-audit.md
docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md
docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md
docs/proofs/restricted-to-full-qw-bridge-proof-package.md
```

## Step 6: Final Sign Bridge

CCM25 uses:

```text
QW(f,g) = Psi(f^* * g).
```

The route needs the final sign bridge:

```text
QW(g,g) = - sum_v W_v(F_g).
```

Therefore:

```text
QW(g,g) >= 0
        |
        v
sum_v W_v(F_g) <= 0.
```

That is the inequality direction needed for CC20 Proposition C.1.

Review target:

```text
Does QW(g,g)=-sum_v W_v(F_g) hold with the displayed signs, so that
route nonnegativity becomes the CC20 nonpositivity hypothesis?
```

Relevant files:

```text
docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md
docs/proofs/final-sign-bridge-spine-discharge.md
docs/proofs/final-sign-bridge-theorem-contract.md
docs/proofs/final-sign-bridge-proof-package.md
```

## Step 7: CC20 Proposition C.1 And RH Target

The final finite vanishing set is:

```text
F = {0, 1/2, 1}.
```

The triple vanishing matches this set under the CC20 Mellin convention:

```text
s = 1/2 - i t

t = 0     -> s = 1/2
t = +i/2  -> s = 1
t = -i/2  -> s = 0
```

The route then transports the CC20 source RH conclusion to the Mathlib-style
target, including zeta equality, zero transport, negative-even exclusion, pole
exclusion, and the critical-line equation `s.re = 1/2`.

Review target:

```text
Does the CC20 source RH conclusion match Mathlib's canonical RH predicate with
the same zeta function, zero predicate, exclusions, and critical-line equation?
```

Relevant files:

```text
docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md
docs/proofs/cc20-rh-exit-object-normalization-discharge.md
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md
docs/proofs/rh-definition-bridge-spine-discharge.md
docs/proofs/rh-definition-bridge-theorem-contract.md
docs/proofs/rh-definition-bridge-proof-package.md
docs/proofs/source-conditional-rh-route-closure-proof-package.md
```

## Non-Importable Shortcuts

These claims must not enter the route as accepted theorem inputs.

| shortcut | route replacement |
|---|---|
| CCM25 finite-operator spectral convergence to zeta zeros | fixed-test scalar `QW_lambda(g,g)=QW(g,g)` through the CCM25 restriction definition |
| determinant convergence toward Xi | not used in the route theorem |
| replacing the positive trace by `S_lambda theta_S(g)` | rejected repair path unless a new trace-scale compatibility theorem proves positivity, same-scale read-off, and nontrivial limit |
| automatic harmless Sonin/prolate defect | Rows 1-7 sign/defect proof chain |
| automatic CCM24 transport for post-`Q` derivative, boundary, and tail terms | Row 3 split into bulk graph transfer, boundary functional transfer, and series-tail bounded comparison |
| source-paper statement ending in "RH" equals Mathlib RH by name | RH definition bridge through zeta equality, zero transport, exclusions, and `s.re=1/2` |

## Review Checklist

External review should return a row-by-row verdict.

| row | reviewer question | local status |
|---|---|---|
| Trace-scale compatibility | Does the ordinary positive trace have the same scalar normalization and lambda-asymptotic scale as `QW_lambda + ledgers + Cdef`, with no missing divergent bulk or hidden finite-part subtraction? | project proof-package coverage |
| Sonin-projection repair path | Does the route avoid replacing the positive trace by a trivializing Sonin-projection scalar? | rejected repair path |
| Semilocal fourth-defect ledger | Does the route classify possible semilocal cross-terms as source post-`Q`, fixed-S transport, rank, pole, or endpoint-strip `Cdef` terms? | project proof-package coverage |
| S-local to global quantifier | Does the proof return a global `QW(g,g)` and CC20 Weil inequality for arbitrary `g` even though the auxiliary finite set `S(g)` depends on the fixed test? | route-evidence bridge |
| CCM24 fixed-S model | Do the CCM24 source hypotheses give the exact `V_S`, support window, Fourier window, bounded comparison, and Sonin comparison used here? | proof-package coverage |
| CCM25 Weil objects | Do `QW`, `Psi`, `QW_lambda`, pole terms, finite-prime terms, and signs match the route test object? | proof-package coverage |
| CC20 trace legality | Do Hilbert-Schmidt, trace-class, cyclicity, Mellin, and sign conventions apply to this transported source object? | proof-package coverage |
| Sign/defect bridge | Does the Rows 1-7 chain classify every CC20 post-`Q` remainder term as killed rank/pole ledger or endpoint-strip `Cdef`? | project proof-package closure |
| Restricted-to-full bridge | Does fixed-test `QW_lambda(g,g)=QW(g,g)` follow from restriction-definition and support stabilization, without spectral convergence? | route-evidence bridge |
| Final sign bridge | Does `QW(g,g)=-sum_v W_v(F_g)` have the right sign for CC20 Proposition C.1? | route-evidence bridge |
| RH definition bridge | Does the CC20 source conclusion match the Mathlib-style RH predicate? | route-evidence bridge |

Accepted responses should say one of:

```text
accepted as stated
accepted after listed correction
rejected for listed obstruction
requires formalization before judgment
```

## Lean Status

The repository has a segmented Lean scaffold:

```text
ConnesWeilRH.lean
ConnesWeilRH/
lakefile.toml
lean-toolchain
```

Lean work is not the current phase. The local pre-Lean gate records that all
proof-package rows are written, but accepted-source and external certification
remain open.

Before treating any future Lean theorem as a proof artifact, run:

```text
#print axioms <theorem_name>
```

The remaining axioms must be exactly the approved source interfaces plus
Mathlib/kernel foundations.

## Repository Layout

```text
docs/
  audits/
    pre-lean-completion-audit.md
    accepted-source-certification-audit.md
    accepted-source-theorem-upgrade-ledger.md
    accepted-source-packet-completion-audit.md
    ccm24-source-interface-accepted-source-packet.md
    ccm25-source-interface-accepted-source-packet.md
    cc20-trace-source-interface-accepted-source-packet.md
    second-external-opinion-audit.md
    trace-scale-source-term-ledger.md
    sign-defect-accepted-source-packet.md
    restricted-to-full-accepted-source-packet.md
    final-sign-accepted-source-packet.md
    cc20-exit-accepted-source-packet.md
    rh-definition-accepted-source-packet.md
    source-reread-v0.2.md
    trace-scale-compatibility-audit.md
    trace-scale-compatibility-discharge-attempt.md
    sonin-projection-repair-rejection-audit.md
    semilocal-fourth-defect-ledger.md
    s-local-global-quantifier-audit.md
    source-import-legitimacy-audit.md
    sign-defect-blocker-audit.md
  manuscripts/
    connes-weil-rh-proof-draft.md
  proofs/
    source-conditional-rh-route-closure-proof-package.md
    cc20-source-remainder-rows1-2-referee-discharge.md
    sonin-prolate-defect-referee-discharge.md

ConnesWeilRH/
  Segmented Lean route scaffold.

formalization/
  Lean readiness and interface planning notes.
```

## Verification Commands

For manuscript and audit hygiene:

```text
git diff --check
run the project unfinished-marker scan over docs
rg -n "[^\x00-\x7F]" docs README.md
```

For future Lean route work, build the segmented target only after the Lean
phase is reopened:

```text
lake build ConnesWeilRH
```

The current repository state is ready for outside mathematical review as
source-conditional route evidence. It is not an accepted-source certificate, a
completed Lean proof, or a public proof of RH.
