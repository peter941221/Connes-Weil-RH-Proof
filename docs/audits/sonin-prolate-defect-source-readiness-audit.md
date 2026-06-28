# Sonin Prolate Defect Source Readiness Audit

Status: source-readiness audit for the sign/defect theorem contract.

Target contract:

```text
docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md
docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md
docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md
docs/audits/cc20-post-q-remainder-term-map.md
docs/audits/ccm24-fixed-s-post-q-transport-obstruction-audit.md
docs/proofs/cc20-post-q-derivative-domain-compatibility-theorem-contract.md
docs/audits/cc20-post-q-derivative-domain-source-decision-audit.md
docs/proofs/cc20-post-q-boundary-evaluation-transport-theorem-contract.md
docs/proofs/cc20-post-q-series-tail-bounded-comparison-theorem-contract.md
docs/proofs/source-endpoint-strip-cdef-domination-theorem-contract.md
docs/proofs/no-hidden-positive-defect-outside-cdef-theorem-contract.md
docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md
docs/proofs/sonin-prolate-defect-referee-discharge.md
```

This audit asks whether CC20, CCM24, or CCM25 already supplies an importable
theorem proving:

```text
Sonin/prolate defect
  =
rank ledger + pole ledger + endpoint-strip Cdef
```

for the fixed-S route. The answer is no.

## Source Evidence

| source | lines | what the source gives |
|---|---:|---|
| `weil-compo.tex` | `86-87` | CC20 says the Weil distribution and Sonin trace differ by a prolate-spheroidal term that must be controlled |
| `weil-compo.tex` | `488-509` | defines the archimedean trace-remainder `delta` and expresses the positive trace functional `L` |
| `weil-compo.tex` | `584-604` | proves `L` is positive and relates it to `W_infty` plus `delta` |
| `weil-compo.tex` | `875-878` | says proving Weil positivity requires controlling `D circ Q`; then refines `W_infty=L-D` into `W_infty=S-E` |
| `weil-compo.tex` | `1132-1140` | gives the positive Sonin functional and the prolate/coefficient error `epsilon` |
| `weil-compo.tex` | `1196-1199` | says one must analyze `E circ Q` to control `W_infty` |
| `weil-compo.tex` | `1338-1346` | gives a formula for `Q epsilon` and refers convergence control to the appendix |
| `weil-compo.tex` | `1260-1264` | says the formal `D_u` identity cannot be applied directly to `xi_n,zeta_n` because they are not in the domain of `D_u` |
| `weil-compo.tex` | `1267-1270`, `1308-1333` | derives the lower moving endpoint and upper fixed endpoint terms by boundary repair |
| `weil-compo.tex` | `2168-2185`, `2243-2250` | gives convergence and tail-control estimates for the `Q epsilon` series |
| `mainc2m24fine.tex` | `1050-1060` | gives a semilocal Sonin-space isomorphism for fixed `S` and `lambda` |
| `mainc2m24fine.tex` | `846-852` | warns that `N_S eta_S != eta_S N_infty` and `|.|_S^2 eta_S(f) != eta_S(|.|^2 f)` outside the archimedean case |
| `mc2arXiv.tex` | `530-540` | gives the restricted `QW_lambda` formula, but not the fixed-S trace defect decomposition |

Primary source pages:

```text
https://arxiv.org/abs/2006.13771
https://arxiv.org/abs/2310.18423
https://arxiv.org/abs/2511.22755
```

## What The Sources Do Prove

CC20 proves a local archimedean mechanism:

```text
positive Sonin trace functional
  =
W_infty
  +
prolate/coefficient remainder.
```

The relevant source formula is:

```text
tr(rep(f) S)
  =
W_infty(f) + integral f(rho^-1) epsilon(rho) d^*rho.
```

CC20 then reduces the problem to controlling the sign of the error after the
operator `Q` imposes the vanishing conditions.

The `E circ Q` side is explicit enough for item-level route search:

```text
Q epsilon
  =
bulk integral
  + moving boundary term
  + fixed boundary term
  + source-controlled series tail.
```

The detailed item map is:

```text
docs/audits/cc20-post-q-remainder-term-map.md
```

This supports the hostile objection rather than discharging it: the source
itself treats the difference term as a real analytic object to control.

## What The Route Needs

The fixed-S route needs a stronger theorem:

```text
PositiveTrace^G_(S,lambda)(g)
  =
QW_lambda(g,g)
  +
Rank_(S,I)(g)
  +
PoleJetExtra_(S,I)(g)
  +
R_(S,I,lambda,J)(g),

|R_(S,I,lambda,J)(g)|
  <= C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

The source evidence above does not supply this theorem. It gives:

```text
local archimedean Sonin/prolate structure
semilocal Sonin-space isomorphism
restricted Weil-form formula
```

It does not give:

```text
fixed-S positive trace defect
  =
rank + pole + endpoint-strip Cdef
```

## Gap Classification

| required leg | source status | judgment |
|---|---|---|
| local archimedean trace-remainder object | present in CC20 | import candidate |
| prolate/Sonin expansion of local remainder | present in CC20 | import candidate |
| item-level `E circ Q` formula | present in CC20 | source ingredient for Row 3 |
| convergence control for the `Q epsilon` series | present in CC20 appendix | source ingredient for Row 3 tail transport |
| semilocal fixed-S Sonin comparison | present in CCM24 | import candidate |
| automatic post-`Q` derivative/boundary/tail transport | not present; CCM24 warns against naive operator transport | hard blocker |
| post-`Q` derivative/domain fixed-S transport | theorem contract now stated; not found as a source theorem | hard blocker |
| source-import decision for derivative/domain transport | classified as project-proof-required | hard blocker remains at source-import level, but proof route narrowed |
| route-evidence proof for derivative/domain transport | proof package now written | project evidence only; not source-import or Lean discharge |
| post-`Q` boundary-evaluation fixed-S transport | theorem contract now stated; not found as a source theorem | hard blocker |
| post-`Q` series-tail bounded-comparison transport | theorem contract now stated; not found as a source theorem | hard blocker |
| fixed-S positive trace read-off to `QW_lambda` | project proof package | not source-discharged |
| transport of the CC20 post-`Q` items through fixed finite `S` | not found as a source theorem | hard blocker |
| identification of CC20 prolate remainder with route endpoint-strip `Cdef` | not found as a source theorem | hard blocker |
| exclusion of a fourth defect class | not found as a source theorem | hard blocker |
| Rows 1-7 project proof packages | written in repository proof packages | project proof-package level only |

## Required New Bridge

The next proof target is not another broad source-line audit. It is the bridge:

```text
CC20LocalProlateRemainder
  +
CCM24FixedSComparison
  +
CC20PostQRemainderFixedSSoninTransport
  +
FixedSTransportNormalForm
  ->
SoninProlateDefectEqualsEndpointStripCdef.
```

The proof must show that every source prolate/Sonin term transported through
the fixed-S route is one of:

```text
1. no-strip rank ledger,
2. no-strip pole ledger,
3. endpoint-strip Cdef term.
```

## Current Judgment

| question | answer |
|---|---|
| Does a source theorem discharge `SoninProlateDefectEqualsEndpointStripCdef`? | no |
| Do the sources contain relevant local and semilocal ingredients? | yes |
| Is this a contradiction in the route? | not yet |
| Is this still a hard blocker for RH certification? | yes |

The source-import status is:

```text
source ingredients located;
Rows 1-7 project proof packages written;
direct accepted source theorem still absent.
```
