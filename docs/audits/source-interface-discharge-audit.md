# Source Interface Discharge Audit

Status: attack plan for removing the source-conditional boundary.

This audit starts from the current Lean and manuscript state. It does not
declare RH proved. Its purpose is narrower and more useful: identify exactly
which imported source-interface contracts must be discharged before the route
can move from source-conditional evidence to a proof artifact.

## Current Boundary

The present route has three verified layers:

```text
route proof packages
  |
  v
Lean route composition from explicit interfaces
  |
  v
Mathlib's _root_.RiemannHypothesis
```

The missing layer is below the route proof packages:

```text
CCM24 / CCM25 / CC20 source interfaces
  |
  v
formal or referee-checked proofs of those exact contracts
```

Evidence:

| evidence | current state |
|---|---|
| manuscript status | `docs/manuscripts/connes-weil-rh-proof-draft.md:3-10` says the draft is source-conditional |
| three-battle audit | `docs/audits/three-battle-completion-audit.md:74-78` says the three-battle phase passes at route-evidence level but is not a Lean proof |
| Lean final theorem | `ConnesWeilRH/Route/RouteTheorem.lean:26-33` proves `_root_.RiemannHypothesis` from `RouteCertificate inputs` |
| source interfaces | `ConnesWeilRH/Source/CCM24.lean`, `CCM25.lean`, and `CC20.lean` provide the imported contracts |
| current axiom audit | `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` reports only `[propext, Classical.choice, Quot.sound]` for the route composition |

The axiom audit is good evidence about the route composition. It is not evidence
that the source interfaces themselves have been formally proved.

## Discharge Matrix

### CCM24

| Lean contract | source lines | what must be proved or imported | first failure mode to attack |
|---|---|---|---|
| `ccm24CanonicalSemilocalModel` | `mainc2m24fine.tex:237-253,786-804` | construct the fixed-`S` Hilbert model, scaling action, `V_S=M_S U_S`, and Fourier grading used by the route | model mismatch between source Hilbert space and route test object |
| `ccm24SupportTransport` | `mainc2m24fine.tex:761-771,983-1003` | prove support and Fourier-support transport for the source-backed fixed-`S` test and its convolution square | support containment uses a route-local window instead of the source window |
| `ccm24BoundedComparison` | `mainc2m24fine.tex:806-823` | produce bounded comparison maps with bounded inverse, strong enough for ledger transport | comparison map exists abstractly but does not preserve the trace/norm class used downstream |
| `ccm24SoninComparison` | `mainc2m24fine.tex:1050-1060` | prove fixed support-window Sonin comparison and exhaustion compatibility | exhaustion changes the order of fixing `g`, `I`, `S_A`, graph order, and `lambda` |

CCM24 should be attacked first at the level of transport legality, not by
building all semilocal analysis at once. The route uses CCM24 mainly to prevent
fixed-`S` drift: the same source-backed test must carry support, Fourier support,
window containment, bounded comparison, and Sonin exhaustion.

### CCM25

| Lean contract | source lines | what must be proved or imported | first failure mode to attack |
|---|---|---|---|
| `ccm25QWDefinition` | `mc2arXiv.tex:445-470` | prove `QW(f,g)=Psi(f^* * g)` plus the sign split for pole, archimedean, and finite-prime terms | sign convention for `Psi` differs from the route's positive-trace inequality |
| `ccm25QWLambdaFormula` | `mc2arXiv.tex:530-540` | prove the restricted `QW_lambda` formula with the correct prime-power pairing | restricted formula uses a different support or lambda convention than Theorem 1 |
| `ccm25FinitePrimeNormalization` | `mc2arXiv.tex:445-470,530-540` | prove global and restricted finite-prime coverage plus term normalization | hidden empty-support error or missing prime-power atom in the restricted index set |
| `ccm25PoleNormalization` | `mc2arXiv.tex:465-470,533-535` | prove the pole functional matches the restricted pole pairing used by the ledger | pole channel is killed under the wrong evaluation convention |

CCM25 is the highest-risk source interface for sign and finite-prime mistakes.
The current Lean split is useful because it exposes three separate finite-prime
targets:

```text
GlobalPrimeIndexCoverageStatement
RestrictedPrimeIndexCoverageStatement
FinitePrimeTermNormalizationStatement
```

Do not collapse these back into one equality. Coverage and normalization are
different proof obligations.

### CC20

| Lean contract | source lines | what must be proved or imported | first failure mode to attack |
|---|---|---|---|
| `cc20ArchimedeanTraceSquare` | `weil-compo.tex:378-387` | prove the support-square trace formula and identify it with the source no-defect trace leg | using positivity before identifying the traced operator |
| `cc20TraceClassTemplate` | `weil-compo.tex:448-464,2106-2121` | prove Hilbert-Schmidt, trace-class, and cyclicity legality for every term used by Theorem 1 | cyclic trace move applied outside trace-class hypotheses |
| `cc20MellinHalfDensityConvention` | `weil-compo.tex:2014-2030` | prove the Mellin/Fourier half-density convention used by test conversion and RH exit | half-density convention mismatch between `g`, `F_g`, and vanishing evaluations |
| `cc20FiniteVanishingRhExit` | `weil-compo.tex:2072-2085` | prove the finite-vanishing Weil-positivity criterion implies Mathlib RH | source criterion is accepted but not bridged to Mathlib's exact `RiemannHypothesis` |
| `cc20SignsAndNormalizations` | `weil-compo.tex:2131-2165` | prove the `u_infty`, `qd u`, and archimedean sign normalization used by the ledger | archimedean sign is reversed when moving from source notation to route notation |

CC20 is the final exit risk. Even if the route proves full Weil positivity, the
project still needs an exact bridge from the source finite-vanishing criterion to
Mathlib's canonical RH statement.

## Attack Order

The route should now be attacked in this order:

```text
1. CCM25 sign / finite-prime / pole normalization
     |
     v
2. CC20 trace legality and Mellin convention
     |
     v
3. CCM24 support-window transport and fixed-test exhaustion legality
     |
     v
4. CC20 finite-vanishing RH exit to Mathlib RH
```

Why this order:

| step | why it comes here |
|---|---|
| CCM25 first | sign, pole, and finite-prime normalization can invalidate the route even if all operator transport is correct |
| CC20 trace legality second | positivity is only meaningful after Hilbert-Schmidt, trace-class, and cyclicity gates are proved |
| CCM24 third | support transport must be checked after the exact test and restricted Weil form are fixed |
| CC20 RH exit last | the final exit should be bridged only after the positivity input has the exact same meaning as the source criterion |

## Immediate Next Proof Target

The current CCM25 restricted-read-off target has two proof packages:

```text
CCM25RestrictedReadOffDischarge(lambda, g)
```

Proof packages:

```text
docs/proofs/ccm25-restricted-read-off-discharge.md
docs/proofs/ccm25-finite-prime-support-pairing-discharge.md
```

It should prove, in one notation, that for the source-backed fixed-`S` test:

```text
1 < lambda
support and Fourier support lie in the CCM24 window contained in [lambda^-1, lambda]
F_g = g^* * g
finite-prime atoms visible to F_g are covered by the restricted prime index set
finite-prime terms use the same von Mangoldt and prime-power pairing convention
the restricted pole pairing is the source pole functional
QW_lambda(g,g) has the exact sign used by the positive-trace inequality
```

This target is the best first strike because it touches the most common failure
points in RH routes:

```text
wrong test
wrong sign
wrong finite-prime support
wrong pole convention
wrong lambda window
```

If this target fails, the failure is local and actionable. If it passes, the
remaining CC20 and CCM24 work can be checked against a fixed normalization spine.

The next concrete CC20 target is:

```text
CC20TraceLegalityMellinDischarge(g)
```

Proof package:

```text
docs/proofs/cc20-trace-legality-mellin-discharge.md
```

It proves, at source-interface proof-package level, that the route has the
right order of operations:

```text
Hilbert-Schmidt gate
  -> ordinary trace-class positive trace
  -> legal cyclic trace moves
  -> CC20 source trace read-off
  -> Mellin half-density bridge to F_g=g^* * g
```

This target blocks the most dangerous CC20 failure mode: taking positivity or
cyclicity before the traced operator has been proved trace-class.

The final CC20 exit target is:

```text
CC20FiniteVanishingRhExitDischarge
```

Proof package:

```text
docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md
```

It bridges:

```text
route triple vanishing
route full Weil positivity
```

to the source criterion:

```text
Connes--Consani Proposition C.1 with F={0,1/2,1}
```

The package also records the sign invariant required at the exit:

```text
QW(g,g) >= 0
  is the same statement as
sum_v W_v(g * bar(g)^sharp) <= 0
```

after the CC20 and CCM25 sign/read-off discharge packages have fixed the source
normalization.

The dedicated sign-bridge target is:

```text
QWToCC20WeilInequalitySignBridge(g)
```

Proof package:

```text
docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md
```

It proves the exact inequality-direction bridge:

```text
QW(g,g) = - sum_v W_v(g * bar(g)^sharp)
```

and therefore:

```text
QW(g,g) >= 0
  ->
sum_v W_v(g * bar(g)^sharp) <= 0.
```

This target should become Lean-visible before certification. The current
`fullWeilPositivity : Prop` interface is too weak to rule out a sign-flipped
final exit by itself.

The source-RH definition bridge target is:

```text
SourceRHToMathlibRH
```

Proof package:

```text
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md
```

It decomposes the last naming risk into four bridges:

```text
source zeta = Mathlib riemannZeta
source non-trivial zero = Mathlib zero with negative-even exclusion and s != 1
source critical line = s.re = 1/2
CC20 source RH -> _root_.RiemannHypothesis
```

This target should become Lean-visible before certification. A source theorem
that concludes "RH" is not enough unless the predicate is transported to
Mathlib's exact definition.

The CCM24 transport target is:

```text
CCM24SupportWindowTransportDischarge(S,I,lambda,g)
```

Proof package:

```text
docs/proofs/ccm24-support-window-transport-discharge.md
```

It proves, at source-interface proof-package level, that the route uses one
source-backed CCM24 window through:

```text
eta_S support transport
Fourier-support transport
V_S=M_S U_S canonical coordinate
bounded comparison with bounded inverse
theta_S / Sonin fixed-window comparison
QW_lambda and Cdef exhaustion
```

This target blocks fixed-`S` drift: the positive trace, restricted Weil form,
and endpoint-strip exhaustion cannot silently use different cutoff windows.

## Completion Criteria

This audit is complete only when every row above has one of these stronger
evidence types:

| evidence type | acceptable? | reason |
|---|---:|---|
| formal Lean theorem with audited axioms | yes | strongest internal evidence |
| accepted imported theorem with exact hypothesis bridge | yes | acceptable source-discharge substitute |
| manuscript proof plus source-line referee audit | partial | useful before Lean, but not final formal certification |
| route-evidence proof package only | no | proves route intent, not source theorem truth |
| exploration note or slogan | no | not stable enough for the final RH claim |

The objective "thoroughly break through RH" is not achieved until the final row
of this matrix has formal or externally accepted evidence and the final theorem
is re-audited against those discharged interfaces.
