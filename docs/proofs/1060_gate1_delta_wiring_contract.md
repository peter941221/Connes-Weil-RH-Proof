# 1060 - GATE 1 delta wiring: the (141)-(143) chain now has a Lean contract and a certificate producer

Date: 2026-08-30.  Follows 1056 (payload inventory), 1057 s2 (verbatim
chain), 1059 s5 (re-scope).  Lean change: new Dev leaf
`ConnesWeilRH/Dev/C1CC20ArchimedeanComparisonWiring.lean` + paired
`...Audit.lean`.

Result up front: **GOOD.**  The delta payload - previously just a docstring
sentence "What is NOT claimed here" in the GATE 1 assembly - now has (a) a
named contract `CC20ArchimedeanComparison` whose fields are exactly the
paper's three chain steps, (b) a producer theorem that composes the
contract into the already-consumed `CC20EndpointTraceCertificate`, and (c) a
composition theorem straight to `0 <= qw g`.  Zero new analysis was invented;
the brick is the wiring, and the remaining analytic payload is now a
three-field checklist instead of a prose paragraph.

## 1. The contract map (paper -> assembly -> certificate)

```text
+--------------------------------------------------------------+
| paper step           | Lean field (new contract)             |
+----------------------+--------------------------------------+
| (142) tr = W_inf + E | h142 : trace = cc20WInfinityLog       |
|                      |   g.convolutionSquare + eTerm         |
| chain E <= gamma *   | hEchain : eTerm <=                    |
|   |k_hat(0)|^2/...   |   (gamma / log 2) * normSq            |
|                      |   (laplaceAt k (1/2))                 |
| (143) k_hat(0) =     | h143 : laplaceAt k (1/2) =            |
|   -2 g_hat(0)        |   -(2 : CC) • laplaceAt g (1/2)       |
| (140) sign of trace  | trace_nonnegative : 0 <= trace        |
+----------------------+--------------------------------------+
```

```text
+--------------------------------------------------------------+
|            GATE 1 ARCHIMEDEAN WIRING, POST-1060               |
|                                                              |
|  C1CC20Gate1Assembly              C1CC20ArchimedeanReadback  |
|   K_I-side residual               W_inf readback +           |
|   trace-(4a/log2)rank <= 0        CC20EndpointTrace          |
|        |                          Certificate {coefficient,  |
|        |                          trace, 0<=trace,           |
|        |  (NOT claimed there,     endpoint_bound}            |
|        |   1046/1057)                     ^                  |
|        v                          |        |                  |
|  gamma payload (140)              |  NEW 1060 leaf:           |
|  supplies coercivity  ----------- |  CC20Archimedean          |
|                                    |  Comparison --(producer)->|
|  E(f) <= gamma/log2 * |k_hat|^2  <-|  three-field contract   |
|                                    |                         |
|  qw_nonneg_of_archimedeanComparison -> 0 <= C1SameOwnerWeil.qw g
+--------------------------------------------------------------+
```

The producer `cc20EndpointTraceCertificate_of_archimedeanComparison`
instantiates `coefficient := 4 * gamma / Real.log 2` - the exact eq-(141)
constant of 1057 s2 - and the whole proof is the vanishing mechanism:

1. half-node vanishing + h143 force `normSq (laplaceAt k (1/2)) = 0`, so
   `E(f) <= 0` through hEchain (no sign needed on gamma);
2. eq-(142) then reads `trace <= W_infinity`;
3. zero-node vanishing kills the certificate's own rank coordinate via the
   existing `cc20RankOneBadDirection_eq_zero_of_vanishesOn_cc20Triple`.

## 2. The coordinate subtlety, recorded deliberately (1057 s5 adjacent)

The chain rank lives at `laplaceAt`-s = 1/2 (the paper's `rho = 0` under the
half-density substitution: `ghat(rho) = laplaceAt (1/2 + i rho)`-style
readback through `C1.healthyMellinReadoff`), while the CERTIFICATE rank
coordinate is `laplaceAt`-s = 0 (the paper's `rho = i/2`).  These are
DIFFERENT nodes and the leaf never identifies them; both are members of the
owner's triple vanishing set {0, 1/2, 1} (paper nodes {rho = 0, -i/2, +i/2},
the union of the intro-theorem and final-theorem vanishing sets), so every
consumer hypothesis holds by design.  This is the safe resolution of the
1057 s5 intro-vs-final flag: our detector tests vanish at ALL THREE nodes,
so whichever convention the published chain intended, the wiring theorem is
correct.  If a future consumer ever weakens the vanishing set, this leaf
must be revisited first.

## 3. Build evidence (AGENTS 7a/7b protocol: log, not exit code)

```text
target: lake build ConnesWeilRH.Dev.C1CC20ArchimedeanComparisonWiring
        ConnesWeilRH.Dev.C1CC20ArchimedeanComparisonWiringAudit
footer: Build completed successfully (3607 jobs).
errors: none (no lines matching ^error:)
sorryAx scan of audit log: 0

#print axioms (all three public declarations):
  laplaceAt_half_eq_zero_of_vanishesOn_cc20Triple
  cc20EndpointTraceCertificate_of_archimedeanComparison   [noncomputable def,
    Type-valued certificate, hence a def]
  qw_nonneg_of_archimedeanComparison
    -> [propext, Classical.choice, Quot.sound]   (standard three only)

Build-iteration lessons (this session):
  * `CC20YoshidaConvolution.CompactLogTest` is a DEF-namespace prefix for
    `laplaceAt`, NOT the type: the structure lives in
    `CCM25Concrete.CompactLogConvolution`; type positions need the open +
    bare `CompactLogTest` (mirrors the readback leaf exactly).
  * a structure with Real fields is Type-valued: producer is
    `noncomputable def`, not `theorem`.
  * `rw [...] at H.field` rejects structure projections: use a calc chain.
```

## 4. What delta still requires (the honest residual)

The three contract fields are analytic premises; landing them is exactly the
GATE 1 payload work already inventoried, now with target statements:

```text
h142  trace identification tr(rep(f) S) = W_inf(f) + E(f):
      needs the rep-theoretic trace object on this owner; this is the same
      "trace" the assembly already carries abstractly (`trace : Lp ... -> R`
      with htrace identifying it to -(4/log 2) q(...)).  Wiring the two is
      an owner-identification brick, not new analysis.
hEchain + h143:  the (140)/(141) gamma-side package:
      (a) construct k from g on the log owner (k(u) = u^(1/2) int_0^u
          v^(-1/2) g(v) d*rho; in log coordinates a half-integrated
          test with a support proof using the vanishing at the one-node
          s = 1, i.e. rho = -i/2 - the FINAL-theorem node);
      (b) the coercivity chain E(f) = <xi|N_I xi> <= gamma |<xi_0|xi>|^2 -
          the gamma paper-scale payload (Bessel branch closed only for
          lam < 1; CC20 lam ~= 1.05158).
So: delta is now gated on gamma, not on an unstructured prose obligation.
```

## 5. Sources

```text
ConnesWeilRH/Dev/C1CC20ArchimedeanComparisonWiring.lean (this batch)
ConnesWeilRH/Dev/C1CC20ArchimedeanReadback.lean (certificate + consumers)
ConnesWeilRH/Dev/C1CC20Gate1Assembly.lean:147-190 (residual + NOT-claimed note)
ConnesWeilRH/Dev/C1HealthyTestSpace.lean:65 (healthyMellinReadoff)
ConnesWeilRH/Source/CC20RHExit.lean:21-29 (triple vanishing set = {0,1/2,1})
docs/proofs/1057 section 2 (verbatim (141)-(143) + chain), section 5 (flag)
build log: /home/peter/delta_wiring_build.log (WSL ext4 mirror)
```
