# 1266 — G8 physical readback execution plan

Date: 2026-09-10.

Status: RESEARCH PLAN with P0 formally closed by record 1267.  It supplies no
`qw` sign and makes no RH claim.

Consumer: the healthy-`CompactLog`, selected-detector, same-owner B5/P2
consumer `G8SameOwnerReadbackData` of record 1257.  It is subordinate to map
records 003, 004, 006, and 007.

## 1. Starting point and notation

Fix one `SelectedWeilSquareOwner` with source test `g`, a Sonin scale
`lambda`, a finite prime-power family `S`, and the literal finite cutoff leg

```text
  C_n = (sourceInclusion lambda)†
          o (g8SourceCutoffPairData ... n).left.
```

There are two distinct positive finite-cutoff carriers:

```text
  T_n = the trace product of g8SourceCutoffPairData,
  P_n = C_n† (E† W_g E) C_n,    E = F + M.
```

`T_n` is the sequence consumed by the existing G8 readback contract.  `P_n`
is the physical-endpoint carrier.  They must not be treated as definitionally
equal.

The following are FORMAL Lean facts (records 1242--1265): both cutoff
families are trace class and positive; their finite traces have nonnegative
real part; and the physical carrier has the exact same-owner split

```text
  P_n = C_n† (M† W_g M) C_n + C_n† K_forward C_n.
```

Here `M` is the finite Euler metric coframe and `K_forward` is the internal
forward correction.  The identity retains the correction inside the positive
Gram.  It is not a finite-prime trace identity and does not imply a cutoff
limit.

## 2. Execution graph

```text
T_n (existing G8 contract)       P_n (positive physical endpoint)
             \                         /
              \                       /
               +---- G8-P0 -----------+
               exact same-owner carrier relation
                         |
                         v
               G8-P1: literal-C_n Euler/readback identity
                         |
                         v
               G8-P2: canonical internal remainder r_n
                         |
                         v
               G8-P3: r_n -> 0 and exact qw(g) limit
                         |
                         v
               G8-P4: assemble existing positive-trace consumer
                         |
                         v
                    0 <= qw(g)  [only then]
```

No arrow in this graph is licensed by a numerical experiment, by an uncut
cross-response identity, or by an owner-changing cyclic trace.

## 3. G8-P0 — carrier alignment (formally closed)

The axiom-clean finite-cutoff relation naming *both* actual carriers is now
proved in record 1267.  With `A` the literal G8 source leg, `J` the source
inclusion, `C = J† A`, and `D` its named complement, the exact relation is
The preferred target is an operator identity of the form

```text
  P_n = T_n + C_n† K_forward C_n
        - (C_n† J† G D_n + D_n† G J C_n + D_n† G D_n),
```

with every term on the same selected source carrier.  The three complement
channels are a real P1 obligation; they are not definitionally zero.

If this equality cannot be obtained, the only alternative is to select `P_n`
as a direct instance of the existing positive-trace consumer.  That branch
must state its own concrete readback fields; it may not introduce a generic
interface or silently replace `T_n` in `G8SameOwnerReadbackData`.

Implementation constraint: preserve the cutoff leg as an opaque named map.
The direct expansion of `g8SourceCutoffPairData.left` has a deterministic Lean
kernel timeout.  Use the already-owned channel-pair, source-compression, and
trace-cycle theorems instead of unfolding that leg.

Acceptance met: paired owning/audit builds are green with standard axioms
only, zero `sorryAx`, and the identity contains the literal cutoff, owner,
scale, and finite family (`1266_g8_p0_alignment_retry23.log`,
`1266_g8_p0_audit.log`).

## 4. G8-P1 — finite visible-prime comparison

Only after P0, derive a finite-cutoff operator/trace identity which keeps the
same `C_n` and decomposes the metric/Euler component into:

```text
  literal finite visible-prime Euler boundary trace
  + named archimedean/survivor/internal terms.
```

The existing uncut identity
`finiteEulerTargetCommutatorResponse = projectionResponse` is insufficient:
it removes the cutoff and lives on a different projection-response expression.
Likewise, the existing Euler-boundary trace theorem can be used only after an
explicit same-owner identification of its operator with the P0/P1 expression.

Acceptance: equality before any `Tendsto`; every summand retains the selected
test `g`, cutoff `C_n`, scale, and visible-prime family.

## 5. G8-P2 — canonical internal readback remainder

Define `r_n` only from the P1 equality: it is the exact sum of the non-Euler
terms left by that equality, including the P0 forward correction when the
alignment branch uses it.  Prove its realness using the established
self-adjoint physical trace and real Euler scalar.

Forbidden: choosing a scalar counterterm after taking traces, subtracting a
divergent external bulk, or assigning a vanishing property by a structure
field without an owner-level formula.

Acceptance: a finite-cutoff identity of real scalars with `r_n` definitionally
or propositionally tied to the P1 residual.

## 6. G8-P3 — analytic limit and exact Weil readback

Prove both analytic statements required by the positive-trace exit:

```text
  r_n -> 0,
  Re Tr(T_n) - r_n -> C1SameOwnerWeil.qw g,
```

or the corresponding two statements for `P_n` in the direct-physical branch.
The value equality must explicitly use the existing same-owner formula

```text
  qw(g) = - archimedeanTerm(g.convolutionSquare)
          - finitePrimeSum(g.convolutionSquare)
```

with its finite visible-prime owner.  Mere convergence to an unnamed finite
scalar is not a readback.  A bounded-response term cannot be declared a
vanishing remainder if an uncancelled cofinal window bulk remains.

Acceptance: no numerical premise, no external renormalization, and the two
convergence statements needed by the selected concrete consumer.

## 7. G8-P4 — contract assembly and capstone

For the alignment branch, construct `G8SameOwnerReadbackData` from P0--P3.
For the direct-physical branch, instantiate the already-existing
positive-trace bridge directly with the proved physical readback.  Invoke the
B5 healthy-detector contradiction only after the bridge yields `0 <= qw(g)`.

This is not a new universal B1 campaign: the consumer remains the selected
healthy detector and its finite visible prime-power set.

## 8. Kill conditions

Record a kill-ledger row in map 006 if a formal P0/P1 identity shows either:

1. the physical carrier necessarily changes owner or requires an external
   subtraction;
2. an uncancelled cofinal bulk prevents a zero remainder;
3. the finite-prime identity applies only after dropping the literal cutoff;
   or
4. the limiting scalar is formally incompatible with the same-owner `qw`
   formula.

An elaboration timeout is not a mathematical kill; it instead requires an
opaque-leg proof through the existing concrete owners.

RH is not claimed.
