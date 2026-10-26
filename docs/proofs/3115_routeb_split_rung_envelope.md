# Route-B split-rung envelope (record 3115)

Status: kernel-checked split-rung envelope and actual-cardinal two-sided
exterior bound; stored-owner numerical comparison passes at model grade.
The three cardinal pins, same-owner gate and RH remain unproved.

## Scope and decision

The owner is exactly the stored row-B capture in
`results/2722f_rowB_capture_data.json`: 56 correction nodes, eight target
nodes, the same target values, and Lean's tenth-power `poweredSeed`.
It is not the arbitrary-rho explicit owner of records 3111 and 3114.

The premise being investigated is the three wired cardinal pins consumed
by `fourPointContradictionRowBPoweredSeedStored3110`. The immediate decision
is whether the already proved derivative bounds still price below those
pins after correcting crossing-cell distances and including both infinite
tails. The bounds are 2, 8, 787283385/10000000, 1500 and 2000000000 at
orders 1, 2, 3, 4 and 7 respectively. No derivative value is inferred from
quadrature or the historical twelve-rung table.

Record 2729 is binding: degree 55 plus frequency weight 2 gives residual
degree 17 at order 4 and -13 at order 7. The four-rung envelope of 3112
is valid, but its full-line quadratic pin premise in 3113 cannot close
for this stored correction owner. Its historical finite-scan success
does not remove that obstruction.

Completion requires a same-run historical control, exact stored-node
capture checks, a corrected finite scan, two-sided analytic tail pricing,
failure propagation to both the result and process status, and a
kernel-checked split-rung envelope with an axiom audit. Numerical pricing
remains diagnostic and is not a Lean pin. A tail theorem must be attached
to the actual cardinal function, rather than only to a free monomial.

Budget: one numerical comparison, at most 15 minutes wall time and 1 GiB
resident memory; one focused Lean entry, at most 20 minutes wall time,
8 GiB resident memory, and 2 GiB additional derived files. At least 8 GiB
of free Linux filesystem space is required before building. Stop on a
control failure, failed price, unavailable import closure, or budget
exhaustion. Do not expand the derivative table or launch a cold full-tree
certificate rebuild.

Route A remains the binding selected-detector producer. Even a successful
stored-owner comparison leaves exact interval replay, the same-owner gate,
and arbitrary-rho parameter duties open.

## Proved exterior bound

The source modules are `C1RouteBSplitRungEnvelope3115.lean` and
`C1RouteBCardinalExterior3115.lean`. The first supplies all five proved
derivative bounds to the existing endpoint envelope. The second proves
`normalized_cardinalSum_le_exterior3115` on the actual cardinal function.
Its inputs are a finite node set, its coefficient function, a real strip
coordinate `sigma in [0,1]`, an exterior threshold `T > 0`, and natural
frequency weight `p`. It requires every node height to satisfy
`abs(Im z) < T`, and `nodes.card + p <= 71`.

To describe the bound, let `c_z` be the coefficient magnitude including
the complete node-separation denominator and the seed value `3^10`.
For each node `w`, set `ds_w = max(abs(Re w), abs(1-Re w))`. For each
active node `z`, set `E_z = exp(max(abs(Re z), abs(1-Re z)))`.
The proved bound, uniform over both signs of `t` with `abs(t) >= T`, is:

```text
H_p(T) = (T/(2*pi))^p
         * sum_z c_z * product_(w != z) (ds_w + T + abs(Im w))
         * (E_z * 2000000000 * 2^7 / (T - abs(Im z))^7)^10

abs(t/(2*pi))^p * norm(cardinalSum(nodes, poweredSeed, y, sigma+i*t))
  <= H_p(T)
```

The proof sets `r = abs(t)/T >= 1`. Each polynomial factor grows by at
most `r`; the seed transform shrinks by at least `r^70`. For the term
with `m` other nodes, the remaining factor is `r^(m+p)/r^70 <= 1`.
The separation estimate
`abs(t-Im z) >= r * (T-abs(Im z))` is proved using absolute values, so
it covers positive and negative frequencies without a symmetry assumption.
The formula uses a linear polynomial-factor bound, which is slightly
larger than the square-root factor in the historical numerical evaluator.
Its price is checked separately in the same new run.

This removes the infinite-domain geometric obligation: the exterior
supremum reduces to the explicit finite expression `H_p(T)`. Evaluating
that expression below a wired constant is still an exact arithmetic
obligation. In particular, the model calculation below does not itself
instantiate the theorem with a proved numerical pin.

## Stored-owner comparison

`scripts/routeb_split_rung_probe_3115.py` preserves the historical engine,
reproduces all three historical results bitwise in the same run, and
checks the exact capture against the Lean source hash and the frozen
owner, targets and values. A disclosed clone repairs only the crossing-cell
distance. The new comparison uses exactly the five proved bounds above.

The finite scan covers both signs through 600; the contraction channel
starts at absolute frequency 64. The exterior calculation uses the
actual-cardinal formula above for all absolute frequencies at least 600.
The diagnostic arithmetic is padded mpmath arithmetic, not a Lean proof
or a directed-rounding certificate.

```text
+---------+-----------------------+-----------------------+-----------+----------+
| Channel | Finite model bound    | Exterior model bound  | Wired cap | Slack    |
+---------+-----------------------+-----------------------+-----------+----------+
| C4      | 6.052429863069846e7   | 3.280759860923577e-58 | 6.1e7     | 0.7798%  |
| C2      | 2.816134421620648e7   | 2.514543830164837e-5  | 2.9e7     | 2.8919%  |
| q       | 2.003103025553781e-16 | 3.945380690782789e-66 | 2.6e-16   | 22.9576% |
+---------+-----------------------+-----------------------+-----------+----------+
```

All model guards pass, including rejection of the four-rung correction
tail with degree 17, empty-owner handling, crossing/endpoint cell distances,
both signed domains, exact capture identity, and compact-cover gap detection.
The numerical run takes about 40 seconds and uses less than 0.1 GiB resident
memory. The narrow C4 margin remains the binding price; adding derivative
orders or extending a sampled grid is not a substitute for its exact replay.

## Verification and reproducibility

Run in a Linux-side ext4 checkout with synchronized source dependencies:

```text
LEAN_NUM_THREADS=1 python3 scripts/routeb_split_rung_audit_3115.py
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 python3 scripts/routeb_split_rung_probe_3115.py
```

The audit invokes Lake on both source modules and
`C1RouteBSplitRungEnvelope3115Audit`, then requires the successful-build
footer, zero return code, no error or `sorryAx`, and every exact theorem
name and allowed axiom set. Lake reports 4161 jobs, mostly cached. The
first successful compilation takes about 30 seconds with peak resident
memory about 4.2 GiB; the final audit reuses those compiled proofs.
All analytic leaves have exactly `[propext, Classical.choice, Quot.sound]`.
The finite nonempty-rung fact has the smaller set `[propext, Quot.sound]`.

The first parser run expected the direct Lean output prefix and rejected
Lake's `info:` prefix despite a successful build. The parser now accepts
both formats, with a realistic Lake-format self-test; the axiom and
success criteria are unchanged. Negative audit controls also reject a
substituted theorem suffix, missing footer, nonzero exit, extra axiom,
weakened analytic footprint, and errors accompanying a successful footer.

The Lean boundary checks cover an empty node set, all-zero target values,
the low/high residual degrees, exclusion of zero frequency from a positive
exterior threshold, and application to the negative frequency direction.
Shared proof outputs remain cached; the entry-local off-diagonal pruner
does not apply to these shared modules.

Artifacts: `results/3115_routeb_split_rung_audit.json` and
`results/3115_routeb_split_rung_probe.json`. Both pin normalized source
hashes; an audit PASS and a numerical MODEL-PASS are distinct statuses.

## Remaining mathematical duties

1. Prove the stored finite-interval bounds and exact exterior prices in
   Lean, using rational interval arithmetic attached to the actual
   envelope. Completion means three unconditional stored-owner pins;
   it is not a universal-rho result.
2. Prove the signed gate on the same test function that has those pins
   and prefix facts. The arbitrary-rho owner of 3114 cannot inherit a
   fixed capture's numerical prices without a new proof.
3. Retain the arbitrary-rho height and inverse-gap costs of 3105 and
   the binding Route-A selected-detector signed budget. Fixed row-B
   caps do not cover all potential off-line zeros, and no RH exit is
   established by this record.
