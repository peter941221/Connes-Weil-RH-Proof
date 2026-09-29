# 2177 — Route A topological extension screen and non-interpolating grandchild

Date: 2026-09-29  
Status: topology-only scoped no-go; `A.005.1` is a `GO-CANDIDATE / UNPRICED`.

## Consumer, owner, and premise

The healthy-detector consumer is unchanged:

```text
selected healthy CompactLog detector g
  -> prove qw(g) >= 0 for that same owner
  -> SourceRH
  -> Mathlib RH.
```

The owner is the exact selected `CompactLog` detector with its actual support,
support-derived finite visible-prime set, triple vanishing, zero detection, and
full tail compatibility. A ROOT window, a known-zero prefix, a fixed-prime
model, and the narrow-root auxiliary span are not admissible replacements.

The only assumptions used by the proposed extension are the existing selected
detector construction, triple vanishing, and the support-derived prime owner.
It may not assume RH, `qw >= 0`, or an RH-equivalent coverage statement. The
premise it is intended to remove is the current selector's unpriced derivative
seminorm together with the absence of a uniform, parameterized signed margin.

## Topology-only screen

The proposed weak-compactness/confluent-node route was screened against the
active owner and the signed C3' consumer. It does not provide a producer Go.

1. A compact-open or ROOT closure is not a density theorem for the selected
   owner. The mixed quadratic terms needed to pass the sign are uncontrolled
   at the ROOT/partition interface (map records 001–002).
2. Finite Mellin interpolation plus a derivative seminorm does not determine
   the signed physical aggregate. The finite-dimensional kernel can change
   the aggregate while preserving the interpolation data (record 1926).
3. The current Jensen/source-zero count at the actual remaining height gives
   about `1.1167e15` possible owner nodes versus the 62-node compact family.
   Hence one interpolation constraint per abstract owner zero is unavailable
   under the current growth interface (record 2121).
4. The near-pin obstruction is quantitative. For support `(a,b)`, target
   value one at `t`, and zero at `z`, the derivative cost obeys

   ```text
   cost >= 4 exp(-X S) / (|z-t| X (b-a)^2),
   X = max(|a|,|b|), S = max(|Re t|,|Re z|).
   ```

   Thus a topology argument that needs a separation-independent H1 budget is
   false; the lower bound diverges as a pin approaches the target (record
   2157).
5. Even if a minimizer exists in a coercive H1 fibre, weak compactness supplies
   existence only. It supplies neither the selected-owner equality nor the
   required negative signed C3' margin. A weak lower-semicontinuity argument
   for a signed functional would still need an independently proved margin.

The mechanism intake screen was run on the preregistered sketch. Its `PRE` hit
is a vocabulary false positive (the sketch explicitly forbids RH input); its
`GAP` hit is genuine: no uniform parameterized signed-margin certificate was
present. Therefore the topology-only branch is recorded as
`SCOPED-NO-GO-FOR-TOPOLOGY-ONLY-EXTENSION`.

## Candidate grandchild `A.005.1`

The only credible extension surviving this screen is an owner-preserving,
non-interpolating **weighted-zero-measure C3' certificate**:

- keep the exact selected owner and its finite visible-prime set;
- do not impose one interpolation constraint per abstract closed-ball zero;
- derive, from the same correction and physical-kernel formula, a displayed
  nonnegative weight `W_(rho,N)(z)` on the exact source-zero owner;
- prove a certified decomposition

  ```text
  Arch + C3'_aggregate <= -epsilon(rho,N) + B_zm(rho,N),
  B_zm = sum_{z in exact owner} W_(rho,N)(z);
  ```

  and then prove the strict numerical gate `B_zm < epsilon(rho,N)`.

The weight must be fixed by the physical-kernel/correction derivation before
pricing. It may not be fitted to a sampled sign, replace the selected owner,
or discard signed cancellation. The first admissible probe is therefore a
fixed-`rho`, fixed-`N` exact-owner enclosure that returns both `epsilon` and
`B_zm`, with an independent interval/rounding control. Failure is any owner
change, non-finite or unbounded weighted sum, or `B_zm >= epsilon`.

This is a smaller quantitative obligation than full-owner interpolation, but it
is not yet priced and is not a producer result. Until that gate is passed,
`A.005.1` remains `GO-CANDIDATE`, while topology alone remains closed.

## Decision

`SCOPED-NO-GO-FOR-TOPOLOGY-ONLY-EXTENSION`; `A.005.1` is the sole registered
grandchild candidate. No Route-A binding owner, consumer, or RH status changes.

Evidence: records 1926, 2121, and 2157; `results/2177_routea_topology_grandchild_sketch.md`;
the mechanism-intake screen log
`results/2177_routea_topology_screen_intake.log` (the `PRE` hit is a stated
negative hypothesis, while the `GAP` hit is genuine).
