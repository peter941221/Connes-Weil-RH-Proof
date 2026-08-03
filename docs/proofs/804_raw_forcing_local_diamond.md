# Proof 804: Local raw forcing diamond

Date: 2026-08-03

Status: axiom-clean local zero-curvature identity. The source-specific
compact-support estimate remains open.

## Result

Let a family represent the visible-prime list `p :: q :: S`, and let
`removeVisiblePrime` delete every prime-power term based at the supplied
visible prime. The two deletion paths have distinct intermediate families:

```text
family -- delete p --> family without p -- delete q --> tail_pq
   |
 delete q
   v
family without q -- delete p --> tail_qp
```

Lean proves the exact signed identity

```text
F(p, q :: S; family, family without p)
  + F(q, S; family without p, tail_pq)
=
F(q, p :: S; family, family without q)
  + F(p, S; family without q, tail_qp),
```

where every `F` is the complete raw forcing

```text
-Re Tr(MarkovCoboundary) + Re Tr(CompletedRemainderIncrement).
```

The proof does not assume that individual forcing terms commute. Each
two-step sum is first identified with the same raw endpoint difference; the
two terminal endpoints agree because their visible-prime lists both represent
`S`.

## Why It Matters

Proof 803 gives equality after choosing an entire deletion order. Proof 804
is its local form: any adjacent deletion swap preserves the complete signed
two-step contribution. This is the correct algebraic object for a future
support-adapted pairing of prime deletions.

```text
local prime swap
       |
       v
same two-step signed forcing
       |
       v
may reorganize a future compact-support argument
       |
       X
does not itself bound the forcing.
```

## Lean Owner

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovRawPermutationDiamond.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovRawPermutationDiamondAudit.lean
```

Key declaration:

```text
rawCompletePhysicalForcing_diamond_of_root_visiblePrimes_perm
```

## Boundary

The existing causal-renewal compact-support theorem bounds an outer renewal
atom after it has been expressed as a probability average. The raw forcing
above still contains the moving Gram-corrected coframe and the matching
completed remainder. No current source theorem identifies this entire
same-object forcing with that outer renewal atom.

Therefore the diamond is not a support-polynomial estimate, does not allow
the Markov and remainder terms to be bounded separately, and does not prove
Gate 3U, the finite-S sign, Burnol's identity, or `_root_.RiemannHypothesis`.
