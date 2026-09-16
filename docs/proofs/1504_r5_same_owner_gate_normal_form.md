# 1504 — the ρ5 same-owner gate as one Lean normal form

**Status: FORMAL.** New leaf
[`C1G8R3SameOwnerGateNormalForm.lean`](../../ConnesWeilRH/Dev/C1G8R3SameOwnerGateNormalForm.lean)
(+ paired audit). Record 1500's equation (3) — the substantive gate — is
now a machine-checked equivalence: given the survivor core, the
unremaindered readback converges to `qw` **iff** the aggregate limit value
equals `qw`, and both directions are packaged. RH is not claimed; the
identification itself remains open.

## What is proved

The endpoint brick (record 1502) gives, under the survivor core square-sum
(★), that the real readback trace `t_n` converges to the real part of the
named aggregate limit operator

```text
B := ordinaryTraceAlong sourceBasis (J† ∘L C† ∘L G ∘L C ∘L J).
```

On top of that, this file proves three things, all pure limit algebra:

1. **The gate as one iff** (`g8R5_readbackTendsto_iff_aggregateLimit_eq_qw`):

   ```text
   ( t_n → qw )  ↔  ( B.re = qw )        given (★).
   ```

   Forward by uniqueness of limits; backward by rewriting the constant.

2. **Sufficiency, packaged** (`g8R5ZeroRemainderReadbackData`): the single
   equation `B.re = qw` CONSTRUCTS a zero-remainder
   `G8SameOwnerReadbackData`, feeding the committed positive-trace consumer
   (`qw_nonnegative_of_g8SameOwnerReadbackData`, record 012 chain)
   unchanged.

3. **Necessity** (`g8R5_aggregateLimit_eq_qw_of_sameOwnerReadbackData`):
   from ANY same-owner readback data — arbitrary remainder — plus (★), the
   aggregate equation `B.re = qw` holds. Nothing analytic is used: it is
   `(t_n − r_n) + r_n = t_n` plus uniqueness of limits.

## Typed guards (record 1501 checklist)

The only estimate-shaped premise is (★). No `qw` sign, no archimedean
sign, no positivity is an input anywhere. The gate is thereby isolated in
exactly the sense record 1500 demanded: the whole remaining content of the
readback is ONE real equation `B.re = qw`, and the Euler content of `S`
(visible-prime coefficient readback, the P2 sub-limit inside `L`) is what
has to be read off it. Convergence work can no longer touch the gate.

## Ledger update (record 1500/1502)

```text
ρ1  ≡ 0            FORMAL
ρ2  → 0            FORMAL (1479/1481)
ρ3  → 0            FORMAL (1480)
ρ4  → 0            FORMAL GIVEN (★)   (record 1502)
ρ5  = B.re = qw    NOW A NAMED IFF THEOREM — the open identification
```

Attack surface for the identification, per records 1503 §5 and 1500 §5:
instantiate `B` through the four-channel ledger (`b_n + 2x_n + l_n`), split
`B` into the channel limits `B + 2X + L` (ρ2/ρ3 instantiations via
1479/1480), and expose the P2 sub-limit of `L` term by term. The channel
limits exist formally; their VALUES are the Euler content.
