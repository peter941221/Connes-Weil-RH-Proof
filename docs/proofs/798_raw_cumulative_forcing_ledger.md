# Proof 798: Raw cumulative forcing ledger

Date: 2026-08-03

Status: axiom-clean Lean closure of finite raw telescoping along an explicit
compatible finite-family chain. It identifies the unique signed cumulative
quantity a raw Gate 3U estimate must control. It does not construct that
chain for the canonical arithmetic family and does not prove an analytic
bound.

## Result

For one finite visible-prime list `S`, Proof 798 requires a dependent
`RawCompletePhysicalFamilyChain S`. Its node at every current list stores the
actual `FinitePrimePowerFamily`, a proof that its `visiblePrimes` is that
current list, and, at a nonempty node, the corresponding tail chain:

```text
Chain([]) contains F_empty with F_empty.visiblePrimes = [],

Chain(p::S) contains F_(p::S) with
  F_(p::S).visiblePrimes = p::S
and a tail Chain(S).
```

The forcing sum is then defined recursively:

```text
Chain([]) = 0,

ForcingChain([]) = 0,

ForcingChain(p::S)
  = F_(p,S; F_(p::S), F_S) + ForcingChain(S).
```

Proof 798 proves the literal raw identity:

```text
rawCompletePhysicalHermitianTrace(chain.family) = ForcingChain(chain).
```

The result uses only Proof 797's zero base and its unscaled one-prime
increment.

The dependent chain is necessary. A premise requiring one global function
for every `List CCM24VisiblePrime` would be uninhabited: a
`FinitePrimePowerFamily.visiblePrimes` list is nodup, while an arbitrary list
can contain duplicate primes.

## What It Fixes

```text
raw endpoint K_S
        |
        | exact finite telescope
        v
signed sum of recombined completed forcings
        |
        | required future source estimate
        v
support-polynomial raw Gate 3U bound
```

The finite family itself stays in each summand. This matters because the
completed remainder depends on the actual prime-power family, not just an
unowned list of visible primes.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovRawCumulativeLedger.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovRawCumulativeLedgerAudit.lean
```

Key declarations:

```text
rawCompletePhysicalForcingChain
rawCompletePhysicalHermitianTrace_eq_forcingChain
```

## Verification

After replacing the uninhabitable global-map premise with the concrete chain,
the focused Ubuntu-24.04 WSL2 ext4 verification passed in a fresh isolated
mirror (3419 jobs):

```text
lake build \
  ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawCumulativeLedger \
  ConnesWeilRH.Dev.CCM24FiniteSCausalMarkovRawCumulativeLedgerAudit
```

The source and audit use exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Scope

The compatibility condition is explicit at each chain node. This module does
not claim that an arbitrary list has a canonical `FinitePrimePowerFamily`,
nor that the canonical selected family already carries the required chain
through all of its suffixes. It also supplies no absolute-value estimate for
the signed sum.
