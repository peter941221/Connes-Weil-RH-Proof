# Proof 313: signed three-branch commutator ledger

Date: 2026-07-16

Status: the exact outer/second-support/prolate commutator expansion and its
separate `-2` root residue are now axiom-clean Lean theorems.  A future source
producer only needs to instantiate the actual operators and prove the
same-object identity `R = E Q E - K_prol` to obtain this recombination.

This does not construct the semilocal `Q`, Sonin `R`, or `K_prol` operators.

## 1. Source decision

The semilocal source was checked before choosing the Lean object:

```text
Connes--Consani--Moscovici,
Zeta zeros and prolate wave operators: Semilocal adelic operators, v2
https://arxiv.org/abs/2310.18423v2
```

Its Theorem 2 constructs a Hilbertian isomorphism between the archimedean and
semilocal Sonin spaces.  It does not identify the missing repository operator
with the ordinary whole-line Fourier-half-line projection.  Therefore Proof
313 does not introduce such a surrogate.

The projection/prolate identity used by the route comes from

```text
Connes--Consani,
Weil positivity and Trace formula, the archimedean place
https://arxiv.org/abs/2006.13771
```

and is recorded in Proof 257 as

```text
E Q E = R + K_prol.
```

Equivalently,

```text
R = E Q E - K_prol.
```

## 2. Exact Lean identity

For continuous linear maps, define

```text
[A,W] = A W - W A.
```

Proof 313 proves, without projection, trace-class, or finite-dimensional
assumptions,

```text
R = E Q E - K
  ->
[R,W]
  = E Q [E,W]
    + E [Q,W] E
    + [E,W] Q E
    - [K,W].
```

The four terms retain their route meanings:

```text
+----------------------------+-------------------------+
| Lean term                  | physical branch         |
+----------------------------+-------------------------+
| E Q [E,W]                 | outer boundary          |
| E [Q,W] E                 | second support          |
| [E,W] Q E                 | reflected outer         |
| -[K_prol,W]               | signed prolate          |
+----------------------------+-------------------------+
```

No absolute value, operator norm, or branchwise estimate appears in the
theorem.  The scalar theorem pairs both sides with the same two root vectors.

## 3. Residue ownership

The CC20 diagonal distribution contributes a separate root pairing

```text
-2 * inner(eta,xi).
```

Proof 313 packages it with the commutator response:

```text
inner(eta,[R,W]xi) - 2 inner(eta,xi)
  =
inner(eta,ThreeBranch(E,Q,K,W)xi) - 2 inner(eta,xi).
```

The regression theorem

```text
cc20CommutatorResidueResponse_zero
```

proves

```text
W=0
  -> response = -2 * inner(eta,xi).
```

Thus a vanishing commutator cannot silently delete the distributional residue.

## 4. Lean declarations

`ThreeBranchCommutatorLedger.lean` provides

```text
cc20Commutator
cc20OuterCommutatorBranch
cc20SecondSupportCommutatorBranch
cc20ReflectedOuterCommutatorBranch
cc20ProlateCommutatorBranch
cc20ThreeBranchCommutator
cc20Commutator_eq_threeBranch_of_eq
cc20Inner_commutator_eq_threeBranch_of_eq
cc20CommutatorResidueResponse
cc20ThreeBranchResidueResponse
cc20CommutatorResidueResponse_eq_threeBranch_of_eq
cc20CommutatorResidueResponse_zero
```

## 5. Verification

Focused WSL2 ext4 build:

```text
lake build ConnesWeilRH.Source.CC20Concrete.ThreeBranchCommutatorLedger \
           ConnesWeilRH.Dev.ThreeBranchCommutatorLedgerAudit

Build completed successfully (2348 jobs).
```

Aggregate build:

```text
lake build ConnesWeilRH.Source.CC20Concrete

Build completed successfully (3539 jobs).
```

The audited theorems depend only on

```text
[propext, Classical.choice, Quot.sound]
```

and introduce no `sorryAx` or project axiom.

## 6. What this closes and what remains

```text
+--------------------------------------------------------------+
| CLOSED                                                       |
|  continuous-operator commutator algebra                      |
|  outer/second-support/reflected-outer/prolate signed ledger  |
|  arbitrary root-paired scalar readback                       |
|  explicit -2 residue ownership and zero-commutator guard     |
+--------------------------------------------------------------+
| OPEN                                                         |
|  actual semilocal Q, Sonin R, and K_prol producers          |
|  proof that their operators satisfy R = E Q E - K_prol       |
|  trace-class legality for the instantiated complete response |
|  match to Proof 310's moving divided-difference owner        |
|  Gate 3U, finite-S sign, Burnol identity, and RH             |
+--------------------------------------------------------------+
```

The next theorem must instantiate this ledger with genuine source operators.
The ledger itself is not that producer and is not a finite-S sign theorem.

Final route status:

```text
RH=UNPROVED
```
