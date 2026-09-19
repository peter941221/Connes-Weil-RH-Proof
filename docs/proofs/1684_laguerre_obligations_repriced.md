# 1684 — Laguerre obligations 2-4 re-priced: obligation 2 splits into a soft transport half (discharged) and the carrier face; obligation 3 is the compactness upgrade; obligation 4 is hygiene

Date: 2026-09-19.

Status: analysis record (paper level, hand-derived from the committed
interface of 1636 and the closed obligation 1 of 1679).  No analytic
producer is proved and RH is not claimed.

## 1. Where front B stands after 1679

Obligation 1 (completeness/normalization of the Laguerre Hardy-side
system) is CLOSED (1679): the translated log-pulled-back Laguerre
functions form a complete ON system of the committed half-line
`L^2((log lambda, inf), du)`.  The remaining obligations of the 1640
producer candidate were 2 (finite-section defect -> 0), 3 (positive
limiting lower bound for the compact observable), 4 (remove FFT
truncation).  This record re-prices each.

## 2. Obligation 2 splits in two

Write `V_n` for the nested finite sections (degree prefixes) of the
ansatz family and

```text
sigma_n = inf { || P_+ U_lambda u || / ||u|| :  0 != u in V_n }.
```

*Soft half (2a, discharged at paper level).*  The family is complete
(obligation 1), so `closure(∪ V_n)` is the whole input space, and
`P_+ U_lambda` is BOUNDED (projection composed with the scaling).  For a
bounded operator `B`, any `eps`-minimizer `u*` of `||Bu||/||u||` is
approached by `u_n in V_n`, and

```text
sigma_n  <=  ||B u_n||  ->  ||B u*||  <=  sigma_full + eps.
```

Monotonicity of `sigma_n` (nested spaces) gives `sigma_n -> sigma_full`.
NO compactness is needed for this half — boundedness plus density
transport suffice.  The correct statement of obligation 2 is therefore:

```text
sigma_n -> 0   <=>   P_+ U_lambda is NOT bounded below on the input space.
```

*Content half (2b).*  "Not bounded below" for the Hardy corner is the
APPROXIMATE-kernel face of the carrier condition — precisely the
Toeplitz-kernel normalization pinned at 1624 (`ker(T_m)` face) and not
implied by any soft argument.  Obligation 2 is thus NOT a numerics
hygiene item: its content half is the carrier face itself.

## 3. Obligation 3 is the upgrade mechanism (1636 interface)

The machine-checked interface of 1636 reads: bounded `x_n` with
`D x_n -> 0` and a COMPACT observable `K` with `K x_n` not -> 0 imply
`D` is not injective — carrier nontrivial.  The Laguerre program
supplies exactly its four inputs:

```text
1. x_n = the section minimizers (finite-dimensional, bounded);
2. K   = the rank-two rational-Hardy observable (h_3, h_4 profiles; 1640);
3. D x_n -> 0  =  obligation 2b (the content half);
4. K x_n not -> 0  =  the observable-mass bookkeeping (measured
   0.92-0.99 along minimizers; the analytic lower bound is the
   obligation).
```

So obligations 2b + 3 TOGETHER are the witness construction, and the
compactness upgrade (1636) converts them into carrier nonemptiness.
The division of labor is sharp: 2b produces approximate kernel
directions; 3 keeps them from escaping weakly; 1636 upgrades.

## 4. Obligation 4 (de-FFT) is hygiene, correctly priced

Obligation 4 concerns the numerical conditioning of the generalized
eigenproblem and the FFT truncation at `N = 16384/32768`.  It gates the
NUMERICAL evidence, not the mathematics: the 1640 readback already
agrees across two independent truncations for the resolved rows.  The
right replacement, when needed, is a fixed quadrature on the
log-coordinate half-line inside the ansatz subspace (F61-permitted);
it is not on the critical path of 2b/3.

## 5. Formalization paths

* 2a (soft transport) is formalizable as a small brick: bounded `B`,
  dense union of nested subspaces, `sigma_n <-> sigma_full`
  (`Filter.tendsto` over a monotone `Real` sequence).  Candidate name:
  `sectionDefects_tendsto_full`.
* 1636's interface is already machine-checked; the remaining Lean work
  is INSTANTIATION (typing `D = P_+ U_lambda` corner in committed
  vocabulary), which is exactly where 2b/3 enter.

## 6. Boundary

Front B completion state: obligation 1 CLOSED (1679); 2a discharged at
paper level (formalization path pinned); 2b = the carrier face (front
B's analytic core, open); 3 = the observable-mass lower bound (open);
4 = hygiene (not critical path).  The carrier base, the gate, and RH
remain open.
