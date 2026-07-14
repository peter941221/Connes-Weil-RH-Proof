# Proof 216: constant PNT-main S-procedure no-go

Date: 2026-07-13

Status: accepted finite Arb no-go inside the raw-root model screened by Proof
215.  At cutoff `c=10^6`, no constant `lambda >= 0` can turn the continuous
PNT-main sign into the proposed pointwise Fourier-symbol bound.  Proof 217
subsequently shows that this raw-root model is not the same-object CC20 Q-root
form, so this result is a diagnostic rejection, not an RH-route theorem.  RH
remains unproved.

## 1. Candidate implication

For support length `T=log(c)`, define

```text
k_c(t)
 = 2 sum_(q=p^m<c) Lambda(q) q^(-1/2) cos(t log q),

k_0(t)
 = 2 integral_0^T exp(b/2) cos(tb) db.
```

Proof 215 proves that the continuous operator with symbol `k_0` is
nonpositive on the `cosh(x/2)`-neutral subspace.  A constant S-procedure would
therefore have followed from

```text
k_c(t)
 <= 2 + (t^2+1/4)/50 + lambda k_0(t)                  (S.1)
```

for every real `t` and one `lambda >= 0` depending on `c`.

This is only a sufficient condition.  It discards the Paley--Wiener coupling
between different frequencies.

## 2. Two-point contradiction

At `c=10^6`, direct Arb evaluation of all `78,734` prime-power terms gives the
following two strict implications.

At

```text
t_-=2769/200=13.845,
```

the continuous symbol is positive and

```text
k_c(t_-)-2-(t_-^2+1/4)/50-1.02 k_0(t_-)
  > 0.0660681162135862408034414769000.
```

Thus (S.1) forces `lambda>1.02`.

At

```text
t_+=289/20=14.45,
```

the continuous symbol is negative and

```text
k_c(t_+)-2-(t_+^2+1/4)/50-k_0(t_+)
  > 0.463406383811911371046988072696.
```

Thus (S.1) forces `lambda<1`.  The two requirements are incompatible.

The accepted 128-bit Arb enclosures are

```text
k_0(t_-)
 = [46.133338437118651554913794501300226 +/- 4.50e-34],

lower margin
 = [0.0660681162135862408034414769001 +/- 6.80e-32],

k_0(t_+)
 = [-136.1549484379915406876868554898395204 +/- 9.32e-35],

upper margin
 = [0.4634063838119113710469880726960 +/- 2.50e-32].
```

No zeta-zero location, PNT error estimate, or floating-point sign decision is
used by the certificate.

## 3. Mechanism

The reconnaissance maximizer tracks

```text
(gamma_1-t_bad) log(c) approximately 4.49,
```

where `gamma_1` is the first critical-line zero ordinate and `4.493...` is the
first positive solution of `tan(u)=u`.  This is the first positive sidelobe of
the hard-cutoff Dirichlet kernel.  That observation explains the location of
the failure; the finite Arb sum, not the explanation, proves it.

The structural lesson is

```text
sign of one global K_0 form
  does not permit replacing K_0 by lambda K_0 frequency by frequency.
```

Any use of the continuous main kernel must retain the finite-interval
Paley--Wiener coupling or use an operator-valued comparison.

## 4. Same-object correction

Proof 217 identifies a more basic route mismatch.  The CC20 M4 identity uses

```text
g=(d/dx+1/2)xi,
```

with the prime form acting on `g` and the scalar/compact remainder acting on
`xi`.  Proof 215 instead screened all terms on one raw vector.  Therefore
Proof 216 rejects only the constant S-procedure inside that raw model; it does
not repair or close the actual Q-root relative form.

## 5. Reproduction

Reconnaissance:

```text
python3 -B docs/proofs/216_all_prime_symbol_sprocedure_probe.py \
  --cutoff 1000000 --t-max 20 --step 0.005
```

Arb certificate:

```text
python3 -B docs/proofs/216_all_prime_symbol_sprocedure_certificate.py \
  --bits 128
```

## 6. Route judgment

```text
finite prime-power enumeration:       exact
two-frequency Arb contradiction:      accepted
constant scalar K_0 S-procedure:      rejected
Paley--Wiener operator comparison:    not tested by this no-go
same-object CC20 Q-root form:          not represented; see Proof 217
Lean owner:                            none
RH:                                    unproved
```
