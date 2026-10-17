# Record 2732: source endpoint derivative majorants

Task card: exact smoothSeed/Real.smoothTransition owner, on 0<x<=1/2.
Consumer: record2730 analytic endpoint remainder in D4/D7 integration.
Premise to remove: derivative magnitudes for the actual phase and
exponential/reciprocal product, not arbitrary input slots.
Completion: kernel-checked phase derivative bound and magnitude-induction
bridge, with standard-trio audit; no assertion of the D4/D7 integrals.
Budget: one named module plus audit, <=30 minutes, single-threaded,
<=4GiB additional storage. Stop on an unavailable analytic premise or
failed bound; no interval-cell batch or automatic extension.
Previous goal turn was progress: record2731 source recurrences were
compiled, audited and pushed. This entry advances those recurrences.


## Exact source bound

Set F(x)=-1/x+1/(1-x), E=exp(F), R=1/(1+E), and
T=Real.smoothTransition. A pointwise majorant is an explicit function
above the absolute value at every point; it is not an integral estimate.
The new source theorem targets, for natural n<=7 and 0<x<=1/2:

```text
|F^(n)(x)| <= 2*n!*x^(-2n)                    (n>=1)
|E^(n)(x)| <= b_n*E(x)*x^(-2n)
|R^(n)(x)| <= c_n*x^(-2n)
|T^(n)(x)| <= d_n*E(x)*x^(-2n)
          <= 8*d_n*x^(-2n)*exp(-1/x).
```

Here n! is the product 1*2*...*n and b,c,d are the positive integer
sequences used by record2730. Slot n refers to the actual n-th derivative
of the source function, using the recurrences proved in 2731.
The phase formula is proved from the exact iterated reciprocal formula
and reflection; its bound uses 1/x >= 1 and 1/(1-x) <= 1/x.
For E, strong induction applies the phase bound to its exponential
recurrence. For R, the denominator 1+E>=1 and E<=1 permit the reciprocal
recurrence to propagate c. Multiplying E and R derivatives gives d.
Finally 1/(1-x)<=2 and exp(2)<8 isolate the endpoint decay exp(-1/x).

The three finite coefficient tables have entries only for orders 0..7;
entries outside that range default to zero and are NOT derivative bounds.
Every theorem that uses such a bound therefore retains n<=7. Their
recurrence identities are proved by finite arithmetic in Lean and tied
back to record2730's exact integer tables in the readback checker.

```text
n    b_n       c_n        d_n
0    1         1          1
1    2         2          4
2    8         16         32
3    44        188        376
4    304       2928       5856
5    2512      56912      113824
6    24064     1326912    2653824
7    261536    36089888   72179776
```

## What remains before an endpoint integral certificate

The new pointwise bound is exactly the analytic input to the 2730 endpoint
charge. To conclude the charge itself, one must still prove that
x^(-2n)*exp(-1/x) is increasing on 0<x<=a when 2n*a<=1,
then integrate the constant bound and replace exp(-4096) by 2^(-4096).
These are separate real inequalities, not implied by a green axiom audit.

After that endpoint certificate, the finite-region interval replay and
integral partition still have to be connected to derivOrderL1. No theorem
`derivOrderL1 4 smoothSeed <= 1500` or order-seven analogue is claimed here.
No cardinal pin, poweredSeed carrier or genuine-rho gate is discharged.


## Verification

Focused Linux-native build, one Lean thread under the resource runner:

    lake build ConnesWeilRH.Dev.C1SeedEndpointMajorants2732Audit

Build completed successfully (3654 jobs). Fourteen audited theorem leaves
have exactly [propext, Classical.choice, Quot.sound], with no new-entry
errors or warnings. Exact source copies and current compiled objects
were checked. All 27 readback checks passed, including coefficient ties
to record2730 and binding-site plus global-count pins for n<=7.

    python3 scripts/check_seed_endpoint_majorants_2732.py --workspace WORKSPACE

WORKSPACE denotes the Linux-native verification checkout. The portable
result is `results/2732_seed_endpoint_majorants.json`; it records relative
source names, source/checker/build-log hashes, the coefficient-reference
hash and per-check results. Shared Dev outputs are retained, as required;
this is not a disposable generated entry assembly.

Existing Mathlib iterated-reciprocal and exponential bounds were read
at source level after the required brick inventory. No numerical rerun
or interval-cell batch was needed for these analytic pointwise theorems.
The proof target contains neither stored analytic conclusions nor extra
phase-derivative hypotheses.
