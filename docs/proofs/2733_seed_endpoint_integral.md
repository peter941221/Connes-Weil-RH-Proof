# Record 2733: exact rational endpoint integral certificate

Task card: source Real.smoothTransition, derivative orders1..7,
endpoint a=1/4096, consumer=record2730 D4/D7 integral split.
Target: prove the uniform endpoint maximum and
4*integral_0^a |T^(n)| <= 32*d_n*a*4096^(2n)/2^4096.
Completion: Lean endpoint integral inequality, standard-trio audit and
exact coefficient/charge tie to2730. Budget one module+audit, <=30min,
<=4GiB new build storage, one thread. Stop on a new analytic premise
or bound failure; no interval-cell batch. Previous goal turn was progress
(record2732 pointwise majorant proved and pushed). Finite-region replay
and full derivOrderL1 inequalities remain separate duties.


## Analytic chain

For a natural exponent m>0, define H_m(t)=t^m*exp(-t). Its exact
source derivative is t^(m-1)*exp(-t)*(m-t). Every factor except (m-t)
is nonnegative on t>=m, so H_m is nonincreasing there. Nonincreasing
(antitone) means a larger input gives an equal or smaller output.

Set a=1/4096. If 0<x<=a and 1<=n<=7, then
1/x>=4096>=2n. The previous pointwise derivative theorem therefore gives:

```text
|T^(n)(x)| <= 8*d_n*(1/x)^(2n)*exp(-1/x)
           <= 8*d_n*4096^(2n)*exp(-4096)
           <= 8*d_n*4096^(2n)/2^4096.
```

The last step uses exp(1)>2 and exact exponentiation, not floating-point
underflow. T is the actual Real.smoothTransition and d_n is the proved
coefficient from2732. The derivatives are continuous on [0,a], hence
integrable. Integral comparison on (0,a) avoids introducing a false
reciprocal identity at x=0; endpoint values do not change the integral.
Integrating the constant bound over length a and multiplying by four:

```text
4*integral_0^a |T^(n)(x)| dx
  <= seedEndpointCharge2733(n)
   = 32*d_n*(1/4096)*4096^(2n)/2^4096.
```

That is exactly the analytic endpoint charge used by the 2730 interval
calculation. The four is retained because2730 prices the seed ladder as
four times the left-half transition integral; no extra factor is inserted
or discarded. This theorem itself certifies the displayed transition
integral, while full seed-ladder assembly remains separate.

The exact fourth- and seventh-order charge inequalities against 10^(-1000)
are proved by rational arithmetic. The local exponentiation threshold is
5000 so norm_num can evaluate the required exponent4096; it does not
relax an inequality, add an axiom or change precision.

## Remaining scope

The endpoint integral is only the missing sliver (0,1/4096]. The finite
region [1/4096,1/2] still needs kernel-checked interval-operation and
partition replay. The 2730 numerical upper bounds1400.650854 and592705255
therefore remain computation-backed readings, not full Lean D4/D7 facts.
No cardinal pin, carrier re-seed, gate or arbitrary-rho producer is
established by this endpoint theorem. No RH claim follows.


## Verification

Focused Linux-native audit build under the resource runner, one Lean thread:

    lake build ConnesWeilRH.Dev.C1SeedEndpointIntegral2733Audit

Build completed successfully (3655 jobs). All eight theorem leaves have
exactly [propext, Classical.choice, Quot.sound]. No new-entry errors or
warnings; current source copies and compiled objects match. All 26
readback gates pass, including the exact charge definition, seven rational
charge ties to2730, and binding-site/global-count pins for the order range.

    python3 scripts/check_seed_endpoint_integral_2733.py --workspace WORKSPACE

WORKSPACE is the Linux-native verification checkout. The portable artifact
`results/2733_seed_endpoint_integral.json` records exact endpoint charge
rationals, source/checker/reference/build-log hashes and every gate.
Shared Dev build outputs are retained; target storage remains at289GiB
free. No numerical integral experiment or cell enumeration was required.

The actual endpoint integral inequality is newly formal. Full D4/D7
integral upper bounds, three pins, carrier transfer and the RH producer
remain open exactly as stated above.
