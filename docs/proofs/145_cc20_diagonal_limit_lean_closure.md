# CC20 Diagonal Limit Lean Closure

Date: 2026-07-12

Status: proved in the source modules and import-facing audits.

The removable singularity is handled in three stages:

1. `hasDerivAt_deriv_sinc_zero` proves the derivative of `deriv sinc` at zero
   is `-1/3`. The proof applies `HasDerivAt.lhopital_zero_nhdsNE` to
   `(x*cos x - sin x)/x^3` and uses continuity of `sinc`.
2. Two further L'Hopital reductions prove
   `hasDerivAt_siQuotientDerivativeProfile_zero` with value `-1/9`.
   The explicit second derivative profile has the punctured identity

   ```text
   F''(x) = sinc'(x)/x - 2*(sin(x)-Si(x))/x^3.
   ```

   Both terms have already audited limits, so
   `tendsto_sineIntegralQuotientSecondDerivativeProfile_zero` follows.
3. The continuous repaired profile is substituted into a continuous Q-delta
   candidate. `cc20QDeltaRegularContinuousCandidate_one` reduces its value to

   ```text
   8*pi^2/9 + sineIntegralQuotient (4*pi) - 1/2.
   ```

   `tendsto_cc20QDeltaRegularCandidate_one_right` then proves the original
   non-diagonal candidate has this right-hand limit. Since `ratioRadius` is
   always at least one, `continuousWithinAt_cc20QDeltaRegularExtension_Ici`
   is the domain-correct scalar continuity statement. It composes with
   `ratioRadius` to prove `continuousAt_cc20RegularKernel_diagonal`.

These results are analytic groundwork only. They do not provide a Hilbert--
Schmidt estimate, a two-variable kernel action identity, a same-object CC20
trace formula, or an unconditional RH theorem.
