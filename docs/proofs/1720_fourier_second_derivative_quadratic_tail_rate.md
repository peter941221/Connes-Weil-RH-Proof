# 1720 — A quantitative Hardy-tail rate is now formal

The qualitative translated-tail theorem only gives convergence to zero.  The
new Dev brick `fourier_norm_mul_sq_le_integral_norm_second_deriv` proves the
next rate: if a vector and its first two derivatives are integrable, then

`||x||^2 * ||Fourier(g)(x)|| <= integral ||g''||`.

The proof is the two-step Fourier derivative identity.  The second derivative
supplies one extra power of `||x||`, and therefore the tail square is
summable on unit annuli once the live Hardy vector is shown to lie in this
Sobolev class.

This is formal infrastructure, not yet the S3 producer: the remaining bridge
is to prove the same second-derivative/integrable-tail hypotheses for the
actual source-Sonin root multiplier (or to prove an equivalent weighted L2
bound).  The healthy CompactLog B5 consumer and route are unchanged.

Evidence: `C1G8R3HardyTailRate.lean` and its paired Audit; focused build log
1720 v8 completed successfully (2967 jobs), with zero `error:` and no
`sorryAx`; the Audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.
