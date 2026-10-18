# 2870 Route B D4 sign interval probe

Direct interval evaluation of the replay-owned fourth derivative does not
certify the proposed signs, even after subdivision. On all three proposed
sign regions, 128, 512, and 2048 uniform cells produced zero sign-certified
cells. The interval ranges straddle zero; near the small-u edge this is pure
underflow/dependency, while in the middle and upper regions the reciprocal and
exponential jet dependencies remain dominant.

This is a method diagnosis. It does not disprove the sign pattern observed by
high-precision point evaluation. It says that the existing interval jet cannot
serve as the sign proof. The next analytic bridge must use a centered Taylor
model, a symbolic derivative polynomial, or a monotonicity argument with
independent bounds.
