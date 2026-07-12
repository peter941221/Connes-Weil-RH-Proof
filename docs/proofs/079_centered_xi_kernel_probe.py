"""Check the centered theta-kernel jump and regular Xi-kernel limit."""

import mpmath as mp


mp.mp.dps = 80


def psi_positive(x: mp.mpf) -> mp.mpf:
    t = mp.exp(2 * x)
    theta_tail = mp.nsum(
        lambda n: mp.exp(-mp.pi * n * n * t), [1, mp.inf]
    )
    return 2 * mp.exp(x / 2) * theta_tail


def regular_xi_kernel(x: mp.mpf) -> mp.mpf:
    return mp.diff(psi_positive, x, 2) - psi_positive(x) / 4


right_derivative = mp.diff(psi_positive, 0, 1)
left_derivative = -right_derivative

print(f"psi(0)={mp.nstr(psi_positive(0), 50)}")
print(f"psi'(0+)={mp.nstr(right_derivative, 50)}")
print(f"psi'(0-)={mp.nstr(left_derivative, 50)}")
print(f"jump={mp.nstr(right_derivative - left_derivative, 50)}")

for x in map(mp.mpf, ["0.1", "0.03", "0.01", "0.003", "0.001"]):
    print(
        f"x={x} regular_xi_kernel={mp.nstr(regular_xi_kernel(x), 40)}"
    )
