"""Probe the pure finite-Euler post-Q remainder on periodic grids.

This is rejection evidence, not a proof: a continuous Calkin-class argument is
still required before the scalar-plus-compact normal form can be ruled out.
"""

import numpy as np


def probe(grid_size: int) -> None:
    log_radius = 30.0
    step = 2 * log_radius / grid_size
    coordinate = (np.arange(grid_size) - grid_size // 2) * step
    frequency = 2 * np.pi * np.fft.fftfreq(grid_size, d=step)

    euler_scale = 2**-0.5
    phase = frequency * np.log(2.0)
    euler_phase = (1 - euler_scale * np.exp(1j * phase)) / (
        1 - euler_scale * np.exp(-1j * phase)
    )

    fourier = np.fft.fft(np.eye(grid_size), axis=0) / np.sqrt(grid_size)
    euler_operator = fourier.conj().T @ (euler_phase[:, None] * fourier)
    support_projection = np.diag((coordinate >= 0).astype(float))
    omega = (
        euler_operator.conj().T
        @ support_projection
        @ euler_operator
        - support_projection
    )
    remainder_coefficient = omega - support_projection @ omega @ support_projection
    spectral_coefficient = fourier @ remainder_coefficient @ fourier.conj().T
    post_q_multiplier = (frequency**2 + 0.25) * np.real(
        np.diag(spectral_coefficient)
    )

    print(f"N={grid_size}")
    euler_period = 2 * np.pi / np.log(2.0)
    for lower, upper in ((5, 10), (10, 20), (20, 30), (30, 40)):
        selected = (np.abs(frequency) >= lower) & (np.abs(frequency) < upper)
        values = post_q_multiplier[selected]
        if values.size == 0:
            continue
        bins = (
            (np.mod(frequency[selected], euler_period) / euler_period) * 4
        ).astype(int)
        means = [values[bins == index].mean() for index in range(4)]
        print(lower, upper, values.mean(), values.std(), means)


for size in (512, 1024, 2048):
    probe(size)
