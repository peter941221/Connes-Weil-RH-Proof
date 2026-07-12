import argparse
import numpy as np


def positive_digamma(values: np.ndarray) -> np.ndarray:
    x = np.asarray(values, dtype=np.float64).copy()
    result = np.zeros_like(x)
    while np.any(x < 10.0):
        mask = x < 10.0
        result[mask] -= 1.0 / x[mask]
        x[mask] += 1.0

    inverse = 1.0 / x
    inverse_sq = inverse * inverse
    result += (
        np.log(x)
        - 0.5 * inverse
        - inverse_sq / 12.0
        + inverse_sq**2 / 120.0
        - inverse_sq**3 / 252.0
        + inverse_sq**4 / 240.0
        - 5.0 * inverse_sq**5 / 660.0
        + 691.0 * inverse_sq**6 / 32760.0
    )
    return result


def gram_data(max_k: int, cutoff: int, chunk: int):
    ks = np.arange(2, max_k + 1, dtype=np.float64)
    gram = np.zeros((len(ks), len(ks)), dtype=np.float64)
    target = np.zeros(len(ks), dtype=np.float64)

    for start in range(1, cutoff + 1, chunk):
        stop = min(start + chunk, cutoff + 1)
        n = np.arange(start, stop, dtype=np.float64)
        weights = 1.0 / (n * (n + 1.0))
        basis = np.remainder(n[:, None], ks[None, :]) / ks[None, :]
        weighted_basis = weights[:, None] * basis
        gram += basis.T @ weighted_basis
        target += weighted_basis.sum(axis=0)

    # The omitted tail has total mass 1/(cutoff+1). Its contribution is small
    # for this rejection-first experiment; report the bound with the results.
    return gram, target, 1.0 / (cutoff + 1.0)


def exact_gram_data(max_k: int):
    ks = np.arange(2, max_k + 1, dtype=np.int64)
    target = np.log(ks) / ks
    gram = np.empty((len(ks), len(ks)), dtype=np.float64)

    for row, j in enumerate(ks):
        for col in range(row, len(ks)):
            k = int(ks[col])
            period = int(np.lcm(j, k))
            residues = np.arange(1, period + 1, dtype=np.float64)
            weights = (
                positive_digamma((residues + 1.0) / period)
                - positive_digamma(residues / period)
            ) / period
            values = (
                np.remainder(residues, j) / j
                * np.remainder(residues, k) / k
            )
            entry = float(values @ weights)
            gram[row, col] = entry
            gram[col, row] = entry

    return gram, target, 0.0


def distance_sq(gram: np.ndarray, target: np.ndarray, size: int) -> float:
    g = gram[:size, :size]
    b = target[:size]
    coeff = np.linalg.solve(g, b)
    return max(0.0, 1.0 - float(b @ coeff))


def mobius_values(limit: int) -> np.ndarray:
    mu = np.ones(limit + 1, dtype=np.float64)
    is_prime = np.ones(limit + 1, dtype=bool)
    mu[0] = 0.0
    for p in range(2, limit + 1):
        if not is_prime[p]:
            continue
        mu[p::p] *= -1.0
        is_prime[2 * p::p] = False
        square = p * p
        if square <= limit:
            mu[square::square] = 0.0
    return mu


def certificate_capture(gram: np.ndarray, target: np.ndarray, n: int, a: np.ndarray):
    old = n - 1
    new = n
    a_gram = gram[:old, :old]
    cross = gram[:old, old:old + new]
    block = gram[old:old + new, old:old + new]
    old_coeff = np.linalg.solve(a_gram, target[:old])
    solve_cross = np.linalg.solve(a_gram, cross)
    residual_correlation = target[old:old + new] - cross.T @ old_coeff
    schur = block - cross.T @ solve_cross
    numerator = float(a @ residual_correlation) ** 2
    denominator = float(a @ schur @ a)
    return numerator / denominator if denominator > 0 else 0.0


def gpu_direction_certificate(
    n_scale: int,
    cutoff: int,
    block_chunk: int,
    tolerance: float,
    max_iterations: int,
):
    """Compute one truncated block certificate without forming the full Gram matrix."""
    import torch

    if not torch.cuda.is_available():
        raise RuntimeError("--gpu-n requires a CUDA-capable PyTorch installation")

    dtype = torch.float64
    device = torch.device("cuda")
    sequence_indices = torch.arange(1, cutoff + 1, device=device, dtype=dtype)
    weights = 1.0 / (sequence_indices * (sequence_indices + 1.0))
    sqrt_weights = torch.sqrt(weights)
    old_indices = torch.arange(2, n_scale + 1, device=device, dtype=dtype)
    old_basis = (
        torch.remainder(sequence_indices[:, None], old_indices[None, :])
        / old_indices[None, :]
    )
    old_basis.mul_(sqrt_weights[:, None])

    mu = mobius_values(2 * n_scale)
    block_integer_indices = np.arange(n_scale + 1, 2 * n_scale + 1)
    block_coefficients = torch.tensor(
        mu[block_integer_indices] / block_integer_indices,
        device=device,
        dtype=dtype,
    )
    weighted_block = torch.zeros(cutoff, device=device, dtype=dtype)
    for start in range(0, n_scale, block_chunk):
        stop = min(start + block_chunk, n_scale)
        block_indices = torch.arange(
            n_scale + 1 + start,
            n_scale + 1 + stop,
            device=device,
            dtype=dtype,
        )
        block_values = (
            torch.remainder(sequence_indices[:, None], block_indices[None, :])
            / block_indices[None, :]
        )
        weighted_block.add_(
            (block_values @ block_coefficients[start:stop]) * sqrt_weights
        )

    inverse_diagonal = 1.0 / (old_basis * old_basis).sum(dim=0)

    def solve_normal_equations(right_hand_side: "torch.Tensor"):
        solution = torch.zeros_like(right_hand_side)
        residual = right_hand_side.clone()
        preconditioned = inverse_diagonal * residual
        direction = preconditioned.clone()
        residual_dot = torch.dot(residual, preconditioned)
        initial_norm = torch.linalg.vector_norm(residual)

        for iteration in range(1, max_iterations + 1):
            image = old_basis.T @ (old_basis @ direction)
            step = residual_dot / torch.dot(direction, image)
            solution.add_(direction, alpha=step)
            residual.sub_(image, alpha=step)
            if torch.linalg.vector_norm(residual) <= tolerance * initial_norm:
                return solution, iteration
            preconditioned = inverse_diagonal * residual
            next_residual_dot = torch.dot(residual, preconditioned)
            direction = preconditioned + direction * (next_residual_dot / residual_dot)
            residual_dot = next_residual_dot

        return solution, max_iterations

    weighted_target = sqrt_weights
    target_rhs = old_basis.T @ weighted_target
    block_rhs = old_basis.T @ weighted_block
    target_coefficients, target_iterations = solve_normal_equations(target_rhs)
    block_projection, block_iterations = solve_normal_equations(block_rhs)
    target_residual = weighted_target - old_basis @ target_coefficients
    block_residual = weighted_block - old_basis @ block_projection

    distance_sq = torch.dot(target_residual, target_residual)
    projected_energy = torch.dot(block_residual, block_residual)
    correlation = torch.dot(target_residual, weighted_block)
    normalized_capture = (
        correlation * correlation / (projected_energy * distance_sq) * np.log(n_scale)
    )
    target_normal_residual = (
        torch.linalg.vector_norm(old_basis.T @ target_residual)
        / torch.linalg.vector_norm(target_rhs)
    )
    block_normal_residual = (
        torch.linalg.vector_norm(old_basis.T @ block_residual)
        / torch.linalg.vector_norm(block_rhs)
    )

    print(f"device={torch.cuda.get_device_name(0)}")
    print(f"N={n_scale} cutoff={cutoff} omitted_weight_mass={1.0 / (cutoff + 1):.3e}")
    print(f"cg_iterations={target_iterations},{block_iterations}")
    print(f"normal_residual={float(target_normal_residual):.3e},{float(block_normal_residual):.3e}")
    print(f"distance_sq={float(distance_sq):.12e}")
    print(f"projected_energy={float(projected_energy):.12e}")
    print(f"correlation={float(correlation):.12e}")
    print(f"mu/k_cert_times_logN={float(normalized_capture):.12e}")


def gpu_gradient_certificate(
    n_scale: int,
    cutoff: int,
    block_chunk: int,
    tolerance: float,
    max_iterations: int,
):
    """Test the dyadic correction that cancels every residual block gradient."""
    import torch

    if not torch.cuda.is_available():
        raise RuntimeError("--gpu-gradient-n requires CUDA-capable PyTorch")

    dtype = torch.float64
    device = torch.device("cuda")
    sequence_indices = torch.arange(1, cutoff + 1, device=device, dtype=dtype)
    sqrt_weights = torch.sqrt(
        1.0 / (sequence_indices * (sequence_indices + 1.0))
    )
    old_indices = torch.arange(2, n_scale + 1, device=device, dtype=dtype)
    old_basis = (
        torch.remainder(sequence_indices[:, None], old_indices[None, :])
        / old_indices[None, :]
    )
    old_basis.mul_(sqrt_weights[:, None])
    inverse_diagonal = 1.0 / (old_basis * old_basis).sum(dim=0)

    def solve_normal_equations(right_hand_side: "torch.Tensor"):
        solution = torch.zeros_like(right_hand_side)
        residual = right_hand_side.clone()
        preconditioned = inverse_diagonal * residual
        direction = preconditioned.clone()
        residual_dot = torch.dot(residual, preconditioned)
        initial_norm = torch.linalg.vector_norm(residual)

        for iteration in range(1, max_iterations + 1):
            image = old_basis.T @ (old_basis @ direction)
            step = residual_dot / torch.dot(direction, image)
            solution.add_(direction, alpha=step)
            residual.sub_(image, alpha=step)
            if torch.linalg.vector_norm(residual) <= tolerance * initial_norm:
                return solution, iteration
            preconditioned = inverse_diagonal * residual
            next_residual_dot = torch.dot(residual, preconditioned)
            direction = preconditioned + direction * (next_residual_dot / residual_dot)
            residual_dot = next_residual_dot

        return solution, max_iterations

    weighted_target = sqrt_weights
    target_rhs = old_basis.T @ weighted_target
    target_coefficients, target_iterations = solve_normal_equations(target_rhs)
    target_residual = weighted_target - old_basis @ target_coefficients
    distance_sq = torch.dot(target_residual, target_residual)

    block_points = torch.arange(
        n_scale, 2 * n_scale + 1, device=device, dtype=dtype
    )
    block_old_values = (
        torch.remainder(block_points[:, None], old_indices[None, :])
        / old_indices[None, :]
    )
    block_residual_values = 1.0 - block_old_values @ target_coefficients
    residual_gradient = block_residual_values[1:] - block_residual_values[:-1]
    new_indices = torch.arange(
        n_scale + 1, 2 * n_scale + 1, device=device, dtype=dtype
    )
    harmonic_mass = torch.sum(1.0 / new_indices)
    constant_gradient = -torch.sum(residual_gradient / new_indices) / (
        1.0 - harmonic_mass
    )
    gradient_coefficients = constant_gradient - residual_gradient
    gradient_error = torch.max(
        torch.abs(residual_gradient - (constant_gradient - gradient_coefficients))
    )

    weighted_block = torch.zeros(cutoff, device=device, dtype=dtype)
    for start in range(0, n_scale, block_chunk):
        stop = min(start + block_chunk, n_scale)
        block_indices = new_indices[start:stop]
        block_values = (
            torch.remainder(sequence_indices[:, None], block_indices[None, :])
            / block_indices[None, :]
        )
        weighted_block.add_(
            (block_values @ gradient_coefficients[start:stop]) * sqrt_weights
        )

    raw_residual = target_residual - weighted_block
    raw_energy = torch.dot(raw_residual, raw_residual)
    block_rhs = old_basis.T @ weighted_block
    block_projection, block_iterations = solve_normal_equations(block_rhs)
    projected_block = weighted_block - old_basis @ block_projection
    projected_energy = torch.dot(projected_block, projected_block)
    correlation = torch.dot(target_residual, projected_block)
    unit_step_residual = target_residual - projected_block
    unit_step_energy = torch.dot(unit_step_residual, unit_step_residual)
    optimal_step = correlation / projected_energy
    normalized_capture = (
        correlation * correlation / (projected_energy * distance_sq) * np.log(n_scale)
    )
    cosine = correlation / torch.sqrt(distance_sq * projected_energy)

    print(f"device={torch.cuda.get_device_name(0)}")
    print(f"N={n_scale} cutoff={cutoff} omitted_weight_mass={1.0 / (cutoff + 1):.3e}")
    print(f"cg_iterations={target_iterations},{block_iterations}")
    print(f"gradient_error={float(gradient_error):.3e}")
    print(f"raw_energy_ratio={float(raw_energy / distance_sq):.12e}")
    print(f"reprojected_unit_step_ratio={float(unit_step_energy / distance_sq):.12e}")
    print(f"optimal_step={float(optimal_step):.12e}")
    print(f"gradient_cert_times_logN={float(normalized_capture):.12e}")
    print(f"gradient_direction_cosine={float(cosine):.12e}")


def gpu_shifted_frame_certificate(
    n_scale: int,
    cutoff: int,
    frame_dimension: int,
    block_chunk: int,
    tolerance: float,
    max_iterations: int,
):
    """Test the fixed moment-zero shifted-Mobius frame with a conservative norm."""
    import torch

    if not torch.cuda.is_available():
        raise RuntimeError("--gpu-frame-n requires CUDA-capable PyTorch")
    if frame_dimension < 1:
        raise ValueError("--frame-dimension must be positive")

    dtype = torch.float64
    device = torch.device("cuda")
    sequence_indices = torch.arange(1, cutoff + 1, device=device, dtype=dtype)
    sqrt_weights = torch.sqrt(
        1.0 / (sequence_indices * (sequence_indices + 1.0))
    )
    old_indices = torch.arange(2, n_scale + 1, device=device, dtype=dtype)
    old_basis = (
        torch.remainder(sequence_indices[:, None], old_indices[None, :])
        / old_indices[None, :]
    )
    old_basis.mul_(sqrt_weights[:, None])
    inverse_diagonal = 1.0 / (old_basis * old_basis).sum(dim=0)

    def solve_normal_equations(right_hand_side: "torch.Tensor"):
        solution = torch.zeros_like(right_hand_side)
        residual = right_hand_side.clone()
        preconditioned = inverse_diagonal * residual
        direction = preconditioned.clone()
        residual_dot = torch.dot(residual, preconditioned)
        initial_norm = torch.linalg.vector_norm(residual)

        for iteration in range(1, max_iterations + 1):
            image = old_basis.T @ (old_basis @ direction)
            step = residual_dot / torch.dot(direction, image)
            solution.add_(direction, alpha=step)
            residual.sub_(image, alpha=step)
            if torch.linalg.vector_norm(residual) <= tolerance * initial_norm:
                return solution, iteration
            preconditioned = inverse_diagonal * residual
            next_residual_dot = torch.dot(residual, preconditioned)
            direction = preconditioned + direction * (next_residual_dot / residual_dot)
            residual_dot = next_residual_dot

        return solution, max_iterations

    weighted_target = sqrt_weights
    target_rhs = old_basis.T @ weighted_target
    target_coefficients, target_iterations = solve_normal_equations(target_rhs)
    target_residual = weighted_target - old_basis @ target_coefficients
    distance_sq = torch.dot(target_residual, target_residual)

    integer_indices = np.arange(n_scale + 1, 2 * n_scale + 1)
    reciprocal_indices = 1.0 / integer_indices
    mu = mobius_values(2 * n_scale)
    coefficient_matrix = np.zeros((n_scale, frame_dimension))
    for shift in range(1, frame_dimension + 1):
        divisible = integer_indices % shift == 0
        coefficient_matrix[divisible, shift - 1] = mu[
            integer_indices[divisible] // shift
        ]
        harmonic_mean = (
            reciprocal_indices @ coefficient_matrix[:, shift - 1]
        ) / reciprocal_indices.sum()
        coefficient_matrix[:, shift - 1] -= harmonic_mean

    frame_coefficients = torch.tensor(
        coefficient_matrix, device=device, dtype=dtype
    )
    fixed_raw_coefficients = np.zeros(n_scale)
    small_mu = mobius_values(8)
    for shift in range(1, 9):
        if small_mu[shift] == 0.0:
            continue
        divisible = integer_indices % shift == 0
        fixed_raw_coefficients[divisible] += (
            -small_mu[shift]
            / shift
            * mu[integer_indices[divisible] // shift]
        )
    fixed_harmonic_sum = reciprocal_indices @ fixed_raw_coefficients
    fixed_coefficients = torch.tensor(
        fixed_raw_coefficients, device=device, dtype=dtype
    )
    frame_values = torch.zeros(
        (cutoff, frame_dimension), device=device, dtype=dtype
    )
    fixed_raw_values = torch.zeros(cutoff, device=device, dtype=dtype)
    block_indices = torch.arange(
        n_scale + 1, 2 * n_scale + 1, device=device, dtype=dtype
    )
    for start in range(0, n_scale, block_chunk):
        stop = min(start + block_chunk, n_scale)
        indices = block_indices[start:stop]
        block_values = (
            torch.remainder(sequence_indices[:, None], indices[None, :])
            / indices[None, :]
        )
        block_values.mul_(sqrt_weights[:, None])
        frame_values.add_(block_values @ frame_coefficients[start:stop])
        fixed_raw_values.add_(block_values @ fixed_coefficients[start:stop])

    frame_gram = frame_values.T @ frame_values
    correlations = frame_values.T @ target_residual
    eigenvalues, eigenvectors = torch.linalg.eigh(frame_gram)
    positive = eigenvalues > eigenvalues[-1] * 1e-11
    whitened_correlations = eigenvectors[:, positive].T @ correlations
    conservative_capture = torch.sum(
        whitened_correlations * whitened_correlations / eigenvalues[positive]
    )
    normalized_capture = conservative_capture / distance_sq * np.log(n_scale)
    normal_residual = (
        torch.linalg.vector_norm(old_basis.T @ target_residual)
        / torch.linalg.vector_norm(target_rhs)
    )
    early_coordinate_max = torch.max(torch.abs(frame_values[:n_scale]))
    gamma_n = (
        torch.remainder(sequence_indices, n_scale) / n_scale * sqrt_weights
    )
    anchored_convolution = (
        fixed_raw_values - n_scale * fixed_harmonic_sum * gamma_n
    )
    fixed_correlation = torch.dot(target_residual, anchored_convolution)
    fixed_energy = torch.dot(anchored_convolution, anchored_convolution)
    fixed_normalized_capture = (
        fixed_correlation
        * fixed_correlation
        / (fixed_energy * distance_sq)
        * np.log(n_scale)
    )
    fixed_early_coordinate_max = torch.max(
        torch.abs(anchored_convolution[: n_scale - 1])
    )

    print(f"device={torch.cuda.get_device_name(0)}")
    print(f"N={n_scale} cutoff={cutoff} frame_dimension={frame_dimension}")
    print(f"cg_iterations={target_iterations}")
    print(f"normal_residual={float(normal_residual):.3e}")
    print(f"frame_rank={int(positive.sum())}")
    print(f"frame_eigenvalue_ratio={float(eigenvalues[0] / eigenvalues[-1]):.12e}")
    print(f"early_coordinate_max={float(early_coordinate_max):.12e}")
    print(f"frame_cert_times_logN={float(normalized_capture):.12e}")
    print(f"anchored_fixed_energy={float(fixed_energy):.12e}")
    print(f"anchored_fixed_early_max={float(fixed_early_coordinate_max):.12e}")
    print(f"anchored_fixed_cert_times_logN={float(fixed_normalized_capture):.12e}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-k", type=int, default=256)
    parser.add_argument("--cutoff", type=int, default=1_000_000)
    parser.add_argument("--chunk", type=int, default=10_000)
    parser.add_argument("--exact", action="store_true")
    parser.add_argument("--extended-candidates", action="store_true")
    parser.add_argument("--gpu-n", type=int)
    parser.add_argument("--gpu-gradient-n", type=int)
    parser.add_argument("--gpu-frame-n", type=int)
    parser.add_argument("--frame-dimension", type=int, default=8)
    parser.add_argument("--gpu-block-chunk", type=int, default=128)
    parser.add_argument("--cg-tolerance", type=float, default=1e-11)
    parser.add_argument("--cg-max-iterations", type=int, default=12_000)
    args = parser.parse_args()

    selected_gpu_modes = sum(
        mode is not None
        for mode in (args.gpu_n, args.gpu_gradient_n, args.gpu_frame_n)
    )
    if selected_gpu_modes > 1:
        parser.error("choose only one GPU experiment mode")

    if args.gpu_frame_n is not None:
        gpu_shifted_frame_certificate(
            args.gpu_frame_n,
            args.cutoff,
            args.frame_dimension,
            args.gpu_block_chunk,
            args.cg_tolerance,
            args.cg_max_iterations,
        )
        return

    if args.gpu_gradient_n is not None:
        gpu_gradient_certificate(
            args.gpu_gradient_n,
            args.cutoff,
            args.gpu_block_chunk,
            args.cg_tolerance,
            args.cg_max_iterations,
        )
        return

    if args.gpu_n is not None:
        gpu_direction_certificate(
            args.gpu_n,
            args.cutoff,
            args.gpu_block_chunk,
            args.cg_tolerance,
            args.cg_max_iterations,
        )
        return

    if args.exact:
        gram, target, tail_mass = exact_gram_data(args.max_k)
    else:
        gram, target, tail_mass = gram_data(args.max_k, args.cutoff, args.chunk)
    print(f"cutoff={args.cutoff} omitted_weight_mass={tail_mass:.3e}")
    print("N distance_sq capture_ratio ratio_times_logN")
    mu = mobius_values(args.max_k)
    n = 4
    while 2 * n <= args.max_k:
        d_n = distance_sq(gram, target, n - 1)
        d_2n = distance_sq(gram, target, 2 * n - 1)
        capture = (d_n - d_2n) / d_n
        indices = np.arange(n + 1, 2 * n + 1)
        candidates = {
            "one": np.ones(n),
            "mu": mu[indices],
            "mu/k": mu[indices] / indices,
            "alt": (-1.0) ** indices,
        }
        if args.extended_candidates:
            log_taper = np.log(2.0 * n / indices)
            candidates.update({
                "mu*k": mu[indices] * indices,
                "mu/sqrt(k)": mu[indices] / np.sqrt(indices),
                "mu/k^2": mu[indices] / indices**2,
                "mu*sqrt(logTail)": mu[indices] * np.sqrt(log_taper),
                "mu*logTail": mu[indices] * log_taper,
            })
        certs = []
        for name, coeff in candidates.items():
            absolute = certificate_capture(gram, target, n, coeff)
            certs.append(f"{name}={absolute/d_n*np.log(n):.3e}")
        print(
            f"{n:4d} {d_n:.10e} {capture:.10e} "
            f"{capture*np.log(n):.10e} " + " ".join(certs)
        )
        n *= 2


if __name__ == "__main__":
    main()
