#!/usr/bin/env python3
"""Probe a cosh-weighted Picone lower bound for the pole-free Weil form.

For C(x)=cosh(x/2) and v=C*u, the exact jump-form ground-state
representation has potential (A_tilde C)/C.  Pole neutrality becomes
integral C^2*u=0.  Replacing the transformed jump kernel by the explicit
complete-graph minorant J(2a)/C(a)^2 gives a rigorous sufficient margin once
the remaining one-dimensional infimum is certified.  This script is only a
high-precision reconnaissance probe; it does not certify that infimum.
"""

from __future__ import annotations

import argparse

import mpmath as mp


def prime_powers_up_to(cutoff: int) -> list[tuple[int, int]]:
    primes: list[int] = []
    for candidate in range(2, cutoff + 1):
        if all(candidate % prime for prime in primes):
            primes.append(candidate)

    result: list[tuple[int, int]] = []
    for prime in primes:
        prime_power = prime
        while prime_power <= cutoff:
            result.append((prime_power, prime))
            prime_power *= prime
    return result


def jump_kernel(distance: mp.mpf) -> mp.mpf:
    distance = abs(distance)
    if distance == 0:
        return mp.inf
    return mp.exp(-distance / 2) / (-mp.expm1(-2 * distance))


def regular_kernel_primitive(length: mp.mpf) -> mp.mpf:
    """Return integral_0^length (J(t)-1/(2t)) dt."""
    if length == 0:
        return mp.mpf("0")
    if abs(length) < mp.mpf("1e-8"):
        return (
            length / 4
            - length**2 / 96
            - length**3 / 96
            + 7 * length**4 / 46080
        )
    u = mp.exp(-length / 2)
    return (
        mp.log(4 / length) / 2
        + mp.pi / 4
        - mp.log((1 + u) / (1 - u)) / 2
        - mp.atan(u)
    )


def continuous_jump_on_cosh(x: mp.mpf, a: mp.mpf) -> mp.mpf:
    c_x = mp.cosh(x / 2)

    def integrand(y: mp.mpf) -> mp.mpf:
        if y == x:
            return mp.mpf("0")
        return jump_kernel(x - y) * (c_x - mp.cosh(y / 2))

    return mp.quad(integrand, [-a, x, a])


def polefree_potential(
    x: mp.mpf,
    a: mp.mpf,
    prime_data: list[tuple[int, int]],
) -> mp.mpf:
    """Evaluate the source potential kappa_a at an interior point."""
    m1_x = regular_kernel_primitive(a + x) + regular_kernel_primitive(a - x)
    prime_degree = mp.mpf("0")
    for prime_power, prime in prime_data:
        shift = mp.log(prime_power)
        weight = mp.log(prime) / mp.sqrt(prime_power)
        prime_degree += weight * (
            int(x <= a - shift) + int(x >= -a + shift)
        )
    return (
        -mp.log(a * a - x * x) / 2
        - mp.log(2 * mp.pi)
        - mp.euler
        - m1_x
        - prime_degree
    )


def polefree_cosh_quotient(
    x: mp.mpf,
    a: mp.mpf,
    prime_data: list[tuple[int, int]],
) -> mp.mpf:
    c_x = mp.cosh(x / 2)

    prime_jump = mp.mpf("0")
    for prime_power, prime in prime_data:
        shift = mp.log(prime_power)
        weight = mp.log(prime) / mp.sqrt(prime_power)
        has_right = x <= a - shift
        has_left = x >= -a + shift
        if has_right:
            prime_jump += weight * (c_x - mp.cosh((x + shift) / 2))
        if has_left:
            prime_jump += weight * (c_x - mp.cosh((x - shift) / 2))

    kappa = polefree_potential(x, a, prime_data)
    applied = continuous_jump_on_cosh(x, a) + prime_jump + kappa * c_x
    return applied / c_x


def endpoint_cell_width(
    cutoff: int,
    prime_data: list[tuple[int, int]],
) -> mp.mpf:
    """Width on which the endpoint indicator pattern is constant."""
    gaps = [
        mp.log(mp.mpf(cutoff) / prime_power)
        for prime_power, _ in prime_data
        if prime_power < cutoff
    ]
    return min([mp.log(2), *gaps])


def endpoint_prime_mass(
    cutoff: int,
    prime_data: list[tuple[int, int]],
) -> mp.mpf:
    return mp.fsum(
        mp.log(prime) / mp.sqrt(prime_power)
        for prime_power, prime in prime_data
        if prime_power < cutoff
    )


def endpoint_potential_from_distance(
    cutoff: int,
    a: mp.mpf,
    distance: mp.mpf,
    prime_data: list[tuple[int, int]],
) -> mp.mpf:
    """Evaluate kappa_a(a-d) stably in the final indicator cell."""
    return (
        -mp.log(distance * (2 * a - distance)) / 2
        - mp.log(2 * mp.pi)
        - mp.euler
        - regular_kernel_primitive(distance)
        - regular_kernel_primitive(2 * a - distance)
        - endpoint_prime_mass(cutoff, prime_data)
    )


def find_endpoint_collar(
    cutoff: int,
    a: mp.mpf,
    prime_data: list[tuple[int, int]],
) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    """Find d with kappa_a(a-d)=0 inside the last indicator cell."""
    cell_width = endpoint_cell_width(cutoff, prime_data)
    inner_distance = cell_width / 2

    def potential_at_log_distance(log_inverse_distance: mp.mpf) -> mp.mpf:
        distance = mp.exp(-log_inverse_distance)
        return endpoint_potential_from_distance(
            cutoff, a, distance, prime_data
        )

    lower = -mp.log(inner_distance)
    if potential_at_log_distance(lower) >= 0:
        raise AssertionError("endpoint cell is already nonnegative at its inner probe")
    upper = max(lower + 1, mp.mpf("1"))
    while potential_at_log_distance(upper) <= 0:
        upper *= 2
    for _ in range(240):
        midpoint = (lower + upper) / 2
        if potential_at_log_distance(midpoint) > 0:
            upper = midpoint
        else:
            lower = midpoint
    root_log_inverse = (lower + upper) / 2
    return mp.exp(-root_log_inverse), root_log_inverse, cell_width


def print_endpoint_collar(
    cutoff: int,
    a: mp.mpf,
    prime_data: list[tuple[int, int]],
) -> tuple[mp.mpf, mp.mpf]:
    distance, log_inverse, cell_width = find_endpoint_collar(
        cutoff, a, prime_data
    )
    prime_mass = endpoint_prime_mass(cutoff, prime_data)
    print(f"endpoint_indicator_cell_width={mp.nstr(cell_width, 18)}")
    print(f"endpoint_prime_mass={mp.nstr(prime_mass, 18)}")
    print(f"endpoint_collar_width={mp.nstr(distance, 25)}")
    print(f"endpoint_collar_log_inverse={mp.nstr(log_inverse, 25)}")
    return distance, log_inverse


def exact_center_quotient(
    cutoff: int,
    a: mp.mpf,
    prime_data: list[tuple[int, int]],
) -> mp.mpf:
    """Closed form for (A_tilde C)(0)/C(0)."""
    prime_sum = mp.fsum(
        mp.log(prime) * (1 + mp.mpf(1) / prime_power)
        for prime_power, prime in prime_data
        if prime_power * prime_power <= cutoff
    )
    return (
        -a
        - mp.log1p(-mp.exp(-a))
        - mp.log(2 * mp.pi)
        - mp.euler
        - prime_sum
    )


def probe(cutoff: int, grid_size: int) -> None:
    a = mp.log(cutoff) / 2
    prime_data = prime_powers_up_to(cutoff)
    endpoint_epsilon = min(mp.mpf("1e-6"), a / (10 * grid_size))
    left = -a + endpoint_epsilon
    right = a - endpoint_epsilon
    points = [
        left + (right - left) * index / (grid_size - 1)
        for index in range(grid_size)
    ]
    quotients = [polefree_cosh_quotient(x, a, prime_data) for x in points]
    minimum_index = min(range(grid_size), key=lambda index: quotients[index])
    minimum_x = points[minimum_index]
    minimum_quotient = quotients[minimum_index]
    center_quotient = polefree_cosh_quotient(mp.mpf("0"), a, prime_data)
    center_quotient_closed = exact_center_quotient(cutoff, a, prime_data)
    if not mp.almosteq(center_quotient, center_quotient_closed):
        raise AssertionError(
            "center quotient does not match its closed form: "
            f"{center_quotient} != {center_quotient_closed}"
        )

    c_endpoint = mp.cosh(a / 2)
    kernel_minorant = jump_kernel(2 * a) / (c_endpoint * c_endpoint)
    c_squared_mass = a + mp.sinh(a)
    weighted_gap = kernel_minorant * c_squared_mass
    sufficient_margin = weighted_gap + minimum_quotient

    print(f"cutoff={cutoff} a={mp.nstr(a, 18)} grid={grid_size}")
    print(f"kernel_minorant={mp.nstr(kernel_minorant, 18)}")
    print(f"C_squared_mass={mp.nstr(c_squared_mass, 18)}")
    print(f"weighted_gap={mp.nstr(weighted_gap, 18)}")
    print(f"center_AtC_over_C={mp.nstr(center_quotient, 18)}")
    print(
        "center_sufficient_margin="
        f"{mp.nstr(weighted_gap + center_quotient_closed, 18)}"
    )
    print(f"min_AtC_over_C={mp.nstr(minimum_quotient, 18)}")
    print(f"min_location={mp.nstr(minimum_x, 18)}")
    print(f"sufficient_margin={mp.nstr(sufficient_margin, 18)}")
    print_endpoint_collar(cutoff, a, prime_data)
    print()


def regular_kernel_primitive_arb(length):
    """Arb version of integral_0^length (J(t)-1/(2t)) dt."""
    from flint import arb

    u = (-length / 2).exp()
    return (
        (arb(4) / length).log() / 2
        + arb.pi() / 4
        - ((1 + u) / (1 - u)).log() / 2
        - u.atan()
    )


def endpoint_potential_arb(
    cutoff: int,
    a,
    log_inverse_distance: str,
    prime_data: list[tuple[int, int]],
):
    """Evaluate kappa_a(a-d) in the final, constant-indicator cell."""
    from flint import arb

    distance = (-arb(log_inverse_distance)).exp()
    prime_mass = arb(0)
    for prime_power, prime in prime_data:
        if prime_power < cutoff:
            prime_mass += arb(prime).log() / arb(prime_power).sqrt()
    return (
        -(distance * (2 * a - distance)).log() / 2
        - (2 * arb.pi()).log()
        - arb.const_euler()
        - regular_kernel_primitive_arb(distance)
        - regular_kernel_primitive_arb(2 * a - distance)
        - prime_mass
    )


def certify_center_margin(cutoff: int, precision_bits: int) -> None:
    """Certify the closed-form center upper bound with Arb intervals."""
    from flint import arb, ctx

    ctx.prec = precision_bits
    a = arb(cutoff).log() / 2
    endpoint_cosh = (a / 2).cosh()
    kernel_minorant = (-a).exp() / (1 - (-4 * a).exp())
    weighted_gap = kernel_minorant * (a + a.sinh()) / (endpoint_cosh**2)

    prime_sum = arb(0)
    for prime_power, prime in prime_powers_up_to(cutoff):
        if prime_power * prime_power <= cutoff:
            prime_sum += arb(prime).log() * (1 + arb(1) / prime_power)

    center_quotient = (
        -a
        - (1 - (-a).exp()).log()
        - (2 * arb.pi()).log()
        - arb.const_euler()
        - prime_sum
    )
    center_margin = weighted_gap + center_quotient
    print(
        f"cutoff={cutoff} Arb_bits={precision_bits} "
        f"certified_center_margin={center_margin.str(25)}"
    )
    if not center_margin < 0:
        raise AssertionError("expected the cosh-Picone center bound to be negative")

    mp.mp.dps = max(80, precision_bits // 3)
    a_mp = mp.log(cutoff) / 2
    distance, root_log_inverse, _ = find_endpoint_collar(
        cutoff, a_mp, prime_powers_up_to(cutoff)
    )
    bracket_radius = mp.mpf("1e-20")
    lower_log = root_log_inverse - bracket_radius
    upper_log = root_log_inverse + bracket_radius
    lower_value = endpoint_potential_arb(
        cutoff, a, mp.nstr(lower_log, 80), prime_powers_up_to(cutoff)
    )
    upper_value = endpoint_potential_arb(
        cutoff, a, mp.nstr(upper_log, 80), prime_powers_up_to(cutoff)
    )
    if not lower_value < 0 or not upper_value > 0:
        raise AssertionError("Arb did not separate the endpoint collar root")
    print(
        f"cutoff={cutoff} Arb_bits={precision_bits} "
        f"endpoint_collar_width={mp.nstr(distance, 25)} "
        f"root_bracket_signs=({lower_value.str(8)}, {upper_value.str(8)})"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cutoff", type=int, nargs="+", default=[5, 13, 29, 53])
    parser.add_argument("--grid-size", type=int, default=161)
    parser.add_argument("--dps", type=int, default=60)
    parser.add_argument("--certify-only", action="store_true")
    parser.add_argument("--collar-only", action="store_true")
    parser.add_argument("--arb-bits", type=int, default=512)
    args = parser.parse_args()

    if args.certify_only:
        for cutoff in args.cutoff:
            certify_center_margin(cutoff, args.arb_bits)
    elif args.collar_only:
        mp.mp.dps = args.dps
        for cutoff in args.cutoff:
            a = mp.log(cutoff) / 2
            print(f"cutoff={cutoff} a={mp.nstr(a, 18)}")
            print_endpoint_collar(cutoff, a, prime_powers_up_to(cutoff))
            print()
    else:
        mp.mp.dps = args.dps
        for cutoff in args.cutoff:
            probe(cutoff, args.grid_size)


if __name__ == "__main__":
    main()
