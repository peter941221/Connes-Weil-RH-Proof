import numpy as np, math
from f0 import null_setup, arch_matrix, prime_matrix, lam_sieve
from scipy.linalg import eigh

def true_pairs(a):
    two_r = 2.0 * a; bound = int(math.floor(math.exp(two_r)))
    lam = lam_sieve(bound)
    pairs = [(q, lam[q] / math.sqrt(q)) for q in range(2, bound + 1)
             if lam[q] > 0 and math.log(q) < two_r - 1e-9]
    return [math.log(q) for q, _ in pairs], [w for _, w in pairs]

def run(a=4.0, K=8, n=4001):
    t, h, coeffs, basis = null_setup(a, K, n)
    funcs = coeffs.T @ basis
    A = arch_matrix(funcs, h)
    ev = lambda m: float(eigh((m + m.T) / 2.0, eigvals_only=True)[-1])
    shifts, weights = true_pairs(a); m = len(shifts)
    P_true = prime_matrix(funcs, coeffs, basis, t, h, a, K, shifts, weights)
    print(f"a={a} K={K}: m={m}, top(arch+prime_true) = {ev(A+P_true):+.2e}")
    for variant in ["2a-perm", "2b-unif", "2c-rndw"]:
        for seed in range(1, 6):
            rng = np.random.default_rng(seed)
            if variant == "2a-perm":
                perm = rng.permutation(m)
                sh_c = [shifts[perm[j]] for j in range(m)]; w_c = list(weights)
            elif variant == "2b-unif":
                sh_c = list(rng.uniform(0.0, 2.0 * a, size=m)); w_c = list(weights)
            else:
                sh_c = list(shifts)
                r = rng.random(m); w_c = list(r * sum(weights) / r.sum())
            Pc = prime_matrix(funcs, coeffs, basis, t, h, a, K, sh_c, w_c)
            print(f"{variant:<10} seed {seed}  top = {ev(A + Pc):+.6f}")

if __name__ == "__main__":
    run()
