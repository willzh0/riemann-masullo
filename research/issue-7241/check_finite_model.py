"""Check the normalized exponential-kernel formulas with finite dense matrices."""

import mpmath as mp
import numpy as np


def wave_multiplier(waves, symbol):
    """Solve B K = K diag(symbol) in standard Euclidean coordinates."""
    return np.linalg.solve(waves.T, (waves * symbol).T).T


def check_matrix(sites):
    sites = np.asarray(sites, dtype=float)
    n = len(sites)
    gram = np.exp(-np.abs(sites[:, None] - sites[None, :]))
    waves = np.linalg.cholesky(gram).T
    gaps = np.diff(sites)
    attenuation = np.exp(-gaps)
    normalization = np.sqrt(-np.expm1(-2 * gaps))
    edge = attenuation / normalization
    prescribed = 1 + np.r_[0.0, edge**2] + np.r_[edge**2, 0.0]

    # The direct solve fixes the biorthogonal vectors by their pairings.
    biorthogonals = np.linalg.solve(waves.T, np.eye(n))
    observed = np.sum(biorthogonals**2, axis=0)
    np.testing.assert_allclose(observed, prescribed, rtol=2e-9, atol=5e-12)

    basis = waves.copy()
    basis[:, 1:] = (
        waves[:, 1:] - waves[:, :-1] * attenuation
    ) / normalization
    np.testing.assert_allclose(basis.T @ basis, np.eye(n), atol=2e-10)

    symbol = np.exp(-0.11 * sites**2 + 0.3j * sites)
    operator = wave_multiplier(waves, symbol)
    h_column_errors = []
    for left in range(n):
        for right in range(left, n):
            inside = (left <= np.arange(n)) & (np.arange(n) <= right)
            section = wave_multiplier(waves, symbol * inside)
            tail = operator - section
            h = symbol * ~inside
            expected = basis * h
            expected[:, 1:] += waves[:, :-1] * (edge * np.diff(h))
            h_column_errors.append(np.max(np.abs(tail @ basis - expected)))
            hs_squared = np.linalg.norm(tail, "fro") ** 2
            edge_squared_sum = np.sum(np.abs(h) ** 2) + np.sum(np.abs(edge * np.diff(h)) ** 2)
            np.testing.assert_allclose(hs_squared, edge_squared_sum, rtol=2e-9, atol=5e-12)
            rank_one_bound = np.abs(h).sum() + np.abs(edge * np.diff(h)).sum()
            nuclear_norm = np.linalg.svd(tail, compute_uv=False).sum()
            assert nuclear_norm <= rank_one_bound + 2e-8
            if left:
                assert edge[left - 1] * abs(symbol[left - 1]) <= nuclear_norm + 2e-8
            if right + 1 < n:
                assert edge[right] * abs(symbol[right + 1]) <= nuclear_norm + 2e-8
            np.testing.assert_allclose(
                np.trace(section), symbol[inside].sum(), atol=2e-8
            )
    worst_error = max(h_column_errors)
    assert worst_error < 2e-8
    return np.max(np.abs(observed / prescribed - 1)), worst_error


def check_pairs():
    """Use high precision to preserve gaps far below a double-precision ulp."""
    mp.mp.dps = 100
    print("height  one-site trace norm  whole-pair trace norm")
    for n in (4, 8, 12):
        gap = mp.power(2, -8 * n)
        sites = [mp.mpf(n) - gap / 2, mp.mpf(n) + gap / 2]
        gram = mp.matrix([[mp.exp(-abs(t - u)) for u in sites] for t in sites])
        waves = mp.cholesky(gram).T
        b = [mp.power(2, -t) for t in sites]
        whole = waves * mp.diag(b) * waves**-1
        first = waves * mp.diag([b[0], 0]) * waves**-1
        first_norm = sum(mp.svd(first, compute_uv=False))
        whole_norm = sum(mp.svd(whole, compute_uv=False))
        edge = 1 / mp.sqrt(mp.expm1(2 * gap))
        expected_first = b[0] * mp.sqrt(1 + edge**2)
        expected_whole = mp.sqrt((b[0] + b[1])**2 + (edge * (b[1] - b[0]))**2)
        assert mp.almosteq(first_norm, expected_first, rel_eps=mp.mpf("1e-65"))
        assert mp.almosteq(whole_norm, expected_whole, rel_eps=mp.mpf("1e-65"))
        print(f"{n:6d}  {mp.nstr(first_norm, 9):>19}  {mp.nstr(whole_norm, 9):>21}")


if __name__ == "__main__":
    rng = np.random.default_rng(7455)
    examples = [
        [1.0],
        [-1.0, 0.75],
        [-4.0, -1.5, -1.49999, 0.0, 0.002, 0.7, 1.0, 4.0],
        np.cumsum(np.exp(rng.uniform(-8.0, 1.0, size=15))) - 1.0,
    ]
    results = [check_matrix(sites) for sites in examples]
    n_intervals = sum(len(sites) * (len(sites) + 1) // 2 for sites in examples)
    print(f"Verified {n_intervals} nonempty intervals in {len(examples)} finite models.")
    print(f"Largest relative coordinate-norm-squared error: {max(r[0] for r in results):.3g}")
    print(f"Largest absolute multiplier-column error: {max(r[1] for r in results):.3g}")
    check_pairs()
