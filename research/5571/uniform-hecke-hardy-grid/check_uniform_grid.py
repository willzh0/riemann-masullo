"""Check the numerical inequalities in the uniform Hardy-grid proof by exact arithmetic.

Run with Python 3.10 or newer. No numeric values of L-functions, zeros, or grids
are used. Polynomial inequalities are verified for every k >= 3 and d >= 1 by
translating k=a+3, d=b+1 and checking their integer coefficients.
"""
from collections import defaultdict
from fractions import Fraction as Q
from math import comb
import json


def shifted_coefficients(terms):
    """The exact powers of a,b in p(a+3,b+1), from p's powers of k,d."""
    shifted = defaultdict(int)
    for (power_k, power_d), coefficient in terms.items():
        for i in range(power_k + 1):
            for j in range(power_d + 1):
                shifted[i, j] += (coefficient * comb(power_k, i)
                                   * 3 ** (power_k - i) * comb(power_d, j))
    return {power: c for power, c in shifted.items() if c}


def check_all():
    checked = {}
    polynomial = {}

    def scalar(name, left, right):
        if not left < right:
            raise ValueError(f"{name}: {left} >= {right}")
        checked[name] = [str(left), str(right)]

    def positive(name, terms):
        shifted = shifted_coefficients(terms)
        minimum = shifted.get((0, 0), 0)
        if minimum <= 0 or any(c < 0 for c in shifted.values()):
            raise ValueError(f"{name}: failed coefficient certificate {shifted}")
        polynomial[name] = {"minimum_at_k3_d1": minimum,
                            "shifted_coefficients": {
                                f"a^{i} b^{j}": c for (i, j), c in sorted(shifted.items())}}

    # Basic outward bounds, with e <= 1+1+1/2+(1/6)/(1-1/4).
    scalar("e_lower", 2, Q(5, 2))
    scalar("e_upper", Q(5, 2) + Q(1, 6) / (1 - Q(1, 4)), Q(11, 4))
    scalar("e_below_2_to_three_halves", Q(11, 4) ** 2, 2**3)
    scalar("quarter_plane_gain", 2, Q(5, 4) ** 4)
    scalar("six_times_B_plus_4_over_2^k", 6 * (1 + Q(4, 8)), 16)
    scalar("two_times_B_plus_40_over_2^k", 2 * (1 + Q(40, 8)), 16)
    scalar("boundary_constant_for_3^d", 9, 16)
    # N-d-2 >= 4[6+k+d(k+4)] and log2(n) clears the extrapolation onset.
    positive("strip_exponent_slack", {(1, 1): 96, (0, 1): -17,
                                      (1, 0): -4, (0, 0): -26})
    positive("extrapolation_onset_slack", {(2, 1): 10**6, (1, 1): -4,
                                            (0, 1): -16, (1, 0): -10, (0, 0): -20})
    scalar("inverse_euler_filter", 2, Q(17, 12) ** 2)
    # 12*(2+(9/4)*2^d)/2^k <= 12*(2/8+9/4), d<=k and k>=3.
    scalar("node_prefactor_over_2^k", 12 * (Q(2, 8) + Q(9, 4)), 32)
    # n>=2^k>=k implies v=6*(2n+2)>=12(k+1); u>=v+1.
    positive("two_v_minus_parenthesized_k_plus_5",
             {(1, 0): 23, (0, 0): 19})
    scalar("fourier_ratio_squared", Q(5, 8)**2, Q(1, 2))
    scalar("fourier_aliasing_prefactor", 1 + Q(8, 3), 4)

    # For the disk sublevel bound log(19/18)>=1/19 by integrating 1/t.
    scalar("jensen_log_lower", Q(1, 20), Q(1, 19))
    scalar("critical_segment_radius_squared", Q(5, 2), Q(8, 5)**2)
    scalar("harnack_ratio", (Q(7, 4) + Q(8, 5)) / (Q(7, 4) - Q(8, 5)), 24)
    scalar("blaschke_denominator", Q(9, 5) + Q(8, 5), 4)
    # A_j, and C_0+d log J, are <=101dk + k + 9d + 7.
    positive("110dk_minus_local_log_bound", {(1, 1): 9, (1, 0): -1,
                                              (0, 1): -9, (0, 0): -7})
    # H-24*(110dk)-N*101k-(40k)*(20*110dk).
    positive("near_clipping_exponent_slack", {(2, 1): 1900, (1, 1): -2640})
    # Near <= 2^29 k^4 2^(-40k); use k<=2^k.
    scalar("near_prefactor", 9 * 3200 * 110**2, 2**29)
    positive("near_2_to_minus_k_over_64", {(1, 0): 35, (0, 0): -35})
    # Far <=4*(460k^2)*(12200k^4)*2^(-100k), using d<=k.
    positive("460k^2_minus_parenthesized_3224_plus_100k^2", {(2, 0): 360, (0, 0): -3224})
    positive("far_moment_bracket_slack", {(2, 0): 100, (1, 0): -220, (0, 0): -2})
    scalar("far_prefactor", 4 * 460 * 12200, 2**25)
    positive("far_2_to_minus_k_over_64", {(1, 0): 93, (0, 0): -31})

    # The clipped predictor's two norm bounds, and the corrected finite row.
    scalar("clipped_predictor_energy_prefactor", 2 + 4 * Q(16, 9)**2, 20)
    scalar("ellipsoid_factor", 50, 2**6)
    positive("log2_n_minus_parenthesized_6_plus_6H", {(2, 1): 400000, (0, 0): -6})
    scalar("rounding_and_row_norm_prefactor", 1 + 2 + 5 + Q(32, 9), 12)
    scalar("12_times_64", 12 * 64, 2**10)
    positive("log2_n_minus_parenthesized_2k_plus_20", {(2, 1): 10**6, (1, 0): -2, (0, 0): -20})
    scalar("final_error_divided_by_epsilon",
           2 * (Q(1, 32) + Q(1, 64)) + 2 * Q(1, 64) + Q(1, 64)**2, 1)
    scalar("gamma_bound_3_to_2", 3, 2**2)
    # b = 7+k+d(k+7) is the sum of log2 M, 2d, and d+1 envelopes.
    green_parts = {(0, 0): 6+1, (1, 0): 1, (0, 1): 4+2+1, (1, 1): 1}
    if green_parts != {(0, 0): 7, (1, 0): 1, (0, 1): 7, (1, 1): 1}:
        raise ValueError("Green logarithmic clearance")
    example_b = 7+3+1*(3+7)
    example_top = 2*example_b+20+1
    if (example_b, example_top) != (20, 61):
        raise ValueError("twenty-bit example")
    return {"parameters": {"k": "integer >= 3", "degree": "1 <= d <= k",
                           "N": "any fixed integer >= 100*d*k", "p": "integer >= k and N/(100*d)",
                           "H": "100000*d*p^2",
                           "log2_J": "100*p", "log2_n_lower": "1000000*d*p^2",
                           "green_log2_clearance_b": "7+k+d*(k+7)",
                           "p_for_L_binary_logarithmic_places": "max(p0,2*b+L+1)"},
            "fractional_strict_inequalities": checked,
            "positive_polynomial_certificates": polynomial}


if __name__ == "__main__":
    print(json.dumps(check_all(), indent=2) + "\n", end="")
