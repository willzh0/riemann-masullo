"""Certify a finite range for the unsmoothed complex quartic prime prefix.

Run with Python 3 and python-flint 0.9.0. The first 8,000,000 prefixes
use the pinned earlier certificate cited in README.md.
"""
from argparse import ArgumentParser

from flint import acb, acb_series, arb, ctx, dirichlet_char


def character_constants():
    character = dirichlet_char(5, 2)
    assert [character(a) for a in range(1, 6)] == [1, acb(0, 1), acb(0, -1), -1, 0]

    def log_derivative(s):
        series = acb_series([s, 1], prec=2).dirichlet_l(character)
        return (series[1] / series[0]).conjugate()

    gamma_term = (arb(5) / arb.pi()).log() - arb.const_euler()
    mass = gamma_term + 2 * log_derivative(1).real
    residue_zero = gamma_term - arb(2).log() + log_derivative(1)
    residue_minus_one = gamma_term - arb(2).log() + 1 + log_derivative(2)
    assert 0 < mass < arb(".204")
    assert abs(residue_zero) < 1 and abs(residue_minus_one) < 1
    return mass


def zero_count_tail(height):
    """Two-sided Stieltjes bounds, including a Gaussian version, at fixed height."""
    leading_log = (5 * height / (2 * arb.pi())).log()
    count_log = (5 * (height + 2) / (2 * arb.pi())).log()
    error = arb(".22737") * count_log + 2 * (1 + count_log).log() - arb(1) / 2
    slope = arb(".22737") + 2 / (1 + count_log)
    center = (leading_log + 1) / (arb.pi() * height)
    radius = (2 * error + slope / 2) / height**2
    print("unsmoothed high-zero inverse-square tail", center - radius, center + radius)

    def gaussian(a):
        assert a >= 0
        power = 1 + 2 * a
        leading = (leading_log / power + 1 / power**2) / (arb.pi() * height)
        error_term = (2 * error + slope / (2 + 2 * a)) / height**2
        return (-a).exp() * (leading + error_term)

    return gaussian


def smoothing(method, lower, upper, height, mass, gaussian_tail, width):
    """Return the two real Mellin bounds, the physical moments and high-zero cost."""
    if method == "cosine":
        cutoff = arb(19_998_000)
        sigma = arb(1) / 200
        variance = (arb.pi() / cutoff)**2
        normalizer = 1 - variance / (2 * sigma**2)
        assert 0 < cutoff < height and normalizer > 0

        def moment(r):
            return (((r - arb(1) / 2) * sigma)**2 / 2).exp() / normalizer

        log_abs = variance.sqrt() * (sigma**2 / 8).exp() / normalizer
        square = variance * (9 * sigma**2 / 8).exp() / normalizer
        mixed = variance * sigma * (2 / arb(1).exp()).sqrt() * (9 * sigma**2 / 4).exp() / normalizer
        multiplier = (9 * sigma**2 / 8 - ((height - cutoff) * sigma)**2 / 2).exp() / normalizer
        high8 = 2 * mass * multiplier * upper**2
        return moment(arb(3) / 2), moment(arb(4) / 3), log_abs, square * upper**2, mixed * upper**2, high8, arb(0)

    assert method == "gaussian"
    v0 = (width / lower)**2
    assert 108 * v0 * (6 * v0).exp() + 6 * v0.exp() < 8
    assert v0.exp() < arb("1.0001")
    assert 2 * (1 + v0 / 4).sqrt() < 3
    log_abs = (v0 * (1 + v0 / 4)).sqrt()
    a = (width * height / upper)**2 / 2
    tail = gaussian_tail(a) / 2
    return ((3 * v0 / 8).exp(), (2 * v0 / 9).exp(), log_abs, arb("1.0001") * width**2,
            3 * v0.sqrt() * width**2, tail * v0.exp() * upper**2, tail / lower**2)


def bounds(method, lower_index, upper_index, prefix_index, beta, lam, mass, height, gaussian_tail, width=arb(0)):
    """Each entry bounds the corresponding nonnegative cost divided by J^7."""
    lower, upper, prefix = map(arb, (lower_index, upper_index, prefix_index))
    assert 100_000 <= prefix_index <= 8_000_000 and prefix_index < lower_index <= upper_index
    low, higher, log_abs, square, mixed, high8, high4 = smoothing(
        method, lower, upper, height, mass, gaussian_tail, width)
    alpha = arb(3) / 4
    ell = 4 * prefix.log()
    bs = beta - arb(5).log() / ell
    br = alpha + (lam / 5).log() / ell
    assert 0 < beta < alpha and 1 < lam <= 5 and bs > 0 and br > 0
    assert (beta * ell).exp() - 1 > 5 * arb(1).exp()
    assert (8 * beta - 6) * (4 * lower.log() + log_abs) + 4 < 0

    def power_sum(a):
        return 1 / (arb(a) + 1) + 1 / lower

    threshold = arb(8_000_000_000)
    sqrt2 = arb(2).sqrt()
    return {
        "inherited prefix": arb(".930294") * (prefix / lower)**7,
        "low zeros": mass * low * power_sum(6),
        "signed prime squares": low * power_sum(6) / (315 * threshold.log()),
        "small-square constant": 2 * arb(4).log() * threshold**3 / (3 * lower**6),
        "higher prime powers": 11 * higher * power_sum(arb(16) / 3) * lower**(-arb(2) / 3),
        "affine term": 4 * power_sum(4) / lower**2 + 8 / lower**6,
        "high zeros": high8 * power_sum(8) + high4 * power_sum(4),
        "short curvature": sqrt2 * (4 * lower.log() + log_abs) * power_sum(8 * beta) * lower**(8 * beta - 6) / 2,
        "middle curvature": sqrt2 * lam**2 * (1 + log_abs / ell) * power_sum(6)
                            * (1 + 1 / (bs * ell)) / (8 * br**2 * ell),
        "bulk curvature": sqrt2 * (square + mixed / ell) * power_sum(8) / (4 * br),
    }


def crossing(calculation, passed, failed):
    def total(index):
        return sum(calculation(index).values(), arb(0))

    assert total(passed) < 1 and total(failed) > 1
    while failed - passed > 1:
        middle = (passed + failed) // 2
        value = total(middle)
        if value < 1:
            passed = middle
        else:
            assert value > 1
            failed = middle
    return passed, failed


def show(title, calculation, index):
    entries = calculation(index)
    print(title, index)
    for key, value in entries.items():
        print(" ", key, value)
    total = sum(entries.values(), arb(0))
    print("  normalized upper", total)
    assert total < 1


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--bits", type=int, default=192)
    args = parser.parse_args()
    assert args.bits >= 96
    ctx.prec = args.bits
    height = arb(20_000_000)
    mass = character_constants()
    print("precision", ctx.prec, "bits")
    print("completed low-zero mass bound B", mass)
    tail = zero_count_tail(height)

    def gaussian(j):
        return bounds("gaussian", 8_000_000, j, 2_340_000, arb(7) / 11, arb(73) / 20,
                      mass, height, tail, arb(413) / 100)

    def first(j):
        return bounds("cosine", 8_000_000, j, 2_350_000, arb(7) / 11, arb(15) / 4,
                      mass, height, tail)

    def last(j):
        return bounds("cosine", 26_000_000, j, 7_500_000, arb(9) / 14, arb(15) / 4,
                      mass, height, tail)

    for title, calculation, passed, failed, expected_end in [
        ("lognormal", gaussian, 15_350_000, 16_000_000, 15_354_595),
        ("cosine from eight million", first, 27_100_000, 28_000_000, 27_154_480),
        ("cosine from 26 million", last, 27_160_000, 28_000_000, 27_173_860),
    ]:
        show(title, calculation, passed)
        end, successor = crossing(calculation, passed, failed)
        assert (end, successor) == (expected_end, expected_end + 1)
        end_total = sum(calculation(end).values(), arb(0))
        next_total = sum(calculation(successor).values(), arb(0))
        print("  last certified integer", end, "upper", end_total)
        print("  same majorant at successor", successor, next_total)


if __name__ == "__main__":
    main()
