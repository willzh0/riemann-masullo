"""Independently compute the two cosine ceilings from a scalar quadratic in U.

The residue-class Hurwitz expansion supplies the zero mass. Requires
python-flint 0.9.0. This file is independent of check_prefix.py.
"""
from flint import acb, arb, ctx


def hurwitz_mass():
    # In L(1+t,chi)=5^(-1-t) sum chi(a) zeta(1+t,a/5),
    # the four poles cancel. Work directly with the constant and linear terms.
    residues = (1, acb(0, 1), acb(0, -1), -1)
    constant = acb(0)
    linear = acb(0)
    for a, value in enumerate(residues, start=1):
        fraction = arb(a) / 5
        constant -= value * fraction.digamma()
        linear -= value * acb.stieltjes(1, fraction)
    log_derivative = linear / constant - arb(5).log()
    return (5 / arb.pi()).log() - arb.const_euler() + 2 * log_derivative.real


def check_window(mass, n, m, beta, endpoint):
    n, m = arb(n), arb(m)
    ell = 4 * m.log()
    lam = arb(15) / 4
    small = beta * ell - arb(5).log()
    large = 3 * ell / 4 + (lam / 5).log()

    def power(k):
        return 1 / (1 + arb(k)) + 1 / n

    sigma = arb(1) / 200
    variance = (arb.pi() / 19_998_000)**2
    inv_d = 1 / (1 - variance / (2 * sigma**2))
    first_abs = inv_d * (sigma**2 / 8).exp() * variance.sqrt()
    moment_three_halves = inv_d * (sigma**2 / 2).exp()
    moment_four_thirds = inv_d * (25 * sigma**2 / 72).exp()
    square = variance * inv_d * (9 * sigma**2 / 8).exp()
    mixed = variance * inv_d * sigma * (2 / arb(1).exp()).sqrt() * (9 * sigma**2 / 4).exp()
    spectral_high = inv_d * (9 * sigma**2 / 8 - (2000 * sigma)**2 / 2).exp()

    sqrt2 = arb(2).sqrt()
    t0 = arb(8_000_000_000)
    constant = arb(930294) / 1_000_000 * (m / n)**7
    constant += (mass + 1 / (315 * t0.log())) * moment_three_halves * power(6)
    constant += (2 * arb(4).log() * t0**3 / 3 + 8) / n**6
    constant += 11 * moment_four_thirds * power(arb(16) / 3) / n**(arb(2) / 3)
    constant += 4 * power(4) / n**2
    constant += sqrt2 * (4 * n.log() + first_abs) * power(8 * beta) * n**(8 * beta - 6) / 2
    constant += sqrt2 * lam**2 * (ell + first_abs) * (1 + 1 / small) * power(6) / (8 * large**2)
    coefficient = power(8) * (2 * mass * spectral_high + sqrt2 * (ell * square + mixed) / (4 * large))
    root = ((1 - constant) / coefficient).sqrt()
    assert endpoint < root < endpoint + 1
    print("continuous majorant crossing", root)
    for j in (endpoint, endpoint + 1):
        value = constant + coefficient * j**2
        assert (value < 1) if j == endpoint else (value > 1)
        print(j, value)


if __name__ == "__main__":
    ctx.prec = 180
    mass = hurwitz_mass()
    print("precision", ctx.prec, "bits")
    print("zero mass from the Hurwitz expansions", mass)
    check_window(mass, 8_000_000, 2_350_000, arb(7) / 11, 27_154_480)
    check_window(mass, 26_000_000, 7_500_000, arb(9) / 14, 27_173_860)
