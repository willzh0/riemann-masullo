"""Certify the shifted residues in MOVING_MEAN.md with python-flint 0.8.0.

All certified inequalities use real or complex balls and rational thresholds.
An exhaustive interval enclosure proves that one trigonometric sum is positive
throughout the transition interval, simultaneously for every admissible cutoff.
"""
import sys

import flint
from flint import acb, acb_series, arb, ctx, fmpq


SEEDS = (-69338619, 103743227, 141888760, -158426096)
BRACKET_DENOMINATOR = 2**24
COS_COEFFICIENTS = (7, -4)
SIN_COEFFICIENTS = (2, -5)
CELLS = 8192


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def l_value(s, quadratic=False):
    values = (1, -1, -1, 1) if quadratic else (1, acb(0, 1), acb(0, -1), -1)
    # Both rows have sum zero. Removing the Hurwitz pole is exact and keeps
    # power-series evaluations well conditioned near s=1 on the moving path.
    if isinstance(s, acb_series):
        terms = [s.zeta(fmpq(r, 5), deflate=True) for r in range(1, 5)]
    else:
        terms = [s.zeta(fmpq(r, 5)) for r in range(1, 5)]
    hurwitz = sum(value * term for value, term in zip(values, terms, strict=True))
    return (-arb(5).log() * s).exp() * hurwitz


def hardy(t):
    root_five = arb(5).sqrt()
    epsilon = acb(((5 + root_five) / 10).sqrt(), ((5 - root_five) / 10).sqrt())
    gamma = acb(fmpq(3, 4), t / 2).gamma()
    angle = acb(0, (arb(5) / arb.pi()).log() * t / 2).exp()
    return (epsilon.sqrt().conjugate() * gamma / abs(gamma) * angle
            * l_value(acb(fmpq(1, 2), t))).real


def check_roots():
    result = []
    kappa = fmpq(21, 100)
    d = BRACKET_DENOMINATOR
    for seed in SEEDS:
        left = arb(fmpq(seed, d))
        right = arb(fmpq(seed + 1, d))
        t = arb(fmpq(2 * seed + 1, 2 * d), fmpq(1, 2 * d))
        h_left, h_right = hardy(left), hardy(right)
        require((h_left < 0 < h_right) or (h_right < 0 < h_left), "Hardy signs")
        rho = acb(fmpq(1, 2), t)
        jet = l_value(acb_series([rho, 1]))
        derivative = jet[1]
        require(abs(derivative) > fmpq(1, 10), "simplicity on bracket")
        # With fixed phase this also proves uniqueness within this bracket.
        mid_derivative = l_value(acb_series([acb(fmpq(1, 2), (left + right) / 2), 1]))[1]
        require((derivative * mid_derivative.conjugate()).real > 0, "derivative direction")
        shifted = kappa + (1 - kappa) * rho
        required_values = (l_value(rho.conjugate()), l_value(shifted),
                           l_value(shifted.conjugate()), l_value(2 * rho, True),
                           l_value(2 * shifted, True))
        require(all(abs(x) > fmpq(1, 1000) for x in required_values), "a competing pole")
        print(f"  t={t.str(12)}, |L'|={abs(derivative).str(8)}, "
              f"|L(reflected)|={abs(required_values[0]).str(8)}")
        result.append(abs(t))
    return result


def check_moving_segments(ordinates):
    cells = 1024
    for t in (-ordinates[0], ordinates[1]):
        rho = acb(fmpq(1, 2), t)
        require(abs(rho) < 7, "complex derivative bound on segment")
        radius = abs(1 - rho) / (2 * cells)
        reference = l_value(acb_series([acb(fmpq(1, 2), t.mid()), 1]))[1]
        min_bounds = [arb(100)] * 3
        for i in range(cells):
            k = fmpq(2 * i + 1, 2 * cells)
            point = 1 + (1 - k) * (rho - 1)
            if i < cells // 32:
                derivative = l_value(acb_series([point, 1]))[1]
                projected = (derivative * reference.conjugate()).real / abs(reference)
                bound = projected - 170 * radius
                slot = 0
            else:
                bound = abs(l_value(acb_series([point]))[0]) - 43 * radius
                slot = 1
            require(bound > fmpq(1, 100), "direct moving segment")
            min_bounds[slot] = min(min_bounds[slot], bound.lower())
            reflected = abs(l_value(acb_series([point.conjugate()]))[0]) - 43 * radius
            require(reflected > fmpq(1, 100), "reflected moving segment")
            min_bounds[2] = min(min_bounds[2], reflected.lower())
        print("  moving segment bounds (initial derivative, direct, reflected): "
              + ", ".join(value.str(8) for value in min_bounds))


def check_jensen(ordinates):
    length = arb(2).log()
    caps = (fmpq(42, 10), fmpq(63, 10), fmpq(85, 10), fmpq(95, 10))
    nodes = []
    product_cap = arb(1)
    for g, cap in zip(ordinates, caps, strict=True):
        node = acb(fmpq(1, 2), g)
        require(abs(node) < cap, "Jensen node radius")
        nodes.extend((node, node.conjugate()))
        product_cap *= cap
    for i, node in enumerate(nodes):
        require(all(abs(node - other) > fmpq(9, 10) for other in nodes[:i]), "overlap")
    lower = 2 * (arb(36)**4 / product_cap).log()
    upper = (1 + 36 * length).log() + 36 * length / arb.pi()
    require(lower > fmpq(133, 10) and upper < fmpq(113, 10), "Jensen gap")
    print(f"  Jensen bounds: lower {lower.str(12)}, upper {upper.str(12)}")


def check_uniform_residue(ordinates):
    length = arb(2).log()
    base = arb(0)
    denominator = arb(0)
    coefficients = tuple(zip(ordinates[:2], COS_COEFFICIENTS, SIN_COEFFICIENTS, strict=True))
    for g, a, b in coefficients:
        node = acb(fmpq(1, 2), g)
        base += (arb(a) / 2 - b * g) / (arb(1) / 4 + g*g)
        denominator += 2 * abs(node * (1 + node)) * arb(a*a + b*b).sqrt()

    cell_bounds = []
    for i in range(CELLS):
        unit_cell = arb(fmpq(2 * i + 1, 2 * CELLS), fmpq(1, 2 * CELLS))
        cell = length * unit_cell
        trig_sum = arb(0)
        for g, a, b in coefficients:
            phase = acb(0, g * cell).exp()
            trig_sum += a * phase.real + b * phase.imag
        lower = trig_sum.lower()
        require(lower > fmpq(1, 100), "trigonometric positivity on an entire cell")
        cell_bounds.append(lower)
    margin = base / denominator
    require(base > fmpq(47638, 100000) and denominator < fmpq(77202, 100), "dual constants")
    require(margin > fmpq(617, 1000000), "claimed uniform residue margin")
    print(f"  all-cell trigonometric lower bound {min(cell_bounds).str(10)}")
    print(f"  dual lower bound {base.str(14)}, denominator {denominator.str(14)}, "
          f"uniform residue ratio > {margin.lower().str(14)}")


def main():
    require(flint.__version__ == "0.8.0", "expected python-flint 0.8.0")
    print(f"python-flint {flint.__version__}, Python {sys.version.split()[0]}")
    for precision in (128, 192):
        ctx.prec = precision
        ctx.cap = 2
        print(f"{precision}-bit ball arithmetic")
        ordinates = check_roots()
        check_moving_segments(ordinates)
        check_jensen(ordinates)
        check_uniform_residue(ordinates)


if __name__ == "__main__":
    main()
