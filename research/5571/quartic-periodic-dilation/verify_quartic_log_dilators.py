"""Certify the first two logarithmic responses and one phase shift at a quartic zero.

Run with Python and python-flint 0.8 or newer. The original sign-bracket numerator
comes from the public mod-five certificate, but every inequality here is replayed.
"""
from flint import acb, acb_series, arb, ctx, fmpq


def character_l(s):
    values = (1, acb(0, 1), acb(0, -1), -1)
    hurwitz_sum = sum(
        value * s.zeta(fmpq(residue, 5)) for residue, value in enumerate(values, 1)
    )
    return (-arb(5).log() * s).exp() * hurwitz_sum


def hardy(t):
    root_five = arb(5).sqrt()
    root_number = acb(((5 + root_five) / 10).sqrt(), ((5 - root_five) / 10).sqrt())
    gamma = acb(arb(3) / 4, t / 2).gamma()
    phase = acb(0, (arb(5) / arb.pi()).log() * t / 2).exp()
    return (root_number.sqrt().conjugate() * gamma / abs(gamma)
            * phase * character_l(acb(arb(1) / 2, t))).real


def verify(precision):
    ctx.prec = precision
    ctx.cap = 3
    denominator = 2**24
    lower = -69338619
    t_left = arb(fmpq(lower, denominator))
    t_right = arb(fmpq(lower + 1, denominator))
    ordinate = arb(fmpq(2 * lower + 1, 2 * denominator), fmpq(1, 2 * denominator))
    s = acb(arb(1) / 2, ordinate)
    left_value, right_value = hardy(t_left), hardy(t_right)
    assert left_value < 0 < right_value
    value_at_mirror = abs(character_l(s.conjugate()))
    assert value_at_mirror > fmpq(197, 100)
    jet = character_l(acb_series([s, 1]))
    first, second = jet[1], -2 * jet[2]
    first_denominator = 2 * abs(s * (1 + s))
    determinant = abs((second * first.conjugate()).imag)
    frobenius = (abs(first)**2 + abs(second)**2).sqrt()
    first_margin = abs(first) / first_denominator
    second_margin = abs(second) / first_denominator
    uniform_margin = determinant / (frobenius * first_denominator)
    shifted_margin = abs(character_l(s - acb(0, 1))) / first_denominator
    crossed_margin = value_at_mirror / first_denominator
    assert first_margin > fmpq(3047, 100000)
    assert second_margin > fmpq(399, 10000)
    assert uniform_margin > fmpq(1019, 100000)
    assert shifted_margin > fmpq(3711, 100000)
    assert crossed_margin > fmpq(5389, 100000)
    print(f"{precision} bits; Hardy endpoints {left_value}, {right_value}")
    print(f"reflected modulus {value_at_mirror}; determinant {determinant}")
    print(f"first {first_margin}; second {second_margin}; all real directions {uniform_margin}")
    print(f"unit phase shift {shifted_margin}; conjugate dilator {crossed_margin}")


if __name__ == "__main__":
    for bit_precision in (128, 192):
        verify(bit_precision)
