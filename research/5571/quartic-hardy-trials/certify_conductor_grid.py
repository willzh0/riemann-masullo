"""Outward rational checks for one conductor-uniform Hardy grid accuracy bound."""
from fractions import Fraction as Q
import json


def verify():
    conductor = 400_000
    degree = 70
    clip_height = 125_000
    retained = 2**100
    log_bound = 90
    assert Q(5, 4)**(degree-3) >= 4*conductor
    assert Q(27, 10)**log_bound > 600*conductor*retained
    assert clip_height - (24+degree)*log_bound >= 64*20*log_bound
    # One native scale u>=2^20 Q^4 handles every primitive input in the row.
    u0 = 2**20 * conductor**4
    assert 4*(52*conductor)**4 <= 32*u0
    assert 72*52*16**2 < 4**16
    assert 16000*16**4 < 2**(5*16)
    assert 2**500 > u0 and 500 < 750_000
    central = 9*3200*log_bound**2 * Q(10, 27)**64
    outside = Q(4*(3224+degree)*(log_bound**2+2*log_bound+2), retained)
    loss = central + outside
    eta = Q(1, 10**24)
    norm_error = Q(1, 10**24)
    assert Q(11, 4)**160 * 20 < 2**240
    assert (4*clip_height) % 160 == 0
    assert (4*clip_height//160)*240 == 750_000
    assert 12*10**24 < 2**100 and 100 < 750_000//2
    squared_error = 2*(loss+eta)+2*norm_error+norm_error**2
    assert squared_error < Q(115423, 10**24) < Q(2, 10**19)
    # Growing family for every k>=2, with N=20k, H=8000k^2 and J=2^(20k).
    k = 2
    assert Q(5, 4)**4 > 2 and 20*k-3 >= 4*(k+2)
    assert Q(27, 10)**7 > 600 and 7+21*k <= 25*k
    assert Q(27, 10)**14 > 2**19
    assert 24+20*k <= 32*k and 3224+20*k <= 1632*k
    assert (25*k)**2+50*k+2 <= 651*k*k
    assert 16*9*3200*625*k*k < 2**(18*k)
    assert 16*4*1632*651*k**3 < 2**(19*k)
    # The two polynomial numerators grow by at most (3/2)^3 per unit step.
    assert Q(3, 2)**2 < 2**18 and Q(3, 2)**3 < 2**19
    assert 50*Q(11,4)**160 < 2**240
    assert 32000 % 160 == 0 and 32000//160*240 == 48000
    assert 20+4*k <= 48000*k*k
    assert 12*64 < 2**10 and k+10 <= 24000*k*k
    return {
        "growing_family": {"k_min": 2, "conductor": "2^k", "disk_exponent": "20k",
                           "least_stage": "2^(48000k^2)", "squared_error_upper": "2^(-k)"},
        "maximum_conductor": conductor,
        "fixed_disk_exponent": degree,
        "retained_log_height_blocks": "2^100",
        "clip_height": clip_height,
        "least_certified_grid_index": "2^750000",
        "central_clipping_cost_upper_in_units_1e-24": (central*10**24).__ceil__(),
        "tail_clipping_cost_upper_in_units_1e-24": (outside*10**24).__ceil__(),
        "grid_squared_error_upper_in_units_1e-24": (squared_error*10**24).__ceil__(),
        "rational_upper_for_squared_error": "2/10^19",
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
