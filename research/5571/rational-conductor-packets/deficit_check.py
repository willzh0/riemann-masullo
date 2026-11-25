"""Numerical finite checks of actual rational complete and prime-only rows.

Requires python-flint 0.9.0. The large-sieve and limiting results are proved
in BASE-TWISTS.md. This checks their sample normalization and exact diagonal
moment identity on genuine Dirichlet characters at two fourth-power cutoffs.
"""
from math import isqrt
from pathlib import Path
import json
from flint import acb, arb, ctx, dirichlet_char, fmpz

ctx.prec = 160


def prime_base(n):
    for p in range(2, isqrt(n)+1):
        if n % p == 0:
            while n % p == 0:
                n //= p
            return p if n == 1 else None
    return n


def next_prime(n):
    while not fmpz(n).is_prime():
        n += 1
    return n


def sign(q, n):
    while n % 2 == 0:
        n //= 2
    return int(fmpz(q).jacobi(n)) if n > 1 else 1


def exercise(j, modulus, fourth):
    x, auxiliary_cutoff = j**4, j**12
    assert x < modulus and fmpz(modulus).is_prime()
    u = next_prime(auxiliary_cutoff+1)
    v = next_prime(u+1)
    assert v <= 2*auxiliary_cutoff
    cells = [(a,b) for a in (-1,1) for b in (-1,1)]
    rows = {c:{} for c in cells}
    plain = {}
    for n in range(2,x):
        p = prime_base(n)
        if p is None:
            continue
        b = (x-n)*arb(p).log()
        rows[sign(u,n),sign(v,n)][n] = 4*b
        if n == p:
            plain[n] = b
    moments = {c:arb(0) for c in cells}
    raw_fourth, mean_deficit, mean_opt = arb(0), arb(0), arb(0)
    for index in range(1,modulus):
        chi = dirichlet_char(modulus,index)
        values = {}
        for data in rows.values():
            values.update((n,chi(n)) for n in data)
        prime = sum((b*values[n] for n,b in plain.items()),acb(0))
        raw_fourth += abs(prime)**4
        selected = []
        for c, data in rows.items():
            value = sum((b*values[n] for n,b in data.items()),acb(0))
            moments[c] += abs(value)**2
            if c != (1,1):
                selected.append((-value.real).max(0))
        if not chi.is_principal():
            mean_deficit += (-prime.real).max(0)
            mean_opt += selected[0].min(selected[1]).min(selected[2])
    for c, data in rows.items():
        expected = sum((b*b for b in data.values()),arb(0))
        assert (moments[c]/(modulus-1)).overlaps(expected)
    if fourth:
        assert x*x < modulus
        grouped = {}
        for p,b in plain.items():
            for s,d in plain.items():
                grouped[p*s]=grouped.get(p*s,arb(0))+b*d
        independent=sum((c*c for c in grouped.values()),arb(0))
        assert (raw_fourth/(modulus-1)).overlaps(independent)
    return dict(j=j,x=x,modulus=modulus,auxiliary=[u,v],primitive_modulus_rows=modulus-2,
                true_complete_cell_sizes={str(c):len(d) for c,d in rows.items()},
                four_complete_second_moments_checked=True,prime_fourth_moment_checked=fourth,
                mean_single_prime_sample_deficit=str(mean_deficit/(modulus-2)),
                mean_optimized_complete_sample_deficit=str(mean_opt/(modulus-2)))


if __name__=="__main__":
    rows=[exercise(2,263,True),exercise(3,257,False)]
    Path(__file__).with_suffix(".json").write_text(json.dumps(rows,indent=2)+"\n",encoding="utf-8")
    for row in rows:
        print(row["x"],row["auxiliary"],row["mean_optimized_complete_sample_deficit"])
