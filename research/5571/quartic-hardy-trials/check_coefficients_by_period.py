"""Compare the first coefficients with ordinary Dirichlet derivatives and a periodic tail."""
import argparse
import json
from math import factorial
from pathlib import Path
from flint import acb, arb, fmpq
from quartic_coeffs import coefficient_row


def choose_integer(n, j):
    result = 1
    for k in range(j):
        result = result*(n-k)//(k+1)
    return result


def verify(cutoff, order, bits):
    assert cutoff % 5 == 0 and order <= 2*arb(cutoff+1).log()
    row, row_error, _ = coefficient_row(max(order, 16), bits)
    values = [acb(0) for _ in range(order+1)]
    chi = [acb(0), acb(1), acb(0,1), acb(0,-1), acb(-1)]
    for n in range(1,cutoff+1):
        if n % 5 == 0:
            continue
        term = chi[n%5]/(n*n)
        logn = -arb(n).log()
        for j in range(order+1):
            values[j] += term
            term *= logn
    first = arb(cutoff+1)
    tails = [arb(2).sqrt()*first.log()**j/first**2 for j in range(order+1)]
    comparisons = []
    for j in range(order+1):
        total, bound = acb(0), arb(0)
        for ell in range(j+1):
            q = fmpq(3**ell * (-1)**(j-ell) * choose_integer(5-ell,j-ell),
                     243 * factorial(ell))
            total += q * values[ell]
            bound += abs(q) * tails[ell]
        diff = abs(row[j] - total)
        assert diff < bound+row_error
        comparisons.append({"index": j, "complex_difference_norm": diff.str(18),
                            "independent_remainder_norm_bound": bound.str(18)})
    return {"integer_cutoff": cutoff, "compared_through_degree": order,
            "other_table_degree": max(order,16), "other_table_error": row_error.str(18),
            "precision_request": bits, "comparisons": comparisons}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cutoff", type=int, default=100000)
    parser.add_argument("--order", type=int, default=8)
    parser.add_argument("--bits", type=int, default=144)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    receipt = verify(args.cutoff,args.order,args.bits)
    args.out.write_text(json.dumps(receipt,indent=2)+"\n",encoding="utf8")
    print("All independent Dirichlet derivative and Mellin kernel coefficient enclosures agree.")
