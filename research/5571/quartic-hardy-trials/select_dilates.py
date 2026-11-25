"""Choose an explicit Gaussian rational trial on a dyadic dilation mesh."""
import argparse
import json
from pathlib import Path
import numpy as np


def select(q, reach, height, cutoff):
    positions = np.arange(q, q*reach + 1)
    sums = np.array([0, 1, 1+1j, 1, 0])
    moments = np.array([0, 1, 1+2j, 1-1j, -3-1j])
    gram = np.zeros((len(positions), len(positions)), complex)
    rhs = np.zeros(len(positions), complex)
    for start in range(q, q*height+1, 1024):
        mesh = np.arange(start, min(start+1024, q*height+1))
        blocks, residues = np.divmod(mesh[:, None] // positions, 5)
        values = (positions/q) * (blocks*(-3-1j + 5*sums[residues]) + moments[residues])
        t = mesh.astype(float)
        weights = q**3*(3*t*t+3*t+1)/(t*(t+1))**3
        adjoint = values.conj().T * weights
        gram += adjoint @ values
        rhs += adjoint.sum(axis=1)
    best = None
    scale = 100000
    for penalty in [0, 1e-6, 1e-5, 1e-4, 5e-4, 1e-3, 5e-3, 1e-2, 2e-2]:
        solution = np.linalg.solve(gram + penalty*np.eye(len(positions)), rhs)
        rounded = (np.rint(solution.real*scale) + 1j*np.rint(solution.imag*scale))/scale
        estimate = (1 - 2*np.vdot(rounded,rhs).real + np.vdot(rounded,gram@rounded).real +
                    3*(1/cutoff + 1.5*sum(abs(rounded.real)+abs(rounded.imag)))**2/cutoff)
        if best is None or estimate < best[0]:
            best = (estimate, rounded)
    bound, result = best
    return {"dilation_denominator": q, "coefficient_denominator": scale,
            "terms": [[int(d), round(z.real*scale), round(z.imag*scale)]
                      for d, z in zip(positions, result) if z != 0]}, bound


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mesh", type=int, required=True)
    parser.add_argument("--reach", type=int, required=True)
    parser.add_argument("--height", type=int, default=8000)
    parser.add_argument("--cutoff", type=int, default=1000000)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    trial, estimate = select(args.mesh, args.reach, args.height, args.cutoff)
    args.out.write_text(json.dumps(trial, indent=2)+"\n", encoding="utf8")
    print(len(trial["terms"]), estimate, flush=True)
