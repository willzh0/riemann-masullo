"""Optionally select a polynomial using floating-point midpoints. Certificates use the exact trial."""
import argparse
import json
from pathlib import Path

import numpy as np


def search(measurement):
    row = np.array([complex(x, y) for x, y in measurement["midpoints_for_trial_selection"]])
    degree = len(row) - 1
    denominator = 10000
    best = None
    for size in range(1, min(degree//3, 48)+2):
        matrix = np.zeros((degree+1, size), dtype=complex)
        for j in range(size):
            matrix[j:, j] = row[:degree+1-j]
        target = np.zeros(degree+1, dtype=complex)
        target[0] = 1
        j = np.arange(size)
        penalty = 6/((degree-j)*(degree-j+1))
        for multiplier in (0, 0.01, 0.05, 0.2, 0.5, 1, 2, 5, 15, 40, 100):
            matrix_augmented = np.vstack((matrix, multiplier*np.diag(penalty)))
            target_augmented = np.concatenate((target, np.zeros(size)))
            solution = np.linalg.lstsq(matrix_augmented, target_augmented, rcond=None)[0]
            numerators = np.rint(solution.real*denominator)+1j*np.rint(solution.imag*denominator)
            values = numerators/denominator
            visible = np.linalg.norm(target-matrix@values)
            tail = np.abs(values)@penalty
            objective = visible**2+tail**2
            if best is None or objective < best[0]:
                best = objective, numerators, visible, tail
    objective, coefficients, visible, tail = best
    assert objective < 1
    return {"degree": degree, "trial_degree": len(coefficients)-1, "denominator": denominator,
            "numerators": [[round(z.real),round(z.imag)] for z in coefficients],
            "selection_visible": float(visible), "selection_tail": float(tail),
            "selection_green": float(-np.log1p(-objective)/2)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--row", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.row.read_text(encoding="utf8"))
    args.out.write_text(json.dumps(search(data),indent=2)+"\n",encoding="utf8")
