"""Check both recorded all-height bounds, including the sharper 144-bit certificate."""
from __future__ import annotations

import argparse
import csv
import gzip
import json
import tempfile
from fractions import Fraction
from pathlib import Path

from verify import check, digest

HERE = Path(__file__).resolve().parent
RUNS = {
    "dirichlet": (104, 20, {"elementary_G_upper": "0.00311657", "jensen_G_upper": "0.00195337"}),
    "hurwitz": (144, 22, {"elementary_G_upper": "0.00311647", "jensen_G_upper": "0.00195327"}),
}


def unpack_ledger(directory, temporary):
    """Hand the original bytewise ledger to the unmodified integer/rational verifier."""
    if (directory / "cells.csv").is_file():
        return directory
    destination = temporary / directory.name
    destination.mkdir()
    raw = gzip.decompress((directory / "cells.csv.gz").read_bytes())
    (destination / "cells.csv").write_bytes(raw)
    (destination / "receipt.json").write_bytes((directory / "receipt.json").read_bytes())
    return destination


def negative_controls(path, destination):
    """An omitted quarter interval and a sign error must both be detected after rehashing."""
    receipt = json.loads((path / "receipt.json").read_text(encoding="utf8"))
    with (path / "cells.csv").open(encoding="ascii", newline="") as handle:
        header, *rows = list(csv.reader(handle))
    first = rows[0]
    reversed_interval = first[:3] + [str(-int(first[4])), str(-int(first[3]))]
    variants = {"omitted_height_cell": rows[1:], "switched_sign": [reversed_interval, *rows[1:]]}
    destination.mkdir()
    rejected = []
    for name, variant in variants.items():
        ledger = destination / "cells.csv"
        with ledger.open("w", encoding="ascii", newline="") as handle:
            writer = csv.writer(handle, lineterminator="\n")
            writer.writerow(header)
            writer.writerows(variant)
        changed = dict(receipt, cells_sha256=digest(ledger))
        (destination / "receipt.json").write_text(json.dumps(changed), encoding="utf8")
        try:
            check(destination)
        except AssertionError:
            rejected.append(name)
        else:
            raise ArithmeticError(f"The verifier accepted the damaged ledger {name!r}.")
    return rejected


def check_run(path, engine):
    proof = check(path)
    receipt = json.loads((path / "receipt.json").read_text(encoding="utf8"))
    bits, terms, limits = RUNS[engine]
    assert receipt["engine"] == engine and receipt["precision_bits"] == bits
    assert receipt["taylor_terms"] == terms and receipt["scale"] == 2**60
    assert proof["T"] == 2048 and proof["quarter_cells"] == 16384 and proof["subcells"] == 1573120
    assert (receipt["fine_bits"], receipt["coarse_bits_min"]) == (16, 7)
    assert receipt["reference"]["two_formula_control_centers_j"] == [-8192, -65, -2, -1, 0, 1, 63, 8191]
    for key, threshold in limits.items():
        # proof[key] was already rounded upwards, so this rational comparison suffices.
        assert Fraction(proof[key]) < Fraction(threshold)
    return {"engine": engine, "precision_bits": bits, "Taylor_terms": terms,
            "strict_bounds": limits, "recorded_seconds": receipt["runtime_seconds_before_final_io"],
            **proof}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("dirichlet", nargs="?", type=Path, default=Path("dirichlet-2048"))
    parser.add_argument("hurwitz", nargs="?", type=Path, default=Path("hurwitz-2048"))
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as scratch:
        temporary = Path(scratch)
        direct = unpack_ledger((HERE / args.dirichlet).resolve(), temporary)
        hurwitz = unpack_ledger((HERE / args.hurwitz).resolve(), temporary)
        results = [check_run(direct, "dirichlet"), check_run(hurwitz, "hurwitz")]
        rejected = negative_controls(direct, temporary / "damaged")
    report = {"character": "chi modulo five with chi(2) = +i", "Cauchy_scale": "3/2",
              "Euler_reference": "s=2", "sharper_certificate": "hurwitz",
              "runs": results, "damaged_ledgers_rejected": rejected}
    output = json.dumps(report, indent=2) + "\n"
    if args.out:
        (HERE / args.out).write_bytes(output.encode("utf8"))
    print(output, end="")


if __name__ == "__main__":
    main()
