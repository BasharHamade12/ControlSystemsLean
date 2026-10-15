#!/usr/bin/env python3
"""Root loci of the 12 exposed edges of the Ex. 6.2 box (Ch. 6).

Writes ex62_edge00.dat .. ex62_edge11.dat (columns: re im, one root per
row) for ex62_loci.tex. Family: z^3 + d2 z^2 + d1 z + d0 with
d2 in [0.042, 0.158], d1 in [-0.058, 0.058], d0 in [-0.06, 0.056].
"""
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
LO = np.array([1.0, 0.042, -0.058, -0.06])  # [d3, d2, d1, d0]
HI = np.array([1.0, 0.158, 0.058, 0.056])
N = 25


def main():
    idx = 0
    for k in (1, 2, 3):  # the varying coefficient
        others = [i for i in (1, 2, 3) if i != k]
        for b in range(4):  # endpoint combos of the fixed coordinates
            rows = []
            for lam in np.linspace(0.0, 1.0, N):
                c = [1.0, 0.0, 0.0, 0.0]
                c[k] = (1.0 - lam) * LO[k] + lam * HI[k]
                c[others[0]] = (LO if (b // 2) % 2 == 0 else HI)[others[0]]
                c[others[1]] = (LO if b % 2 == 0 else HI)[others[1]]
                for r in np.roots(c):
                    rows.append((r.real, r.imag))
            arr = np.array(rows)
            print(f"edge{idx:02d}: max|root| = {np.abs(arr).max():.4f}")
            np.savetxt(HERE / f"ex62_edge{idx}.dat", arr, fmt="%.6f")
            idx += 1
    assert idx == 12


if __name__ == "__main__":
    main()
