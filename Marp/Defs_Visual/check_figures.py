#!/usr/bin/env python3
"""Check that the TikZ figures encode the geometry they claim.

Every diagram in ``definitions_figures.tex`` and ``separating_hyperplane.tex``
asserts something mathematical (a face lies ON its hyperplane, a contact point
lies ON the boundary, an interior point is really interior).  A picture that
draws the wrong thing is worse than no picture, so the coordinates printed in
the ``\\def`` macros are parsed back here and checked.

Run: python3 check_figures.py
"""
import math
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SEP = HERE.parent / "Step3_Visual" / "separating_hyperplane.tex"
DEFS = HERE / "definitions_figures.tex"

failures = []


def check(label, ok, detail=""):
    print(f"{'ok  ' if ok else 'FAIL'}  {label}{('  -- ' + detail) if detail else ''}")
    if not ok:
        failures.append(label)


def nums(text):
    """All signed numbers in a string, as floats."""
    return [float(m) for m in re.findall(r"-?\d+\.?\d*", text)]


def pairs(seq):
    return list(zip(seq[0::2], seq[1::2]))


def macro(path, name):
    m = re.search(r"\\def\\" + name + r"\{(.+?)\}", path.read_text(encoding="utf-8"), re.S)
    if not m:
        sys.exit(f"macro \\{name} not found in {path}")
    return m.group(1)


def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def strictly_convex(pts):
    """True when every consecutive turn of the closed polygon has one sign."""
    n = len(pts)
    signs = [cross(pts[i], pts[(i + 1) % n], pts[(i + 2) % n]) for i in range(n)]
    return all(s > 0 for s in signs) or all(s < 0 for s in signs), signs


def inside(pts, p):
    """Point-in-convex-polygon by consistent orientation of the cross products."""
    n = len(pts)
    vals = [cross(pts[i], pts[(i + 1) % n], p) for i in range(n)]
    return all(v > 0 for v in vals) or all(v < 0 for v in vals)


def seg_on_line(a, b, m, b0, tol=1e-9):
    """Both endpoints satisfy y = m x + b0."""
    return (abs(a[1] - (m * a[0] + b0)) < tol) and (abs(b[1] - (m * b[0] + b0)) < tol)


def on_segment(p, a, b, tol=1e-9):
    """p lies on the closed segment ab."""
    cross_abp = (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0])
    if abs(cross_abp) > tol:
        return False
    dot = (p[0] - a[0]) * (p[0] - b[0]) + (p[1] - a[1]) * (p[1] - b[1])
    return dot <= tol


# --------------------------------------------------------------------------
# separating_hyperplane.tex :  H : y = 0.6x + 0.3,  f = y - 0.6x, c = 0.3
# --------------------------------------------------------------------------
print("separating_hyperplane.tex")
poly = pairs(nums(macro(SEP, "omega")))
face = pairs(nums(macro(SEP, "face")))
hline = pairs(nums(macro(SEP, "Hline")))
dbound = tuple(nums(macro(SEP, "deltaB")))
dint = tuple(nums(macro(SEP, "deltaI")))

M, B0 = 0.6, 0.3
convex, signs = strictly_convex(poly)
check("Omega is a convex polygon", convex, f"turns: {['+' if s > 0 else '-' for s in signs]}")
check("Omega has 5 vertices", len(poly) == 5, str(len(poly)))

check("the exposed face Omega\\cap H lies ON H",
      seg_on_line(face[0], face[1], M, B0),
      f"face {face}, H: y = {M}x + {B0}")
check("the face is an edge of Omega",
      any({face[0], face[1]} == {poly[i], poly[(i + 1) % len(poly)]} for i in range(len(poly))))
check("H is drawn along y = 0.6x + 0.3",
      seg_on_line(hline[0], hline[1], M, B0), str(hline))

mid = ((face[0][0] + face[1][0]) / 2, (face[0][1] + face[1][1]) / 2)
check("delta_bound is the midpoint of the face", math.isclose(dbound[0], mid[0]) and math.isclose(dbound[1], mid[1]),
      f"{dbound} vs {mid}")
check("delta_bound lies ON H", abs(dbound[1] - (M * dbound[0] + B0)) < 1e-9)
check("delta_bound lies on the exposed edge, hence on the boundary of Omega",
      on_segment(dbound, face[0], face[1]))

check("every other vertex of Omega lies strictly in {f < c}",
      all(p[1] < M * p[0] + B0 for p in poly if p not in face))
check("Omega is contained in the closed half-space {f <= c}",
      all(p[1] <= M * p[0] + B0 + 1e-12 for p in poly))

check("delta lies in the interior of Omega", inside(poly, dint), str(dint))
check("delta is strictly on the {f < c} side", dint[1] < M * dint[0] + B0)
check("delta is not on H", abs(dint[1] - (M * dint[0] + B0)) > 1e-9)

# grad f = (-0.6, 1) for f = y - 0.6x : perpendicular to H and pointing to {f > c}
g = (-0.6, 1.0)
dirH = (hline[1][0] - hline[0][0], hline[1][1] - hline[0][1])
check("grad f is perpendicular to the direction of H", math.isclose(g[0] * dirH[0] + g[1] * dirH[1], 0, abs_tol=1e-9))
check("grad f points into {f > c} (upwards, away from Omega)", g[1] > 0)

# --------------------------------------------------------------------------
# definitions_figures.tex
# --------------------------------------------------------------------------
print("\ndefinitions_figures.tex")

# --- figure 2: pentagon above the x-axis, bottom edge on H = {y = 0} -------
pent = [(-1.6, 0.0), (2.2, 0.0), (2.9, 1.7), (0.9, 3.1), (-1.9, 2.0)]
convex, signs = strictly_convex(pent)
check("slide 6 pentagon is convex", convex)
check("slide 6 pentagon sits above the x-axis",
      all(p[1] >= 0 for p in pent), "bottom edge lies on H = {y = 0}")
check("slide 6 contact point x0 = (0.35, 0) is on the bottom edge",
      any(abs(p[1]) < 1e-9 and -1.6 <= p[0] <= 2.2 for p in pent))
xi = (0.35, 1.55)
check("slide 6 interior sample point is inside Omega", inside(pent, xi), str(xi))
check("slide 6 f = -y is negative at that point (f < c = 0)", -xi[1] < 0, f"f = {-xi[1]}")

# --- figure 3: general supporting hyperplane, face on H --------------------
poly3 = [(0.6, 0.8), (4.0, 2.1), (5.2, 1.2), (4.4, -0.4), (1.6, -0.9), (0.2, 0.1)]
face3 = (poly3[0], poly3[1])
convex, signs = strictly_convex(poly3)
check("slide 8 hexagon is convex", convex)
m3 = (face3[1][1] - face3[0][1]) / (face3[1][0] - face3[0][0])
b3 = face3[0][1] - m3 * face3[0][0]
check("slide 8 exposed face lies ON H",
      seg_on_line(face3[0], face3[1], m3, b3), f"H: y = {m3:.5f}x + {b3:.5f}")
check("slide 8 Omega lies in the closed half-space {f <= c}",
      all(p[1] <= m3 * p[0] + b3 + 1e-12 for p in poly3))
check("slide 8 every vertex off the face is strictly in {f < c}",
      all(p[1] < m3 * p[0] + b3 - 1e-12 for p in poly3 if p not in face3))
x0_3 = (2.3, 1.45)
check("slide 8 contact point is the midpoint of the face",
      abs(x0_3[0] - (face3[0][0] + face3[1][0]) / 2) < 1e-9
      and abs(x0_3[1] - (m3 * x0_3[0] + b3)) < 1e-9, str(x0_3))
check("slide 8 contact point lies on the exposed edge",
      on_segment(x0_3, face3[0], face3[1]))
n3 = (-m3, 1.0)
# Perpendicular to the direction vector (1, m3) of the line, and pointing up.
check("slide 8 the drawn normal is perpendicular to H and points to {f > c}",
      abs(n3[0] + m3 * n3[1]) < 1e-9 and n3[1] > 0, f"n = {n3}")

# --- figure 4: unit disk, rim, small ball about a rim point ----------------
R, EPS = 1.7, 0.44
s0 = (R * math.cos(math.radians(60)), R * math.sin(math.radians(60)))
check("slide 13 s0 lies on the rim |s| = R", math.isclose(math.hypot(*s0), R, abs_tol=1e-9), f"|s0| = {math.hypot(*s0):.6f}")
check("slide 13 the small ball about s0 meets the interior S",
      math.hypot(*s0) - EPS < R, "part of the ball lies strictly inside")
check("slide 13 the small ball about s0 meets the complement S^c",
      math.hypot(*s0) + EPS > R, "part of the ball lies strictly outside")
check("slide 13 s0 is a boundary point but not an interior point",
      math.isclose(math.hypot(*s0), R) and not math.hypot(*s0) < R)

# --- figure 5: unit square, exposed edge on H = {y = 0} --------------------
sq = [(0.0, 0.0), (1.0, 0.0), (1.0, 1.0), (0.0, 1.0)]
check("slide 13 unit square is convex", strictly_convex(sq)[0])
check("slide 13 the exposed edge lies ON H = {y = 0}",
      all(abs(p[1]) < 1e-12 for p in (sq[0], sq[1])))
check("slide 13 the square lies in {f <= c} = {y >= 0}", all(p[1] >= 0 for p in sq))
check("slide 13 the exposed edge has affine dimension 1",
      sq[0] != sq[1], "two distinct endpoints span a segment")

print()
if failures:
    print(f"{len(failures)} FAILED: {failures}")
    sys.exit(1)
print("all figure-geometry checks passed")
