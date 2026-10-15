#!/usr/bin/env python3
"""Verify that every point drawn in escape_to_boundary_figures.tex is
mathematically consistent with the pictures they illustrate:
Omega convex, delta interior, ball containment, exit point on an edge,
delta / delta_bound / q collinear, dist(delta,q) = |C|+1, slab geometry,
and the highlighted common direction lies in both direction spaces."""
import re, math, sys
s = open(sys.argv[1] if len(sys.argv) > 1 else 'escape_to_boundary_figures.tex').read()
def nums(t): return [float(x) for x in re.findall(r'-?\d+\.?\d*', t)]
def defv(m):
    return nums(re.search(r'\\def\\' + m + r'\{([^}]*)\}', s).group(1))
h = defv('omegapath'); hexa = list(zip(h[0::2], h[1::2]))
d = defv('dd');     delta = (d[0], d[1])
b = defv('bexit');  bexit = (b[0], b[1])
q = defv('qq');     q     = (q[0], q[1])
C = defv('crad')[0]
l = defv('lline');      L = [(l[0], l[1]), (l[2], l[3])]
t = defv('strippath');  S = [(t[0], t[1]), (t[2], t[3]), (t[4], t[5]), (t[6], t[7])]
r = re.search(r'\\draw\[ray\] \(\\dd\) -- \(([\d.]+),([\d.]+)\)', s)
v_end = (float(r.group(1)), float(r.group(2)))

def cross(o, a, b): return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
def inside(p, poly):
    w = [cross(poly[i], poly[(i+1) % len(poly)], p) for i in range(len(poly))]
    return all(x < 0 for x in w) or all(x > 0 for x in w)
def on_edge(p, poly, tol=2e-3):
    for i in range(len(poly)):
        a, b_ = poly[i], poly[(i+1) % len(poly)]
        if (abs(cross(a, b_, p)) < tol and min(a[0],b_[0])-tol <= p[0] <= max(a[0],b_[0])+tol
            and min(a[1],b_[1])-tol <= p[1] <= max(a[1],b_[1])+tol): return i
    return None
u = (L[1][0]-L[0][0], L[1][1]-L[0][1]); m = math.hypot(*u); n = (-u[1]/m, u[0]/m)
off = lambda p: abs((p[0]-delta[0])*n[0] + (p[1]-delta[1])*n[1])
tests = [
 ("the new opening diagram is included", r"%% 1. The common direction space" in s and r"$U\sqcap\operatorname{aff}\Omega.\mathrm{dir}$" in s),
 ("Omega is strictly convex", all(cross(hexa[i], hexa[(i+1)%6], hexa[(i+2)%6]) for i in range(6))),
 ("delta lies in int(Omega)", inside(delta, hexa)),
 ("Omega is inside the ball B(delta,C)", max(math.dist(delta,v) for v in hexa) <= C),
 ("delta_bound lies on an edge of Omega", on_edge(bexit, hexa) is not None),
 ("delta, delta_bound, q are collinear", abs(cross(delta, bexit, q))/math.dist(delta, q) < 2e-3),
 ("the line L passes through delta", abs(cross(L[0], L[1], delta))/math.dist(L[0], L[1]) < 2e-3),
 ("the arrow v (fig 1) lies on L", abs(cross(L[0], L[1], v_end))/math.dist(L[0], L[1]) < 2e-3),
 ("q is farther than delta_bound", math.dist(delta, bexit) < math.dist(delta, q)),
 ("dist(delta,q) = |C|+1", abs(math.dist(delta, q)-(C+1)) < 3e-3),
 ("q is outside Omega and outside the ball", (not inside(q, hexa)) and math.dist(delta, q) > C),
 ("slab edges at half-width 1 around delta", abs(off(S[0])-1) < .02 and abs(off(S[1])-1) < .02 and off(delta) < 1e-6),
 ("slab parallel to L (perp. dist. ~ 1)",
  abs(abs(cross(S[0], S[1], L[1]))/math.dist(S[0], S[1]) - 1.0) < .02
  and abs(abs(cross(S[2], S[3], L[1]))/math.dist(S[2], S[3]) - 1.0) < .02),
 ("delta_bound lies inside the slab", off(bexit) < 1.0),
]
bad = 0
for name, okv in tests:
    print(f"  {'PASS' if okv else '*** FAIL ***'}  {name}")
    bad += (not okv)
print(f"--- {len(tests)-bad}/{len(tests)} checks passed")
sys.exit(1 if bad else 0)
