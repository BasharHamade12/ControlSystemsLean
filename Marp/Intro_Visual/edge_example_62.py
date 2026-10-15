import numpy as np, itertools
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D


# ---- Box Omega: (delta2, delta1, delta0); delta3 = 1 is fixed -------------
lo = np.array([0.042, -0.058, -0.06])
hi = np.array([0.158,  0.058,  0.056])


# 8 vertices of the box
verts = [np.array(v) for v in itertools.product(*zip(lo, hi))]


# 12 edges: pairs of vertices that differ in exactly one coordinate
edges = []
for i, a in enumerate(verts):
    for j, b in enumerate(verts):
        if i < j and np.sum(a != b) == 1:
            edges.append((a, b, int(np.argmax(a != b))))  # k = varying coefficient
assert len(edges) == 12


names = [r"$\delta_2$", r"$\delta_1$", r"$\delta_0$"]
cols  = ["#1f77b4", "#d62728", "#2ca02c"]   # colour = varying coefficient


# ---- Root loci along each edge: delta(z; lambda) = (1-l)*a + l*b ----------
lam = np.linspace(0, 1, 400)
loci, maxmod = [], 0.0
for a, b, k in edges:
    pts = []
    for l in lam:
        d = (1 - l) * a + l * b
        pts.append(np.roots([1, d[0], d[1], d[2]]))   # z^3 + d2 z^2 + d1 z + d0
    pts = np.array(pts)                                # shape (400, 3)
    loci.append(pts)
    maxmod = max(maxmod, np.abs(pts).max())
print("max |root| over all edges:", maxmod)


# Sanity check: random members of the box
rng = np.random.default_rng(0)
m = max(np.abs(np.roots([1, *(lo + rng.random(3) * (hi - lo))])).max()
        for _ in range(20000))
print("max |root| over random box samples:", m)


# ---- Figure ---------------------------------------------------------------
fig = plt.figure(figsize=(12, 5.4), dpi=200)


# Left: 3D box
ax = fig.add_subplot(1, 2, 1, projection="3d")
for a, b, k in edges:
    ax.plot(*zip(a, b), color=cols[k], lw=2.4)
V = np.array(verts)
ax.scatter(*V.T, color="k", s=22, zorder=5)
ax.set_xlabel(names[0], labelpad=6)
ax.set_ylabel(names[1], labelpad=6)
ax.set_zlabel(names[2], labelpad=2)
ax.view_init(22, -58)
ax.set_box_aspect((1, 1, 1))
ax.set_title(r"Box $\Omega$: 8 vertices, 12 edges" + "\n(colour = coefficient that varies)",
             fontsize=11)
ax.legend(handles=[Line2D([0], [0], color=c, lw=2.5, label=f"vary {n}  (4 edges)")
                   for c, n in zip(cols, names)],
          loc="upper left", fontsize=8, frameon=False)


# Right: root loci + unit circle
ax2 = fig.add_subplot(1, 2, 2)
th = np.linspace(0, 2 * np.pi, 400)
ax2.fill(np.cos(th), np.sin(th), color="#edf6f0", zorder=0)   # stability region
ax2.plot(np.cos(th), np.sin(th), "k--", lw=1.3, zorder=1)     # unit circle
for (a, b, k), pts in zip(edges, loci):
    for r in range(3):                                         # 3 roots per polynomial
        ax2.plot(pts[:, r].real, pts[:, r].imag, color=cols[k], lw=1.6, alpha=.85, zorder=3)
        ax2.scatter(pts[[0, -1], r].real, pts[[0, -1], r].imag,
                    color="k", s=10, zorder=4)                 # endpoints = vertices
ax2.axhline(0, color="#aaa", lw=.6)
ax2.axvline(0, color="#aaa", lw=.6)
ax2.set_aspect("equal")
ax2.set_xlim(-1.15, 1.15)
ax2.set_ylim(-1.15, 1.15)
ax2.set_xlabel("Re $z$")
ax2.set_ylabel("Im $z$")
ax2.text(0.72, 0.78, r"$|z|=1$", fontsize=10)
ax2.set_title(f"Root loci of the 12 edges  $R(E)$\n"
              f"all inside the unit disc (max $|z|$ = {maxmod:.2f})", fontsize=11)


plt.tight_layout()
plt.savefig("edge_example_62.png", bbox_inches="tight", facecolor="white")
