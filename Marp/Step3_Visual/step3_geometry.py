#!/usr/bin/env python3
"""Shared 3D geometry for the "escape to the boundary" figures.

Every consumer of the Step-3 picture (the interactive viser viewer and the
Manim animation) imports its coordinates from here, so the numbers describing
the proof exist in exactly one place.

The 2D coordinates are the ones used by ``escape_to_boundary_figures.tex``;
they are lifted into 3D by putting the affine slice ``aff(Omega)`` in the
horizontal plane ``z = 0``.

Mathematical content (see ``PreliminaryLemmas.lean``):

* ``OMEGA``       -- the polytope Omega, a convex hexagon in ``aff(Omega)``
* ``SLICE``       -- the affine slice ``aff(Omega) ∩ U``, a blue "slab" of
                     half-width 1 around the line ``L``
* ``DELTA``       -- a point of ``Omega ∩ U`` (the polynomial whose root we chase)
* ``SHARED_DIR``  -- a nonzero ``v ∈ U ⊓ aff(Omega).dir``, the shared direction
* ``DELTA_BOUND`` -- the resulting point of ``U ∩ ∂Omega``
* ``Q``           -- a point beyond Omega, reached by the ray from Delta
"""
import math

import numpy as np

# --------------------------------------------------------------------- 2D data
# Convex hexagon, listed counter-clockwise; lifted to z = 0.
OMEGA_2D = [
    (-2.5, -0.8),
    (-1.4, -1.8),
    (1.4, -1.8),
    (2.5, -0.8),
    (2.5, 0.8),
    (1.4, 1.8),
    (-1.4, 1.8),
    (-2.5, 0.8),
]

DELTA_2D = (0.0, 0.0)
DELTA_BOUND_2D = (2.5, 0.0)
Q_2D = (4.2, 0.0)

# The affine slice aff(Omega) ∩ U is a slab of half-width SLAB_HALF_WIDTH
# around the line L = Delta + R*v.
SLAB_HALF_WIDTH = 1.0
SLAB_EXTENT = 4.7

# aff(Omega).dir is drawn as a horizontal square of this half-size.
AFF_PLANE_HALF = 4.7
AFF_PLANE_HALF_Y = 3.2

# U is the plane spanned by the x-axis and U_DIRECTION; drawn as a patch.
U_PLANE_HALF_X = 4.7
U_PLANE_HALF_V = 2.5
U_TILT = math.radians(55.0)
U_DIRECTION_2D = (0.0, math.cos(U_TILT), math.sin(U_TILT))

# Boundedness witness: Omega ⊂ closure(B(Delta, BALL_RADIUS)).
BALL_RADIUS = 3.2


# ------------------------------------------------------------------- 3D helpers
def v3(x, y, z=0.0):
    """Build a 3D numpy point."""
    return np.array([float(x), float(y), float(z)], dtype=float)


OMEGA = [v3(x, y) for x, y in OMEGA_2D]
DELTA = v3(*DELTA_2D)
DELTA_BOUND = v3(*DELTA_BOUND_2D)
Q = v3(*Q_2D)
U_DIRECTION = v3(*U_DIRECTION_2D)

# The shared direction v: the x-axis, which lies in both U and aff(Omega).dir.
SHARED_DIR = v3(1.0, 0.0)

# The line L = Delta + R*v.
LINE_EXTENT = 4.3


def polygon_edges(points, close=True):
    """Return an (n, 2, 3) array of consecutive edge segments of a polygon."""
    pts = list(points) + ([points[0]] if close else [])
    return np.array([[pts[i], pts[i + 1]] for i in range(len(pts) - 1)])


def triangulate(points):
    """Fan-triangulate a convex polygon given in counter-clockwise order."""
    return np.array([[0, i, i + 1] for i in range(1, len(points) - 1)], dtype=np.int32)


def slab_corners(half_width=SLAB_HALF_WIDTH, extent=SLAB_EXTENT):
    """Corners of the affine slice (the blue slab) around the line L."""
    return [
        v3(-extent, -half_width),
        v3(extent, -half_width),
        v3(extent, half_width),
        v3(-extent, half_width),
    ]


def aff_plane_corners(half_x=AFF_PLANE_HALF, half_y=AFF_PLANE_HALF_Y):
    """Corners of the horizontal plane aff(Omega).dir."""
    return [v3(-half_x, -half_y), v3(half_x, -half_y), v3(half_x, half_y), v3(-half_x, half_y)]


def u_plane_corners(half_x=U_PLANE_HALF_X, half_v=U_PLANE_HALF_V):
    """Corners of the tilted plane U = span{x-axis, U_DIRECTION}."""
    u = U_DIRECTION
    return [
        v3(0, 0, 0) + (-half_x) * v3(1, 0, 0) + (-half_v) * u,
        v3(0, 0, 0) + (half_x) * v3(1, 0, 0) + (-half_v) * u,
        v3(0, 0, 0) + (half_x) * v3(1, 0, 0) + (half_v) * u,
        v3(0, 0, 0) + (-half_x) * v3(1, 0, 0) + (half_v) * u,
    ]


def sphere_wireframe(center, radius, n_meridians=12, n_rings=6, samples=64):
    """Segments of a latitude/longitude sphere wireframe, as an (n, 2, 3) array."""
    center = np.asarray(center, dtype=float)
    segments = []
    for k in range(1, n_rings):
        phi = math.pi * k / n_rings
        ring = [
            center
            + radius
            * v3(
                math.sin(phi) * math.cos(2 * math.pi * j / samples),
                math.sin(phi) * math.sin(2 * math.pi * j / samples),
                math.cos(phi),
            )
            for j in range(samples + 1)
        ]
        segments.append(np.array([[ring[i], ring[i + 1]] for i in range(samples)]))
    for k in range(n_meridians):
        theta = 2 * math.pi * k / n_meridians
        arc = []
        for j in range(samples + 1):
            phi = math.pi * j / samples
            arc.append(
                center
                + radius
                * v3(
                    math.sin(phi) * math.cos(theta),
                    math.sin(phi) * math.sin(theta),
                    math.cos(phi),
                )
            )
        segments.append(np.array([[arc[i], arc[i + 1]] for i in range(samples)]))
    return np.concatenate(segments, axis=0)
