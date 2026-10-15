#!/usr/bin/env python3
"""Interactive 3D viewer for the "escape to the boundary" proof.

Each region is drawn as a translucent filled surface plus a coloured
outline, so the legend colours actually appear in the figure:

    Omega                  orange     outline of the polytope of polynomials
    aff(Omega)             pale blue  outline of the affine hull of Omega
    U                      teal       outline of {delta : delta(s) = 0}
    aff(Omega) ∩ U         green      the shared slice: exactly this line
    L = delta + R v        purple     the same line, travelled as a path
    ray delta -> q         blue       used to leave the bounded region
    boundary crossing      red        delta_bound ∈ U ∩ ∂Omega

The only labels placed on the figure itself are the points and the lines; the
region names live in the legend rather than cluttering the drawing.

Usage
-----
    cd Marp/Step3_Visual
    ../../.venv-3dview/bin/python escape_to_boundary_viewer.py

Then open the printed URL (http://localhost:8080) in any browser: drag to
orbit, scroll to zoom, and use the step dropdown/buttons. The first seven
steps are an intro region tour — each one highlights a single region (Ω,
aff(Ω), U, the shared slice, L, the ray, ∂Ω) and says what it is — followed
by the six proof steps of Lemma 6.1.

Note on the green region: the set aff(Omega) ∩ U is, in the geometry drawn
here, exactly the line L itself (two planes meeting along the x-axis). It is
highlighted as its green line only — no widened band: what is lit up is the
intersection and nothing else.

Requires ``viser`` (+ ``numpy``, ``trimesh``); see requirements-viewer.txt.
"""
import argparse

import numpy as np

import step3_geometry as geo

try:
    import viser
except ImportError:  # pragma: no cover - friendly message for a missing dep
    raise SystemExit(
        "This viewer needs `viser`.\n"
        "Install the project venv and its viewer deps:\n"
        "    cd /home/bashar/ControlSystems\n"
        "    python3 -m venv --system-site-packages .venv-3dview\n"
        "    .venv-3dview/bin/python -m pip install -r "
        "Marp/Step3_Visual/requirements-viewer.txt\n"
    )

# ------------------------------------------------------------------- palette
# One distinct hue per region; LEGEND lists them in the same order.
C_OMEGA = (232, 138, 36)  # the polytope Ω
C_AFF = (110, 165, 205)  # the affine hull aff(Ω)
C_U = (52, 160, 165)  # the root slice U
C_SLICE = (60, 160, 95)  # aff(Ω) ∩ U, the shared slice
C_LINE = (118, 81, 168)  # L = δ + ℝv
C_RAY = (54, 120, 184)  # the escaping ray
C_RED = (200, 51, 61)  # boundary crossing / δ_bound
C_INK = (39, 49, 59)

LEGEND = [
    ("Ω  polytope of polynomials", C_OMEGA),
    ("aff(Ω)  affine hull of Ω", C_AFF),
    ("U  root slice {δ : δ(s) = 0}", C_U),
    ("aff(Ω) ∩ U  shared slice: the intersection line", C_SLICE),
    ("L = δ + ℝv  travelling along that line", C_LINE),
    ("ray δ → q  escapes Ω", C_RAY),
    ("∂Ω  boundary crossing δ_bound", C_RED),
]

STAGES = [
    "Shared direction: U ∩ aff(Ω).dir",
    "Choose a nonzero direction v in the intersection",
    "The full line L = δ + ℝv stays in the shared slice",
    "Follow the ray to an outside point q",
    "The segment [δ, q] crosses the boundary of Ω",
    "δ_bound ∈ U ∩ ∂Ω",
]

STAGE_EXPLANATIONS = [
    "The plane U and the direction plane aff(Ω).dir meet along a line. Every "
    "point of that line is a direction the proof may travel in without leaving "
    "either constraint.",
    "The intersection has dimension ≥ 1, so it contains a nonzero vector v. "
    "This is the direction Step 2 extracts from the dimension count.",
    "Because δ ∈ U and v ∈ U, the whole line L = δ + ℝv lies in U; because "
    "v ∈ aff(Ω).dir and δ ∈ aff(Ω), it also lies in aff(Ω). So L stays in the "
    "green shared slice.",
    "Ω is bounded, so it sits inside a ball B(δ, C). Walking far enough along v "
    "leaves that ball, giving a point q outside Ω.",
    "The segment [δ, q] starts inside Ω and ends outside it. Being connected, "
    "it must cross the boundary ∂Ω at some point δ_bound.",
    "That crossing point is a convex combination of δ and q, both of which lie "
    "in the slice, so δ_bound ∈ U as well: δ_bound ∈ U ∩ ∂Ω.",
]

# ---------------------------------------------------------- intro region tour
# The first seven steps: each spotlights ONE region (in LEGEND order) and says
# what it is. ``key`` must match the ``region`` tag the node was registered
# with inside Scene; the six proof steps then follow unchanged.
REGION_TOUR = [
    {
        "key": "omega",
        "title": "Ω — the polytope of polynomials",
        "explain": (
            "**Ω (orange) — the polytope of polynomials.** `Polytope.Ω = "
            "convexHull ℝ vertices` in the coefficient space: every convex "
            "combination Σ λᵢ·Pᵢ of the family's polynomials, with λᵢ ≥ 0 and "
            "Σ λᵢ = 1. Compact and convex with nonempty interior — its "
            "compactness is what later gives the finite bound C for the "
            "escape ray."
        ),
    },
    {
        "key": "aff",
        "title": "aff(Ω) — the affine hull of Ω",
        "explain": (
            "**aff(Ω) (pale blue) — the affine hull of Ω.** The smallest "
            "affine subspace containing the polytope: everything reachable "
            "from Ω by affine combinations. Its direction space "
            "`aff(Ω).dir` contains every difference of two points of Ω, so "
            "only moves along that direction space stay inside the hull — "
            "Step 2's dimension count is made against it."
        ),
    },
    {
        "key": "u",
        "title": "U — the root slice {δ : δ(sᵣ) = 0}",
        "explain": (
            "**U (teal) — the root slice.** A linear subspace of coefficient "
            "vectors through 0; in the proof it is `P_sr n s.re` = "
            "{ δ : δ(sᵣ) = 0 }, the polynomials vanishing at the root we "
            "chase (`dim U = n`). Any move inside U keeps that root, which "
            "is why the whole argument is carried out inside U."
        ),
    },
    {
        "key": "slice",
        "title": "aff(Ω) ∩ U — the shared slice",
        "explain": (
            "**aff(Ω) ∩ U (green) — the shared slice.** Points that are in "
            "the affine hull of Ω *and* in the root slice U at once. In the "
            "geometry drawn here that set is exactly one line — the green "
            "line (the two planes meet along the x-axis). It is lit up as a "
            "line and nothing else: what is highlighted is the intersection "
            "exactly, no widened band stands in for it. "
            "Step 2 (`intersection_affine_dim_ge_one`) only proves "
            "dim(meetDir) ≥ 1 — which is all the proof needs (in general the "
            "slice can be higher-dimensional; here dim = 1)."
        ),
    },
    {
        "key": "line",
        "title": "L = δ + ℝv — the line in the slice",
        "explain": (
            "**L = δ + ℝv (purple) — the line in the slice.** The whole line "
            "through the starting polynomial δ in the shared direction v. "
            "Since δ, v ∈ U and v ∈ aff(Ω).dir, every point δ + t·v stays in "
            "U ∩ aff(Ω) (`line_in_intersection`) — and in this depiction it "
            "holds in reverse too: L *is* the intersection, the same green "
            "line the previous step lit up. Step 2 found v; this is the "
            "line the proof will travel along."
        ),
    },
    {
        "key": "ray",
        "title": "ray δ → q — escapes Ω",
        "explain": (
            "**ray δ → q (blue) — escaping Ω.** Ω is compact, so it sits "
            "inside a ball B(δ, C) (drawn as a grey wireframe once the proof "
            "steps begin). "
            "`ray_escapes_of_bounded` walks to q = δ + t_out·v with "
            "t_out = (|C|+1)/‖v‖, outside the ball and therefore outside Ω — "
            "the proof has left the polytope while still in the slice."
        ),
    },
    {
        "key": "boundary",
        "title": "∂Ω — the boundary point δ_bound",
        "explain": (
            "**∂Ω (red) — the boundary crossing δ_bound.** The segment "
            "[δ, q] starts inside Ω and ends outside it; being connected it "
            "must meet `frontier Ω` (`segment_boundary_intersection`). "
            "Because the segment lies on L, the crossing stays in U: "
            "δ_bound ∈ U ∩ ∂Ω — the boundary point Lemma 6.1 is after."
        ),
    },
]

N_TOUR = len(REGION_TOUR)
STEP_TITLES = [entry["title"] for entry in REGION_TOUR] + STAGES
STEP_EXPLANATIONS = [entry["explain"] for entry in REGION_TOUR] + STAGE_EXPLANATIONS


FOV_DEGREES = 50.0
# Camera stand-off chosen so the 6.5-unit geometry radius fits inside
# FOV_DEGREES, viewed from 35 degrees above the flat z = 0 plane.
CAM_POS = (0.0, -12.65, 8.86)
CAM_LOOKAT = (0.0, 0.0, 0.0)


def segments(pts):
    """Normalize to the (N, 2, 3) start/end array that viser expects."""
    return np.asarray(pts, dtype=np.float64).reshape(-1, 2, 3)
def ring(points):
    """Convert a closed 3D polygon into an (n, 2, 3) edge array."""
    return geo.polygon_edges([np.asarray(p, dtype=float) for p in points])


# ------------------------------------------------- scene-node prop utilities
def _capture(handle):
    """Snapshot the styling props we may need to restore or dim later."""
    orig = {}
    for attr in ("opacity", "color", "colors", "thickness"):
        if not hasattr(handle, attr):
            continue
        try:
            val = getattr(handle, attr)
        except Exception:  # pragma: no cover - prop not readable on this handle
            continue
        if val is None:
            continue
        orig[attr] = np.array(val, copy=True) if isinstance(val, np.ndarray) else val
    return orig


def _apply(handle, props):
    for attr, val in props.items():
        setattr(handle, attr, val)


def _dim(props):
    """Recessive styling for a region the current tour step is NOT about."""
    if "opacity" in props:
        # Fills: keep the hue, drop the fill right down.
        return {**props, "opacity": float(props["opacity"]) * 0.25}
    out = dict(props)
    if "colors" in out:
        out["colors"] = (np.asarray(out["colors"], dtype=np.float32) * 0.45).astype(
            np.uint8
        )
    if "color" in out:
        out["color"] = tuple(int(c * 0.45) for c in out["color"])
    if "thickness" in out:
        out["thickness"] = max(1.0, float(out["thickness"]) * 0.55)
    return out


def _focus(props):
    """Brighter, thicker styling for the region being highlighted."""
    out = dict(props)
    if "thickness" in out:
        out["thickness"] = float(out["thickness"]) * 1.6
    if "opacity" in out:
        out["opacity"] = min(1.0, float(out["opacity"]) * 1.4)
    return out


class Scene:
    """Builds the color-coded regions and tracks which ones each stage shows."""

    def __init__(self, server):
        self.server = server
        self.nodes = {}
        self._build_regions()
        self._build_shared_direction()
        self._build_paths()
        self._build_markers()
        self._build_labels()

    def add(self, name, handle, stages, region=None, label=False):
        """Register a handle, the proof stages it shows in, and its region tag.

        ``region`` links the node to one REGION_TOUR entry (None = proof-step
        only, "base" = δ and its label, always shown); ``label`` marks text
        labels, which the tour shows only for the region being highlighted.
        """
        self.nodes[name] = {
            "handle": handle,
            "stages": set(stages),
            "region": region,
            "label": label,
            "orig": _capture(handle),
        }
        return handle

    def _build_regions(self):
        """Draw the regions as translucent filled surfaces plus outlines.

        Each region gets an ``add_mesh_simple`` fill (so its legend colour
        actually appears in the figure) with a matching outline on top.
        Small z-offsets avoid z-fighting between the coplanar
        aff(Ω) / slice / Ω layers that all sit in z = 0.
        """
        s = self.server
        edge = (188, 196, 204)  # neutral grey so region outlines stay recessive

        def fill(name, pts, color, opacity, z=0.0, stages=range(6), region=None):
            verts = np.asarray(
                [[float(p[0]), float(p[1]), float(p[2]) + z] for p in pts],
                dtype=np.float64,
            )
            faces = geo.triangulate(pts)
            self.add(
                name,
                s.scene.add_mesh_simple(
                    f"/regions/{name}",
                    vertices=verts,
                    faces=faces,
                    color=color,
                    opacity=opacity,
                    side="double",
                    cast_shadow=False,
                    receive_shadow=False,
                ),
                stages,
                region=region,
            )

        # Filled surfaces first (rendered underneath the outlines).
        # aff(Ω) at the bottom, then U, then the shared slice, then Ω on top.
        fill("aff_fill", geo.aff_plane_corners(), C_AFF, 0.25, z=-0.03, region="aff")
        fill("u_fill", geo.u_plane_corners(), C_U, 0.30, z=0.0, region="u")
        fill("slice_fill", geo.slab_corners(), C_SLICE, 0.45, z=-0.015)
        fill("omega_fill", geo.OMEGA, C_OMEGA, 0.55, z=0.015, region="omega")

        # Ω -- the polytope. Outline only; this is the star of the picture.
        self.add(
            "omega_edge",
            s.scene.add_line_segments(
                "/regions/omega_edge",
                points=segments(ring(geo.OMEGA)),
                colors=C_OMEGA,
                thickness=4.0,
                thickness_units="screen",
            ),
            range(6),
            region="omega",
        )

        # aff(Ω) -- the ambient affine plane, drawn as its border rectangle.
        self.add(
            "aff_edge",
            s.scene.add_line_segments(
                "/regions/aff_plane_edge",
                points=segments(ring(geo.aff_plane_corners())),
                colors=C_AFF,
                thickness=2.5,
                thickness_units="screen",
            ),
            range(6),
            region="aff",
        )

        # U -- the root slice, drawn as its border parallelogram.
        self.add(
            "u_edge",
            s.scene.add_line_segments(
                "/regions/u_plane_edge",
                points=segments(ring(geo.u_plane_corners())),
                colors=C_U,
                thickness=2.5,
                thickness_units="screen",
            ),
            range(6),
            region="u",
        )

        # aff(Ω) ∩ U -- the shared slice, drawn as its border rectangle.
        slab = geo.slab_corners()
        self.add(
            "slice_edge",
            s.scene.add_line_segments(
                "/regions/shared_slice_edge",
                points=segments(ring(slab)),
                colors=C_SLICE,
                thickness=3.5,
                thickness_units="screen",
            ),
            range(6),
        )

        # Centre lines of the two big planes, so their orientation is legible
        # without any filled surface to shade it.
        self.add(
            "aff_axes",
            s.scene.add_line_segments(
                "/regions/aff_plane_axes",
                points=segments(
                    np.array(
                        [
                            [geo.v3(-geo.AFF_PLANE_HALF, 0, 0), geo.v3(geo.AFF_PLANE_HALF, 0, 0)],
                            [geo.v3(0, -geo.AFF_PLANE_HALF_Y, 0), geo.v3(0, geo.AFF_PLANE_HALF_Y, 0)],
                        ]
                    )
                ),
                colors=edge,
                thickness=1.5,
                thickness_units="screen",
            ),
            range(6),
        )
        self.add(
            "slice_center",
            s.scene.add_line_segments(
                "/regions/shared_slice_center",
                points=segments(
                    np.array(
                        [
                            [geo.v3(-geo.SLAB_EXTENT, 0, 0), geo.v3(geo.SLAB_EXTENT, 0, 0)]
                        ]
                    )
                ),
                colors=C_SLICE,
                thickness=4.0,
                thickness_units="screen",
            ),
            range(6),
            region="slice",
        )

    def _build_shared_direction(self):
        s = self.server
        extent = geo.LINE_EXTENT
        shared = np.array(
            [
                [geo.v3(-extent, 0, 0), geo.v3(extent, 0, 0)],
                [geo.v3(0, 0, 0), geo.SHARED_DIR * 2.1],
            ]
        )
        self.add(
            "shared_dir",
            s.scene.add_line_segments(
                "/direction/shared",
                points=segments(shared),
                colors=C_RED,
                thickness=5.0,
                thickness_units="screen",
            ),
            [0],
        )
        # Witness directions showing each plane contributes something distinct.
        witnesses = np.array(
            [
                [geo.DELTA, geo.U_DIRECTION * 1.7],
                [geo.DELTA, geo.v3(0, 1.5, 0)],
            ]
        )
        self.add(
            "witnesses",
            s.scene.add_arrows(
                "/direction/witnesses",
                points=segments(witnesses),
                colors=np.array([C_U, C_AFF], dtype=np.uint8),
                shaft_radius=0.022,
                head_radius=0.055,
                head_length=0.16,
            ),
            [0],
        )

    def _build_paths(self):
        s = self.server
        e = geo.LINE_EXTENT

        # v -- the chosen nonzero direction inside the intersection.
        self.add(
            "v_arrow",
            s.scene.add_arrows(
                "/path/v",
                points=segments(np.array([[geo.DELTA, geo.v3(1.7, 0, 0)]])),
                colors=C_LINE,
                shaft_radius=0.026,
                head_radius=0.065,
                head_length=0.18,
            ),
            [1],
        )
        # L -- the full line through δ in direction v.
        self.add(
            "line_L",
            s.scene.add_line_segments(
                "/path/line_L",
                points=segments(np.array([[geo.v3(-e, 0, 0), geo.v3(e, 0, 0)]])),
                colors=C_LINE,
                thickness=3.0,
                thickness_units="screen",
            ),
            [2, 5],
            region="line",
        )
        # The escaping ray δ → q.
        self.add(
            "ray",
            s.scene.add_arrows(
                "/path/ray",
                points=segments(np.array([[geo.DELTA, geo.Q]])),
                colors=C_RAY,
                shaft_radius=0.026,
                head_radius=0.065,
                head_length=0.18,
            ),
            [3],
            region="ray",
        )
        # The segment [δ, q].
        self.add(
            "segment",
            s.scene.add_arrows(
                "/path/segment",
                points=segments(np.array([[geo.DELTA, geo.Q]])),
                colors=C_RED,
                shaft_radius=0.03,
                head_radius=0.075,
                head_length=0.2,
            ),
            [4, 5],
            region="boundary",
        )

    def _build_markers(self):
        s = self.server
        self.add(
            "delta",
            s.scene.add_icosphere(
                "/markers/delta", radius=0.09, color=C_INK, subdivisions=2
            ),
            range(6),
            region="base",
        )
        self.add(
            "q",
            s.scene.add_icosphere("/markers/q", radius=0.1, color=C_RED, subdivisions=2),
            [3, 4],
            region=("ray", "boundary"),
        )
        self.add(
            "bound",
            s.scene.add_icosphere(
                "/markers/delta_bound", radius=0.12, color=C_RED, subdivisions=2
            ),
            [4, 5],
            region="boundary",
        )
        # Boundedness witness: the ball that Ω sits inside.
        self.add(
            "ball",
            s.scene.add_line_segments(
                "/markers/ball_wireframe",
                points=segments(geo.sphere_wireframe(geo.DELTA, geo.BALL_RADIUS)),
                colors=(154, 165, 177),
                thickness=1.5,
                thickness_units="screen",
            ),
            [3],
        )



    def _build_labels(self):
        s = self.server

        def lab(name, text, position, color, stages, scale=1.0, region=None):
            self.add(
                name,
                s.scene.add_label(
                    f"/labels/{name}",
                    text,
                    position=np.asarray(position, dtype=float),
                    font_size_mode="screen",
                    font_screen_scale=scale,
                ),
                stages,
                region=region,
                label=True,
            )

        # Region names are deliberately absent from the figure -- the legend is
        # what identifies the colours. Only points and lines get labels, and
        # they are spread out so none of them collide.
        lab("l_delta", "δ", geo.v3(0.24, -0.30, 0.10), C_INK, range(6), region="base")
        lab("l_zero", "0", geo.v3(-0.34, -0.26, 0.10), C_INK, [0])
        lab("l_shared", "U ∩ aff(Ω).dir", geo.v3(-1.9, 1.25, 0.10), C_RED, [0], 0.9)
        lab("l_uvec", "u ∈ U", geo.U_DIRECTION * 2.3, C_U, [0], 0.9)
        lab("l_wvec", "w ∈ aff(Ω).dir", geo.v3(0.5, 2.35, 0.10), C_AFF, [0], 0.9)
        lab("l_v", "v", geo.v3(2.15, 0.42, 0.10), C_LINE, [1], 1.2)
        lab("l_line", "L = δ + ℝv", geo.v3(-2.9, -0.45, 0.10), C_LINE, [2], 1.0, region="line")
        lab(
            "l_slice",
            "aff(Ω) ∩ U = L",
            geo.v3(1.7, 0.38, 0.10),
            C_SLICE,
            [2],
            0.9,
            region="slice",
        )
        lab("l_ball", "Ω ⊂ B(δ, C)", geo.v3(-3.6, -2.6, 2.4), C_INK, [3], 0.9)
        lab("l_q", "q", geo.v3(4.75, -0.42, 0.10), C_RED, [3, 4], 1.2, region=("ray", "boundary"))
        lab("l_seg", "[δ, q]", geo.v3(1.55, -0.62, 0.10), C_RED, [4], 1.0, region="boundary")
        lab("l_bound", "δ_bound", geo.v3(2.35, 0.78, 0.10), C_RED, [4, 5], 1.1, region="boundary")

    def show_stage(self, stage):
        """Toggle every node so only the current stage's items are visible."""
        for node in self.nodes.values():
            handle = node["handle"]
            _apply(handle, node["orig"])  # undo any tour highlighting/dimming
            handle.visible = stage in node["stages"]
        self.server.flush()

    def show_region(self, idx):
        """Intro tour: spotlight one region, keep the others as recessive context.

        The focused region gets brighter/thicker styling; every other region
        stays visible but dimmed; proof-step-only decorations are hidden; only
        the focused region's labels (plus δ's) are shown.
        """
        key = REGION_TOUR[idx]["key"]
        for name, node in self.nodes.items():
            handle = node["handle"]
            region = node["region"]
            if region is None:  # proof-step-only decoration
                handle.visible = False
                continue
            if region == "base":  # δ and its label: always shown, full strength
                _apply(handle, node["orig"])
                handle.visible = True
                continue
            focused = key in (region if isinstance(region, tuple) else (region,))
            if node["label"]:
                handle.visible = focused  # region labels only for the focus
            else:
                handle.visible = True
            _apply(handle, _focus(node["orig"]) if focused else _dim(node["orig"]))
        self.server.flush()


def build_gui(server, scene):
    """Legend panel plus stage controls. Returns a callable to set the stage."""

    state = {"stage": 0}

    with server.gui.add_folder("Legend"):
        server.gui.add_html(
            "<div style='font:400 11px system-ui;color:#7b8794'>"
            "Steps 1–7 highlight one row of this legend at a time "
            "(what each region is); steps 8–13 run the proof.</div>"
        )
        for text, color in LEGEND:
            hex_color = "#%02x%02x%02x" % color
            server.gui.add_html(
                "<div style='display:flex;align-items:center;gap:8px;"
                "font:400 12px system-ui;margin:3px 0'>"
                f"<span style='width:14px;height:14px;border-radius:3px;"
                f"flex:0 0 auto;background:{hex_color};"
                "border:1px solid rgba(0,0,0,.25)'></span>"
                f"<span>{text}</span></div>"
            )

    with server.gui.add_folder("Stage"):
        options = tuple(f"{i + 1}. {t}" for i, t in enumerate(STEP_TITLES))
        dropdown = server.gui.add_dropdown("Step", options=options, initial_value=options[0])
        explanation = server.gui.add_markdown(STEP_EXPLANATIONS[0])
        prev_button = server.gui.add_button("◀ Previous")
        next_button = server.gui.add_button("Next ▶")
        server.gui.add_html(
            "<div style='font:400 11px system-ui;color:#7b8794'>"
            "Steps 1–7 introduce the regions; steps 8–13 walk through "
            "Lemma 6.1.</div>"
        )

    def apply(stage, sync_widgets=True):
        state["stage"] = stage % len(STEP_TITLES)
        if state["stage"] < N_TOUR:
            scene.show_region(state["stage"])
        else:
            scene.show_stage(state["stage"] - N_TOUR)
        explanation.content = STEP_EXPLANATIONS[state["stage"]]
        if sync_widgets:
            dropdown.value = options[state["stage"]]

    @dropdown.on_update
    def _(_event):
        apply(int(dropdown.value.split(".", 1)[0]) - 1, sync_widgets=False)

    @prev_button.on_click
    def _(_event):
        apply(state["stage"] - 1)

    @next_button.on_click
    def _(_event):
        apply(state["stage"] + 1)

    return apply


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--port", type=int, default=8080)
    parser.add_argument("--host", default="0.0.0.0")
    parser.add_argument(
        "--stage",
        type=int,
        default=None,
        help="apply this step at startup (0-6 = region tour, 7-12 = proof)",
    )
    args = parser.parse_args()

    server = viser.ViserServer(host=args.host, port=args.port, verbose=False)
    server.scene.set_up_direction("+z")
    server.scene.configure_default_lights(enabled=True, cast_shadow=False)
    # The geometry is largely FLAT: the polytope, the affine hull and the
    # shared slice all sit exactly in z = 0, and only U tilts out of it. So a
    # steep camera sees the picture edge-on. Frame the z = 0 plane from a
    # moderate elevation, at the distance that just fits the 6.5-unit radius
    # inside a 50-degree vertical FOV.
    # CAM_POS/CAM_LOOKAT are also re-applied per client below, because a
    # browser that connects (or reloads) starts from its own default view and
    # would otherwise ignore this framing.
    server.initial_camera.look_at = CAM_LOOKAT
    server.initial_camera.up = (0.0, 0.0, 1.0)
    server.initial_camera.fov = np.radians(FOV_DEGREES)
    server.initial_camera.min_orbit_distance = 1.0
    server.initial_camera.max_orbit_distance = 60.0
    server.initial_camera.position = CAM_POS

    @server.on_client_connect
    def _(client):
        client.camera.position = CAM_POS
        client.camera.look_at = CAM_LOOKAT
        client.camera.up_direction = (0.0, 0.0, 1.0)
        client.camera.fov = np.radians(FOV_DEGREES)
        client.camera.min_orbit_distance = 1.0
        client.camera.max_orbit_distance = 60.0

    scene = Scene(server)
    apply = build_gui(server, scene)

    stage = 0 if args.stage is None else args.stage
    stage %= len(STEP_TITLES)
    apply(stage, sync_widgets=False)
    print(f"step {stage + 1}/{len(STEP_TITLES)}: {STEP_TITLES[stage]}")

    print(f"Escape-to-the-boundary viewer: http://localhost:{args.port}")
    print("Open that URL in a browser. Ctrl+C to stop.")
    try:
        server.sleep_forever()
    except KeyboardInterrupt:
        print("\nstopped")


if __name__ == "__main__":
    main()
