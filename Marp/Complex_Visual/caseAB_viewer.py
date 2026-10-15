#!/usr/bin/env python3
"""Interactive 3D viewer for the Lemma 6.2 complex-case split (Case A vs B).

Two side-by-side panels in real 3D (the TikZ figure on the slide is a flat
projection of this same geometry):

    Panel A (Case A)   the complex slice shares a direction v with the
                       face flat: the red P_sc line lies IN the blue
                       aff(F) plane through the witness point.
    Panel B (Case B)   transverse: the red P_sc line pierces the blue
                       plane, meeting it only at the witness point.

Legend colours:

    aff(F)             pale blue  outline of the face's affine flat
    dir aff(F)         teal       the parallel direction plane through 0
    F                  orange     the 2D exposed face (triangle)
    P_sc line          red        the complex-slice line through the witness
    v                  red arrow  the shared direction (Case A only)
    witness            dark       the root witness point (delta*)
    0                  grey       the origin (anchor of the dir plane)

Usage
-----
    cd Marp/Complex_Visual
    ../../.venv-3dview/bin/python caseAB_viewer.py

Then open the printed URL (http://localhost:8081) in any browser: drag to
orbit, scroll to zoom, and use the stage dropdown/buttons. Stage 1 shows both
panels; stages 2-3 isolate Case A / Case B.

Requires ``viser`` (+ ``numpy``); see requirements-viewer.txt.
"""
import argparse

import numpy as np

try:
    import viser
except ImportError:  # pragma: no cover - friendly message for a missing dep
    raise SystemExit(
        "This viewer needs `viser`.\n"
        "Install the project venv and its viewer deps:\n"
        "    cd /home/bashar/ControlSystems\n"
        "    python3 -m venv --system-site-packages .venv-3dview\n"
        "    .venv-3dview/bin/python -m pip install -r "
        "Marp/Complex_Visual/requirements-viewer.txt\n"
    )

# ------------------------------------------------------------------- palette
C_AFF = (110, 165, 205)  # aff(F): the face's affine flat
C_DIR = (64, 158, 156)  # dir aff(F): the parallel direction plane through 0
C_FACE = (232, 138, 36)  # F: the 2D exposed face
C_LINE = (200, 51, 61)  # P_sc line through the witness
C_INK = (39, 49, 59)  # the witness point itself
C_ORIGIN = (154, 165, 177)  # the origin marker

LEGEND = [
    ("aff(F)  the face's affine flat (blue plane)", C_AFF),
    ("dir aff(F)  direction plane through the origin (teal)", C_DIR),
    ("F  the 2D exposed face (orange triangle)", C_FACE),
    ("P_sc line  complex-slice line through the witness (red)", C_LINE),
    ("v  shared direction, Case A only (red arrow)", C_LINE),
    ("witness  the root carrier point (dark)", C_INK),
]

STAGES = [
    "Both panels: shared direction vs transverse pierce",
    "Case A: P_sc shares the direction v with the flat",
    "Case B: transverse, meets the flat only at the witness",
]

STAGE_EXPLANATIONS = [
    "Two copies of the same face flat side by side, each with its teal "
    "direction plane through the origin underneath. LEFT (Case A): the red "
    "complex-slice line lies parallel to the flat, sharing the nonzero "
    "direction v — the escape of the real case works. RIGHT (Case B): the "
    "red line pierces the flat, meeting it only at the witness point — no "
    "shared direction, so no escape; the proof must approximate instead.",
    "Case A (dim >= 1): the slice and the face directions share v (red "
    "arrow). Walking from the witness along v stays root-preserving inside "
    "the flat until the relative boundary — exactly the real-case escape, "
    "replayed in P_sc (`exists_boundary_point_in_face_rootspace_complex`).",
    "Case B (dim = 0): the only common point is the witness itself. The "
    "proof takes outside non-roots s_k converging to s*, builds nearby "
    "carriers delta_k in the flat by Cramer's rule, and the limit forces "
    "the witness onto the relative boundary.",
]

# ------------------------------------------------------------------ geometry
# Local frame: the direction plane is z = 0 (through the origin); the affine
# flat is lifted to z = H so the two parallel planes are visibly distinct.
H = 1.1
PLANE = [
    (0.0, 0.0, H),
    (4.6, 0.3, H),
    (5.4, 2.6, H),
    (0.8, 2.3, H),
]
DIR_PLANE = [(x, y, 0.0) for (x, y, _) in PLANE]
TRI = [
    (1.6, 0.7, H + 0.012),
    (3.7, 0.85, H + 0.012),
    (2.6, 1.95, H + 0.012),
]
DSTAR = np.array([2.62, 1.12, H + 0.02])
# Case A: in-plane direction (lies in z = 0).
VA = np.array([1.55, 0.22, 0.0])
VA = VA / np.linalg.norm(VA)
# Case B: transverse direction (leaves z = 0 immediately).
VB = np.array([0.35, -0.8, 1.0])
VB = VB / np.linalg.norm(VB)

OFF_A = np.array([-6.4, 0.0, 0.0])
OFF_B = np.array([1.0, 0.0, 0.0])


def segments(pts):
    """Normalize to the (N, 2, 3) start/end array that viser expects."""
    return np.asarray(pts, dtype=np.float64).reshape(-1, 2, 3)


def ring(points):
    """Closed 3D polygon into an (n, 2, 3) edge array."""
    pts = [np.asarray(p, dtype=float) for p in points]
    return np.array(
        [[pts[i], pts[(i + 1) % len(pts)]] for i in range(len(pts))]
    )


def quad_faces():
    return np.array([[0, 1, 2], [0, 2, 3]], dtype=np.int32)


def panel(server, tag, off, line_dir, half_len, with_arrow):
    """Build one panel; returns {node name: handle}."""
    handles = {}

    def add(name, handle):
        handle.visible = True
        handles[name] = handle
        return handle

    verts = np.asarray([np.asarray(p) + off for p in PLANE])
    add(
        f"{tag}/aff_fill",
        server.scene.add_mesh_simple(
            f"/{tag}/aff_fill",
            vertices=verts,
            faces=quad_faces(),
            color=C_AFF,
            opacity=0.28,
            side="double",
            cast_shadow=False,
            receive_shadow=False,
        ),
    )
    add(
        f"{tag}/aff_edge",
        server.scene.add_line_segments(
            f"/{tag}/aff_edge",
            points=segments(ring(verts)),
            colors=C_AFF,
            thickness=2.5,
            thickness_units="screen",
        ),
    )
    # dir aff(F): the parallel direction plane through the origin.
    dverts = np.asarray([np.asarray(p) + off for p in DIR_PLANE])
    add(
        f"{tag}/dir_fill",
        server.scene.add_mesh_simple(
            f"/{tag}/dir_fill",
            vertices=dverts,
            faces=quad_faces(),
            color=C_DIR,
            opacity=0.15,
            side="double",
            cast_shadow=False,
            receive_shadow=False,
        ),
    )
    add(
        f"{tag}/dir_edge",
        server.scene.add_line_segments(
            f"/{tag}/dir_edge",
            points=segments(ring(dverts)),
            colors=C_DIR,
            thickness=1.5,
            thickness_units="screen",
        ),
    )
    origin = server.scene.add_icosphere(
        f"/{tag}/origin", radius=0.06, color=C_ORIGIN, subdivisions=2
    )
    origin.position = np.asarray(off, dtype=float)
    add(f"{tag}/origin", origin)
    tri = np.asarray([np.asarray(p) + off for p in TRI])
    add(
        f"{tag}/face_fill",
        server.scene.add_mesh_simple(
            f"/{tag}/face_fill",
            vertices=tri,
            faces=np.array([[0, 1, 2]], dtype=np.int32),
            color=C_FACE,
            opacity=0.55,
            side="double",
            cast_shadow=False,
            receive_shadow=False,
        ),
    )
    add(
        f"{tag}/face_edge",
        server.scene.add_line_segments(
            f"/{tag}/face_edge",
            points=segments(ring(tri)),
            colors=C_FACE,
            thickness=3.5,
            thickness_units="screen",
        ),
    )
    c = DSTAR + off
    p0, p1 = c - half_len * line_dir, c + half_len * line_dir
    witness = server.scene.add_icosphere(
        f"/{tag}/witness", radius=0.09, color=C_INK, subdivisions=2
    )
    witness.position = c
    add(f"{tag}/witness", witness)
    add(
        f"{tag}/slice_line",
        server.scene.add_line_segments(
            f"/{tag}/slice_line",
            points=segments(np.array([[p0, p1]])),
            colors=C_LINE,
            thickness=5.0,
            thickness_units="screen",
        ),
    )
    if with_arrow:
        add(
            f"{tag}/v_arrow",
            server.scene.add_arrows(
                f"/{tag}/v_arrow",
                points=segments(np.array([[c, c + 1.3 * line_dir]])),
                colors=C_LINE,
                shaft_radius=0.026,
                head_radius=0.065,
                head_length=0.18,
            ),
        )
    def lab(name, text, pos, scale=1.0):
        add(
            f"{tag}/label_{name}",
            server.scene.add_label(
                f"/{tag}/label_{name}",
                text,
                position=np.asarray(pos, dtype=float),
                font_size_mode="screen",
                font_screen_scale=scale,
            ),
        )

    lab("aff", "aff(F)", off + np.array([3.1, 3.0, H + 0.05]), 0.9)
    lab("dir", "dir aff(F)", off + np.array([5.9, 2.75, 0.05]), 0.9)
    lab("origin", "0", off + np.array([-0.35, -0.3, 0.05]), 0.9)
    lab("witness", "witness", off + np.array([2.0, 1.55, H + 0.1]), 0.9)
    lab("psc", "P_sc", c + half_len * line_dir + np.array([0.15, 0.15, 0.1]), 1.0)
    if with_arrow:
        lab("v", "v", c + 1.65 * line_dir + np.array([0.0, 0.0, 0.1]), 1.2)
    return handles


FOV_DEGREES = 50.0
CAM_POS = (0.0, -14.5, 10.5)
CAM_LOOKAT = (0.0, 0.9, 0.5)


def build_gui(server, set_stage):
    """Legend panel plus stage controls."""
    with server.gui.add_folder("Legend"):
        server.gui.add_html(
            "<div style='font:400 11px system-ui;color:#7b8794'>"
            "The same face flat twice: Case A shares a direction with the "
            "complex slice, Case B meets it in one point.</div>"
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
        options = tuple(f"{i + 1}. {t}" for i, t in enumerate(STAGES))
        dropdown = server.gui.add_dropdown("Step", options=options, initial_value=options[0])
        explanation = server.gui.add_markdown(STAGE_EXPLANATIONS[0])
        prev_button = server.gui.add_button("◀ Previous")
        next_button = server.gui.add_button("Next ▶")

    state = {"stage": 0}

    def apply(stage, sync_widgets=True):
        state["stage"] = stage % len(STAGES)
        set_stage(state["stage"])
        explanation.content = STAGE_EXPLANATIONS[state["stage"]]
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
    parser.add_argument("--port", type=int, default=8081)
    parser.add_argument("--host", default="0.0.0.0")
    parser.add_argument(
        "--stage",
        type=int,
        default=None,
        help="apply this step at startup (0 = both, 1 = Case A, 2 = Case B)",
    )
    args = parser.parse_args()

    server = viser.ViserServer(host=args.host, port=args.port, verbose=False)
    server.scene.set_up_direction("+z")
    server.scene.configure_default_lights(enabled=True, cast_shadow=False)
    server.initial_camera.look_at = CAM_LOOKAT
    server.initial_camera.up = (0.0, 0.0, 1.0)
    server.initial_camera.fov = np.radians(FOV_DEGREES)
    server.initial_camera.min_orbit_distance = 1.0
    server.initial_camera.max_orbit_distance = 80.0
    server.initial_camera.position = CAM_POS

    @server.on_client_connect
    def _(client):
        client.camera.position = CAM_POS
        client.camera.look_at = CAM_LOOKAT
        client.camera.up_direction = (0.0, 0.0, 1.0)
        client.camera.fov = np.radians(FOV_DEGREES)
        client.camera.min_orbit_distance = 1.0
        client.camera.max_orbit_distance = 80.0

    by_name = {}
    by_name.update(panel(server, "caseA", OFF_A, VA, 1.9, with_arrow=True))
    by_name.update(panel(server, "caseB", OFF_B, VB, 1.7, with_arrow=False))

    def set_stage(stage):
        for n, h in by_name.items():
            h.visible = stage == 0 or (
                (stage == 1 and n.startswith("caseA"))
                or (stage == 2 and n.startswith("caseB"))
            )
        server.flush()

    apply = build_gui(server, set_stage)
    stage = 0 if args.stage is None else args.stage
    apply(stage % len(STAGES), sync_widgets=False)
    print(f"step {stage % len(STAGES) + 1}/{len(STAGES)}: {STAGES[stage % len(STAGES)]}")

    print(f"Case A/B 3D viewer: http://localhost:{args.port}")
    print("Open that URL in a browser. Ctrl+C to stop.")
    try:
        server.sleep_forever()
    except KeyboardInterrupt:
        print("\nstopped")


if __name__ == "__main__":
    main()
