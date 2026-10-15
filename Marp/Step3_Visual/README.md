# Step 3 — Escape-to-the-boundary figures

These six TikZ diagrams illustrate the geometric argument in
`CoeffBox.exists_boundary_point_in_submodule`
(`ControlSystems/DiscreteTime/EdgeTheorem/PreliminaryLemmas.lean`). The goal is
for each image to show one idea clearly, with the matching explanation in the
captions rather than a dense collection of labels inside the drawing.

## Files

| File | Purpose |
|---|---|
| `escape_to_boundary_figures.tex` | TikZ source; six preview pages, one diagram each |
| `escape_to_boundary_figures.pdf` | Compiled six-page source |
| `step3_fig-1.png` … `step3_fig-6.png` | PNGs embedded by `Marp/presentation.md` |
| `check_geometry.py` | Checks the shared coordinates and geometric relationships |
| `../../Manim/escape_to_boundary_3d.py` | Standalone detailed Manim 3D animation of the six stages (video, not in slides) |

## Manim 3D animation

The interactive 3D view of the same six stages is a standalone Manim
`ThreeDScene` at `Manim/escape_to_boundary_3d.py`. It uses the same geometry
and color palette as the figures here, with a slowly orbiting camera, and
renders to a video file (it is **not** embedded in the Marp slides). From the
`Manim/` directory:

```bash
manim render -qm escape_to_boundary_3d.py EscapeToBoundary3D   # 720p
manim render -qh escape_to_boundary_3d.py EscapeToBoundary3D   # 1080p
```

Note: rendering a full 3D scene with camera sweeps is CPU-heavy and can take
several minutes even at 480p/720p; let it run to completion. The output lands
in `Manim/media/videos/escape_to_boundary_3d/<quality>/EscapeToBoundary3D.mp4`.

## Build

From this directory:

```bash
pdflatex escape_to_boundary_figures.tex
pdftoppm -r 220 -png escape_to_boundary_figures.pdf step3_fig
python3 check_geometry.py
```

## What the figures show

1. The direction spaces `U` and `aff(Ω).dir` intersect; the red line highlights a shared direction.
2. A positive-dimensional intersection provides a nonzero direction `v`.
3. The full line `δ + ℝv` stays in the shared slice.
4. The ray reaches a point `q` outside the bounded polytope.
5. The segment from `δ` to `q` crosses the polytope boundary.
6. The crossing remains in the slice because it lies on the same line.

Figures 2–6 use the same convex hexagon and line geometry, so the proof sequence
reads as one argument. In those panels, the slice is a blue shaded affine slab;
the polytope is orange; the selected direction/path is purple, blue, or red
according to the step; and the boundary crossing is marked in red. The origin
and the larger space `U` are omitted from those proof panels to keep attention
on the shared slice; Figure 1 separately visualizes the direction spaces.

Slides 28–30 split the sequence for readability. Slide 28 introduces the
shared direction `U ⊓ aff(Ω).dir` with its own large schematic; Slides 29–30
show the five escape-to-boundary steps, with the final two diagrams enlarged
and the shared-slice conclusion highlighted.
