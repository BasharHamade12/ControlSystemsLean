# Lemma 6.2 complex-case split — figures

The Case A vs Case B split (`dim(P_sc ⊓ dir) ≥ 1` vs `= 0`) for the
"Lemma 6.2: complex case — what is extra" slide, in the same blue/orange/red
palette as the other figures: blue flat `aff(F)`, orange face triangle `F`,
red complex-slice line through the witness point.

## Files

| File | Purpose |
|---|---|
| `complex_split.tex` | TikZ source (flat projection); one preview page with both panels |
| `complex_split.pdf` | Compiled source |
| `complex_caseAB.png` | Flat-projection PNG (superseded on the slide, kept as record) |
| `complex_3d.tex` | TikZ-3D source (true perspective projection); one preview page |
| `complex_3d.pdf` | Compiled source |
| `complex_caseAB_3d.png` | PNG embedded by `Marp/presentation.md` |
| `check_labels.py` | Overlap check: `python3 check_labels.py complex_3d.pdf` (parses `pdftotext -bbox`, fails on any label collision) |
| `caseAB_viewer.py` | Standalone interactive viser 3D viewer (not in slides) |
| `requirements-viewer.txt` | Viewer dependencies |

## Build

From this directory:

```bash
pdflatex complex_split.tex
pdftoppm -r 200 -png -singlefile complex_split.pdf complex_caseAB
# true-3D version (embedded in the slides):
pdflatex complex_3d.tex
pdftoppm -r 200 -png -singlefile complex_3d.pdf complex_caseAB_3d
# label-collision check (must print OK):
python3 check_labels.py complex_3d.pdf
```

## Interactive 3D viewer

Same geometry in real rotatable 3D (the TikZ figure is its flat projection),
with a legend and a 3-stage dropdown (both panels / Case A / Case B):

```bash
cd Marp/Complex_Visual
../../.venv-3dview/bin/python caseAB_viewer.py   # serves on :8081
```

Then open the printed URL in a browser: drag to orbit, scroll to zoom.
