# Intro figures (control background slides)

TikZ schematics for the opening control-systems slides, in the deck's
orange/blue/red palette.

## Files

| File | Purpose |
|---|---|
| `tmd.tex` | TikZ source: wall, primary $m_1$ ($k_1$, $c_1$, force $u(t)$), TMD $m_2$ ($k_2$, $c_2$), displacement $y(t)$ |
| `tmd.pdf` | Compiled source |
| `tmd.png` | PNG embedded by `Marp/presentation.md` (Kharitonov example slide) |
| `ex62_loci.py` | Computes the 12 edge root loci (`ex62_edge0.dat` … `ex62_edge11.dat`) with numpy |
| `ex62_loci.tex` | pgfplots source: unit circle + orange loci dots |
| `ex62_loci.pdf` | Compiled source |
| `ex62_loci.png` | Superseded loci-only PNG (kept as record) |
| `edge_example_62.py` | Two-panel figure (needs working matplotlib): 3D coefficient box colored by varying coefficient + unit disc with the 12 continuous edge root loci |
| `edge_example_62.png` | PNG embedded by `Marp/presentation.md` (Edge-at-work example) |

## Build

From this directory:

```bash
pdflatex tmd.tex
pdftoppm -r 200 -png -singlefile tmd.pdf tmd
# edge root loci (needs the venv numpy):
../../.venv-3dview/bin/python ex62_loci.py
pdflatex ex62_loci.tex
pdftoppm -r 200 -png -singlefile ex62_loci.pdf ex62_loci
```
