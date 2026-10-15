#!/usr/bin/env python3
"""Detect overlapping figure labels from pdftotext -bbox output."""
import itertools
import subprocess
import sys
import xml.etree.ElementTree as ET

NS = "{http://www.w3.org/1999/xhtml}"
TITLE = {"Case", "A:", "B:", "shared", "direction", "transverse"}


def load(pdf, page_no=0):
    subprocess.run(["pdftotext", "-bbox", pdf, "/tmp/boxes.xml"], check=True)
    t = ET.parse("/tmp/boxes.xml")
    pages = list(t.getroot().iter(NS + "page"))
    words = []
    for w in pages[page_no].iter(NS + "word"):
        words.append(
            (w.text, float(w.get("xMin")), float(w.get("xMax")),
             float(w.get("yMin")), float(w.get("yMax")))
        )
    return words


def main():
    pdf = sys.argv[1]
    words = load(pdf)
    dimx = {}
    for w in words:
        txt, x0, x1, y0, y1 = w
        if txt == "dim(P":
            dimx["A" if (x0 + x1) / 2 < 220 else "B"] = (x0 + x1) / 2

    def label_of(txt, cx, cy, panel):
        if txt in TITLE or txt in {"dim(P", "\u2293", "dir)", "\u2265", "1", "="}:
            return "CAPTION"
        if txt in ("s", "c", "0"):
            ref = dimx.get(panel, None)
            if ref is not None and abs(cx - ref) < 70:
                return "CAPTION"
            return "PSC" if txt in ("s", "c") else "ZERO"
        if txt == "v":
            return "V"
        if txt == "P":
            return "PSC"
        if txt in ("\u03b4", "\u22c6"):
            return "DST"
        if txt in ("aff", "F", "dir"):
            return "AFF" if cy < 90 else "DIR"
        return "?" + txt

    groups = {}
    for w in words:
        txt, x0, x1, y0, y1 = w
        cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
        panel = "A" if cx < 220 else "B"
        groups.setdefault((panel, label_of(txt, cx, cy, panel)), []).append(w)
    boxes = {}
    for k, ws in groups.items():
        boxes[k] = (
            min(w[1] for w in ws) - 1.5, min(w[3] for w in ws) - 1.5,
            max(w[2] for w in ws) + 1.5, max(w[4] for w in ws) + 1.5,
        )

    def ov(a, b):
        return a[0] < b[2] and b[0] < a[2] and a[1] < b[3] and b[1] < a[3]

    bad = 0
    for a, b in itertools.combinations(sorted(boxes), 2):
        if a[0] == b[0] and ov(boxes[a], boxes[b]):
            print("OVERLAP:", a, "x", b)
            print("   ", [round(v, 1) for v in boxes[a]], "vs",
                  [round(v, 1) for v in boxes[b]])
            bad += 1
    print("OK - no label overlaps" if bad == 0 else f"{bad} OVERLAPS")
    return bad


if __name__ == "__main__":
    raise SystemExit(1 if main() else 0)
