# Basedslider deck — Edge Theorem (Lemma 6.1 / 6.2, real case)

`presentation_basedslider.slide` is the same talk as the Marp deck, rewritten in
Basedslider's `.slide` scripting language. It is a **single self-contained file**:
every figure, 3D viewer and code panel is inline (HTML/SVG/JS in an `html` block,
or plain text/code elements). No external images, fonts or scripts are referenced,
so the file can be moved or committed on its own.

- 63 slides (`slide "…" { … }` blocks), 1920×1080 document units.
- Opens and edits in the Basedslider app (canvas ↔ code stay in sync).

## Opening / editing

1. Launch Basedslider (`bun run dev` in `~/Basedslider/client`, or the desktop build).
2. **File → Open** `Marp/presentation_basedslider.slide` (or drag it onto the window).
3. Present with the app's present mode: click / → advances, and blocks carrying
   `animate { effect: "fadeIn"; trigger: "onClick"; … }` reveal one at a time, so a
   single slide covers what used to be several Marp slides.

The DSL itself is documented in `~/Basedslider/docs/slide-language.md`; a short
version is in `~/Basedslider/.claude/skills/slide-dsl/SKILL.md`.

## Slide index

| # | Slide | # | Slide |
|---|-------|---|-------|
| 1 | Formalizing the Edge Theorem for Robust Control Stability in Lean4 | 33 | Step 2 — Dimension count: the picture |
| 2 | Outline | 34 | Step 3: Escape — Lean + map |
| 3 | What is a control system? | 35 | Step 3 — exists_boundary_point_in_submodule |
| 4 | From state-space to transfer function | 36 | Step 3 — ray_escapes_of_bounded |
| 5 | Example: mass-spring-damper | 37 | Step 3 — segment_boundary_intersection |
| 6 | Poles and stability | 38 | Step 3 — slice wrappers Psr/Psc |
| 7 | Kharitonov's theorem | 39 | Step 3 — Escape: the picture |
| 8 | Kharitonov vs Edge Theorem (discrete systems) | 40 | Step 4: Exposed face — Lean + map (1/2) |
| 9 | The Edge Theorem at work (discrete) | 41 | Step 4: Exposed face — Lean + map (2/2) |
| 10 | Section 1 · Preliminaries | 42 | Step 4 — Exposed face: the picture |
| 11 | Polytopic family of polynomials | 43 | Step 5: Descend — Lean + map (1/2) |
| 12 | Coefficient vectors (CoeffVec) | 44 | Step 5: Descend — Lean + map (2/2) |
| 13 | Polytope: Lean formalization | 45 | Step 5 — Descend: the picture |
| 14 | Affine span, direction, dimension — definition | 46 | Step 6: Degenerate cases — Lean + map |
| 15 | Affine span, direction, dimension — Lean | 47 | Step 6 — Degenerate cases: the picture |
| 16 | Supporting hyperplane | 48 | Lemma 6.1 (real case) — recap |
| 17 | Root spaces | 49 | Lemma 6.1: complex case — what is extra |
| 18 | Root space — definition | 50 | Section 5 · Lemma 6.2, real case |
| 19 | Exposed faces and edges | 51 | Lemma 6.2 (real case) — overview |
| 20 | Boundary and exposed faces — definition | 52 | Lemma 6.2 (real case) — goal |
| 21 | Boundary and exposed faces — Lean | 53 | Lemma 6.2 (real case) — walkthrough 6.1–6.6 |
| 22 | Boundary and exposed edge — example | 54 | Lemma 6.2 (real case) — walkthrough 6.7–6.9 |
| 23 | Edge Theorem | 55 | Lemma 6.2 (real case) — walkthrough 6.10–6.12 |
| 24 | Assumption 6.1 & Lemmas 6.1–6.2 | 56 | Lemma 6.2 (real case) — proof map (1/2) |
| 25 | Lemmas 6.1–6.2 — statements | 57 | Lemma 6.2 (real case) — proof map (2/2) |
| 26 | Edge Theorem — statement | 58 | Lemma 6.2: complex case — what is extra |
| 27 | Edge Theorem — proof outline | 59 | Lemma 6.2 — Case A vs Case B: the picture |
| 28 | Section 4 · Proof of Lemma 6.1, real case | 60 | Edge Theorem — formal proof |
| 29 | Lemma 6.1 (real case) — proof overview | 61 | Edge Theorem — lemmas behind steps 1–5 (1/2) |
| 30 | Step 1: Unpack the root — Lean + map | 62 | Edge Theorem — lemmas behind steps 1–5 (2/2) |
| 31 | Step 1 — Unpack: the picture | 63 | Edge Theorem — Lean implementation |
| 32 | Step 2: Dimension count — Lean + map | | |

Pattern used for the six proof steps (slides 30–47): one **Lean + map** slide
(highlighted Lean tactic block on the left, click-through map of proof steps on
the right) followed by one **picture** slide carrying the interactive viewer.

## Conventions used in this file

- **Elements**: one block per element, `text { … } …rect…code…html…`; most carry a
  stable id (`code "e130" { … }`, `html "e122" { … }`), the rest are plain
  (`text { … }`). Composition: 467 `text`, 240 `rect`, 31 `code`, 22 `latex`,
  11 `html`, 9 `image`.
- **Canvas**: 1920×1080, absolute `x/y/width/height` on every element.
- **Title**: `x: 120, y: 56–64`, `fontSize: 42–46`, `fontWeight: 700`, `#12233a`,
  followed by an accent rule `x: 120, y: 148–170, width: 120, height: 6, #1f4e79`.
- **Theorem banner**: `#f2f6fa` block with a 8 px `#1f4e79` left bar, label text at
  23 px and statement text at 16–18 px.
- **Body text**: 18–21 px, `lineHeight: 1.45`, `#24313f`; labels `#12233a`.
- **Math**: elements set `math: true`; the content is KaTeX. **Each `$…$` span must
  sit on one line** — prose is pre-wrapped, because a formula split across a line
  break renders its `$` literally.
- **Code**: `code { … language: "lean"; theme: "light" }`, 15–17 px, panel height
  includes the caption line drawn inside the block.
- **Pictures / 3D viewers**: an `html "eNNN" { … }` block whose `content` is a single
  escaped string holding a complete `<!DOCTYPE html>` document (its own `<style>`,
  canvas and script; newlines as `\n`, quotes as `\"`). The embedded viewers are
  plain 2D-canvas 3D projections — no Three.js, no network. Full-width viewers go on
  their own slide; in a narrow column their overlay labels collide, so those slides
  use a 2D snapshot instead (embedded as a base64 `image { … src: "data:image/png…" }`).
- **Reveals**: `animate { id: "aNNN"; effect: "fadeIn"; trigger: "onClick"; duration: 350–400; easing: "easeOut" }`
  where the Marp deck had incremental slides; `trigger: "afterPrevious"` chains a
  group that appears together.

## Relation to the Marp deck

| | Marp | Basedslider |
|---|---|---|
| Source | `Marp/presentation.md`, `Marp/presentation_animated.md` | `Marp/presentation_basedslider.slide` |
| Slides | 56 (animated copy: incremental) | 63 (incremental via `animate`) |
| Figures | PNGs from `Marp/*_Visual/` | inline HTML/SVG/JS, live and rotatable |
| Renderer | Marp CLI → PDF/PPTX | Basedslider present mode |

Content is the same run-through: intro → preliminaries → exposed faces →
Lemma 6.1 (real + complex) → Lemma 6.2 (real + complex) → Edge Theorem assembled.
The Basedslider version spends extra slides on the interactive step viewers and on
splitting the two densest reference slides (lemma tables, proof maps) into halves so
they stay legible at presentation size.
