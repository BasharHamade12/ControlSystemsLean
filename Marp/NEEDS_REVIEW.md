# NEEDS_REVIEW — things not machine-verified (Edge Theorem deck)

`build.py verify` passes (code verbatim, numbering, trackers, refs, images,
escaping). The items below need a human (or Lean) eye.

## Lean / math

1. **`Separation.lean` signature (slide 43).** The `geometric_hahn_banach_open_point`
   statement is copied from Mathlib prose, not from a repo file. Not covered by
   `build.py` (no local source). Recheck against the Mathlib version you build against.
2. **CoeffVec example box (slide 5).** The `-- α : CoeffVec 2 …` comment is a
   hand-written illustration, not source text. Intentionally unverified.
3. **How-the-lemmas slide (20) and Recap (58).** Prose glue (Lemma 6.1 + 6.2 ⇒
   Edge Theorem; degenerate cases cite `lemma61_real:191-203`,
   `polytope_dim1_is_exposed_edge`). No Lean counterpart on the slide; line
   numbers were read from `Lemma61.lean`/`EdgeDescent.lean` but are not in `build.py`.
4. **Lemma 6.2, real case** is now Section 5 (slides ~61–81, verified verbatim).
   Still open: the **complex case** (`lemma62_complex_case`, `Lemma62.lean:1155`,
   $W$-matrix Case A/B through line 1446 incl. the `lemma62` dispatcher) and
   **Lemma 6.1's complex case** (`lemma61_complex`, `descend_to_exposed_face`).
   The full-theorem assembly (`EdgeTheorem.lean`) is not presented.
   All three are disclosed on slides 18 and 89 — confirm this matches your intent.
5. **Assumption slides (7, 17).** Wording ("additionally requires", "everything
   assumes it") is editorial; confirm against the textbook's Assumption 6.1.
6. **Map tables paraphrase.** Proof-map "Mathematical content" cells are summaries,
   not quotes. Spot-check slides 28, 41, 48–49, 56–57 against the files.

## Figures

7. PNGs taken as-is (`Defs_Visual/`, `Step3_Visual/`, `Step4_Visual/` copies).
   `Defs_Visual/check_figures.py` passed at figure-cleanup time; re-run it and
   `Step3_Visual/check_geometry.py` if you regenerate figures.
8. `Step4_Visual/` duplicates two `Step3_Visual/` PNGs (by design, so each step
   owns its folder). If disk/layout matters, replace copies with moves and update
   the two `src=` paths (slides 42, 43-era figure).

## Rendering / layout

9. Built with `@marp-team/marp-cli v4.5.1` (via npx). If your Marp version differs,
   re-run `build.py all` + the PDF/PNG export below and recheck dense slides
   (33, 40, 46–47, 54–55, 60–65).
10. Trackers overlap code top-right on full-Lean slides by design (absolute box,
    `_class: tracked` reserves title space). Shrink-proof: keep claim texts short.
11. Minimum-type rule (≥0.7em effective) holds at `section { font-size: 1.4em }`.
    If you change the base size, re-check `.claims-tr` (0.50em) and
    `.codeside .lean pre` (0.53em) floors first.

12. `build.py verify` compares snippets against the **working-tree** `.lean`
    files. The working tree has uncommitted `.lean` modifications (pre-existing,
    not from this task — verify with `git diff`); re-run `build.py all` after
    any `git checkout` or Lean edit.
