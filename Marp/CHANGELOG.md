# CHANGELOG — Marp deck restructure (Edge Theorem, Lean formalization)

## Step 4 claim: matched to lemma, math unbroken, refit
- Claim rewritten to mirror `exists_exposed_face_containing_boundary_point`
  (all three hypotheses up front).
- Fixed math-kill: a missing `$` plus a stray `$` had unpaired delimiters and
  silently disabled KaTeX for the paragraph (bisected with isolated renders);
  restored `PsrSet n r` notation.
- Refit after the two-line claim (code 0.32em, zero box margins). Render-checked.


## Appendices removed (56 slides)
- Deleted all 9 Appendix A.1/A.2/A.3 slides; helper-lemma detail now lives
  only on the four Step 3 lemma Lean + map slides.
- Dangling appendix cross-refs reworded (slice-wrappers map, Lemma 6.2 proof
  + helpers rows). `build.py` appendix SNIPPETS entries removed.
- `SLIDES.md` entries dropped, `README.md` count 56. `renumber` + `verify` green.


## Fix ②-box alignment + trimmed-slide verbatim rule
- `Step 3: Escape — Lean + map`: the ② box closed two lines early (end-anchor
  matched `have h_line…` instead of the proof line); extended to all four
  lines. The lemma slide's 3.2 box was already correct.
- Kept-trimmed `Affine span — Lean` slide (no `dim` docstring): new `STRIP_DOC`
  set + `strip_doc` make its SNIPPETS check docstring-insensitive; head fixed
  to `:338-351`. Refitted slide 26 after the proof-div expansion (scoped type
  tightening). Render-checked. `verify` green.


## Merge: supporting-hyperplane definition + example (65 slides)
- Slides 9–10 merged into one two-column `Supporting hyperplane` slide
  (definition left, example + figure right); `renumber` rerun.
- Synced `Affine span, direction, dimension — Lean` to the new `dim` docstring
  in `EdgeTheoremDefs.lean`. `SLIDES.md` entry merged. `verify` green.


## Appendix trims + repair (66 slides)
- Removed `Appendix A.2: Segment crossing — goal`, `— walkthrough`,
  `Appendix A.3: Slice wrappers — goal` (appendix Lean slides now open with
  their own Goal/Theorem divs instead).
- Repaired slide separators swallowed by the deletions (re-split merged
  chunks, reattached orphaned `_class` markers, `renumber` rerun).
- `Edge Theorem — proof outline` rewritten formally (6.1 ⇒ face/edge,
  6.2 boundary-to-relboundary, strict-dim descent chain).
- `SLIDES.md` entries dropped. `build.py verify`: all checks passed.


## Master-lemma slide: goal + proof on top, detailed 3.5 row
- `Step 3: Escape — exists_boundary_point_in_submodule (Lean + map)` opens with
  a `.thm` Goal + 3.1–3.5 proof sketch; map row 3.5 expanded (segment scalar,
  rewrite lemmas, slice membership). Fit via scoped tightening (title, thm,
  code 0.42em). Render-checked. `verify` green.


## Maps: Lean-lines column removed everywhere (two columns only)
- All 15 remaining three-column maps (3 Step-3 lemma slides, A.1 Lean + map,
  7 Lemma 6.2 walkthroughs, 4 `Lean line | Mathematical content` proof maps)
  converted to `| Step | Content |`; 55 rows dropped to number + formal content.
- Map panels (`.side`) bolded at 0.85em. Render-checked. `verify` green.


## Formal math div on the six Lean + map slides (trackers removed there)
- Each step slide now opens with a `.thm` div (Claim + Proof sketch) above the
  codeside; the pipeline tracker box was removed from these six slides and
  `step_of` exempts `Step N: … — Lean + map` (other Step/Appendix/Lemma 6.2
  slides keep their boxes; `verify` green).
- Fit work on Steps 4–5 (41/43 code lines): claim-only divs, Step 5 verbatim
  span narrowed to 691–733 (docstring off-slide), code pres at
  0.34em/1.15→1.1, per-slide `<style scoped>` tightening title/thm/codeside.
- Render-checked all six step slides: nothing clipped.


## Collapse: one Lean + map slide per step (100 → 69 slides)
- Each of Steps 1–6 now has exactly one `— Lean + map` slide (full proof code,
  one grouped box per step number, two-column Map: number + formal content).
  The `Lean lines` map column is gone; separation/subface statements folded
  into the Step 4 row 4.3 / Step 5 row 5.4 formal content.
- Deleted 31 slides: all step goal slides, Step 2/3/4/5 Lean splits +
  walkthroughs + proof maps, Step 3 roster/figures/math-proof, Step 4
  separation-theorem slide, Step 5 subface-separation slide, Step 6 goal.
  Kept: preliminaries, Edge Theorem block, Step 3 lemma slides + appendices
  A.1–A.3, Lemma 6.2 section, recap, future work.
- New merged slides built from verified sources (Step 3 via anchors, Steps 4–5
  via group transfer from the old walkthroughs); Step 4/5 pres at 0.47em.
- `build.py`: SNIPPETS retitled/extended (Steps 2–6 merged), FULLSPANS Step 3/4/5
  entries removed, WALKTHROUGH_PAIRS trimmed to 6.x. `renumber` + `verify` green.
- Docs: `SLIDES.md` step regions rewritten, `README.md` slide count 69.


## New: Step 6 Degenerate cases (slides 76–77, 100 slides total)
- `Step 6: Degenerate cases — goal` (thm + D.1/D.2 sketch) and
  `Step 6: Degenerate cases — Lean + map` (codeside `Lemma61.lean:191-203`,
  grouped boxes ①/② + side map), inserted before the recap.
- Tracker: all-done box (`step_of`: `Step 6:` → `recap`); labels D.1/D.2 + ①②
  avoid the Lemma 6.2 `6.x` namespace. SNIPPETS entry added; outline item 4
  now reads "Steps 1–6". `SLIDES.md` entries added.
- `build.py renumber` + `verify`: all checks passed (snippet verbatim ok).


## Titles: full Topic — Kind pass (98 slides)
- 21 renames: title-slide TODO dropped; `— definition` (affine span, root space,
  boundary faces); `— example` (supporting hyperplane, boundary edge);
  `Lemmas 6.1–6.2 — statements`; `Edge Theorem — statement` / `— proof outline`;
  `Lemma 6.1 (real case) — proof overview`; Step 3 `— helper lemmas`,
  `— figures (1/2)/(2/2)`, `— math proof`; Step 5 `— subface separation`;
  `Lemma 6.1 (real case) — recap`; `Lemma 6.2 (real case) — overview` +
  `— math proof (1/2)/(2/2)`; `Future work — outlook`.
- Stale `vertex fallback` wordings → `singleton fallback` (overview, Step 5 goal).
- `build.py`: SNIPPETS titles + `step_of` recap branch updated; `renumber` rerun.
- `SLIDES.md` headings synced. `build.py verify`: all checks passed.


## Sync: dim-0 singleton rewrite (EdgeDescent.lean + VertexEdge.lean)
- `descend_to_exposed_edge` / `exists_exposed_edge_through_vertex` take `(hn : n ≥ 1)`;
  dim-0 case now proves `G = {δ_bound}` (`exposed_face_dim_zero_singleton`) and calls
  `exists_exposed_edge_of_singleton` (`VertexEdge.lean`) — vertex axiom gone.
- Deck: Step 5 Lean (1/2) signature + heads (`690-706`/`707-733`); Lean (2/2) recursive
  call + dim-0 block; walkthrough 5.6–5.10 code (5.8 call, 5.10 `mk4` box) + head
  (`714-733`); walkthrough 5.1 head (`700-713`); 5.3/5.10 map rows; proof-map (1/2)
  + (2/2) line refs (`:717`/`:764`, `:29`, `:777`, `:737`).
- `build.py verify`: all checks passed. `lake build`: succeeds.


Source: `Marp/presentation.md` (59 slides) → new deck (93 slides).
Tooling: `Marp/build.py` (`renumber` | `trackers` | `regroup` | `verify` | `all`).
All Lean snippets verified verbatim against
`ControlSystems/DiscreteTime/EdgeTheorem/*.lean` by `build.py verify`
(snippet/fullspan/walkthrough-subset checks). No math was changed.

## Old id → new number (old ids retired; comments are now `<!-- SLIDE N | Title -->`)

| Old | New | Note |
|---|---|---|
| 1 | 1 | Title: placeholders → `TODO:` markers |
| 2 | 2 | Outline rewritten to match delivered sections |
| — | 3 | NEW divider: Section 1 · Preliminaries |
| 3 | 4 | Polytope: "compact convex subset" → "compact and convex" + converse-fails note |
| 4 | 5 | Unchanged (figure-free def slide) |
| 5 | 6 | + interior-nonempty assumption note; redundant restatement paragraph
  dropped and over-long caption removed (both overflowed the figure) |
| 5b | 7, 8 | Lean moved out of math boxes into a `dim`/`meetDir` Lean box; SPLIT (was overflowing: definitions | Lean code) |
| 8 | 8 | Moved before example (definition + figure) |
| 6 | 9 | Example only (definition column removed; now follows the definition) |
| 7 | 10 | Unchanged |
| 9 | 11 | Kept subsection divider |
| 10 | 12 | Code boxes expanded to verbatim spans (doc comments included) |
| 11 | 13 | Kept subsection divider |
| 12 | 14, 15 | Code box expanded to verbatim span `EdgeTheoremDefs.lean:140-151`; SPLIT (was overflowing: definitions | Lean code) |
| 13 | 15 | "Def. 3.1/3.2" numbering dropped |
| 14 | 16 | Kept divider |
| (31, Assumption block) | 17 | NEW: Assumption 6.1 moved ahead of the lemmas |
| 15 | 18 | Lemmas 6.1 + 6.2; Lemma 6.2 marked "proof not covered here" |
| 31 (Theorem block) | 19 | Assumption block removed (now slide 17); tracker removed (§3 has no tracker) |
| — | 20 | NEW: How the lemmas give the theorem (prose glue, no Lean claims) |
| — | 21 | NEW divider: Section 4 |
| 32 | 22 | Moved from file end to section start; stale "slides 30a–30d" ref fixed; tracker removed |
| 16 | 23, 24 | Split: goal + numbered proof 1.1–1.3 | Lean (verbatim `Lemma61.lean:142-153`) + mini-map |
| 17 | 25 | Setup/Claim → numbered proof 2.1–2.6 in `.thm` box |
| 18 | 26 | Unchanged (verified verbatim) |
| 19, 20, 21, 22, 23, 24 | 27 | MERGED (6 progressive slides → 1 codeside walkthrough, marks kept) |
| 25 | 28 | Retitled; rows ①–⑥ → 2.1–2.6 |
| 26 | 29 | Retitled "— lemmas"; pointer → "see Appendix A.1–A.3" |
| 28 | 30 | Moved to step front; retitled "— goal" + goal `.thm` box |
| 29 | 31 | Retitled "— figures 1" |
| 30 | 32 | Retitled "— figures 2" |
| 27 | 33 | Retitled "— proof"; bound prose fixed to pairwise `Metric.isBounded_iff` form; headings 3.1–3.5 |
| 27a0 | 34, 35 | SPLIT (was ~30 lines, overflowed at 1.4em base) |
| 27a | 36 | Retitled walkthrough 3.1 |
| 27b | 37 | Retitled walkthrough 3.2 |
| 27c | 38 | Retitled walkthrough 3.3 |
| 27d | 39 | Retitled walkthrough 3.4 |
| 27e | 40 | Step ⑤ code restored to verbatim (rcases/calc reinstated); retitled walkthrough 3.5 |
| 27g | 41 | Retitled; rows → 3.1–3.5 with Appendix pointers |
| (new) | 42 | NEW: Step 4 goal + figure (merged old 30c1, which is deleted) |
| 30a3 | 43 | Moved ahead of Lean slides; retitled "— separation theorem" |
| 30a | 44 | Retitled "— Lean (1/2)" (verified verbatim) |
| 30a2 | 45 | Retitled "— Lean (2/2)"; caption cleaned |
| 30b | 46 | Converted two-column text → codeside walkthrough 4.1–4.5 + map |
| 30c | 47 | Converted two-column text → codeside walkthrough 4.6–4.10 + map |
| 30c1 | — | MERGED into slide 42 (figure + takeaway moved) |
| 30d | 48, 49 | SPLIT (12 rows → 6 + 6); rows → 4.1–4.10 |
| (new) | 50 | NEW: Step 5 goal + numbered proof 5.1–5.10 |
| 30e3 | 51 | Moved ahead of Lean slides |
| 30e1 | 52 | Fixed to verbatim (`Module.finrank`, restored `have hm_F_ge_2`, docstring kept) |
| 30e2 | 53 | Fixed to verbatim (restored `have hG_dim_0` derivation, exact comment, `termination_by`/`decreasing_by`) |
| 30f | 54 | Converted two-column text → codeside walkthrough 5.1–5.5 (exact excerpt) + map |
| 30g | 55 | Converted two-column text → codeside walkthrough 5.6–5.10 (exact excerpt) + map |
| 30h | 56, 57 | SPLIT (12 rows → 6 + 6: (1/2) lost its marker in an edit, restored) |
| — | 58 | NEW: Recap (incl. degenerate cases `lemma61_real:191-203`) |
| — | 59 | NEW divider: Appendix |
| 27h | 60 | Moved to Appendix; retitled A.1 Lean |
| 27i | 61 | Moved to Appendix; headings → A.1.1–A.1.4; `•`→`\cdot` in math (KaTeX warning) |
| 27i2 | 62 | Moved to Appendix; retitled A.1 math proof |
| 27j | 63 | Moved to Appendix; side-by-side code + helper table (was overflowing); retitled A.2 Lean |
| 27k | 64 | Moved to Appendix; headings → A.2.1–A.2.4 |
| 27l | 65 | Moved to Appendix; side-by-side code (35% cap) + mini-map; rows → A.1/A.2/A.3 |
| — | 66 | NEW: Future work (Lemma 6.2 proof, complex case — not covered) |

## Section 5 · Lemma 6.2, real case (new, 21 slides)

`ray_escapes_of_bounded` now has the full format: goal slide (theorem + use
sites) and proof-map slide (A.1.1–A.1.4 with `BasicLemmas.lean` line numbers).
Convention learned by testing: inside tables/math use backslash-pipe `\|`
(never `&#124;`, which breaks KaTeX); entities (`&lt;`/`&gt;`) only inside `<pre>`.

Same locked format (goal → numbered proof 6.1–6.12 → verbatim Lean →
codeside walkthrough → map). `lemma62_real_case` (`Lemma62.lean:92-211`,
120 lines) split into 7 Lean slides; 7 walkthroughs generated from them;
`relativeBoundary` def box (`PreliminaryLemmas.lean:422-423`); maps split
6.1–6.6 / 6.7–6.12; tracker extended with claim ⑥ (regenerated deck-wide);
outline / Lemma-6.2 slide / future-work slide updated (complex 6.2 case open).

## Code corrections (all verified by `build.py verify`)

- Step 1 Lean: was abbreviated (`...`, collapsed `have`); now verbatim `Lemma61.lean:142-153`.
- Walkthrough 3.5: restored dropped `rcases`, two-line `calc`, original indentation.
- Step 5 Lean: `dim` → `Module.finrank ℝ` (7 sites), restored `have hm_F_ge_2`,
  `have hG_dim_0` derivation, exact `-- dim(G) = 0…` comment, `termination_by`/`decreasing_by`.
- Def boxes: `Polytope` (2-space `nonempty`, doc comments), `RootSpaceSet` (2-space
  continuation), `ExposedFace` (single-line signature), `CoeffVec`/`polyOfVec`
  (doc comments, original line breaks), `meetDir`/`dim` (+ `dim` docstring),
  wrappers (+ `/-- Complex case…` docstring).
- Step 3 prose: single-point bound → pairwise `Metric.isBounded_iff` bound.

## CSS / layout

- Removed `bleed: true`; added `math: katex`; styled `lead`/`list`/`section`
  (dividers distinct); deleted `section#28–30` selectors and all `!important`;
  removed invalid `max-width=20%`.
- Figure classes merged to 3 documented sizes: `.figs-sm/.figs-md/.figs-lg`
  (+ `.cols-2/.cols-3`); all 11 usages migrated.
- Page numbers shrunk (12px grey); bottom margins zeroed.
- Tracker: single source (`build.py` CLAIMS); bottom `.claims` boxes deleted (4);
  top-right box on all 43 proof slides, identical within each step
  (→ in-step, ✓ after; all-✓ on recap/appendix); `_class: tracked` reserves title space.
- Markdown-in-HTML: inserted missing blank lines after `</div>` (CommonMark was
  swallowing the next paragraph); expanded single-line `<figcaption>` and
  `.fig-takeaway` divs so math renders; `&lt;`/`&gt;` inside `$…$` replaced with
  raw `<`/`>` (KaTeX warnings); `•`→`\cdot` in math mode.
- Minimum effective type ≥0.7em at 1.4em base (tracker/code floors hold).

## Images

- `Marp/Step4_Visual/` created with copies of `separating_hyperplane-1/-3.png`;
  Step 4 slides reference it (originals kept in `Step3_Visual/` for its scripts).

## Appendix A.1 completed (2 slides)

`ray_escapes_of_bounded` now has the full format: goal slide (theorem + use
sites) and proof-map slide (A.1.1–A.1.4 with `BasicLemmas.lean` line numbers).
Convention learned by testing: inside tables/math use backslash-pipe `\|`
(never `&#124;`, which breaks KaTeX); entities (`&lt;`/`&gt;`) only inside `<pre>`.
Deck total: 89 → 91 slides.

## Appendix A.2/A.3 completed (3 slides)

Same format as A.1: A.2 got a goal slide (theorem + use site at
`PreliminaryLemmas.lean:357`) and a proof-map slide (A.2.1–A.2.4 with exact
source lines, incl. helper lemmas `:224/:241/:252/:265` and
`segment_is_connected` at `BasicLemmas.lean:46`); A.3 got a goal slide
(dispatch to both slices + call sites `Lemma61.lean:163-164/:232-233`).
Deck total: 91 → 94 slides.

## Order audit fixes
- Step 3: goal slide now precedes the lemmas roster (template: goal first).
- Appendix A.1 now follows the template order goal → math proof → Lean →
  walkthrough → map (math proof moved ahead of Lean).
- Incident: a chunk-swap script deleted the A.1 walkthrough slide; rewritten
  from the known proof content and visually verified. Lesson recorded:
  always re-run `build.py verify` + slide count after chunk surgery.

## Step-3 helpers moved into the main flow

- Appendix A.1–A.3 (11 slides) moved between the Step-3 proof map and the
  Step-4 goal; the now-empty Appendix divider deleted; outline Appendix item
  removed (Future work renumbered). Labels (`Appendix A.1` etc.) and all
  cross-references kept, so no ref changed.
- Tracker rule extended: `Appendix A.*` slides show step-3 state (→3), since
  they detail Step 3.3/3.4 (`build.py step_of`). Deck total: 94 → 93 slides.

## Step highlights: left-bar groups, one number per group

- Consecutive Lean lines belonging to one numbered step share one highlight
  group with a single trailing `N.M` label (53 groups deck-wide).
- Style journey (all verified by test renders): grey fill → per-shade blue
  backgrounds (dropped) → full blue-bordered boxes (looked striped: every
  fragment draws its own border) → final: light-blue tint + 4px blue left bar.
  Note: a multi-line `<mark>` only styles its first line in this renderer, so
  each line carries its own `<mark>`; the shared tint + bar + single number
  reads as one group.
- `build.py` `norm_code` strips `<mark[^>]*>`, so grouping is check-neutral.

## Grouped step boxes: bordered box + number badge (current)

- Consecutive Lean lines that share a step number now live in ONE bordered box:
  `<span class="grp mkN"><span class="gn">N.M</span><span class="gbox">…lines…</span></span>`
  inside the same `<pre>`. Spans, not divs: a `<div>` inside `<pre>` is invalid
  HTML, and an inline-flex span keeps the `<pre>` inline formatting context, so
  source newlines behave exactly as before (no blank-line artifacts).
- The step number renders **once**, as a badge to the left of the box
  (`.lean .gn`); **every** labeled step is boxed — single- and multi-line —
  53 boxes across the 18 marked slides (26, 29, 38–42, 59, 60, 67, 68, 84–90).
- The mk1–mk5 tint moved from per-line `<mark>` to the box background
  (`.lean .grp.mkN .gbox`); unmarked lines stay plain text.
- New `build.py regroup` command: parses `<mark>…</mark>  N.M` runs, collapses
  same-label runs, idempotent (re-run rewrites 0 blocks); now part of `all`.
  `verify`'s `norm_code` and the raw-angle-bracket check strip the new
  `<span>` tags, so all snippet/fullspan/walkthrough verbatim checks still
  compare clean Lean source.
- Coverage gap closed: walkthroughs 3.2–3.4 were not in `WALKTHROUGH_PAIRS`
  (unchecked against `PreliminaryLemmas.lean`); the three pairs were added.
- Incident: the first `regroup` run dropped indentation that sat *before* the
  `<mark>` (slide 26 style: `␣␣<mark class="mk1">unfold …`). Caught by the
  snippet check; slide 26 repaired, and `STEP_LINE` now captures the prefix and
  prepends it to each grouped line. Lesson: every marked slide must be covered
  by a verbatim or walkthrough-subset check.
- Visual check: `marp --images png` for all 93 slides; inspected 26, 29, 41,
  59, 84, 85, 90 (mixed marked/unmarked, tall boxes, circled ①–④ badges,
  `codeside` + Map layouts).

## Rendering fixes: tracker HTML-block glue + stray `$` opener (slide 57)

- **Root cause:** `build.py trackers` inserted the tracker box with no blank
  line after it. CommonMark treats a `<div>` HTML block as continuing to the
  next blank line, so the line *following* the box was swallowed as raw HTML on
  **13 slides** (32–35, 48, 52, 54, 57, 62, 70, 71, 91, 92): `**Theorem**` /
  `**Goal**` paragraphs, figure prose and proof-map tables were emitted as
  literal text — no `<p>`, no bold, no KaTeX. `cmd_trackers` now appends the
  blank line (`box + "\n"`); all 67 tracker slides regenerated.
- Slide 57 also opened with a stray `$` (`$**Theorem** …`), an unclosed math
  span (odd `$` count → KaTeX would render the rest as math garbage); removed.
- Deck-wide checks after the fix: every paragraph has an even single-`$` count;
  rendered HTML scan of all 93 sections finds 0 literal `**` and 0 raw `$`
  outside `<code>`/`<pre>`; slide 57's theorem renders as
  `<p><strong>Theorem</strong> (<code>…</code>) … <span class="katex">…`.

## Step boxes for the remaining Lean + map slides (30, 43, 46, 50, 54)

- The five slides that pair a Lean `<pre>` with a step table/Map but had **no**
  bordered boxes now carry them: **30** steps 2.1–2.6 (per its proof-map
  table), **43** one statement box badge `3` (its 3-line `…` signature has no
  per-step lines to split), **46** A.1.1–A.1.4, **50** A.2.1–A.2.4, **54** two
  `A.3` boxes (Psr/Psc wrappers). Deck total: **72 boxes across 23 slides**
  (was 53/18).
- `build.py` `STEP_LINE` and `norm_code`'s legacy-label strip now also accept
  `A.x` / `A.x.y` and bare-digit labels, so appendix badges regroup like `N.M`.
- Appendix assignments follow the proof maps, with walkthrough-aligned tie-breaks
  where the map ranges were sloppy: A.1.3 = `ht_nonneg`…`h_t_mul` (80–88, so
  every A.1.3 walkthrough bullet sits in its box), A.1.4 = rewrite + `le_abs_self`
  + `linarith` (89–91); on slide 50 the first box is A.2.4 (`h_conn` is
  precomputed, per the map), A.2.1 = `h_closed` + `by_contra` + `push_neg` (per
  the walkthrough), so A.2.4 appears twice — same duplicate-number pattern as
  `4.4` on slide 59.
- **Slide 29 off-by-one fixed:** its badges were shifted one row against its own
  Map (`unfold meetDir` unboxed, box N showing the row N+1 code). Renumbered to
  2.1–2.6 (new 2.6 box for `finrank_inf_ge_one`) and dropped the dangling ①–⑥
  column from the table — rows now match the plain `| **N.M** |` style of the
  Step 4/5 walkthrough Maps (59, 67).
- Slide 46 structure fix: a stray duplicate `.lean` opener wrapped the theorem
  in an empty gray box above a second header; the theorem now stands alone like
  its sibling slides (50, 44), and the head reads `… A.1.1–A.1.4 highlighted`
  instead of `no highlights`.
- Slide 51 prose: dangling `against ①` (slide 50 had no circled marker) →
  `against A.2.1`, referencing the new badge.
- Verification: `build.py all` green (snippet/fullspan/walkthrough checks still
  byte-exact); rendered-HTML scan — badges exactly as specified on all six
  slides, 0 literal `**`, 0 raw `$`; PNG tint-pixel checks (mk1–mk6 present per
  slide, no unexpected tints); puppeteer geometry: slide 54's two boxes equal
  (50 px, uniform 8 px line gaps).

## Rendering fixes: blank line inside `<pre>` ended the HTML block

- **Root cause (pre-existing, 5 slides: 6, 8, 13, 16, 54):** each of those
  `<pre>` blocks contains an interior blank line (separating two definitions).
  The `<pre>` sat on the line right after a `<div class="lean">` line, so
  CommonMark's HTML block was the *div's* type-6 block, which **ends at a blank
  line**. Everything after the blank — the second definition — was therefore
  markdown-processed: softbreaks rendered as `<br />\n` (double-spaced code) and
  a stray `<p>` wrapped the tail. Visible as doubled line spacing below the gap
  on all five slides.
- **Fix:** a blank line before each of those `<pre>` opening lines, so the
  `<pre>` starts its own type-1 HTML block, which ends only at `</pre>` and
  ignores interior blanks. No visual change outside the code block; the blank
  lines inside the code are required by the verbatim snippet checks and stay.
- **Guard added to `verify`:** `blank line inside pre keeps HTML block` — any
  `<pre>` containing an interior blank must start at line start with a blank
  line before it (5 `ok` runs, all green).
- Confirmation: rendered HTML now has **0** `<br>`/`<p>` inside any `<pre>`;
  both slide-54 boxes render at identical height. (Broken figure icons seen in
  `--images png` output were a render artifact — the flag
  `--allow-local-files` was missing; with the HTML served from `Marp/`, all 13
  deck images load with `naturalWidth > 0`.)

## New slide: Appendix A.1 — "Lean + map" (deck 93 → 94)

- Inserted **"Appendix A.1: Ray escape — Lean + map"** between the A.1 `Lean`
  and `walkthrough` slides: `.codeside` with the full boxed proof (A.1.1–A.1.4,
  same markup as the `Lean` slide) on the left and the proof-map table
  (4 rows, from the `proof map` slide) in the `.side` panel on the right —
  the pattern of slides 27 (Step 1) and 55 (A.3). The standalone `Lean` and
  `proof map` slides are kept.
- `build.py` `SNIPPETS` gained the matching verbatim check for the new title
  (`BasicLemmas.lean:73-91`, anchors `lemma ray_escapes_of_bounded`…`linarith`),
  so both A.1 Lean slides are byte-checked against the source.
- Layout: the copied `<pre>` kept slide 46's inline `font-size:0.58em`
  (overriding `.codeside .lean pre`), and the `.side` table's min-content
  forced the `1fr` track wide, starving the code column (485 px) and clipping
  A.1.3's 87-char lines. Fixed: inline style dropped and both grid tracks
  `minmax(0,1.58fr) minmax(0,1fr)` — pre `scrollWidth == clientWidth`
  (no overflow), table fits, all four boxes render unclipped (checked by
  puppeteer geometry + full PNG pass of all 94 slides).

## Rendering fixes: separator glued to `</div>` merged two slides + verify guard

- **Root cause (introduced with the new slide, same class as the tracker-glue
  fix):** the inserted slide ended `…</div>\n---` — no blank line. The `<div
  class="codeside">` HTML block (type 6, ends only at a blank line) swallowed
  the `---`, so the walkthrough slide silently merged into the Lean + map
  slide: rendered deck had **93 sections for 94 markdown slides**.
- Fixed by the blank line before the separator; a stray blank inserted into
  the frontmatter by the same pass was reverted.
- **New verify guard:** `blank line before slide separator` — every `\n---\n`
  (frontmatter closer exempt) must be preceded by an empty line, so a glued
  separator can never merge slides again. `build.py all` green: 94 slides,
  68 tracker slides, regroup idempotent, 5 pre-block guards, 14 snippet +
  4 fullspan + 18 walkthrough checks, all image paths resolve.
