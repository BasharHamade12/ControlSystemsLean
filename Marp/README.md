# Marp deck — Edge Theorem (Lemma 6.1, real case)

## Build

```bash
# consistency first (renumber, regroup step boxes, verify;
# no writes except those)
python3 Marp/build.py all
# render (needs network once for the Marp CLI)
npx -p @marp-team/marp-cli marp Marp/presentation.md --pdf --allow-local-files
npx -p @marp-team/marp-cli marp Marp/presentation.md --images png --allow-local-files -o out.png
```

## Files

- `presentation.md` — the deck (56 slides; Steps 1–6 collapsed to one Lean + map slide each).
- `build.py` — single source of truth for slide numbers;
  `regroup` collapses consecutive `<mark>` lines that share a step number into
  one bordered box (`.grp`/`.gn`/`.gbox`) with the number badge on the right;
  `verify` checks numbering, verbatim Lean snippets, walkthrough
  subsets, cross-refs, escaping, image paths.
- `highlight_lean.py` — VS Code Light+-style syntax highlighting for `<pre>`
  code (keywords blue, tactics magenta, types/known constants teal,
  single-capital variables dark blue, strings dark red, numbers green,
  comments green, `sorry` red); rerunnable and idempotent, `verify`-safe
  (spans are stripped before comparison).
- `CHANGELOG.md` — old → new slide map and every content/code correction.
- `NEEDS_REVIEW.md` — what automation could not verify.
- `Defs_Visual/`, `Step3_Visual/`, `Step4_Visual/`, `Complex_Visual/`, `Intro_Visual/` — figure sources and PNGs.
