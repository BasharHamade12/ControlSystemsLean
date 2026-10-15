#!/usr/bin/env python3
"""Build/verify script for Marp/presentation.md (Edge Theorem deck).

Usage:
  python3 build.py renumber   # sequential <!-- SLIDE N | Title --> comments
  python3 build.py trackers   # no-op (tracker boxes were removed from the deck)
  python3 build.py regroup    # group step-numbered <mark> lines into bordered boxes
  python3 build.py verify     # run all consistency checks (no writes)
  python3 build.py all        # renumber + trackers + regroup + verify

How to build the deck itself (needs network once for the Marp CLI):
  npx -p @marp-team/marp-cli marp Marp/presentation.md --pdf --allow-local-files
Single source of truth for slide numbers: renumber below.
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
MD = HERE / "presentation.md"
LEAN = HERE.parent / "ControlSystems" / "DiscreteTime" / "EdgeTheorem"

def split_slides(text):
    """Split deck into (frontmatter, [slide chunks])."""
    parts = text.split("\n---\n")
    return parts[0], parts[1:]


def slide_title(chunk):
    m = re.search(r"^# (.+)$", chunk, flags=re.M)
    return m.group(1).strip() if m else "(untitled)"


# ------------------------------------------------------------------- commands
def cmd_renumber():
    text = MD.read_text(encoding="utf-8")
    front, slides = split_slides(text)
    out = [front]
    for n, chunk in enumerate(slides, start=1):
        title = slide_title(chunk)
        chunk = re.sub(r"^<!-- (?!_).*?-->",
                        f"<!-- SLIDE {n} | {title} -->",
                        chunk, count=1, flags=re.M)
        out.append(chunk)
    MD.write_text("\n---\n".join(out), encoding="utf-8")
    print(f"renumbered {len(slides)} slides")


def cmd_trackers():
    print("trackers were removed from the deck; nothing to do")


# --------------------------------------------------------------- step boxes
STEP_LINE = re.compile(
    r'(?P<prefix>[ \t]*)<mark class="(?P<mk>mk\d)">(?P<code>.*?)</mark>'
    r'(?P<label>\s+(?:\d+(?:\.\d+)?|A\.\d+(?:\.\d+)?|[①②③④⑤⑥⑦⑧⑨⑩]))[ \t]*$')


def regroup_pre(inner):
    """Collapse consecutive `<pre>` lines that share a step number into one
    `<span class="grp mkN"><span class="gbox">…` box with the number badge on the right.

    Idempotent: already-grouped markup no longer matches STEP_LINE, so a second
    run returns the input unchanged."""
    out = []
    lines = inner.split("\n")
    i, n = 0, len(lines)
    while i < n:
        m = STEP_LINE.match(lines[i])
        if not m:
            out.append(lines[i])
            i += 1
            continue
        label, mk = m.group("label").strip(), m.group("mk")
        codes = []
        while i < n:
            m = STEP_LINE.match(lines[i])
            if not m or m.group("label").strip() != label:
                break
            codes.append(m.group("prefix") + m.group("code"))
            i += 1
        out.append(f'<span class="grp {mk}"><span class="gn">{label}</span>'
                   f'<span class="gbox">' + "\n".join(codes) + "</span></span>")
    return "\n".join(out)


def cmd_regroup():
    text = MD.read_text(encoding="utf-8")
    n_pre = n_grp = 0

    def repl(m):
        nonlocal n_pre, n_grp
        head, inner, tail = m.group(1), m.group(2), m.group(3)
        if "<mark" not in inner:
            return m.group(0)
        new = regroup_pre(inner)
        if new != inner:
            n_pre += 1
            n_grp += new.count('class="grp')
        return head + new + tail

    text = re.sub(r"(<pre[^>]*>)(.*?)(</pre>)", repl, text, flags=re.S)
    MD.write_text(text, encoding="utf-8")
    print(f"regroup: {n_pre} pre blocks rewritten into {n_grp} step boxes")


# ------------------------------------------------------------- verification
SNIPPETS = [
    # (exact slide title, lean file, first-line prefix, last-line exact)
    # Each slide's first <pre> must equal the contiguous source span.
    ("Step 1: Unpack the root \u2014 Lean + map", "Lemma61.lean",
     "theorem lemma61_real", "exact mem_P_sr_of_isRoot s.re \u03b4 h\u03b4_root"),
    ("Step 2: Dimension count \u2014 Lean + map", "PreliminaryLemmas.lean",
     "lemma intersection_affine_dim_ge_one", "exact finrank_inf_ge_one U aff\u03a9.direction hU_dim haff_dim"),
    ("Step 3: Escape \u2014 `exists_boundary_point_in_submodule` (Lean + map)",
     "PreliminaryLemmas.lean", "lemma exists_boundary_point_in_submodule",
     "exact \u27e8\u03b4_bound, h_eq \u25b8 hmem_U, h_front\u27e9"),
    ("Step 3: Escape \u2014 `ray_escapes_of_bounded` (Lean + map)", "BasicLemmas.lean",
     "lemma ray_escapes_of_bounded", "linarith"),
    ("Step 3: Escape \u2014 `segment_boundary_intersection` (Lean + map)",
     "PreliminaryLemmas.lean", "lemma segment_boundary_intersection", "exact hx_uv"),
    ("Step 3: Escape \u2014 slice wrappers `Psr`/`Psc` (Lean + map)",
     "PreliminaryLemmas.lean", "lemma exists_boundary_point_in_Psr",
     "exists_boundary_point_in_submodule P (P_sc n s) \u03b4 h\u03b4_in_\u03a9 h\u03b4_in_Psc aff\u03a9 h\u03b4_aff hA_dim"),
    ("Supporting hyperplane: Lean", "EdgeTheoremDefs.lean",
     "structure SupportingHyperplane", "touches : \u2203 x \u2208 P.\u03a9, f x = c"),
    ("Boundary and exposed faces \u2014 Lean", "EdgeTheoremDefs.lean",
     "/-- The exposed face of `P` for `hp`", "Module.finrank \u211d (affineSpan \u211d (ExposedFace hp)).direction = 1"),
    ("Root space \u2014 definition", "EdgeTheoremDefs.lean",
     "def RootSpaceSet", "RootSpaceSet P.\u03a9"),
    ("Polytope: Lean formalization", "EdgeTheoremDefs.lean",
     "A polytope \u03a9 in coefficient space<<PREV", "convexHull \u211d (P.vertices : Set (CoeffVec n))"),
    ("Coefficient vectors (`CoeffVec`)", "EdgeTheoremDefs.lean",
     "/-- Coefficient vector", "abbrev CoeffVec (n : \u2115) := Fin (n + 1) \u2192 \u211d"),
    ("Affine span, direction, dimension \u2014 Lean", "EdgeTheoremDefs.lean",
     "abbrev meetDir", "Module.finrank \u211d U"),
    ("Lemma 6.2 (real case) \u2014 goal", "PreliminaryLemmas.lean",
     "def relativeBoundary", "F \\ intrinsicInterior \u211d F"),
    ("Step 6: Degenerate cases \u2014 Lean + map", "Lemma61.lean",
     "\u00b7 by_cases hm0 : m = 0", "exact h\u03b4_root)) P.\u03a9 h\u03b4_in_\u03a9"),
    ("Step 3: Escape \u2014 Lean + map", "PreliminaryLemmas.lean",
     "lemma exists_boundary_point_in_submodule",
     "exact \u27e8\u03b4_bound, h_eq \u25b8 hmem_U, h_front\u27e9"),
    ("Step 4: Exposed face \u2014 Lean + map", "ExposedFaceLemmas.lean",
     "lemma exists_exposed_face_containing_boundary_point",
     "hr_in_rootspace\u27e9"),
]

FULLSPANS = [
    # split slides whose concatenation must equal one contiguous source span
    (["Step 5: Descend \u2014 Lean + map (1/2)",
      "Step 5: Descend \u2014 Lean + map (2/2)"],
     "EdgeDescent.lean",
     "lemma descend_to_exposed_edge",
     "decreasing_by exact hG_dim_lt"),
]

# Walkthrough slides must be contiguous subsets either of full-code slides
# (list of titles) or, when those were removed, directly of a source span
# (fname, start anchor, end anchor).
WALKTHROUGH_PAIRS = [  # (walkthrough title, full-code slide title(s) in order)
    ("Lemma 6.2 (real case) \u2014 walkthrough 6.1\u20136.6",
     ("Lemma62.lean", "theorem lemma62_real_case", "exact Subtype.ext h")),
    ("Lemma 6.2 (real case) \u2014 walkthrough 6.7\u20136.9",
     ("Lemma62.lean", "have hv_U : v \u2208 U := by",
      "ray_stay_set_bddAbove hF_convex h\u03b4_star_in_F t_out ht_out_pos ht_out")),
    ("Lemma 6.2 (real case) \u2014 walkthrough 6.10\u20136.12",
     ("Lemma62.lean", "let t1 := sSup S", "LAST:exact h_r_in_RF")),
]


def norm_code(pre_html):
    code = re.sub(r'<span class="gn">[^<]*</span>', "", pre_html)  # step-number badges
    code = re.sub(r"</?(?:mark|span)[^>]*>", "", code)
    code = re.sub(r" +(\d\.\d+|A\.\d+(?:\.\d+)?|[①②③④⑤⑥⑦⑧⑨⑩])$", "", code, flags=re.M)  # legacy labels
    code = code.replace("&lt;", "<").replace("&gt;", ">").replace("&#124;", "|")
    lines = [line.rstrip() for line in code.splitlines()]
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    return "\n".join(lines)


def noblank(s):
    """Drop blank lines (split slides may carry the break's blank on either side)."""
    return "\n".join(l for l in s.splitlines() if l.strip())


def strip_doc(s):
    """Drop /-- ... -/ doc-comments (display-trimmed slides stay verbatim)."""
    return re.sub(r"/--.*?-/", "", s, flags=re.S)


# snippet slides allowed to trim doc-comments from the displayed code
STRIP_DOC = {
    "Affine span, direction, dimension \u2014 Lean",
}


def find_span(src, start, end):
    """Locate contiguous source span; start may end with <<PREV (include prior line);
    end may start with LAST: (take the last matching line, for repeated closers)."""
    if start.strip().endswith("<<PREV"):
        base = start.strip()[:-len("<<PREV")]
        i = next(k for k, l in enumerate(src) if l.strip().startswith(base.strip())) - 1
    else:
        i = next(k for k, l in enumerate(src) if l.strip().startswith(start.strip()))
    if end.strip().startswith("LAST:"):
        tail = end.strip()[len("LAST:"):]
        js = [k for k, l in enumerate(src) if k >= i and (
            l.strip() == tail.strip() or l.strip().startswith(tail.strip())
            or l.strip().endswith(tail.strip()))]
        if not js:
            raise StopIteration
        j = js[-1]
    else:
        j = next(k for k, l in enumerate(src) if k >= i and (
            l.strip() == end.strip() or l.strip().startswith(end.strip())
            or l.strip().endswith(end.strip())))
    return i, j


def cmd_verify():
    text = MD.read_text(encoding="utf-8")
    front, slides = split_slides(text)
    titles = [slide_title(c) for c in slides]
    fails = []

    def check(label, ok, detail=""):
        print(f"{'ok  ' if ok else 'FAIL'}  {label}{('  -- ' + detail) if detail else ''}")
        if not ok:
            fails.append(label)

    # 1. CSS: no id selectors, no !important, no bleed
    css = front
    check("CSS has no #id selectors", not re.search(r"section#", css))
    check("CSS has no !important", "!important" not in css)
    check("no 'bleed' directive", "bleed" not in front.split("style:")[0])
    check("lead/list/section classes styled",
          all(s in css for s in [".lead", ".list", ".section"]))

    # 2. numbering: sequential, no old ids
    nums = [int(m.group(1)) for c in slides
            for m in [re.search(r"<!-- SLIDE (\d+)", c)] if m]
    check("slide comments sequential 1..N",
          nums == list(range(1, len(slides) + 1)), f"found {len(nums)}/{len(slides)}")
    check("no leftover old ids",
          not re.search(r"SLIDE (5b|27[a-z]|30[a-z]|16b|30goal|30e0|30d2|30h2|27a01)", text))

    # 3. cross-refs: no numeric slide mentions in prose
    prose = re.sub(r"^<!--.*?-->", "", text, flags=re.M)
    check("no stale 'slide N' references",
          not re.search(r"[Ss]lides? \d+", prose))

    # 3b. a separator glued to a non-blank line is swallowed by an open HTML
    #     block (</div> --- with no blank line) and silently merges two slides
    seps = list(re.finditer(r"\n---\n", text))
    start = 1 if text.startswith("---") else 0  # 0th match closes the frontmatter
    bad_sep = sum(1 for k, m in enumerate(seps)
                  if k >= start and text[m.start() - 1:m.start()] != "\n")
    check("blank line before slide separator", bad_sep == 0,
          f"{bad_sep} of {len(seps) - start}")

    # 4. trackers were removed from the deck: no box or marker may remain
    for t, c in zip(titles, slides):
        check(f"no tracker box: {t[:45]}", '<div class="claims-tr">' not in c)
        if '<div class="claims-tr">' in c:
            continue
        check(f"no tracker marker: {t[:45]}", "_class: tracked" not in c)

    # 5. snippets verbatim
    pres_by_title = {}
    for t, c in zip(titles, slides):
        pres_by_title.setdefault(t, []).extend(
            re.findall(r"<pre[^>]*>(.*?)</pre>", c, flags=re.S))
    for title_sub, fname, start, end in SNIPPETS:
        if title_sub not in pres_by_title or not pres_by_title[title_sub]:
            check(f"snippet slide present: {title_sub[:40]}", False); continue
        code = norm_code(pres_by_title[title_sub][0])
        src = (LEAN / fname).read_text(encoding="utf-8").splitlines()
        try:
            i, j = find_span(src, start, end)
        except StopIteration:
            check(f"snippet anchors: {title_sub[:40]}", False, f"{fname}"); continue
        exp = "\n".join(src[i:j + 1])
        if title_sub in STRIP_DOC:
            code, exp = noblank(strip_doc(code)), noblank(strip_doc(exp))
        check(f"snippet verbatim: {title_sub[:40]}", code == exp,
              "" if code == exp else f"{fname}:{i + 1}-{j + 1}")

    for titles, fname, start, end in FULLSPANS:
        pres = []
        for tt in titles:
            if tt not in pres_by_title or not pres_by_title[tt]:
                check(f"fullspan slide present: {tt[:40]}", False); pres = None; break
            pres.append(norm_code(pres_by_title[tt][0]))
        if pres is None:
            continue
        code = "\n".join(pres)
        src = (LEAN / fname).read_text(encoding="utf-8").splitlines()
        try:
            i, j = find_span(src, start, end)
        except StopIteration:
            check(f"fullspan anchors: {titles[0][:40]}", False, f"{fname}"); continue
        exp = "\n".join(src[i:j + 1])
        check(f"fullspan verbatim: {titles[0][:40]}", noblank(code) == noblank(exp),
              "" if noblank(code) == noblank(exp) else f"{fname}:{i + 1}-{j + 1}")

    # 6. walkthroughs are contiguous subsets of their full listing
    # (norm: strip marks/labels; noblank: split slides may carry the break blank).
    # fulls is either slide titles or a (fname, start, end) source span.
    for wtitle, fulls in WALKTHROUGH_PAIRS:
        w = [t for t in pres_by_title if t == wtitle]
        if not w:
            check(f"walkthrough pair: {wtitle[:40]}", False); continue
        wcode = noblank(norm_code(pres_by_title[w[0]][0]))
        if isinstance(fulls, tuple):
            fname, start, end = fulls
            src = (LEAN / fname).read_text(encoding="utf-8").splitlines()
            try:
                i, j = find_span(src, start, end)
            except StopIteration:
                check(f"walkthrough anchors: {wtitle[:40]}", False, f"{fname}"); continue
            fcode = noblank("\n".join(src[i:j + 1]))
        else:
            f = [t for t in pres_by_title if t in fulls]
            if len(f) != len(fulls):
                check(f"walkthrough pair: {wtitle[:40]}", False); continue
            fcode = noblank("\n".join(norm_code(pres_by_title[t][0]) for t in fulls))
        check(f"walkthrough subset: {wtitle[:40]}", wcode in fcode)

    # 7. escaping + images
    for t, c in zip(titles, slides):
        for pre in re.findall(r"<pre[^>]*>(.*?)</pre>", c, flags=re.S):
            inner = re.sub(r'<span class="gn">[^<]*</span>', "", pre)
            inner = re.sub(r"</?(?:mark|span)[^>]*>", "", inner)
            inner = re.sub(r"&(lt|gt|#124|amp|quot);", "", inner)
            if "<" in inner or ">" in inner:
                check(f"no raw angle brackets in pre: {t[:40]}", False)
                break
    # 7b. a <pre> holding a blank line must open its own HTML block (start of a
    # line, preceded by a blank line); otherwise the surrounding HTML block ends
    # at the blank line and markdown leaks <br>/<p> into the code rendering.
    for m in re.finditer(r"<pre[^>]*>(.*?)</pre>", text, flags=re.S):
        if not re.search(r"\n[ \t]*\n", m.group(1)):
            continue
        ls = text.rfind("\n", 0, m.start()) + 1
        at_start = m.start() == ls
        prev = text[:ls - 1].rsplit("\n", 1)[-1] if ls else ""
        ok = at_start and not prev.strip()
        check("blank line inside pre keeps HTML block", ok,
              "" if ok else f"line {text.count(chr(10), 0, m.start()) + 1}")

    imgs = re.findall(r'<img src="([^"]+)"', text)
    missing = [p for p in imgs if not (HERE / p.lstrip("./")).exists()]
    check("all image paths resolve", not missing, ", ".join(missing))

    print()
    if fails:
        print(f"{len(fails)} FAILED: {fails}")
        return 1
    print("all checks passed")
    return 0


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "verify"
    if cmd == "renumber":
        cmd_renumber()
    elif cmd == "trackers":
        cmd_trackers()
    elif cmd == "verify":
        sys.exit(cmd_verify())
    elif cmd == "regroup":
        cmd_regroup()
    elif cmd == "all":
        cmd_renumber()
        cmd_trackers()
        cmd_regroup()
        sys.exit(cmd_verify())
    else:
        sys.exit(f"unknown command: {cmd}")
