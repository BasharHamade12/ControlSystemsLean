#!/usr/bin/env python3
"""Add VS Code Light+-style syntax highlighting to Lean code in Marp slides.

Wraps tokens inside <pre> blocks in <span class="tok-*"> spans:
  tok-kw    commands/keywords (theorem, def, have, calc, ...)
  tok-tac   tactics (rw, simp, exact, omega, ...)
  tok-type  types & known constants (Capitalized, Prop/Type, or any
            theorem|lemma|def|abbrev name collected from the Lean sources)
  tok-str   string literals      tok-num  numbers/true/false
  tok-com   comments (-- and /- -/)      tok-sorry  sorry/admit (red)

Only text runs are tokenized (existing tags are never touched), so reruns
are idempotent. build.py's verify strips all spans before comparing, so
highlighting cannot break snippet checks. The one thing it must never do
is alter HTML entities (&lt; &gt; &#124; &amp;) -- they pass through byte-
identically.

Usage: python3 Marp/highlight_lean.py   (run from repo root)
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MD = ROOT / "Marp" / "presentation.md"
LEAN = ROOT / "ControlSystems" / "DiscreteTime" / "EdgeTheorem"

KW = {
    "module", "public", "private", "protected", "noncomputable", "unsafe",
    "partial", "import", "open", "namespace", "end", "section", "variable",
    "universe", "axiom", "example", "abbrev", "def", "theorem", "lemma",
    "structure", "class", "instance", "inductive", "coinductive", "where",
    "extends", "deriving", "syntax", "macro", "elab", "command", "attribute",
    "set_option", "mutual", "include", "omit", "export", "if", "then",
    "else", "match", "with", "fun", "do", "return", "for", "in", "have",
    "let", "show", "suffices", "from", "at", "calc", "conv", "termination_by",
    "decreasing_by", "all_goals", "mutual",
}
TAC = {
    "by", "intro", "intros", "apply", "exact", "refine", "rw", "rwa",
    "simp", "simpa", "dsimp", "simp_rw", "norm_num", "norm_cast",
    "push_cast", "ring", "ring_nf", "omega", "linarith", "nlinarith",
    "abel", "aesop", "decide", "rfl", "trivial", "assumption",
    "contradiction", "congr", "ext", "funext", "cases", "rcases",
    "obtain", "by_cases", "by_contra", "push_neg", "contrapose",
    "revert", "generalize", "set", "clear", "rename", "rename_i",
    "constructor", "cases_on", "rec_on", "induction", "coinduction",
    "convert", "change", "unfold", "positivity", "field_simp",
    "norm_num1", "gcongr", "congrm", "guard_hyp", "guard_target",
    "trace", "show_term", "extract_goal", "choose", "replace",
    "clear_value", "subst", "injection", "use", "exists", "assumption",
    "solve_by_elim", "any_goals", "first", "repeat", "try", "skip",
    "done", "fail_if_success", "nomatch", "classical", "infer_instance",
    "congr", "simp_all", "simp only", "intro", "observe",
}
BOOL = {"true", "false"}
SORRY = {"sorry", "admit"}
SPECIAL_TYPES = {"\u2115", "\u2102", "\u211d"}  # N C R

DEF_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|coinductive)"
    r"\s+([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)"
)


def collect_consts():
    consts = set()
    for f in LEAN.glob("*.lean"):
        for line in f.read_text(encoding="utf-8").splitlines():
            m = DEF_RE.match(line)
            if m:
                consts.add(m.group(1))
    return consts


def is_type_start(ch):
    return ch.isupper() or ch in SPECIAL_TYPES


TOKEN_RE = re.compile(
    r"(?P<entity>&(?:#\d+|[A-Za-z]+);)"
    r"|(?P<blockcom>/\-.*?\-/)"
    r"|(?P<linecom>--[^\n]*)"
    r'|(?P<string>"(?:[^"\\\n]|\\.)*")'
    r"|(?P<ident>[^\W\d_][\w']*(?:\.[^\W\d_][\w']*)*)"
    r"|(?P<number>\d[\d_]*)"
    r"|(?P<other>.)",
    re.S,
)


def classify_ident(tok, consts):
    if tok in KW:
        return "tok-kw"
    if tok in TAC or (tok[-1:] in "!?" and tok[:-1] in TAC):
        return "tok-tac"
    if tok in BOOL:
        return "tok-num"
    if tok in SORRY:
        return "tok-sorry"
    if tok in consts or tok in SPECIAL_TYPES:
        return "tok-type"
    if len(tok) == 1 and tok[0].isupper():
        # Single capitals are near-always bound variables in Mathlib style
        # (P, F, U, V, ...), not types. Lowercase locals stay default ink.
        return "tok-var"
    head = tok.split(".")[0]
    if is_type_start(head[0]):
        return "tok-type"
    return None


def highlight_run(text, consts):
    out = []
    for m in TOKEN_RE.finditer(text):
        kind = m.lastgroup
        tok = m.group()
        if kind in ("entity", "other"):
            out.append(tok)
        elif kind in ("blockcom", "linecom"):
            out.append(f'<span class="tok-com">{tok}</span>')
        elif kind == "string":
            out.append(f'<span class="tok-str">{tok}</span>')
        elif kind == "number":
            out.append(f'<span class="tok-num">{tok}</span>')
        else:  # ident
            cls = classify_ident(tok, consts)
            out.append(f'<span class="{cls}">{tok}</span>' if cls else tok)
    return "".join(out)


TAG_RE = re.compile(r"</?[^>]+>")
# Step-number badges must pass through untouched: build.py's norm_code
# strips `<span class="gn">...</span>` only when its content has no tags,
# so tokenizing badge text would break snippet verification.
ATOM_RE = re.compile(r'<span class="gn">[^<]*</span>|</?[^>]+>')


def highlight_pre(inner, consts):
    """Tokenize text runs only; existing tags and gn badges stay byte-identical."""
    out = []
    pos = 0
    for m in ATOM_RE.finditer(inner):
        if m.start() > pos:
            out.append(highlight_run(inner[pos:m.start()], consts))
        out.append(m.group())
        pos = m.end()
    out.append(highlight_run(inner[pos:], consts))
    return "".join(out)


def strip_tok(inner):
    """Remove existing tok spans (innermost first); makes reruns idempotent."""
    pat = re.compile(r'<span class="tok-[a-z]+">([^<]*)</span>')
    while True:
        inner, n = pat.subn(r"\1", inner)
        if n == 0:
            return inner


def main():
    consts = collect_consts()
    print(f"collected {len(consts)} known constants")
    text = MD.read_text(encoding="utf-8")
    n_pre = 0

    def repl(m):
        nonlocal n_pre
        head, inner, tail = m.group(1), m.group(2), m.group(3)
        inner = strip_tok(inner)
        new = highlight_pre(inner, consts)
        if new != inner:
            n_pre += 1
        return head + new + tail

    text = re.sub(r"(<pre[^>]*>)(.*?)(</pre>)", repl, text, flags=re.S)
    MD.write_text(text, encoding="utf-8")
    print(f"highlighted {n_pre} pre blocks")


if __name__ == "__main__":
    main()
