# Lecture Notes — Edge Theorem in Lean 4

Companion notes for the 59-slide Marp deck (`presentation.md`). For every
slide: first its actual content (rewritten as study text, with code and
formulas intact), then explanations, examples, and presenter tips.
**Say** = script material; **Example** = worked detail; **Q&A** = seminar
preparation.

---

## Slide 1 — Edge Theorem in Lean 4 (Lemma 6.1, real case)

**On the slide.** Title, subtitle ("polytopic families and exposed edges"),
author/institute placeholder.

**Notes.** Frame the talk in one minute: one theorem from robust control —
stability of infinitely many polynomials from finitely many edge checks —
plus its machine-checked proof in Lean 4, centering on Lemma 6.1's real case
where all geometric ideas live. Mention the deck's guarantees: every Lean
snippet is verbatim source (checked by `Marp/build.py`), code is
syntax-highlighted. **Say:** "By the end you will know why infinitely many
polynomials reduce to finitely many one-parameter checks — and you will
have seen each step as Lean code."

## Slide 2 — Outline

**On the slide.** Eight parts: 1 Background; 2 Preliminaries; 3 Exposed
faces and edges; 4 Edge Theorem; 5 Lemma 6.1 real case + complex extra;
6 Lemma 6.2 real case + helper + complex extra; 7 Edge Theorem assembled;
8 Future work.

**Notes.** Walk it briskly; the point is the arc (motivation → toolkit →
theorem + proofs → assembly). Tell the room the technical core is parts 5–6
and the payoff is part 7.

## Slide 3 — What is a control system?

**On the slide.** "A **control system** manages, commands, directs, or
regulates the behavior of other devices or systems using control loops —
from simple applications like a home thermostat to complex industrial
processes."

**Notes.** Ground non-control listeners: thermostat (single on/off loop)
vs industrial plant (thousands of coupled loops). Stress *regulates* —
guaranteeing regulation *despite plant uncertainty* is the whole motive for
robust stability, i.e. everything after this slide.

## Slide 4 — From state-space to transfer function

**On the slide.** From $\dot{x} = Ax + Bu$, $y = Cx + Du$ with $x(0) = 0$:
(1) Laplace transform: $sX(s) = AX(s) + BU(s)$, $Y(s) = CX(s) + DU(s)$;
(2) $(sI - A)X(s) = BU(s)$, so $X(s) = (sI-A)^{-1}BU(s)$; (3) substitute:
$Y(s) = C(sI-A)^{-1}BU(s) + DU(s)$; (4) boxed
$G(s) = \frac{Y(s)}{U(s)} = C(sI-A)^{-1}B + D$.

**Notes.** The $x(0) = 0$ assumption is what makes $G(s)$ well-defined —
flag it, someone always asks. Note $(sI-A)^{-1} =
\mathrm{adj}(sI-A)/\det(sI-A)$: poles = roots of $\det(sI-A)$, previewing
the characteristic-polynomial viewpoint. **Example:** for scalar
$a,b,c,d$ the formula collapses to $G(s) = cb/(s-a) + d$.

## Slide 5 — Example: mass-spring-damper

**On the slide.** $m = 1\,\mathrm{kg}$, $c = 2$, $k = 3$; $u(t)$ force,
$y(t)$ displacement; $m\ddot{y} + c\dot{y} + ky = u(t)$, i.e.
$\ddot{y} + 2\dot{y} + 3y = u(t)$; states $x_1 = y$, $x_2 = \dot{y}$;
$A = [[0,1],[-3,-2]]$, $B = [0,1]^T$, $C = [1,0]$, $D = 0$; boxed
$G(s) = [1\ 0]\,\frac{1}{s^2+2s+3}\!\begin{bsmallmatrix}s+2&1\\-3&s\end{bsmallmatrix}\![0\ 1]^T
= \frac{1}{s^2+2s+3}$.

**Notes.** States = "the system's memory needs both position and velocity."
Work the adjugate on the board if asked: $[1\ 0]\cdot(\cdot)\cdot[0\ 1]^T$
picks entry $(1,2)$ of the adjugate, i.e. $1$. This $G(s)$ recurs on Slides
6 (poles) and 8 (as a stable example to contrast).

## Slide 6 — Poles and stability

**On the slide.** Criterion quote (stable ⟺ all poles strictly negative
real parts; unstable if some pole has positive real part); formal
**Definition (Hurwitz stability):** $p(s)$ (resp. $G(s)$) is Hurwitz stable
iff every root (resp. pole) satisfies $\mathrm{Re}(s) < 0$; worked example
$G(s) = 1/(s^2+2s+3)$, $s = \frac{-2\pm\sqrt{-8}}{2} = -1 \pm j\sqrt{2}$,
real parts $-1 < 0$ ⇒ stable.

**Notes.** Name the definition (Hurwitz = strictly left), use engineering
$j$, do the quadratic formula aloud once. **Q&A:** poles exactly on the
axis = marginal stability (neither, by design — matches the `frontier`
reasoning later, which needs strictness).

## Slide 7 — Kharitonov's theorem

**On the slide.** Interval family:

$\mathcal{P} = \{p(s) = a_n s^n + \cdots + a_1 s + a_0 \mid a_i \in [\underline{a}_i, \bar{a}_i],\ \bar{a}_n > 0\}$

Four vertex polynomials (min/max alternating every two coefficients):

- $K_1 = \underline{a}_n s^n + \underline{a}_{n-1}s^{n-1} + \bar{a}_{n-2}s^{n-2} + \bar{a}_{n-3}s^{n-3} + \cdots$
- $K_2 = \bar{a}_n s^n + \bar{a}_{n-1}s^{n-1} + \underline{a}_{n-2}s^{n-2} + \underline{a}_{n-3}s^{n-3} + \cdots$
- $K_3 = \underline{a}_n s^n + \bar{a}_{n-1}s^{n-1} + \bar{a}_{n-2}s^{n-2} + \underline{a}_{n-3}s^{n-3} + \cdots$
- $K_4 = \bar{a}_n s^n + \underline{a}_{n-1}s^{n-1} + \underline{a}_{n-2}s^{n-2} + \bar{a}_{n-3}s^{n-3} + \cdots$

Boxed: $\mathcal{P}$ Hurwitz stable $\iff K_1$–$K_4$ each Hurwitz stable.

Example paragraph: primary $m_1,k_1,c_1$ + TMD $m_2,k_2,c_2$ in intervals give fourth-order $p(s) = a_4s^4 + \cdots + a_0 = 0$ with $a_i \in [\underline{a}_i,\bar{a}_i]$; plus the TMD schematic figure (vertical wall–$k_1$/$c_1$–$m_1$–$k_2$/$c_2$–$m_2$ with $u(t)$/$y(t)$ arrows and blue braces).

**Notes.** Emphasize the pattern is *not* "all 16 corners" — the alternating
min/max is the whole trick. Where such boxes come from: manufacturing
tolerances on physical parameters. **Say:** "Four checks replace infinitely
many — but only for boxes, only for the half-plane, only fixed degree.
Watch those qualifications." The TMD figure (wall–$k_1$/$c_1$–$m_1$–$k_2$/$c_2$–$m_2$,
blue braces) is worth 20 seconds of pointing.

## Slide 8 — Kharitonov vs Edge Theorem (discrete systems)

**On the slide.** Left — why Kharitonov fails: half-plane trick only (no
even/odd symmetry on the unit circle); transforming tangles intervals into
a polytope; real models are dependent anyway. Right — verified
counterexample: $p(z) = a_3z^3+a_2z^2+a_1z+a_0$ on
$a_0{\in}[-0.2,0.5]$, $a_1{\in}[0.3,0.5]$, $a_2{\in}[0.6,1.3]$,
$a_3{\in}[0.9,1.2]$; all four $K_i$ Schur stable (max moduli $0.83, 0.79,
0.98, 0.82$); but vertex $0.9z^3+1.3z^2+0.3z+0.5$ has a root of modulus
$1.47$ — unstable. Takeaway line on polytopes vs intervals.

**Notes.** Stress the numbers were found by search and checked directly —
"four green lights, system unstable." **Q&A:** "Does *some* finite vertex
set work for Schur?" — yes, larger Schur-type vertex sets exist in the
literature, but no 4-corner test; the Edge Theorem takes the geometric
route instead.

## Slide 9 — The Edge Theorem at work (discrete)

**On the slide.** Theorem box (Bartlett–Hollot–Lin 1988): fixed-degree
polytope $\Omega$; $\partial R(\Omega) \subseteq \bigcup_E R(E)$; stability
iff edges stable; edges are one-parameter families
$a(\lambda) = (1-\lambda)a^{(1)} + \lambda a^{(2)}$. Worked Ex. 6.2 in plain
words: box, 12 corner-joining edges, disc, robust Schur stability; plus the
two-panel figure (3D coefficient box colored by varying coefficient; unit
disc with all 12 computed edge root loci, max $|z| = 0.50$).

**Notes.** Point at the margin in the figure — the loci stay *well* clear
of the circle; that visible gap is the robustness margin (damping ratios,
stability degree read off from it). This slide pays off the whole intro:
"twelve checks replace the infinite family — with a picture, not just yes/no."

## Slide 10 — Section 1 · Preliminaries

**On the slide.** Divider only.

**Notes.** "The toolkit — five definitions we will use everywhere."

## Slide 11 — Polytopic family of polynomials

**On the slide.** $P(s) = \lambda_1P_1(s) + \cdots + \lambda_nP_n(s)$,
$\lambda_i \ge 0$, $\sum\lambda_i = 1$; **Definition (Polytope):**
$\Omega = \mathrm{conv}\{v_1,\dots,v_N\}$, compact and convex (converse
fails); $\dim\Omega := \dim\mathrm{aff}(\Omega)$.

**Notes.** A polytope is finitely-generated convexity. Counterexample for
the converse: the closed disc (compact convex, not a polytope). Dimension =
affine dimension — plant this, Steps 2–5 are Grassmann arithmetic on it.

## Slide 12 — Coefficient vectors (`CoeffVec`)

**On the slide.** Restatement ($\delta(s) \leftrightarrow
\underline\delta \in \mathbb{R}^{n+1}$); Lean:
```lean
abbrev CoeffVec (n : ℕ) := Fin (n + 1) → ℝ
```
```lean
/-- Convert a coefficient vector α : Fin(n+1) → ℝ to a polynomial
    δ(s) = α(0) + α(1)·s + ... + α(n)·sⁿ -/
noncomputable def polyOfVec {n : ℕ} (α : CoeffVec n) : Polynomial ℝ :=
  ∑ j : Fin (n + 1), Polynomial.monomial j.val (α j)
```
Example $n = 2$: `CoeffVec 2` = `Fin 3 → ℝ`; $\alpha = (1,-2,3)$ gives
`polyOfVec α = 1 + (-2)·s + 3·s²`, i.e. $3s^2-2s+1$ (plus a comment block
recording exactly this).

**Notes.** This identification turns polynomial questions into geometry in
$\mathbb{R}^{n+1}$ — "coefficient space" from here on. **Q&A:** `Fin`
instead of tuples so the dimension is a parameter Lean computes with
(`finrank_CoeffVec`), needed by the dimension counts.

## Slide 13 — Polytope: Lean formalization

**On the slide.** Lean:
```lean
structure Polytope (n : ℕ) where
  vertices : Finset (CoeffVec n)
  nonempty  : vertices.Nonempty
  interior_nonempty : (interior (convexHull ℝ (vertices : Set (CoeffVec n)))).Nonempty

/-- The actual set Ω ⊆ ℝ^{n+1} as the convex hull of the vertices. -/
def Polytope.Ω (P : Polytope n) : Set (CoeffVec n) :=
  convexHull ℝ (P.vertices : Set (CoeffVec n))
```
Assumption box (nonempty interior always assumed); pentagon figure (convex
pentagon $v_1$–$v_5$ with an interior point as convex combination).

**Notes.** The nonempty-interior requirement is *not* in textbooks but the
formalization needs it: it forces $\mathrm{aff}\,\Omega$ full-dimensional,
which every dimension count relies on. Point at the interior point in the
figure while saying it.

## Slide 14 — Affine span, direction, dimension — definition

**On the slide.** Affine set closed under lines ($A = p+V$);
$\mathrm{aff}(S)$ smallest affine superset; $\mathrm{dir}(A)$ translation
subspace; $\dim$ via bases ($0$ point, $1$ line, $2$ plane).

**Notes.** Running example: two points span a line, three non-collinear a
plane. Everything in Steps 2–5 is arithmetic on these numbers.

## Slide 15 — Affine span, direction, dimension — Lean

**On the slide.** Lean:
```lean
abbrev meetDir (n : ℕ) (U : Submodule ℝ (CoeffVec n))
    (affΩ : AffineSubspace ℝ (CoeffVec n)) : Submodule ℝ (CoeffVec n) :=
  (affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction

noncomputable abbrev dim {M : Type*} [AddCommGroup M] [Module ℝ M]
    (U : Submodule ℝ M) : ℕ :=
  Module.finrank ℝ U
```
i.e. `meetDir` = direction of $\mathrm{aff}(U \cap \mathrm{aff}\,\Omega)$,
`dim` = finrank.

**Notes.** Read `meetDir` as "the directions along which we can still
travel" — it appears in every escape step.

## Slide 16 — Supporting hyperplane

**On the slide.** $H = \{f = c\}$ supports convex $\Omega$ iff $f \le c$ on
$\Omega$ and $f(x_0) = c$ somewhere; exposed set $\Omega \cap H$. Example:
$f(x,y) = -y$, $c = 0$ ($x$-axis), exposed set = bottom edge.

**Notes.** The bottom edge is the mental model for every "exposed" object
later: a flat touching the body from outside.

## Slide 17 — Supporting hyperplane: Lean

**On the slide.** Full structure:
```
structure SupportingHyperplane (P : Polytope n) where
  f : CoeffVec n →ₗ[ℝ] ℝ
  c : ℝ
  nonzero : f ≠ 0
  upper_bound : ∀ x ∈ P.Ω, f x ≤ c
  touches : ∃ x ∈ P.Ω, f x = c
```

**Notes.** Read as a checklist; *nonzero* does real work (rules out
$0 = 0$), and proving it for the Hahn–Banach functional is a genuine later
step (4.4).

## Slide 18 — Root spaces (divider)

**On the slide.** Divider only. "From geometry back to polynomials."

## Slide 19 — Root space — definition

**On the slide.** Notation ($\mathrm{polyOfVec}(\delta)(s) = \delta_0 +
\cdots + \delta_n s^n$); **Definition (Root space):** $R(W) = \{s \in
\mathbb{C} \mid \exists\,\delta \in W,\ \delta(s) = 0\}$, $R(P) := R(P.\Omega)$;
Lean:
```lean
def RootSpaceSet {n : ℕ}
  (W : Set (CoeffVec n)) : Set ℂ :=
  { s | ∃ δ ∈ W,
      ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s }

/-- The root space of a polytope `P`: all complex numbers `s` such that
some coefficient vector in `P.Ω` yields a polynomial vanishing at `s`. -/
def RootSpace (P : Polytope n) : Set ℂ :=
  RootSpaceSet P.Ω
```

**Notes.** Existential = projection: $s$ qualifies if *some* member
vanishes there. **Example:** $s^2+1$ and $s^2-2s+1$ contribute
$\{i,-i\} \cup \{1\}$.

## Slide 20 — Exposed faces and edges (divider)

**On the slide.** Divider only. "The boundary actors."

## Slide 21 — Boundary and exposed faces — definition

**On the slide.** Closure/boundary ($\partial S = \bar S \setminus
\mathrm{int}(S)$); intrinsic interior/relative boundary ($\mathrm{relint}$
= interior within the flat; $S \setminus \mathrm{relint}$); exposed
$F = \Omega \cap H$; edge = dim 1, face = dim 2; Lean pointer.

**Notes.** Relative interior = deep inside the *face*, not the room —
Lemma 6.2 lives entirely here; flag it early.

## Slide 22 — Boundary and exposed faces — Lean

**On the slide.** Lean (`EdgeTheoremDefs.lean:140-151`):
```lean
/-- The exposed face of `P` for `hp`: `F = Ω ∩ {x | hp.f x = hp.c}`. -/
def ExposedFace {n : ℕ} {P : Polytope n} (hp : SupportingHyperplane P) :
    Set (CoeffVec n) :=
  { x | x ∈ P.Ω ∧ hp.f x = hp.c }

open Affine

/-- `E` is an exposed edge of `P` if it is an exposed face of affine dimension 1. -/
def IsExposedEdge {n : ℕ} (P : Polytope n) (E : Set (CoeffVec n)) : Prop :=
  ∃ hp : SupportingHyperplane P,
    E = ExposedFace hp ∧
    Module.finrank ℝ (affineSpan ℝ (ExposedFace hp)).direction = 1
```

**Notes.** The formalization's dialect: geometry as sets, dimension as
`finrank`.

## Slide 23 — Boundary and exposed edge — example

**On the slide.** Disc ($\partial S = \{|s|=1\}$, ball about a rim point
hits both sides) and unit square with bottom edge exposed by $\{y=0\}$.

**Notes.** Fallback pictures for lost listeners: every abstract step has a
square analogue (slice = line, escape = walk to edge, face = the edge).

## Slide 24 — Edge Theorem (divider)

**On the slide.** Divider only. "All tools assembled."

## Slide 25 — Assumption 6.1

**On the slide.** Leading coefficient keeps its sign on $\Omega$
($\delta_n > \Delta > 0$); assumed by everything below.

**Notes.** Without it the degree could drop and roots escape to infinity —
root spaces would jump. In Lean it is the explicit `hleading` hypothesis
wherever the complex case needs it.

## Slide 26 — Lemmas 6.1–6.2 — statements

**On the slide.** Full statements: **Lemma 6.1.** Let $\Omega \subset
\mathbb{R}^{n+1}$ be a polytope satisfying Assumption 6.1. Then (1) if
$s_r \in \mathbb{R}$ and $s_r \in R(\Omega)$, then $\exists$ an exposed edge
$E$ of $\Omega$ with $s_r \in R(E)$; (2) if $s_c \in \mathbb{C}$ and $s_c \in
R(\Omega)$, then $\exists$ an exposed face $F$ of $\Omega$ with $s_c \in R(F)$.
**Lemma 6.2.** For any exposed face $F$ of $\Omega$,
$\partial R(F) \subseteq R(\partial F)$.

**Notes.** Read both aloud slowly — the talk's load-bearing statements:
6.1 sorts roots by kind, 6.2 pushes face-boundary roots onto smaller faces.

## Slide 27 — Edge Theorem — statement

**On the slide.** $\partial R(\Omega) \subseteq \bigcup_{E} R(E)$ over
exposed edges, under Assumption 6.1.

**Notes.** Translate: where roots can *first* go unstable is on the edges —
the testable form (infinite family, finitely many checks).

## Slide 28 — Edge Theorem — proof outline

**On the slide.** Three assembly steps: (1) **Lemma 6.1.** Every $s \in
R(\Omega)$ lies in $R(F)$ for some exposed face $F$; if $s = s_r \in
\mathbb{R}$ then $F = E$ can be taken to be an exposed edge. (2) **Lemma
6.2.** For $F$ exposed, $\partial R(F) \subseteq R(\mathrm{rel}\,\partial F)$:
a boundary root of a face is already a root on its relative boundary.
(3) **Descent.** Let $s \in \partial R(\Omega)$: by (1), $s \in R(F_0)$;
while $s \in \partial R(F_k)$, (2) moves the root to $R(F_{k+1})$,
$F_{k+1} \subsetneq F_k$, so dimensions drop strictly and the process ends
at an exposed edge $E$ with $s \in R(E)$. Together:
$\partial R(\Omega) \subseteq \bigcup_E R(E)$.

**Notes.** Roadmap for Sections 4–5; ask the room to keep it visible
mentally throughout.

## Slide 29 — Section 4 · Proof of Lemma 6.1, real case

**On the slide.** Divider only. "The core — six steps, each as Lean beside
its meaning."

## Slide 30 — Lemma 6.1 (real case) — proof overview

**On the slide.** Lemma restatement (real $s_r \in R(\Omega)$ → exposed edge
$E \ni s_r$; complex $s_c \in R(\Omega)$ → exposed face $F \ni s_c$) plus six
detailed steps: (1) **Unpack the root.** From $s \in R(\Omega) = \{s \mid
\exists\,\delta \in \Omega,\ \tilde P_\delta(s) = 0\}$ with $\mathrm{Im}(s) =
0$, obtain $\delta \in \Omega$ with $\tilde P_\delta(s) = 0$; write $s =
\bar{r}$ ($r = \mathrm{Re}(s)$), so $P_\delta(r) = 0$, i.e. $\delta \in
\ker(\mathrm{ev}_r) = P_{s_r}(r)$, a real slice of dimension $n$. (2)
**Dimension count.** For $U = P_{s_r}$, $A = \mathrm{aff}\,\Omega$ with
$\dim U = n$, $\dim\mathrm{dir}(A) \ge 2$: with $V = \mathrm{dir}(A)$,
$\dim(U \cap V) = \dim U + \dim V - \dim(U+V) \ge n + 2 - (n+1) = 1$, so
$\dim\mathrm{dir}(\mathrm{aff}(U \cap A)) \ge 1$. (3) **Escape to the
boundary.** The positive-dimensional direction yields $v \neq 0$ in
$U \sqcap \mathrm{dir}(A)$; $\delta + tv$ stays in the slice, boundedness
forces an exit point, so $[\delta, \delta + t_{\mathrm{out}}v]$ meets
$\partial\Omega$ at $\delta_{\mathrm{bound}} \in U \cap \partial\Omega$.
(4) **Exposed face.** At $\delta_{\mathrm{bound}} \in \mathrm{frontier}
\setminus \mathrm{int}$, geometric Hahn–Banach for the convex open
$\mathrm{int}\,\Omega$ gives nonzero continuous linear $f$ with $f <
f(\delta_{\mathrm{bound}})$ on the interior; $F = \Omega \cap \{f = c\}$
is exposed, contains $\delta_{\mathrm{bound}}$, carries $(r:\mathbb{C}) \in
R(F)$. (5) **Descend.** From $(r:\mathbb{C}) \in R(F)$, $\dim \ge 2$:
extract $\delta_F \in F \cap P_{s_r}$, escape to a relative-boundary point,
pass to a proper exposed subface $G$ with $\dim G < \dim F$; recurse until
$\dim = 1$ (edge) or $0$ (singleton + edge through it). (6) **Degenerate
cases.** $m = 0$ contradicts nonempty interior; $m = 1$ makes $\Omega$
itself the edge.

**Notes.** Itinerary, not content — promise to return. Plant the mantra:
*everything happens inside the root slice*.

## Slide 31 — Step 1: Unpack the root

**On the slide.** Claim ($s = \bar r$, $\delta \in P_{s_r}(r)$) plus proof
($s \in R(\Omega)$ gives $\delta$; $\mathrm{Im}(s) = 0$ gives $s = \bar r$
by `Complex.ext`; root at $\bar r$ reads $P_\delta(r) = 0$) plus:
```lean
theorem lemma61_real (hn : n ≥ 1) (P : Polytope n) (s : ℂ) (hs : s ∈ RootSpace P) :
    s.im = 0 → ∃ E, IsExposedEdge P E ∧ s ∈ RootSpaceSet E := by
  intro hreal
  -- 1.1: s ∈ R(Ω) gives δ ∈ Ω with root
  unfold RootSpace RootSpaceSet at hs
  obtain ⟨δ, hδ_in_Ω, hδ_root⟩ := hs
  -- 1.2: Im(s) = 0 gives s = ↑r
  have hs_real : s = ↑s.re := by
    apply Complex.ext
    · simp
    · simp [hreal]
  -- 1.3: root at ↑r means δ ∈ P_sr(r)
  have hδ_in_Psr : δ ∈ (P_sr n s.re : Set (CoeffVec n)) := by
    rw [hs_real] at hδ_root
    exact mem_P_sr_of_isRoot s.re δ hδ_root
```
Map: 1.1 unpacks the existential ($s \in R(\Omega)$ gives $\delta \in
\Omega$ with $\tilde P_\delta(s) = 0$); 1.2 `Complex.ext`
($\mathrm{Im}(s)=0$ gives $s = \bar{r}$ with $r = \mathrm{Re}(s)$); 1.3
lands in the slice (root at $\bar{r}$ gives $P_\delta(r) = 0$, i.e.
$\delta \in P_{s_r}(r)$).

**Notes.** The slice is a hyperplane (one condition) — that "codimension 1"
drives Step 2.

## Slide 32 — Step 2: Dimension count

**On the slide.** Claim: let $U$ be linear with $\dim U = n$,
$\mathrm{aff}\,\Omega$ affine with $\dim(\mathrm{dir}(\mathrm{aff}\,\Omega))
\ge 2$, and $\delta \in U \cap \mathrm{aff}\,\Omega$; then
$\dim(\mathrm{meetDir}) \ge 1$. Proof: 2.1 $\mathrm{meetDir} =
\mathrm{dir}(\mathrm{aff}(U \cap \mathrm{aff}\,\Omega))$ by definition; 2.2
$\mathrm{Aint} = U \sqcap \mathrm{aff}\,\Omega$; 2.3
$\mathrm{dir}(\mathrm{Aint}) = U \cap \mathrm{dir}(\mathrm{aff}\,\Omega)$
($U$ as an affine subspace has direction $U$); 2.4 $\mathrm{aff}(U \cap
\mathrm{aff}\,\Omega) = \mathrm{Aint}$; 2.5 hence $\dim(\mathrm{meetDir}) =
\dim(U \cap \mathrm{dir}(\mathrm{aff}\,\Omega))$; 2.6 $\dim(U \cap V) = \dim
U + \dim V - \dim(U+V) \ge n + 2 - (n+1) = 1$. Map rows 2.1–2.6 say the same
step by step, ending with the Grassmann computation. Plus:
```lean
lemma intersection_affine_dim_ge_one {n : ℕ} (U : Submodule ℝ (CoeffVec n))
    (affΩ : AffineSubspace ℝ (CoeffVec n))
    (δ : CoeffVec n) (hδU : δ ∈ U) (hδΩ : δ ∈ affΩ)
    (hU_dim : dim U = n) (haff_dim : dim affΩ.direction ≥ 2) :
    dim (meetDir n U affΩ) ≥ 1 := by
  -- 2.1: unfold meetDir
  unfold meetDir
  -- 2.2: the infimum of affine subspaces
  let Aint : AffineSubspace ℝ (CoeffVec n) := U.toAffineSubspace ⊓ affΩ
  -- 2.3: its direction is the intersection
  have hA_dir : Aint.direction = U ⊓ affΩ.direction :=
    intersection_direction_eq U affΩ δ hδU hδΩ
  -- 2.4: spanning the intersection gives back the infimum
  have hA_eq : affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n))) = Aint := by
    rw [affineSpan_inter U affΩ]
  -- 2.5-2.6: rewrite + Grassmann rank computation
  rw [hA_eq, hA_dir]
  exact finrank_inf_ge_one U affΩ.direction hU_dim haff_dim
```

**Notes.** "Two big subspaces of a small room overlap in at least a line —
that line is our escape route." Grassmann:
$\dim(U\cap V) = n + 2 - (n+1) = 1$.

## Slide 33 — Step 3: Escape (master lemma)

**On the slide.** Claim: polytope $\Omega$, linear $U$, $\delta \in \Omega
\cap U$ with $\dim(\mathrm{meetDir}) \ge 1$ ⇒ $\exists\,\delta_{\mathrm{bound}}
\in U \cap \partial\Omega$. Proof: $\dim \ge 1$ gives $v \neq 0$;
$\delta + tv \in U$ (subspace) and $\in \mathrm{aff}\,\Omega$ (affine line
stays); compact ⇒ bounded with radius $C$, $t_{\mathrm{out}} = (|C|+1)/|v|$
escapes; the segment meets $\partial\Omega$; rewriting gives
$\delta_{\mathrm{bound}} = \delta + (c\cdot t_{\mathrm{out}})v \in U \cap
\partial\Omega$. Formal map: ① nontrivial direction gives $v \neq 0$; ② line
stays in $U \cap \mathrm{aff}\,\Omega$; ③ $t_{\mathrm{out}} > 0$ escapes
(distance $\|C\|+1 > C$); ④ segment meets $\partial\Omega$ (else two disjoint
opens disconnect it); ⑤ witness on the line ⇒ in $U$ and in $\partial\Omega$.
Plus the five-box proof: ① nontrivial direction gives $v \ne 0$; ② the line
$\delta + tv$ stays in $U \cap \mathrm{aff}\,\Omega$; ③ boundedness gives
$t_{\mathrm{out}} = (|C|+1)/\|v\|$ outside; ④ segment meets $\partial\Omega$
(or $\delta$ was there); ⑤ rewriting puts the witness on the line, hence
in $U$.
```lean
lemma exists_boundary_point_in_submodule {n : ℕ} (P : Polytope n)
    (U : Submodule ℝ (CoeffVec n)) (δ : CoeffVec n)
    (hδ_in_Ω : δ ∈ P.Ω) (hδ_in_U : δ ∈ (U : Set (CoeffVec n)))
    (affΩ : AffineSubspace ℝ (CoeffVec n)) (hδ_aff : δ ∈ affΩ)
    (hA_dim : dim (meetDir n U affΩ) ≥ 1) :
    ∃ δ_bound, δ_bound ∈ (U : Set (CoeffVec n)) ∩ frontier P.Ω := by
  -- ① dimension ≥ 1 makes U ⊓ dir nontrivial → v ≠ 0
  have h_dim_pos : 0 < dim (meetDir n U affΩ) := by omega
  haveI : Nontrivial ↥(U ⊓ affΩ.direction) :=
    intersection_nontrivial U affΩ δ hδ_in_U hδ_aff h_dim_pos
  obtain ⟨v_sub, hv_sub_nonzero⟩ := exists_ne (0 : ↑(U ⊓ affΩ.direction))
  -- ② the line stays in U ∩ affΩ
  let v : CoeffVec n := v_sub.val
  have h_line_in_intersection : ∀ (t : ℝ), δ + t • v ∈ (U : Set (CoeffVec n)) ∩
      (affΩ : Set (CoeffVec n)) :=
    line_in_intersection U affΩ δ hδ_in_U hδ_aff v_sub
  -- ③ boundedness gives an exit time
  have hv_nonzero : v ≠ 0 := by
    intro h; apply hv_sub_nonzero; exact Submodule.coe_eq_zero.mp h
  have h_escapes : ∃ (t : ℝ), 0 < t ∧ δ + t • v ∉ P.Ω :=
    ray_escapes_of_bounded P.isBounded δ v hδ_in_Ω hv_nonzero
  obtain ⟨t_out, ht_out_pos, ht_out⟩ := h_escapes
  -- ④ already on the boundary, or the segment meets it
  by_cases hδ_front : δ ∈ frontier P.Ω
  · exact ⟨δ, hδ_in_U, hδ_front⟩
  · obtain ⟨δ_bound, h_seg, h_front⟩ :=
      segment_boundary_intersection P δ hδ_in_Ω hδ_front v hv_nonzero t_out ht_out
  -- ⑤ the witness lies on the line, hence in U
    rw [segment_eq_image] at h_seg
    obtain ⟨c, hc_in_Icc, hc_eq⟩ := h_seg
    have h_rewrite : (1 - c) • δ + c • (δ + t_out • v) = δ + (c * t_out) • v :=
      segment_point_rewrite δ v c t_out
    have h_mem := h_line_in_intersection (c * t_out)
    rcases h_mem with ⟨hmem_U, hmem_aff⟩
    have h_eq : δ_bound = δ + (c * t_out) • v := by
      calc δ_bound = (1 - c) • δ + c • (δ + t_out • v) := by rw [←hc_eq]
        _ = δ + (c * t_out) • v := by rw [h_rewrite]
    exact ⟨δ_bound, h_eq ▸ hmem_U, h_front⟩
```

**Notes.** Do the ③ distance computation on the board
($\mathrm{dist} = t\|v\| = |C|+1 > C$) — the proof's only calculation.

## Slide 34 — `exists_boundary_point_in_submodule` walkthrough

**On the slide.** Goal box (polytope $\Omega$, linear $U$, $\delta \in
\Omega \cap U$, $\dim \ge 1$ ⇒ $\delta_{\mathrm{bound}} \in U \cap
\partial\Omega$) + Proof 3.1–3.5 (nontrivial direction; line in
intersection; escape time with $v \ne 0$ inherited; boundary case split;
rewriting) + full highlighted proof + map: 3.1 `dim ≥ 1` gives nonzero $v$;
3.2 line in $U \cap \mathrm{aff}\,\Omega$; 3.3 $t_{\mathrm{out}} > 0$ escapes;
3.4 segment crosses $\partial\Omega$; 3.5 witness stays in the slice (on the
segment, hence in $U$; in $\partial\Omega$ by 3.4). Full code:
```lean
lemma exists_boundary_point_in_submodule {n : ℕ} (P : Polytope n)
    (U : Submodule ℝ (CoeffVec n)) (δ : CoeffVec n)
    (hδ_in_Ω : δ ∈ P.Ω) (hδ_in_U : δ ∈ (U : Set (CoeffVec n)))
    (affΩ : AffineSubspace ℝ (CoeffVec n)) (hδ_aff : δ ∈ affΩ)
    (hA_dim : dim (meetDir n U affΩ) ≥ 1) :
    ∃ δ_bound, δ_bound ∈ (U : Set (CoeffVec n)) ∩ frontier P.Ω := by
  -- 3.1
  have h_dim_pos : 0 < dim (meetDir n U affΩ) := by omega
  haveI : Nontrivial ↥(U ⊓ affΩ.direction) :=
    intersection_nontrivial U affΩ δ hδ_in_U hδ_aff h_dim_pos
  obtain ⟨v_sub, hv_sub_nonzero⟩ := exists_ne (0 : ↑(U ⊓ affΩ.direction))
  -- 3.2
  let v : CoeffVec n := v_sub.val
  have h_line_in_intersection : ∀ (t : ℝ), δ + t • v ∈ (U : Set (CoeffVec n)) ∩
      (affΩ : Set (CoeffVec n)) :=
    line_in_intersection U affΩ δ hδ_in_U hδ_aff v_sub
  -- 3.3
  have hv_nonzero : v ≠ 0 := by
    intro h; apply hv_sub_nonzero; exact Submodule.coe_eq_zero.mp h
  have h_escapes : ∃ (t : ℝ), 0 < t ∧ δ + t • v ∉ P.Ω :=
    ray_escapes_of_bounded P.isBounded δ v hδ_in_Ω hv_nonzero
  obtain ⟨t_out, ht_out_pos, ht_out⟩ := h_escapes
  -- 3.4
  by_cases hδ_front : δ ∈ frontier P.Ω
  · exact ⟨δ, hδ_in_U, hδ_front⟩
  · obtain ⟨δ_bound, h_seg, h_front⟩ :=
      segment_boundary_intersection P δ hδ_in_Ω hδ_front v hv_nonzero t_out ht_out
  -- 3.5
    rw [segment_eq_image] at h_seg
    obtain ⟨c, hc_in_Icc, hc_eq⟩ := h_seg
    have h_rewrite : (1 - c) • δ + c • (δ + t_out • v) = δ + (c * t_out) • v :=
      segment_point_rewrite δ v c t_out
    have h_mem := h_line_in_intersection (c * t_out)
    rcases h_mem with ⟨hmem_U, hmem_aff⟩
    have h_eq : δ_bound = δ + (c * t_out) • v := by
      calc δ_bound = (1 - c) • δ + c • (δ + t_out • v) := by rw [←hc_eq]
        _ = δ + (c * t_out) • v := by rw [h_rewrite]
    exact ⟨δ_bound, h_eq ▸ hmem_U, h_front⟩
```

**Notes.** Slow lane for Slide 33; the map narrates each box. Skip briskly
if the room followed.

## Slide 35 — `ray_escapes_of_bounded` walkthrough

**On the slide.** Full lemma (A.1.1–A.1.4): bounded radius $C$; witness
$t_{\mathrm{out}} = (|C|+1)/\|v\|$; distance identity via `dist_eq_norm`,
`abel`, `norm_smul`; contradiction $\|C\|+1 \le C \le \|C\|$.
```lean
lemma ray_escapes_of_bounded {n : ℕ} {S : Set (CoeffVec n)}
    (hB : Bornology.IsBounded S) (δ v : CoeffVec n)
    (hδ : δ ∈ S) (hv : v ≠ 0) : ∃ t : ℝ, 0 < t ∧ δ + t • v ∉ S := by
  rcases Metric.isBounded_iff.mp hB with ⟨C, hC⟩
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  refine ⟨(|C| + 1) / ‖v‖, div_pos (by positivity) hv_norm_pos, ?_⟩
  intro h_contra
  -- dist = t‖v‖ = |C|+1 contradicts dist ≤ C
  have ht_nonneg : (0 : ℝ) ≤ (|C| + 1) / ‖v‖ := (div_pos (by positivity) hv_norm_pos).le
  have h_dist : dist (δ + ((|C| + 1) / ‖v‖) • v) δ = ((|C| + 1) / ‖v‖) * ‖v‖ := by
    rw [dist_eq_norm]
    have h_sub : δ + ((|C| + 1) / ‖v‖) • v - δ = ((|C| + 1) / ‖v‖) • v := by abel
    rw [h_sub, norm_smul, Real.norm_eq_abs _,
      abs_of_nonneg ht_nonneg]
  have h_le : dist (δ + ((|C| + 1) / ‖v‖) • v) δ ≤ C := hC h_contra hδ
  have h_t_mul : ((|C| + 1) / ‖v‖) * ‖v‖ = |C| + 1 :=
    div_mul_cancel₀ _ (ne_of_gt hv_norm_pos)
  rw [h_dist, h_t_mul] at h_le
  have : C ≤ |C| := le_abs_self C
  linarith
```
Map: A.1.1 boundedness gives radius $C$ ($\mathrm{dist} \le C$ on $S$);
A.1.2 $t_{\mathrm{out}} = (\|C\|+1)/\|v\| > 0$ witnesses the existential;
A.1.3 four facts — (i) $t \ge 0$ (quotient of positives), (ii)
$\mathrm{dist} = t\|v\|$ (norm of difference, cancel, pull out scalar),
(iii) $\mathrm{dist} \le C$ (boundedness applied), (iv) $t\|v\| = \|C\|+1$
(cancellation); A.1.4 $\|C\|+1 \le C \le \|C\|$, impossible.

**Notes.** "Bounded ⇒ escapable, computably": the exit time is an explicit
formula, a selling point of the formalization.


Nothing proves it directly — it's by contradiction. After `refine` supplies the witness $t_{\text{out}} = (|C|+1)/\|v\|$ and its positivity, the remaining goal $\delta + t{\cdot}v \notin S$ (i.e. membership implies `False`) is introduced as `h_contra`. Then: boundedness applied to that assumed member gives $\mathrm{dist} \le C$ (`h_le`), while the computation gives $\mathrm{dist} = |C|+1$ (`h_dist`, `h_t_mul`) — and $|C|+1 \le C \le |C|$ is arithmetic nonsense, so `linarith` derives `False`, discharging the assumption. That `False` *is* the proof of $\notin$.

## Slide 36 — `segment_boundary_intersection` walkthrough

**On the slide.** Claim (off-frontier $\delta$, $v \ne 0$, escaped endpoint
⇒ boundary point on the segment) + Proof (A.2.1 closed + contradiction;
A.2.2 two-opens cover; A.2.3 both opens meet it, disjoint; A.2.4
connectedness forces a point in both — in $\emptyset$) + full lemma code.
Map: A.2.1 assume no segment point hits the frontier, goal becomes `False`;
A.2.2 covered by $\mathrm{int}\,\Omega \cup \mathrm{int}(\Omega^c)$
(`frontier_eq_for_closed`); A.2.3 both opens meet the segment and are
disjoint; A.2.4 `segment_is_connected` forces a point in both — in
$\emptyset$. Full code:
```lean
lemma segment_boundary_intersection {n : ℕ} (P : Polytope n) (δ : CoeffVec n)
    (hδ_in_Ω : δ ∈ P.Ω) (hδ_not_front : δ ∉ frontier P.Ω)
    (v : CoeffVec n) (_hv_nonzero : v ≠ 0) (t_out : ℝ) (ht_out : δ + t_out • v ∉ P.Ω) :
    ∃ δ_bound ∈ segment ℝ δ (δ + t_out • v), δ_bound ∈ frontier P.Ω := by
  -- A.2.4 (connectivity fact first)
  have h_conn : IsConnected (segment ℝ δ (δ + t_out • v)) :=
    segment_is_connected δ v t_out
  -- A.2.1
  have h_closed : IsClosed P.Ω := P.isCompact.isClosed
  by_contra h_no_front
  push_neg at h_no_front
  -- A.2.2
  have h_cover : segment ℝ δ (δ + t_out • v) ⊆ (interior P.Ω) ∪ interior (P.Ωᶜ) :=
    segment_cover_by_interior_and_complement P δ v t_out h_closed h_no_front
  -- A.2.3
  have h_in_u : (segment ℝ δ (δ + t_out • v) ∩ interior P.Ω).Nonempty :=
    segment_intersects_interior P δ v t_out hδ_in_Ω hδ_not_front h_closed
  have h_in_v : (segment ℝ δ (δ + t_out • v) ∩ interior (P.Ωᶜ)).Nonempty :=
    segment_intersects_complement_interior P δ v t_out ht_out h_closed
  have huv_empty : interior P.Ω ∩ interior (P.Ωᶜ) = ∅ :=
    interior_and_complement_interior_disjoint P
  -- A.2.4 (connectedness applied)
  have h_pre := h_conn.2 (interior P.Ω) (interior (P.Ωᶜ)) isOpen_interior isOpen_interior
  have h_inter_nonempty := h_pre h_cover h_in_u h_in_v
  obtain ⟨x, hx_s, hx_uv⟩ := h_inter_nonempty
  rw [huv_empty] at hx_uv
  exact hx_uv
```

**Notes.** The one place topology enters: walking inside→outside you must
cross the doorway. Needs $\Omega$ closed ($\partial\Omega =
\Omega\setminus\mathrm{int}\,\Omega$).

## Slide 37 — Slice wrappers `Psr`/`Psc`

**On the slide.** Two wrapper lemmas (real $U := P_{s_r}$, complex $U :=
P_{s_c}$), each a one-line application of `exists_boundary_point_in_submodule`,
plus doc comment on the complex case; map: A.1 `ray_escapes_of_bounded`
($t_{\mathrm{out}}$ outside $S$); A.2 `segment_boundary_intersection`
(two-opens cover ⇒ $\partial\Omega$ hit); A.3 `_in_Psr` / `_in_Psc` ($U :=
P_{s_r}$ / $P_{s_c}$, this slide).
```lean
lemma exists_boundary_point_in_Psr {n : ℕ} (P : Polytope n) (r : ℝ) (δ : CoeffVec n)
    (hδ_in_Ω : δ ∈ P.Ω) (hδ_in_Psr : δ ∈ PsrSet n r)
    (affΩ : AffineSubspace ℝ (CoeffVec n)) (hδ_aff : δ ∈ affΩ)
    (hA_dim : dim (meetDir n (P_sr n r) affΩ) ≥ 1) :
    ∃ δ_bound, δ_bound ∈ PsrSet n r ∩ frontier P.Ω :=
  exists_boundary_point_in_submodule P (P_sr n r) δ hδ_in_Ω hδ_in_Psr affΩ hδ_aff hA_dim

/-- Complex case (U = P_sc n s): thin wrapper over the generic lemma. -/
lemma exists_boundary_point_in_Psc {n : ℕ} (P : Polytope n) (s : ℂ) (δ : CoeffVec n)
    (hδ_in_Ω : δ ∈ P.Ω) (hδ_in_Psc : δ ∈ PscSet n s)
    (affΩ : AffineSubspace ℝ (CoeffVec n)) (hδ_aff : δ ∈ affΩ)
    (hA_dim : dim (meetDir n (P_sc n s) affΩ) ≥ 1) :
    ∃ δ_bound, δ_bound ∈ PscSet n s ∩ frontier P.Ω :=
  exists_boundary_point_in_submodule P (P_sc n s) δ hδ_in_Ω hδ_in_Psc affΩ hδ_aff hA_dim
```

**Notes.** "Prove once, use twice — real and complex cases share their
escape." Preview: the complex case reuses everything with a thinner slice.

## Slide 38 — Step 4: Exposed face

**On the slide.** Claim: boundary point $\delta_{\mathrm{bound}} \in
\mathrm{frontier}\,P.\Omega \cap \mathrm{PsrSet}\,n\,r$ (i.e.
$P_{\delta_{\mathrm{bound}}}(r) = 0$) with nonempty interior gives exposed
$F \ni \delta_{\mathrm{bound}}$ with $(r:\mathbb{C}) \in R(F)$. Plus the
ten-box proof (4.1 frontier in/out of interior … 4.10 root carried) and map:
4.1 frontier points lie in $\Omega$ but never inside; 4.2 interior convex +
open (Hahn–Banach premises); 4.3 geometric Hahn–Banach gives $f$ with $f <
f(\delta_{\mathrm{bound}})$ on the interior; 4.4 $f \ne 0$ (else $0 < 0$)
and likewise $f_{\mathrm{lin}} \ne 0$; 4.5 $c := f(\delta_{\mathrm{bound}})$;
4.6 $f \le c$ extends to all of $\Omega$; 4.7 assemble $(f, c, \text{nonzero},
\text{upper bound}, \text{touches})$; 4.8 point in face; 4.9 root carried
($P_{\delta_{\mathrm{bound}}}(r) = 0$ certifies $(r:\mathbb{C}) \in R(F)$);
4.10 conclude.
```lean
lemma exists_exposed_face_containing_boundary_point {n : ℕ} (P : Polytope n)
    (r : ℝ) (δ_bound : CoeffVec n)
    (hδ_bound_front : δ_bound ∈ frontier P.Ω)
    (hδ_bound_Psr : δ_bound ∈ PsrSet n r)
    (h_int_nonempty : (interior P.Ω).Nonempty) :
    ∃ F : Set (CoeffVec n), IsExposedFace P F ∧ δ_bound ∈ F ∧ (r : ℂ) ∈ RootSpaceSet F := by
  -- 4.1: frontier point in Ω but never inside
  have hδ_bound_in_Ω : δ_bound ∈ P.Ω := frontier_point_in_Ω P δ_bound hδ_bound_front
  have hδ_bound_not_int : δ_bound ∉ interior P.Ω :=
    frontier_point_not_interior P δ_bound hδ_bound_front
  -- 4.2: int Ω is convex and open (Hahn–Banach premises)
  have h_convex : Convex ℝ P.Ω := convex_convexHull ℝ _
  have h_int_convex : Convex ℝ (interior P.Ω) := h_convex.interior
  have h_int_open : IsOpen (interior P.Ω) := isOpen_interior
  -- 4.3: geometric Hahn–Banach gives the separating functional
  obtain ⟨f, hf_strict⟩ :=
    geometric_hahn_banach_open_point h_int_convex h_int_open hδ_bound_not_int
  -- 4.4: it (and its linear map) is nonzero
  have hf_ne : f ≠ 0 := supporting_func_nonzero P f δ_bound hf_strict h_int_nonempty
  -- 4.5: the level
  let c : ℝ := f δ_bound
  let f_lin : CoeffVec n →ₗ[ℝ] ℝ := f.toLinearMap
  have hf_lin_ne : f_lin ≠ 0 := by
    intro heq
    apply hf_ne
    ext x
    have : f_lin x = 0 := by
      rw [heq]
      simp
    exact this
  -- 4.6: bound extends to all of Ω; 4.7: assemble the hyperplane
  have hc_upper : ∀ x ∈ P.Ω, f_lin x ≤ c :=
    supporting_hyperplane_upper_bound P f c hf_strict h_int_nonempty
  let hp : SupportingHyperplane P := {
    f           := f_lin
    c           := c
    nonzero     := hf_lin_ne
    upper_bound := hc_upper
    touches     := ⟨δ_bound, hδ_bound_in_Ω, rfl⟩
  }
  -- 4.8: the point is in the face; 4.9-4.10: it carries the root
  have hδ_in_face : δ_bound ∈ ExposedFace hp := by
    unfold ExposedFace
    simp only [Set.mem_setOf_eq]
    exact ⟨hδ_bound_in_Ω, rfl⟩
  have hr_in_rootspace : (r : ℂ) ∈ RootSpaceSet (ExposedFace hp) :=
    rootspace_mem_of_eval_zero r δ_bound hδ_bound_Psr (ExposedFace hp) hδ_in_face
  exact ⟨ExposedFace hp, ⟨hp, rfl⟩, hδ_in_face, hr_in_rootspace⟩
```

**Notes.** Compress to "separate, take the level set, it exposes a face
carrying the root" if short on time.

## Slide 39 — Step 5: Descend (1/2)

**On the slide.** Claim: $\Omega \subset \mathbb{R}^{n+1}$ polytope, $n \ge
1$, exposed $F$ with $\dim\mathrm{aff}(F) \ge 2$, $r \in \mathbb{R}$ with
$(r:\mathbb{C}) \in R(F)$ ⇒ exposed edge $E$ with $(r:\mathbb{C}) \in R(E)$.
Code 5.1–5.6 (below) + map: 5.1 $(r:\mathbb{C}) \in R(F)$ gives $\delta_F \in
F$ in the zero set $U$; 5.2 $\dim U = n$, $\dim \ge 2$ give a nonzero
root-preserving direction (Grassmann); 5.3 escape to
$\delta_{\mathrm{bound}} \in F$ on the relative boundary; 5.4 supporting
hyperplane cuts out proper $G \subset F$ ($\dim G < \dim F$); 5.5 witness
keeps vanishing; 5.6 root moves $F \to G$.
```lean
lemma descend_to_exposed_edge {n : ℕ} (hn : n ≥ 1) (P : Polytope n) (r : ℝ)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hs_F : (r : ℂ) ∈ RootSpaceSet F)
    (hF_dim_ge_2 : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 2) :
    ∃ E, IsExposedEdge P E ∧ (r : ℂ) ∈ RootSpaceSet E := by
  let m_F := Module.finrank ℝ (affineSpan ℝ F).direction
  by_cases hm_F_1 : m_F = 1
  · refine ⟨F, isExposedEdge_of_dim_1 hF_exp hm_F_1, hs_F⟩
  · have hm_F_ge_2 : m_F ≥ 2 := by omega
    -- 5.1: unpack δ_F in the slice
    obtain ⟨δ_F, hδ_F_in_F, hδ_F_root⟩ :
      ∃ δ ∈ F, ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot (r : ℂ) := hs_F
    let affF := affineSpan ℝ F
    have hδ_F_Psr : δ_F ∈ PsrSet n r := mem_P_sr_of_isRoot r δ_F hδ_F_root
    -- 5.2: count inside F
    have h_inter_dim : Module.finrank ℝ (meetDir n (P_sr n r) affF) ≥ 1 :=
      intersection_affine_dim_ge_one (P_sr n r) affF δ_F hδ_F_Psr
        (subset_affineSpan ℝ F hδ_F_in_F) (P_sr_dimension r) hm_F_ge_2
    -- 5.3: escape to the relative boundary
    obtain ⟨δ_bound, hδ_bound_inter, hδ_bound_front, hδ_bound_not_relint⟩ :=
      exists_boundary_point_in_face_rootspace P r δ_F F hF_exp hδ_F_in_F hδ_F_Psr h_inter_dim
    -- 5.5 (witness facts before the subface they feed)
    have hδ_bound_in_F : δ_bound ∈ F := hδ_bound_inter.1
    have hδ_bound_Psr : δ_bound ∈ (P_sr n r : Set (CoeffVec n)) := hδ_bound_inter.2
    -- 5.4: proper exposed subface of strictly smaller dimension
    obtain ⟨G, hG_exp, hδ_bound_in_G, hG_dim_lt⟩ :=
      exists_proper_subface_of_boundary_point P F hF_exp δ_bound
        hδ_bound_in_F hδ_bound_front hδ_bound_not_relint hm_F_ge_2
    -- 5.6: the root moves F → G
    have hs_G : (r : ℂ) ∈ RootSpaceSet G :=
      rootspace_mem_of_eval_zero r δ_bound hδ_bound_Psr G hδ_bound_in_G
```

**Notes.** Mention the 5.5-before-5.4 quirk (witness facts precede the
subface they feed). Read map row first ("what"), then code ("how").

## Slide 40 — Step 5: Descend (2/2)

**On the slide.** Code 5.7–5.10 (above) + map: 5.7 dimension drops each
iteration, so the process terminates; 5.8 if $\dim G \ge 2$ recurse on $G$;
5.9 if $\dim G = 1$, $G$ is already an edge ($E = G$); 5.10 if $\dim G = 0$,
$G = \{\delta_{\mathrm{bound}}\}$, take an exposed edge through the vertex
and transfer the root.
```lean
    -- 5.8: recurse while dim ≥ 2
    by_cases hG_dim_ge_2 : Module.finrank ℝ (affineSpan ℝ G).direction ≥ 2
    · exact descend_to_exposed_edge hn P r G hG_exp hs_G hG_dim_ge_2
    -- 5.9: dim 1 is already an edge
    · by_cases hG_dim_1 : Module.finrank ℝ (affineSpan ℝ G).direction = 1
      · refine ⟨G, isExposedEdge_of_dim_1 hG_exp hG_dim_1, hs_G⟩
      -- 5.10: dim 0 is a singleton; take an edge through it
      · have hG_dim_0 : Module.finrank ℝ (affineSpan ℝ G).direction = 0 := by
          have h_not_ge_2 : ¬ Module.finrank ℝ (affineSpan ℝ G).direction ≥ 2 := hG_dim_ge_2
          have h_not_1 : ¬ Module.finrank ℝ (affineSpan ℝ G).direction = 1 := hG_dim_1
          omega
        have hG_single : G = {δ_bound} :=
          exposed_face_dim_zero_singleton G hG_dim_0 δ_bound hδ_bound_in_G
        obtain ⟨E, hE_edge, hδ_in_E⟩ :=
          exists_exposed_edge_of_singleton hn P δ_bound G hG_exp hG_single
        have h_root_E : (r : ℂ) ∈ RootSpaceSet E :=
          rootspace_mem_of_eval_zero r δ_bound hδ_bound_Psr E hδ_in_E
        exact ⟨E, hE_edge, h_root_E⟩
  termination_by Module.finrank ℝ (affineSpan ℝ F).direction
  decreasing_by exact hG_dim_lt
```
(5.7 = the two termination lines.)

**Notes.** Mention the 5.5-before-5.4 quirk (witness facts precede the
subface they feed). Emphasize `termination_by`: dimension drops every
round, so recursion ends — then demo one round on the unit square.

## Slide 41 — Step 6: Degenerate cases

**On the slide.** Claim ($m := \dim\mathrm{aff}(\Omega)$: $m = 0$
impossible, $m = 1$ is the edge) + Proof (D.1 via
`polytope_direction_dim_pos`, D.2 via `polytope_dim1_is_exposed_edge` with
$s = \bar r$ moving the root) plus the ①② code. Map: D.1 ① $m = 0$
contradicts nonempty interior ($\dim \ge 1$); D.2 ② $m = 1$: $\Omega$ itself
the edge, root $\Omega \to E$. Plus:
```lean
  · by_cases hm0 : m = 0
    · have h_pos : Module.finrank ℝ (affineSpan ℝ P.Ω).direction ≥ 1 :=
        polytope_direction_dim_pos P
      omega
    · have hm1 : m = 1 := by omega
      have h_Ω_is_edge : IsExposedEdge P P.Ω :=
        polytope_dim1_is_exposed_edge hn P hm1
      refine ⟨P.Ω, h_Ω_is_edge, ?_⟩
      rw [hs_real]
      exact rootspace_mem_of_eval_zero s.re δ
        (mem_P_sr_of_isRoot s.re δ (by
          rw [← hs_real]
          exact hδ_root)) P.Ω hδ_in_Ω
```

**Notes.** Thirty seconds: closes the $\dim \ge 2$ loophole (D.1
contradiction, D.2 $\Omega$ itself the edge).

## Slide 42 — Lemma 6.1 (real case) — recap

**On the slide.** Five numbered items: (1) Step 1 unpacked $s \in R(\Omega)$
to $\delta \in P_{s_r}(r)$, $s = \bar r$; (2) Step 2 gave $\dim(U \cap
\mathrm{aff}\,\Omega) \ge 1$; (3) Step 3 reached $\delta_{\mathrm{bound}} \in
P_{s_r} \cap \partial\Omega$; (4) Step 4 exposed $F \ni \delta_{\mathrm{bound}}$
with $\bar r \in R(F)$; (5) Step 5 descended $F \to \cdots \to E$ with
$\bar r \in R(E)$, $\dim E = 1$; plus degenerate note ($m = 0$ contradicts
interior, $m = 1$ is the edge).

**Notes.** Checkpoint: have the room recite the chain before Lemma 6.2.

## Slide 43 — Lemma 6.1: complex case — what is extra

**On the slide.** Math column — **Claim.** If $s \in R(\Omega)$ with
$\mathrm{Im}(s) \ne 0$, then $s \in R(F)$ for an exposed face $F$ with
$\dim\mathrm{aff}(F) \le 2$ — a face, not an edge. **Thinner slice.** $U =
\{\delta \mid P_\delta(s) = 0\}$ has dimension $n - 1$: plugging real $r$
gives one equation, non-real $s$ gives two (real and imaginary parts each
zero); each cuts one dimension, so $(n+1) - 2 = n - 1$ vs $n$ real.
**Stronger count.** Grassmann gives $\dim(U \cap \mathrm{dir}\,A) \ge
(n-1) + 3 - (n+1) = 1$: escape needs $\dim\mathrm{dir} \ge 3$ (nonempty
interior gives $\mathrm{aff}\,\Omega = \top$, dim $n+1$) and $n \ge 2$.
**Weaker target.** One condition gives a line to walk to an edge; two give
isolated points that cannot slide — descent stops at dim 2. **New
degenerate case $n = 1$.** Linear $P_\delta(s) = \delta_0 + \delta_1 s$ gives
$\delta_0 + \delta_1 s = 0$; $\delta_1 \ne 0$ ⇒ $s = -\delta_0/\delta_1 \in
\mathbb{R}$, contradiction; $\delta_1 = 0$ violates Assumption 6.1 ($v_1 > 0$
on vertices extends by `convexHull_min`). Lean column —
`P_sc_dimension` ($n \ge 1$, $s.im \ne 0$: slice dim $n-1$, evaluation onto
$\mathbb{C}$ rank 2); `mem_P_sc_of_isRoot`,
`intersection_affine_dim_ge_one_complex` (needs dir dim $\ge 3$),
`exists_boundary_point_in_Psc` (Steps 1–3 in $P_{s_c}$);
`exists_exposed_face_containing_boundary_point_complex` (Step 4);
`descend_to_exposed_face_with_dim` (Step 5 to dim $\le 2$); Assumption 6.1 as
`hleading`, threaded `lemma61_complex_with_dim` → `lemma61_complex` →
`lemma61`, $n = 1$ by positivity (`convexHull_min`).

**Notes.** Key sentence: "one condition gives a line to walk, two give
points that cannot slide." The $n = 1$ argument in full: $s = -\delta_0 /
\delta_1$ is a quotient of reals; $\delta_1 = 0$ contradicts positivity on
vertices, extended by convexity (`convexHull_min`).

## Slide 44 — Section 5 · Lemma 6.2, real case

**On the slide.** Divider only.

**Notes.** "Lemma 6.1 puts roots on faces; Lemma 6.2 pushes face-boundary
roots onto face boundaries — the descent engine."

## Slide 45 — Lemma 6.2 (real case) — overview

**On the slide.** Theorem box: let $F$ be an exposed face of $\Omega$ with
$\dim\mathrm{aff}(F) = 2$; then $\partial R(F) \subseteq R(\partial F)$ —
every boundary point of the root space of $F$ is a root on the relative
boundary (`lemma62`, `Lemma62.lean:1446`). Plus: the Lean proof splits on
`s_star.im = 0` (`by_cases hreal`); the real case (`lemma62_real_case`,
this section) goes through $P_{s_r}$ as in Lemma 6.1; the complex case
(`lemma62_complex_case`) needs the $W$-matrix machinery (later slide).

**Notes.** One-line version: boundary points of a face's root space already
live on the face's relative boundary.

## Slide 46 — Lemma 6.2 (real case) — goal

**On the slide.** Goal box: $F$ exposed with $\dim\mathrm{aff}(F) = 2$,
$s^\star \in \mathrm{frontier}\,R(F)$ real ($\mathrm{Im}(s^\star) = 0$) ⇒
$s^\star \in R(\mathrm{relativeBoundary}\,F)$ (`lemma62_real_case`,
`Lemma62.lean:127`). Proof sketch: 6.1–6.3 $R(F)$ closed so $s^\star \in
R(F)$, $s^\star = \bar r$; 6.4–6.5 unpack $\delta^\star \in F$, split on
relint; 6.6–6.8 escape to $\delta_{\mathrm{bound}} \in F \cap P_{s_r}$ off
relint; 6.9–6.12 transfer root, close Case A identically. Lean:
`relativeBoundary F := F \ intrinsicInterior ℝ F`
(`PreliminaryLemmas.lean:422-423`).

**Notes.** Define `relativeBoundary` aloud and point back to Slide 21 —
everything hinges on it.

## Slide 47 — Walkthrough 6.1–6.6

**On the slide.** Header (`Lemma62.lean:92-124`, 6.1–6.6 highlighted) plus
boxes 6.1 (compact/convex), 6.2 ($s^\star = \bar r$), 6.3 (closed ⇒
membership), 6.4 (unpack $\delta^\star$ into $P_{s_r}$), 6.5 (relint split,
$U,V$ setup), 6.6 (dims $n$/$\ge 2$ ⇒ nonzero
$v$); map rows 6.1–6.6 (see Slide 50 for the full table).
```lean
theorem lemma62_real_case {n : ℕ}  (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2)
    (s_star : ℂ) (hs_star_front : s_star ∈ frontier (RootSpaceSet F)) (hreal : s_star.im = 0) :
    s_star ∈ RootSpaceSet (relativeBoundary F) := by
  -- 6.1
  have hF_compact : IsCompact F := isExposedFace_isCompact P hF_exp
  have hF_convex : Convex ℝ F := isExposedFace_convex P hF_exp
  -- 6.2
  have h_s_star_eq : s_star = (s_star.re : ℂ) := by
    apply Complex.ext <;> simp [hreal]
  -- 6.3
  have h_root_closed : IsClosed (RootSpaceSet F) :=
    rootSpaceSet_isClosed_of_isCompact hF_compact
  have hs_star_in_RF : s_star ∈ RootSpaceSet F := by
    have h_sub : frontier (RootSpaceSet F) ⊆ RootSpaceSet F := by
      calc
        frontier (RootSpaceSet F) ⊆ closure (RootSpaceSet F) := frontier_subset_closure
        _ = RootSpaceSet F := h_root_closed.closure_eq
    exact h_sub hs_star_front
  -- 6.4
  rcases hs_star_in_RF with ⟨δ_star, hδ_star_in_F, hδ_star_root⟩
  have hδ_star_in_Psr : δ_star ∈ PsrSet n s_star.re :=
    mem_P_sr_of_isRoot s_star.re δ_star (by
      rw [h_s_star_eq] at hδ_star_root
      exact hδ_star_root)
  -- 6.5
  by_cases hδ_star_relint : δ_star ∈ intrinsicInterior ℝ F
  · let U : Submodule ℝ (CoeffVec n) := P_sr n s_star.re
    let V : Submodule ℝ (CoeffVec n) := (affineSpan ℝ F).direction
  -- 6.6
    have hU_dim : dim U = n := P_sr_dimension s_star.re
    have hV_dim_ge_2 : dim V ≥ 2 := by rw [hF_dim_2]
    have h_inter_dim_ge_1 : dim (U ⊓ V) ≥ 1 :=
      finrank_inf_ge_one U V hU_dim hV_dim_ge_2
    have h_inter_finrank_pos : 0 < dim (U ⊓ V) := by omega
    have h_inter_nontrivial : Nontrivial ↥(U ⊓ V) :=
      Module.nontrivial_of_finrank_pos h_inter_finrank_pos
    obtain ⟨v_sub, hv_sub_ne⟩ := exists_ne (0 : ↥(U ⊓ V))
    let v : CoeffVec n := v_sub.val
    have hv_ne : v ≠ 0 := by
      intro h; apply hv_sub_ne; exact Subtype.ext h
```

**Notes.** Read map row first ("what"), then code ("how").

## Slide 48 — Walkthrough 6.7–6.9

**On the slide.** Boxes 6.7 (split $v$ into $U$/$V$ parts: `hv_U`, `hv_V`,
`hv_affF_dir`; escape time $t_{\mathrm{out}}$ via `ray_escapes_of_bounded`;
ray-stay set $S$ nonempty at $t = 0$), 6.8 ($S$ closed: continuous ray meets
closed $F$), 6.9 (one-line helper call); map rows: 6.7 $v$ splits into slice
and direction parts, $t_{out}$ escapes $F$, ray-stay set nonempty at $t=0$;
6.8 $S$ closed; 6.9 $S$ bounded above (helper).
```lean
  -- 6.7
    have hv_U : v ∈ U := by
      have h := v_sub.property
      rw [Submodule.mem_inf] at h
      exact h.1
    have hv_V : v ∈ V := by
      have h := v_sub.property
      rw [Submodule.mem_inf] at h
      exact h.2
    have hv_affF_dir : v ∈ (affineSpan ℝ F).direction := hv_V
    obtain ⟨t_out, ht_out_pos, ht_out⟩ :=
      ray_escapes_of_bounded hF_compact.isBounded δ_star v hδ_star_in_F hv_ne
    let S : Set ℝ := {t | 0 ≤ t ∧ δ_star + t • v ∈ F}
    have hS_nonempty : S.Nonempty := ⟨0, ⟨by norm_num, by simpa using hδ_star_in_F⟩⟩
  -- 6.8
    have hS_closed : IsClosed S := by
      have h_cont : Continuous (fun (t : ℝ) => δ_star + t • v) := by
        refine Continuous.add continuous_const ?_
        exact Continuous.smul continuous_id continuous_const
      have h_preimage_closed : IsClosed {t | δ_star + t • v ∈ F} :=
        hF_compact.isClosed.preimage h_cont
      have h_nonneg_closed : IsClosed {t : ℝ | 0 ≤ t} := isClosed_Ici
      have hS_eq : S = {t | δ_star + t • v ∈ F} ∩ {t : ℝ | 0 ≤ t} := by
        ext t; constructor
        · rintro ⟨ht_nonneg, ht_mem⟩; exact ⟨ht_mem, ht_nonneg⟩
        · rintro ⟨ht_mem, ht_nonneg⟩; exact ⟨ht_nonneg, ht_mem⟩
      rw [hS_eq]
      exact h_preimage_closed.inter h_nonneg_closed
  -- 6.9 (the helper call)
    have h_bdd_above : BddAbove S :=
      ray_stay_set_bddAbove hF_convex hδ_star_in_F t_out ht_out_pos ht_out
```

**Notes.** At 6.9, note the one-line call to `ray_stay_set_bddAbove`
(`Lemma62.lean:91-121`) — the boundedness argument factored out as its own
lemma, proved once and reused here.

## Slide 49 — Walkthrough 6.10–6.12

**On the slide.** Boxes 6.10 (supremum $t_1 \in S$; $\delta_{\mathrm{bound}}
= \delta^\star + t_1 v \in F \cap P_{s_r}$ via `add_mem`/`smul_mem`), 6.11
($\delta_{\mathrm{bound}} \notin$ relint; transfer to
$R(\mathrm{relativeBoundary})$; rewrite to $s^\star$), 6.12 (Case A:
$\delta^\star$ itself, same transfer); map rows: 6.10 supremum stays in
closed $S$; 6.11 off relint, root moves; 6.12 $\delta^\star$ itself.
```lean
  -- 6.10
    let t1 := sSup S
    have h_max : t1 ∈ S := by
      simpa [t1] using hS_closed.csSup_mem hS_nonempty h_bdd_above
    rcases h_max with ⟨h_t1_nonneg, h_t1_mem⟩
    let δ_bound : CoeffVec n := δ_star + t1 • v
    have hδ_bound_in_F : δ_bound ∈ F := h_t1_mem
    have hv_in_Psr : v ∈ (P_sr n s_star.re : Set (CoeffVec n)) := hv_U
    have hδ_bound_in_Psr : δ_bound ∈ (P_sr n s_star.re : Set (CoeffVec n)) := by
      dsimp [δ_bound]
      apply Submodule.add_mem (P_sr n s_star.re)
      · exact hδ_star_in_Psr
      · exact Submodule.smul_mem (P_sr n s_star.re) t1 hv_in_Psr
  -- 6.11
    have h_not_relint : δ_bound ∉ intrinsicInterior ℝ F :=
      not_mem_intrinsicInterior_of_escapes_along_direction
        F hF_convex δ_star hδ_star_in_F v hv_ne hv_affF_dir
        S rfl hS_nonempty h_bdd_above
        t1 rfl h_t1_nonneg h_t1_mem
        t_out ht_out_pos ht_out
    have hδ_bound_rel_boundary : δ_bound ∈ relativeBoundary F :=
      ⟨hδ_bound_in_F, h_not_relint⟩
    have h_r_in_RF : (s_star.re : ℂ) ∈ RootSpaceSet (relativeBoundary F) :=
      rootspace_mem_of_eval_zero s_star.re δ_bound hδ_bound_in_Psr (relativeBoundary F) hδ_bound_rel_boundary
    rw [h_s_star_eq]
    exact h_r_in_RF
  -- 6.12 (Case A: δ⋆ already on the relative boundary)
  · have hδ_star_rel_boundary : δ_star ∈ relativeBoundary F :=
      ⟨hδ_star_in_F, hδ_star_relint⟩
    have h_r_in_RF : (s_star.re : ℂ) ∈ RootSpaceSet (relativeBoundary F) :=
      rootspace_mem_of_eval_zero s_star.re δ_star hδ_star_in_Psr (relativeBoundary F) hδ_star_rel_boundary
    rw [h_s_star_eq]
    exact h_r_in_RF
```

**Notes.** Slow down at 6.10 (the supremum — subtlest box).

## Slide 50 — Proof map (1/2)

**On the slide.** Full table: 6.1 $F$ compact and convex; 6.2 $s^\star =
\bar r$; 6.3 $R(F)$ closed ⟹ $s^\star \in R(F)$; 6.4 $\delta^\star \in F \cap
P_{s_r}(r)$; 6.5 Case A (off relint) vs Case B (escape); 6.6 $U \sqcap V$
nontrivial → nonzero $v$; helpers row (Step-2 formula `finrank_inf_ge_one`
+ ray escape `ray_escapes_of_bounded`).

**Notes.** Reference during questions on the opening half.

## Slide 51 — Proof map (2/2)

**On the slide.** Full table: 6.7 direction split, escape time, ray-stay
set; 6.8 $S$ closed (preimage ∩ `Ici`); 6.9 $S$ bounded above by $t_{out}$
(helper `ray_stay_set_bddAbove`); 6.10 supremum gives
$\delta_{\mathrm{bound}} \in F \cap P_{s_r}$; 6.11 off relint, root moves,
rewrite to $s^\star$; 6.12 $\delta^\star$ itself, same transfer; dispatcher
row (`lemma62`, real branch here, complex branch next slide); complex-twin
row (`lemma62_complex_case`, $W$-matrix Case A/B).

**Notes.** Reference during questions on the escape half.

## Slide 52 — Lemma 6.2: complex case — what is extra

**On the slide.** Math column — **Claim.** Same goal for non-real
$s^\star$: a boundary root of $R(F)$ already lives on the relative boundary
of $F$ (complex slice $P_{s_c}$ in place of $P_{s_r}$). **New split:**
$P_{s_c}(s^\star)$ vs $\mathrm{dir}\,\mathrm{aff}\,F$ generically meet only
in $\{0\}$ — no direction to walk; Case A shares a nonzero direction $v$,
Case B ($\dim = 0$) is transverse. **Case A ($\dim \ge 1$).** Walk $v$ to the
relative boundary and transfer the root — the real-case escape.
**Case B ($\dim = 0$).** Non-roots $s_k \to s^\star$; Cramer on $V_0, V_1$
($\det \ne 0$) gives $\delta_k \to \delta^\star$ in $\mathrm{aff}(F)$
carrying $s_k$. **Limit.** $\delta_k \notin F$ yet $\delta_k \to
\delta^\star$ rules out interior — $\delta^\star$ is on the relative
boundary carrying $s^\star$. Lean column (under the 3D figure: shared line
in flat vs piercing line) — same opening via `isExposedFace_isCompact`,
`rootSpaceSet_isClosed_of_isCompact`, `mem_P_sc_of_isRoot`; Case A:
`exists_boundary_point_in_face_rootspace_complex` (via
`h_inter_dim_of_meet`), then `rootspace_mem_of_isRoot`; Case B:
`exists_seq_notin_RootSpaceSet_tendsto` (the $s_k$), `faceCols` basis with
`detOf_ne_zero_of_transverse` + `tendsto_detOf`, Cramer `lam0`/`lam1` with
`hev_root`, `hdeltak_tendsto`, interior-vs-`hev_notF` contradiction
(`hnot_ri`); machinery: `Wcol`/`Wmul` (`evalAtComplex_Wcol`,
`Wmul_mem_Psc`, `tendsto_Wmul`), `evalAtComplex` + `tendsto_evalAtComplex$,
transverse $2\times2$ `detOf`.

**Notes.** Dwell on the figure; rotate the interactive viewer
(`Complex_Visual/caseAB_viewer.py`, port 8081) live if possible. One line
does the work: "usually no direction to walk (transverse), so approximate
from outside and let the limit do the pushing."

## Slide 53 — Edge Theorem — formal proof

**On the slide.** Theorem box: $\Omega \subset \mathbb{R}^{n+1}$ ($n \ge 1$)
polytope satisfying Assumption 6.1; every $s \in \partial R(\Omega)$ lies in
$R(E)$ for some exposed edge $E$. Proof column: (1) $s \in \partial
R(\Omega)$, $R(\Omega)$ closed ⇒ $s \in R(\Omega)$, $s \notin
\mathrm{int}\,R(\Omega)$; (2) $\mathrm{Im}(s) = 0$ ⇒ edge $E$ by Lemma 6.1
real, done; (3) $\mathrm{Im}(s) \ne 0$ ⇒ exposed face $F$, $s \in R(F)$,
$\dim \le 2$ by Lemma 6.1 complex; (4) $\dim = 2$: $R(F)$ closed and
$\mathrm{int}\,R(F) \subseteq \mathrm{int}\,R(\Omega) \not\ni s$, so $s \in
\partial R(F)$, Lemma 6.2 gives $s \in R(\mathrm{relativeBoundary}\,F)$,
witness on relative boundary gives proper $G \subsetneq F$ ($\dim G \le 1$),
$s \in R(G)$; (5) $\dim \le 1$: edge ($\dim = 1$) or singleton ($\dim = 0$)
sitting on an edge through it ⇒ $s \in R(E)$. Lean column
(`EdgeTheorem.lean`): closedness + unpacking
(`rootSpaceSet_isClosed_of_isCompact`, `frontier_subset_closure`); Step 2 =
`edge_real`; Step 3 = `lemma61_complex_with_dim`; Step 4 `interior_mono`
+ `face_boundary_subset`; last descent `exists_proper_subface_of_boundary_point`
via `isExposedEdge_of_dim_1` or `exposed_face_dim_zero_singleton` +
`exists_exposed_edge_of_singleton` (= `exposed_face_root_dim_le1_to_edge`);
assembly `edge_theorem` (`by_cases hreal`, `by_cases hdim2`).

**Notes.** Deliver slowly — the capstone. Point out the two `by_cases`
structure `edge_theorem` exactly as the five steps do.

## Slide 54 — Lemmas behind steps 1–5

**On the slide.** Five signatures with what/how lines in two columns
(steps 1–3 left, 4–5 right):
```lean
-- Step 1: closedness workhorse
lemma rootSpaceSet_isClosed_of_isCompact {n : ℕ} {W : Set (CoeffVec n)} (hW : IsCompact W) :
    IsClosed (RootSpaceSet W)
```
What: root spaces over compact sets are closed. How: $R(W) = \pi(Z)$ for
$Z \subseteq W \times \mathbb{C}$ closed, $\pi$ closed as $W$ compact.
```lean
-- Step 2: real case, one line
theorem edge_real {n : ℕ} (hn : n ≥ 1) (P : Polytope n) (s : ℂ)
    (hs : s ∈ RootSpace P) (hreal : s.im = 0) :
    ∃ E, IsExposedEdge P E ∧ s ∈ RootSpaceSet E
```
What: every real root lives on an exposed edge. How: Lemma 6.1, real case.
```lean
-- Step 3: complex case with dimension bound
theorem lemma61_complex_with_dim (hn : n ≥ 1) (P : Polytope n) (s : ℂ) (hs : s ∈ RootSpace P)
    (hleading : ∀ v ∈ P.vertices, 0 < v (Fin.last n)) : s.im ≠ 0 →
    ∃ F, IsExposedFace P F ∧ s ∈ RootSpaceSet F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction ≤ 2
```
What: every non-real root lives on a face of dimension at most two. How:
Steps 1–5 in the $(n-1)$-slice to $\dim \le 2$ (count needs $\dim \ge 3$);
$n = 1$ excluded by the leading coefficient.
```lean
-- Step 4: Lemma 6.2 for the assembly
theorem face_boundary_subset {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2) :
    frontier (RootSpaceSet F) ⊆ RootSpaceSet (relativeBoundary F)
```
What: boundary roots of a 2D face live on its relative boundary. How:
split on $\mathrm{Im}(s^\star) = 0$.
```lean
-- Step 5: low-dimensional faces to edges
private theorem exposed_face_root_dim_le1_to_edge {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (s : ℂ) (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hsF : s ∈ RootSpaceSet F)
    (hF_dim : Module.finrank ℝ (affineSpan ℝ F).direction ≤ 1) :
    ∃ E, IsExposedEdge P E ∧ s ∈ RootSpaceSet E
```
What: roots on dim-$\le 1$ faces move to an edge. How: $\dim = 1$ already an
edge; $\dim = 0$ singleton on an edge through it.

**Notes.** Reference slide for "which lemma does step 3?" Rehearse the
$\pi(Z)$ line: "$R(W)$ is the shadow the zero set casts on $\mathbb{C}$,
and shadows of closed sets along compact directions stay closed."

## Slide 55 — Lean implementation

**On the slide.** Full `edge_theorem` statement (`EdgeTheorem.lean:82-89`):
```lean
theorem edge_theorem {n : ℕ} (hn : n ≥ 1) (P : Polytope n) (s : ℂ)
    (hleading : ∀ v ∈ P.vertices, 0 < v (Fin.last n))
    (hs : s ∈ frontier (RootSpace P)) :
    ∃ E, IsExposedEdge P E ∧ s ∈ RootSpaceSet E := by
```
plus the complete proof in two columns (`:90-121` left: closedness
(`hroot_closed` via `rootSpaceSet_isClosed_of_isCompact`), membership
(`hs_mem` via `frontier_subset_closure`), non-interior (`hs_not_int`),
`by_cases hreal` → `edge_real`, complex face via
`lemma61_complex_with_dim`, `by_cases hdim2`, dim-2 setup
(`hroot_closed_F`, `hsF_not_int` by `interior_mono`, `hsF_front`); `:122-151`
right: `face_boundary_subset` → witness on relative boundary →
`exists_proper_subface_of_boundary_point` → `by_cases hG1` (edge at dim 1,
singleton + `exists_exposed_edge_of_singleton` at dim 0); dim-$\le 1$ closes
by `exposed_face_root_dim_le1_to_edge`).

**Notes.** Be honest: the slide shows the wiring at small font; the file
has the rest. End with "no sorrys, no axioms — `lake env lean` agrees."

## Slide 56 — Future work — outlook

**On the slide.** Three items (complex 6.2, complex 6.1, assembling the Edge
Theorem) — all three now exist in Lean.

**Notes.** Never end on a stale slide without saying so — reframe live as
"polish and extensions" (nested families §6.4, performance measures from
root loci). The audience will notice before you do.
