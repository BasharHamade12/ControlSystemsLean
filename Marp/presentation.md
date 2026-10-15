---
marp: true
theme: default
paginate: true
size: 16:9
math: katex
style: |
  section { font-size: 1.4em; padding: 0 56px; }
  section > :first-child { margin-top: 0; }
  section > :last-child { margin-bottom: 0; padding-bottom: 0; }
  section::after { font-size: 12px; color: #aaaaaa; bottom: 6px; right: 12px; }
  footer { font-size: 12px; height: 0; padding: 0; margin: 0; }
  /* slide kinds (used via <!-- _class: ... -->) */
  .lead { text-align: center; }
  .lead h1 { font-size: 1.8em; }
  .list ul, .list ol { line-height: 1.6; }
  .section { text-align: center; }
  .section h1 { font-size: 2em; color: #1f4e79; margin-top: 16%; }
  h1 { margin-bottom: 6px; font-size: 1.5em; }
  h3 { margin: 4px 0; font-size: 1.05em; }
  p, ul, ol { margin: 4px 0; }
  blockquote { margin: 5px 0; }
  code { font-size: 0.62em; }
  pre { font-size: 0.55em; }
  table { font-size: 0.7em; }
  /* --- step-annotation tables (wrap a table in <div class="steps">) ---- */
  .steps table { width: 100%; border-collapse: collapse; margin: 4px 0 0; font-size: 0.86em; }
  .steps th { background: #dedede; border: 1px solid #a8a8a8; padding: 5px 10px; text-align: left; }
  .steps td { border: 1px solid #a8a8a8; padding: 6px 10px; vertical-align: top; line-height: 1.3; }
  .steps .item { padding: 3px 0; }
  .steps .item + .item { border-top: 1px dotted #9a9a9a; margin-top: 7px; padding-top: 9px; }
  .steps .n { font-weight: bold; white-space: nowrap; margin-right: 2px; }
  .steps .n.new { background: #c9c9c9; border-radius: 4px; padding: 2px 7px; margin-right: 7px; }
  .lean { background: #e8e8e8; border-radius: 10px; overflow: hidden; margin: 6px 0; }
  .lean-head { background: #d0d0d0; color: #1a1a1a; font-family: monospace; font-size: 0.6em; font-weight: bold; padding: 3px 12px; }
  .lean pre { margin: 0; padding: 6px 12px; color: #111111; font-family: monospace; font-size: 0.68em; font-weight: bold; line-height: 1.4; background: transparent; }
  .lean mark { background: #b5b5b5; color: #000000; border-radius: 3px; padding: 1px 4px; }
  /* numbered-step highlight shades (bright blue, assigned per slide by build.py) */
  .lean mark.mk1 { background: #d9ecff; }
  .lean mark.mk1 { background: #bfe0ff; }
  .lean mark.mk1 { background: #a3d2ff; }
  .lean mark.mk1 { background: #84c2ff; }
  .lean mark.mk1 { background: #63b0ff; }
  .lean mark.mk1 { background: #429dff; }
  /* --- grouped step boxes: consecutive lines sharing a step number ---- */
  .lean .grp { display: inline-flex; align-items: stretch; vertical-align: top; margin: 1px 0; }
  .lean .gn { display: flex; align-items: center; padding: 0 7px; font-weight: bold; white-space: nowrap;
    background: #c9c9c9; border: 1px solid #a8a8a8; border-left-width: 0; border-radius: 0 4px 4px 0; order: 2; }
  .lean .gbox { border: 1px solid #a8a8a8; border-radius: 5px 0 0 5px; padding: 1px 7px; white-space: pre; order: 1; }
  .lean .grp.mk1 .gbox { background: #d9ecff; }
  .lean .grp.mk2 .gbox { background: #bfe0ff; }
  .lean .grp.mk3 .gbox { background: #a3d2ff; }
  .lean .grp.mk4 .gbox { background: #84c2ff; }
  .lean .grp.mk5 .gbox { background: #63b0ff; }
  .lean .grp.mk6 .gbox { background: #429dff; }
  /* --- Lean syntax highlighting (VS Code Light+ inspired; applied by highlight_lean.py) --- */
  .lean .tok-kw { color: #0000FF; }
  .lean .tok-tac { color: #AF00DB; }
  .lean .tok-type { color: #267F99; }
  .lean .tok-var { color: #001080; }
  .lean .tok-str { color: #A31515; }
  .lean .tok-num { color: #098658; }
  .lean .tok-com { color: #008000; }
  .lean .tok-sorry { color: #E51400; font-weight: bold; }
  .columns { display: grid; grid-template-columns: 1fr 1fr; column-gap: 24px; font-size: 0.8em; line-height: 1.35; }
  .columns h3 { margin: 0 0 4px 0; font-size: 1.05em; color: #1a1a1a; }
  .columns .col { background: #f8f9fa; border: 1px solid #d0d7de; border-radius: 8px; padding: 10px 14px; }
  .columns ul { margin: 0 0 6px 0; padding-left: 20px; }
  .columns li { margin-bottom: 2px; }
  /* --- Full-lemma + side-explanation layout (Step 3) ---------------------- */
  .codeside { display: grid; grid-template-columns: 1.45fr 1fr; column-gap: 16px; align-items: start; margin-top: 4px; }
  .codeside .lean { margin: 0; }
  .codeside .lean pre { font-size: 0.53em; line-height: 1.32; padding: 6px 10px; }
  .codeside .side { background: #f8f9fa; border: 1px solid #d0d7de; border-radius: 8px; padding: 8px 10px; font-size: 0.95em; font-weight: bold; line-height: 1.35; }
  .codeside > div { min-width: 0; }
  .codeside .side table { width: 100%; table-layout: fixed; }
  .codeside .side td, .codeside .side th { white-space: normal; overflow-wrap: break-word; }
  .codeside .side h3 { margin: 0 0 4px 0; font-size: 1.05em; color: #1a1a1a; }
  .codeside .side ul { margin: 0; padding-left: 18px; }
  .codeside .side li { margin-bottom: 2px; }
  .codeside .side .dim { opacity: 0.55; }
  /* figure grids: .figs base (1 col); add .cols-2/.cols-3; size via .figs-sm/.figs-md/.figs-lg */
  .figs { display: grid; gap: 12px; margin-top: 10px; margin-bottom: 0; }
  .cols-2 { grid-template-columns: repeat(2, minmax(0, 1fr)); }
  .cols-3 { grid-template-columns: repeat(3, minmax(0, 1fr)); }
  .fig-card { display: flex; flex-direction: column; align-items: center; justify-content: flex-start; min-width: 0; margin: 0; padding: 6px 8px; background: #fff; border: 1px solid #d4dbe3; border-radius: 7px; }
  .figs-sm .fig-card img { width: 100%; height: 230px; object-fit: contain; }
  .figs-md .fig-card img { width: 100%; height: 330px; object-fit: contain; }
  .figs-lg .fig-card img { width: 100%; height: 420px; object-fit: contain; }
  .fig-card figcaption { align-self: stretch; margin-top: 2px; text-align: center; font-size: 0.72em; line-height: 1.15; }
  .fig-card b { color: #1f4e79; }
  .fig-takeaway { margin-top: 10px; margin-bottom: 0; padding: 9px 12px; border-left: 5px solid #2f7d4f; background: #edf6f0; font-size: 0.85em; line-height: 1.2; text-align: center; }
  /* formal theorem statement (Step 4 slides) */
  .thm { margin: 4px 0 5px; padding: 5px 10px; border-left: 4px solid #1f4e79; background: #f2f6fa; font-size: 0.83em; line-height: 1.3; }
  .thm p { margin: 0; }
  /* --- Current claims: top-right tracker, generated by Marp/build.py --- */
  section { position: relative; }
  .claims-tr { position: absolute; top: 8px; right: 20px; width: 290px; max-height: 34%; overflow: hidden; padding: 4px 8px; border: 1px solid #d9c48a; border-left: 4px solid #8a5a00; background: #fff8e6; font-size: 0.50em; line-height: 1.25; border-radius: 0 8px 8px 0; z-index: 10; }
  .claims-tr b.t { color: #6b4a00; }
  .claims-tr ul { margin: 2px 0 0; padding-left: 14px; }
  .claims-tr li { margin-bottom: 1px; }
  .claims-tr .todo { opacity: 0.45; }
header: ''
footer: ''
---

<!-- _class: lead -->


<!-- SLIDE 1 | Edge Theorem in Lean 4 (Lemma 6.1, real case) -->
# Edge Theorem in Lean 4 (Lemma 6.1, real case)
## TODO: subtitle — polytopic families and exposed edges

TODO: Author Name · Institute

---
<!-- _class: list -->

<!-- SLIDE 2 | Outline -->
# Outline

1. **Background** — Why the Edge Theorem is needed in Control Systems 
2. **Preliminaries** — coefficient vectors, polytopes, affine span/direction/dimension, supporting hyperplanes, root spaces
3. **Exposed faces and edges** — boundary geometry and examples
4. **Edge Theorem** — Assumption 6.1, Lemmas 6.1–6.2, theorem, how the lemmas fit
5. **Proof of Lemma 6.1 (real case)** — Steps 1–6 in Lean, recap, complex-case extra
6. **Proof of Lemma 6.2 (real case)** — goal, math proof, helper lemma, Lean walkthroughs, maps, complex-case extra
7. **Edge Theorem assembled** — formal proof, lemmas behind the steps, Lean implementation


---
<!-- SLIDE 3 | What is a control system? -->
# What is a control system?

<style scoped>
h1 { font-size: 1.2em; margin-bottom: 4px; }
blockquote, ul, p { font-size: 0.88em; }
</style>

> A **control system** manages, commands, directs, or regulates the behavior of other devices or systems using control loops — from simple applications like a home thermostat to complex industrial processes.

<div class="columns">
<div class="col">

**Continuous-time state-space model:**
$$
\dot{x}(t) = A x(t) + B u(t)
$$
$$
y(t) = C x(t) + D u(t)
$$

</div>
<div class="col">

**Discrete-time state-space model:**
$$
x[k+1] = A_d x[k] + B_d u[k]
$$
$$
y[k] = C_d x[k] + D_d u[k]
$$

</div>
</div>

**Where:** $x$ is the state vector 
 $y$ the output vector
  $u$ the input (control) vector 
  $A, B, C, D$ the state, input, output, and feedthrough matrices, respectively.

---

<!-- SLIDE 4 | From state-space to transfer function -->
# From state-space to transfer function

<style scoped>
h1 { font-size: 1.2em; margin-bottom: 4px; }
ol, p { font-size: 0.88em; }
ol { line-height: 1.5; }
</style>

Starting from $\dot{x}(t) = Ax(t) + Bu(t)$, $y(t) = Cx(t) + Du(t)$, with zero initial conditions ($x(0) = 0$):

Applying Laplace transform: 
$sX(s) = AX(s) + BU(s)$, $Y(s) = CX(s) + DU(s)$.
$(sI - A)X(s) = BU(s)$, 
so $X(s) = (sI - A)^{-1}BU(s)$.
$\implies Y(s) = C(sI - A)^{-1}BU(s) + DU(s)$.

<div class="thm">

$G(s) = \dfrac{Y(s)}{U(s)} = C(sI - A)^{-1}B + D$ — the **transfer function**.

</div>

---

<!-- SLIDE 5 | Example: mass-spring-damper -->
# Example: mass-spring-damper

<style scoped>
h1 { font-size: 1.2em; margin-bottom: 4px; }
p { font-size: 0.88em; margin: 3px 0; }
</style>

$m = 1\,\mathrm{kg}$, $c = 2\,\mathrm{N{\cdot}s/m}$, $k = 3\,\mathrm{N/m}$; input $u(t)$ = force (N), output $y(t)$ = displacement (m).
$$m\ddot{y} + c\dot{y} + ky = u(t) \quad\Rightarrow\quad \ddot{y} + 2\dot{y} + 3y = u(t)$$
States $x_1 = y$ (position), $x_2 = \dot{y}$ (velocity):
$$\begin{cases} \dot{x}_1 = x_2 \\ \dot{x}_2 = -3x_1 - 2x_2 + u \end{cases}
\qquad\Rightarrow\qquad
A = \begin{bmatrix} 0 & 1 \\ -3 & -2 \end{bmatrix},\;
B = \begin{bmatrix} 0 \\ 1 \end{bmatrix},\;
C = \begin{bmatrix} 1 & 0 \end{bmatrix},\;
D = 0$$
<div class="thm">

$G(s) = C(sI-A)^{-1}B + D
= \begin{bmatrix} 1 & 0 \end{bmatrix}
\frac{1}{s^2+2s+3}\begin{bmatrix} s+2 & 1 \\ -3 & s \end{bmatrix}
\begin{bmatrix} 0 \\ 1 \end{bmatrix}
= \dfrac{1}{s^2+2s+3}$

</div>

---

<!-- SLIDE 6 | Poles and stability -->
# Poles and stability

<style scoped>
h1 { font-size: 1.2em; margin-bottom: 4px; }
blockquote, p { font-size: 0.88em; }
</style>

> **Stability criterion.** A system is **stable** iff all poles of $G(s)$ have strictly negative real parts; it is **unstable** if some pole of $G(s)$ has positive real part.



**Example.** $G(s) = \dfrac{1}{s^2+2s+3}$: the poles solve $s^2 + 2s + 3 = 0$,
$$s = \frac{-b \pm \sqrt{b^2-4ac}}{2a} = \frac{-2 \pm \sqrt{-8}}{2} = -1 \pm j\sqrt{2}$$
so with $p_1 = -1 + j\sqrt{2}$ and $p_2 = -1 - j\sqrt{2}$,
$\mathrm{Re}(p_1) = \mathrm{Re}(p_2) = -1 < 0$ $\Rightarrow$ the system is **stable**. 

---

<!-- SLIDE 7 | Kharitonov's theorem -->
# Kharitonov's theorem

<style scoped>
h1 { font-size: 1.15em; margin-bottom: 4px; }
.thm { font-size: 0.72em; }
p { font-size: 0.85em; margin: 3px 0; }
</style>

<div class="thm">

Interval family $\mathcal{P} = \{p(s) = a_n s^n + \cdots + a_1 s + a_0 \mid a_i \in [\underline{a}_i, \bar{a}_i],\ \bar{a}_n > 0\}$. Four vertex polynomials:
$$K_1 = \underline{a}_n s^n + \underline{a}_{n-1}s^{n-1} + \bar{a}_{n-2}s^{n-2} + \bar{a}_{n-3}s^{n-3} + \cdots$$
$$K_2 = \bar{a}_n s^n + \bar{a}_{n-1}s^{n-1} + \underline{a}_{n-2}s^{n-2} + \underline{a}_{n-3}s^{n-3} + \cdots$$
$$K_3 = \underline{a}_n s^n + \bar{a}_{n-1}s^{n-1} + \bar{a}_{n-2}s^{n-2} + \underline{a}_{n-3}s^{n-3} + \cdots$$
$$K_4 = \bar{a}_n s^n + \underline{a}_{n-1}s^{n-1} + \underline{a}_{n-2}s^{n-2} + \bar{a}_{n-3}s^{n-3} + \cdots$$
$$\mathcal{P}\ \text{Hurwitz stable} \iff K_1, K_2, K_3, K_4\ \text{each Hurwitz stable.}$$

</div>

**Example (primary structure + TMD).** Primary: $m_1 \in [\underline{m}_1, \bar{m}_1]$, $k_1 \in [\underline{k}_1, \bar{k}_1]$, $c_1 \in [\underline{c}_1, \bar{c}_1]$; tuned mass damper: $m_2 \in [\underline{m}_2, \bar{m}_2]$, $k_2 \in [\underline{k}_2, \bar{k}_2]$, $c_2 \in [\underline{c}_2, \bar{c}_2]$. The equations of motion give $p(s) = a_4 s^4 + a_3 s^3 + a_2 s^2 + a_1 s + a_0 = 0$ with $a_i \in [\underline{a}_i, \bar{a}_i]$ — an interval family, so these four polynomials decide its stability.

<div class="figs"><figure class="fig-card"><img src="./Intro_Visual/tmd.png" alt="Wall, primary mass m1 on spring k1 and damper c1 driven by force u(t) with displacement y(t), coupled to tuned mass damper m2 on spring k2 and damper c2" style="height:120px;"></figure></div>

---

<!-- SLIDE 8 | Kharitonov vs Edge Theorem (discrete systems) -->
# Kharitonov vs Edge Theorem (discrete systems)

<style scoped>
h1 { font-size: 1.2em; margin-bottom: 4px; }
.columns { font-size: 0.85em; }
.columns li { margin-bottom: 3px; }
</style>

<div class="columns">
<div class="col">

### Why Kharitonov fails (discrete)
- Kharitonov's proof relies on a special even/odd symmetry of the imaginary axis. The unit circle has no such symmetry, so four stable corner polynomials prove nothing — an unstable member can still hide in the family.
- A bilinear map sends the disc to the half-plane, but it mixes all coefficients together


</div>
<div class="col">

### Counterexample: Kharitonov fails (discrete)
- Interval family $p(z) = a_3 z^3 + a_2 z^2 + a_1 z + a_0$ with $a_0 \in [-0.2, 0.5]$, $a_1 \in [0.3, 0.5]$, $a_2 \in [0.6, 1.3]$, $a_3 \in [0.9, 1.2]$.
- All four Kharitonov polynomials are stable (largest root moduli $0.83$, $0.79$, $0.98$, $0.82$ — all $< 1$).
- But the vertex member $p^\star(z) = 0.9z^3 + 1.3z^2 + 0.3z + 0.5$ has a root of modulus $1.47 > 1$ — unstable. Four stable corners, yet the family is not stable. 

</div>
</div>

<div class="fig-takeaway">Discrete-time robustness needs polytopes, not intervals — and a theorem that works on any stability region.</div>

---

<!-- SLIDE 9 | The Edge Theorem at work (discrete) -->
# The Edge Theorem at work (discrete)

<style scoped>
h1 { font-size: 1.2em; margin-bottom: 4px; }
.thm { font-size: 0.82em; }
p { font-size: 0.88em; margin: 4px 0; }
</style>

<div class="thm">

**Theorem (Edge Theorem; Bartlett–Hollot–Lin 1988).** Let $\Omega$ be a polytope of fixed-degree polynomials. Then $\partial R(\Omega) \subseteq \bigcup_{E} R(E)$ over the exposed edges $E$ of $\Omega$. Hence the family is stable (Hurwitz, Schur, …) iff every exposed edge is — and each edge is a one-parameter family $a(\lambda) = (1-\lambda)a^{(1)} + \lambda a^{(2)}$, $\lambda \in [0,1]$.

</div>

**Example (Ch. 6, Ex. 6.2).** Family $\delta(z;\underline{\delta}) = z^3 + \delta_2 z^2 + \delta_1 z + \delta_0$ with $\underline{\delta} = (\delta_3,\delta_2,\delta_1,\delta_0) \in \Omega := \{1\} \times [0.042,0.158] \times [-0.058,0.058] \times [-0.06,0.056] \subset \mathbb{R}^4$: 
a compact $3$-dimensional box ($8$ vertices, $12$ edges) with leading coefficient $\equiv 1$.

<div class="figs"><figure class="fig-card"><img src="./Intro_Visual/edge_example_62.png" alt="Left: the coefficient box with 8 vertices and 12 edges colored by varying coefficient. Right: unit disc with the 12 edge root loci inside" width="551" height="350" style="height:350px;width:auto;"><figcaption><b>Ex. 6.2:</b> the box (left) and its 12 edge root loci inside |z| < 1 (right)</figcaption></figure></div>


---
<!-- _class: fragment -->
*** The edge theorem applies to each 1-parameter family (edge) of polynomials. The 12 edges of the coefficient box each give a root locus inside |z| < 1. ***

<!-- SLIDE 10 | Section 1 · Preliminaries -->
<!-- _class: section -->
# Section 1 · Preliminaries

---

<!-- SLIDE 11 | Polytopic family of polynomials -->
# Polytopic family of polynomials

A polytopic family of polynomials can be thought of as the convex hull of a
finite number of points (polynomials). Mathematically, this can be represented as
the family

$$
P(s) = \lambda_1 P_1(s) + \cdots + \lambda_n P_n(s)
$$

where $P_i(s)$ are fixed real polynomials and the $\lambda_i$ are real with
$\lambda_i \geq 0$ and $\sum \lambda_i = 1$.

> **Definition (Polytope).**
> Let $v_1,\dots,v_N \in \mathbb{R}^d$. The *polytope* spanned by
> $v_1,\dots,v_N$ is the set of all convex combinations of these points:
> $$
> \Omega \;=\; \operatorname{conv}\{v_1,\dots,v_N\}
> \;=\;
> \left\{
> \sum_{i=1}^{N} \lambda_i\, v_i
> \;\middle|\;
> \lambda_i \in \mathbb{R},\; \lambda_i \ge 0,\;
> \sum_{i=1}^{N} \lambda_i = 1
> \right\}.
> $$
> Equivalently, $\Omega$ is compact and convex.

---

<!-- SLIDE 12 | Coefficient vectors (`CoeffVec`) -->
# Coefficient vectors (`CoeffVec`)

**Restatement.**
A degree-$n$ polynomial $\delta(s)=\delta_0+\delta_1 s+\cdots+\delta_n s^n$
is identified with its coefficient vector
$\underline\delta=(\delta_0,\delta_1,\dots,\delta_n)\in\mathbb{R}^{n+1}$.

**Lean** (`EdgeTheoremDefs.lean`):

<div class="lean"><div class="lean-head">EdgeTheoremDefs.lean</div>
<pre><span class="tok-com">/-- Coefficient vector `(α₀,…,αₙ) : ℝ^{n+1}` for `δ(s) = α₀+α₁s+…+αₙsⁿ`. -/</span>
<span class="tok-kw">abbrev</span> <span class="tok-type">CoeffVec</span> (n : <span class="tok-type">ℕ</span>) := <span class="tok-type">Fin</span> (n + <span class="tok-num">1</span>) → <span class="tok-type">ℝ</span></pre></div>

<div class="lean"><div class="lean-head">EdgeTheoremDefs.lean:95-99</div>
<pre><span class="tok-com">/-- Convert a coefficient vector α : Fin(n+1) → ℝ to a polynomial
    δ(s) = α(0) + α(1)·s + ... + α(n)·sⁿ
-/</span>
<span class="tok-kw">noncomputable</span> <span class="tok-kw">def</span> <span class="tok-type">polyOfVec</span> {n : <span class="tok-type">ℕ</span>} (α : <span class="tok-type">CoeffVec</span> n) : <span class="tok-type">Polynomial</span> <span class="tok-type">ℝ</span> :=
  ∑ j : <span class="tok-type">Fin</span> (n + <span class="tok-num">1</span>), <span class="tok-type">Polynomial.monomial</span> j.val (α j)</pre></div>

**Example** ($n=2$).
`CoeffVec 2` = `Fin 3 → ℝ`, i.e. $\mathbb{R}^3$. Take
$\alpha = (\alpha_0,\alpha_1,\alpha_2) = (1,\,-2,\,3)$, i.e.
$\alpha(0)=1,\ \alpha(1)=-2,\ \alpha(2)=3$. Then

$$
\texttt{polyOfVec}\ \alpha = 1 + (-2)\,s + 3\,s^2 = 3s^2 - 2s + 1.
$$

<div class="lean"><div class="lean-head">EdgeTheoremDefs.lean</div>
<pre><span class="tok-com">-- α : CoeffVec 2,  α 0 = 1,  α 1 = -2,  α 2 = 3</span>
<span class="tok-com">-- polyOfVec α = 3s² - 2s + 1</span></pre></div>
<!-- _class: fragment -->
*** The coefficient vector uniquely determines the polynomial. This example shows α = (1, -2, 3) giving 3s² - 2s + 1. ***

---

<!-- SLIDE 13 | Polytope: Lean formalization -->
# Polytope: Lean formalization

**Lean** (`EdgeTheoremDefs.lean`):

<div class="lean"><div class="lean-head">EdgeTheoremDefs.lean</div>

<pre><span class="tok-com">/--
A polytope Ω in coefficient space ℝ^{n+1}.
It is defined as the convex hull of a finite set of vertices V,
and is assumed to have nonempty topological interior.
-/</span>
<span class="tok-kw">structure</span> <span class="tok-type">Polytope</span> (n : <span class="tok-type">ℕ</span>) <span class="tok-kw">where</span>
  vertices : <span class="tok-type">Finset</span> (<span class="tok-type">CoeffVec</span> n)
  nonempty  : vertices.Nonempty
  interior_nonempty : (interior (convexHull <span class="tok-type">ℝ</span> (vertices : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)))).<span class="tok-type">Nonempty</span>

<span class="tok-com">/-- The actual set Ω ⊆ ℝ^{n+1} as the convex hull of the vertices. -/</span>
<span class="tok-kw">def</span> <span class="tok-type">Polytope.Ω</span> (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n) : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n) :=
  convexHull <span class="tok-type">ℝ</span> (<span class="tok-type">P.vertices</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n))</pre></div>

> **Assumption.** The Lean `Polytope` structure additionally requires nonempty interior (`interior_nonempty`). Everything in this deck assumes it.



<div class="figs figs-sm">
<figure class="fig-card"><img src="./Defs_Visual/def_polytope.png" alt="Convex pentagon with vertices v1 to v5 and an interior point expressed as a convex combination of the vertices"></figure>
</div>

---

<!-- SLIDE 14 | Affine span, direction, dimension — definition -->
# Affine span, direction, dimension — definition
> **Definition (Affine subspace).** $A \subseteq \mathbb{R}^{d}$ is affine iff $\forall x,y \in A,\ \forall t \in \mathbb{R},\ (1-t)x + t y \in A$: closed under lines. Equivalently $A = p + V$ for $p \in A$ and a linear subspace $V = \mathrm{dir}(A)$.

> **Definition (Affine span).** For $S \subseteq \mathbb{R}^{d}$, $\mathrm{aff}(S) = \bigcap\{A \text{ affine} \mid S \subseteq A\}$, the smallest affine subspace containing $S$.

> **Definition (Direction).** For an affine subspace $A$, $\mathrm{dir}(A) = \{v \mid \forall p \in A,\ p + v \in A\}$, the underlying linear subspace of translations preserving $A$.

> **Definition (Dimension).** For a linear subspace $U \subseteq \mathbb{R}^{d}$, $\dim U$ is the number of vectors in any basis of $U$, i.e. the maximal size of a linearly independent subset of $U$. For an affine subspace $A$, $\dim A := \dim \mathrm{dir}(A)$. Hence $\dim \mathrm{aff}(F) = 0$ means a point, $= 1$ a line, $= 2$ a plane.

**Lean** (`EdgeTheoremDefs.lean:341-354`): continued on the next slide.

---

<!-- SLIDE 15 | Affine span, direction, dimension — Lean -->
# Affine span, direction, dimension — Lean

<div class="lean"><div class="lean-head">EdgeTheoremDefs.lean:338-351</div>

<pre><span class="tok-kw">abbrev</span> <span class="tok-type">meetDir</span> (n : <span class="tok-type">ℕ</span>) (<span class="tok-var">U</span> : <span class="tok-type">Submodule</span> <span class="tok-type">ℝ</span> (<span class="tok-type">CoeffVec</span> n))
    (affΩ : <span class="tok-type">AffineSubspace</span> <span class="tok-type">ℝ</span> (<span class="tok-type">CoeffVec</span> n)) : <span class="tok-type">Submodule</span> <span class="tok-type">ℝ</span> (<span class="tok-type">CoeffVec</span> n) :=
  (affineSpan <span class="tok-type">ℝ</span> ((<span class="tok-var">U</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) ∩ (affΩ : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)))).direction


<span class="tok-kw">noncomputable</span> <span class="tok-kw">abbrev</span> <span class="tok-type">dim</span> {<span class="tok-var">M</span> : <span class="tok-type">Type</span>*} [<span class="tok-type">AddCommGroup</span> <span class="tok-var">M</span>] [<span class="tok-type">Module</span> <span class="tok-type">ℝ</span> <span class="tok-var">M</span>]
    (<span class="tok-var">U</span> : <span class="tok-type">Submodule</span> <span class="tok-type">ℝ</span> <span class="tok-var">M</span>) : <span class="tok-type">ℕ</span> :=
  <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> <span class="tok-var">U</span></pre></div>

---

<!-- SLIDE 16 | Supporting hyperplane -->
# Supporting hyperplane

<div class="columns">
<div class="col">

> **Definition (Supporting hyperplane).**
> Let $\Omega \subseteq \mathbb{R}^{d}$ be convex and
> $f : \mathbb{R}^{d} \to \mathbb{R}$ a nonzero linear functional. The affine set
> $H = \{\, x \in \mathbb{R}^{d} : f(x) = c \,\}$ is a *supporting hyperplane*
> of $\Omega$ if
> **(i)** $f(x) \le c$ for all $x \in \Omega$
> **(ii)** $f(x_{0}) = c$ for some $x_{0} \in \Omega$.
> The *exposed set* is $\Omega \cap H$.

<!--
<div class="figs figs-sm">
<figure class="fig-card"><img src="./Defs_Visual/def_supporting_hyperplane.png" alt="Convex body inside the half-space f at most c with the complementary side shaded and the flat contact set on the hyperplane H"><figcaption>

<b>Supporting hyperplane:</b> $\Omega\subseteq\{f\le c\}$, the shaded side is $\{f>c\}$, and the flat part $\Omega\cap H$ of $\partial\Omega$ touches $H$ at $x_0$

</figcaption></figure>
</div> -->

</div>
<div class="col">

> **Example (Concrete supporting hyperplane).**
> Take $f(x,y) = -y$ and $c = 0$.
> $H = \{\, (x,y) : y = 0 \,\}$
> is the $x$-axis. The polytope $\Omega$ lies above it, so
> $f(x,y) = -y \le 0 = c$ on $\Omega$, and the point
> $x_{0}$ belongs to both $\Omega$ and $H$.
> Hence $H$ supports $\Omega$, and the exposed set $\Omega \cap H$
> is the bottom edge of the polytope.

<div class="figs figs-sm">
<figure class="fig-card"><img src="./Defs_Visual/def_supporting_example.png" alt="Pentagon above the x-axis with the bottom edge highlighted as the exposed set and the functional f = -y pointing downwards"><figcaption>

<b>Example $f=-y$, $c=0$:</b> $\Omega$ above $H=\{y=0\}$; $\Omega \cap H$ is the bottom edge

</figcaption></figure>
</div>

</div>
</div>

---

<!-- SLIDE 17 | Supporting hyperplane: Lean -->
# Supporting hyperplane: Lean

**Lean** (`EdgeTheoremDefs.lean`):

<div class="lean"><div class="lean-head">EdgeTheoremDefs.lean</div>
<pre><span class="tok-kw">structure</span> <span class="tok-type">SupportingHyperplane</span> (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n) <span class="tok-kw">where</span>
  f : <span class="tok-type">CoeffVec</span> n →ₗ[<span class="tok-type">ℝ</span>] <span class="tok-type">ℝ</span>
  c : <span class="tok-type">ℝ</span>
  nonzero : f ≠ <span class="tok-num">0</span>
  upper_bound : ∀ x ∈ <span class="tok-type">P.Ω</span>, f x ≤ c
  touches : ∃ x ∈ <span class="tok-type">P.Ω</span>, f x = c</pre></div>

---

<!-- _class: section -->


<!-- SLIDE 18 | Root spaces -->
# Root spaces

---

<!-- SLIDE 19 | Root space — definition -->
# Root space — definition
**Notation.**
For $\delta = (\delta_0,\dots,\delta_n) \in \mathbb{R}^{n+1}$,
$\operatorname{polyOfVec}(\delta)(s)
= \delta_0 + \delta_1 s + \cdots + \delta_n s^n$.

> **Definition (Root space).**
> Let $W \subseteq \mathbb{R}^{n+1}$. Then
> $$
> R(W) = \{\, s \in \mathbb{C} \mid
> \exists\, \delta \in W,\ \delta(s) = 0 \,\},
> $$
> and for a polytope $P$, $R(P) := R(P.\Omega)$.

**Lean** (`EdgeTheoremDefs.lean`):

<div class="lean"><div class="lean-head">EdgeTheoremDefs.lean</div>

<pre><span class="tok-kw">def</span> <span class="tok-type">RootSpaceSet</span> {n : <span class="tok-type">ℕ</span>}
  (<span class="tok-var">W</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) : <span class="tok-type">Set</span> <span class="tok-type">ℂ</span> :=
  { s | ∃ δ ∈ <span class="tok-var">W</span>,
      ((<span class="tok-type">polyOfVec</span> δ).map (algebraMap <span class="tok-type">ℝ</span> <span class="tok-type">ℂ</span>)).<span class="tok-type">IsRoot</span> s }

<span class="tok-com">/--
The root space of a polytope `P`: all complex numbers `s` such that
some coefficient vector in `P.Ω` yields a polynomial vanishing at `s`.
-/</span>
<span class="tok-kw">def</span> <span class="tok-type">RootSpace</span> (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n) : <span class="tok-type">Set</span> <span class="tok-type">ℂ</span> :=
  <span class="tok-type">RootSpaceSet</span> <span class="tok-type">P.Ω</span></pre></div>

---
<!-- _class: section -->

<!-- SLIDE 20 | Exposed faces and edges -->
# Exposed faces and edges

---

<!-- SLIDE 21 | Boundary and exposed faces — definition -->
# Boundary and exposed faces — definition
> **Definition (Closure and boundary).**
> $\overline{S} = \bigcap \{\, F \supseteq S : F
> \text{ closed} \,\}$ (smallest closed set containing $S$);
> $\partial S = \overline{S} \setminus \operatorname{int}(S)$.

> **Definition (Intrinsic interior / relative boundary).**
> For $S \subseteq \mathbb{R}^{d}$, the *intrinsic interior*
> $\operatorname{relint}(S)$ is the interior of $S$ relative to
> its affine span: $x \in \operatorname{relint}(S)$ iff
> $x \in S$ and $\exists\,\varepsilon > 0$ with
> $B(x, \varepsilon) \cap \operatorname{aff}(S) \subseteq S$.
> The *relative boundary* is $S \setminus \operatorname{relint}(S)$.

> **Definition (Exposed face / edge).**
> For $H$ supporting $\Omega$, $F = \Omega \cap H$ is
> *exposed*; $\dim\operatorname{aff}(F) = 1$ gives an
> *exposed edge* $E$, $= 2$ an *exposed face*.

**Lean** (`EdgeTheoremDefs.lean:140-151`)

---

<!-- SLIDE 22 | Boundary and exposed faces — Lean -->
# Boundary and exposed faces — Lean
<div class="lean"><div class="lean-head">EdgeTheoremDefs.lean:140-151</div>

<pre><span class="tok-com">/-- The exposed face of `P` for `hp`: `F = Ω ∩ {x | hp.f x = hp.c}`. -/</span>
<span class="tok-kw">def</span> <span class="tok-type">ExposedFace</span> {n : <span class="tok-type">ℕ</span>} {<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n} (hp : <span class="tok-type">SupportingHyperplane</span> <span class="tok-var">P</span>) :
    <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n) :=
  { x | x ∈ <span class="tok-type">P.Ω</span> ∧ hp.f x = hp.c }

<span class="tok-kw">open</span> <span class="tok-type">Affine</span>

<span class="tok-com">/-- `E` is an exposed edge of `P` if it is an exposed face of affine dimension 1. -/</span>
<span class="tok-kw">def</span> <span class="tok-type">IsExposedEdge</span> {n : <span class="tok-type">ℕ</span>} (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n) (<span class="tok-var">E</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) : <span class="tok-type">Prop</span> :=
  ∃ hp : <span class="tok-type">SupportingHyperplane</span> <span class="tok-var">P</span>,
    <span class="tok-var">E</span> = <span class="tok-type">ExposedFace</span> hp ∧
    <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> (<span class="tok-type">ExposedFace</span> hp)).direction = <span class="tok-num">1</span></pre></div>

---

<!-- SLIDE 23 | Boundary and exposed edge — example -->
# Boundary and exposed edge — example
<div class="columns">
<div class="col">

> **Example (Boundary).**
> $S = \{\, s : |s| \le 1 \,\}$ is closed, so
> $\overline{S} = S$, and
> $\operatorname{int}(S) = \{\, s : |s| < 1 \,\}$. Thus
> $\partial S = \{\, s : |s| = 1 \,\}$.

<div class="figs figs-sm">
<figure class="fig-card"><img src="./Defs_Visual/def_boundary.png" alt="Closed unit disk with its interior, its rim as the boundary, and a small ball about a rim point meeting both the disk and its complement"><figcaption>

<b>Boundary:</b> $\operatorname{int}(S)=\{|s|<1\}$, $\partial S=\{|s|=1\}$ — a small ball about $s_0$ meets both $S$ and $S^{c}$

</figcaption></figure>
</div>

</div>
<div class="col">

> **Example (Exposed edge).**
> Let $\Omega = \operatorname{conv}\{(0,0),(1,0),(1,1),(0,1)\}$
> (unit square) and $H = \{(x,y) : -y = 0\}$. Then
> $\Omega \cap H = [\,(0,0),\,(1,0)\,]$
> with $\dim\operatorname{aff}(\Omega \cap H) = 1$:
> an exposed edge.

<div class="figs figs-sm">
<figure class="fig-card"><img src="./Defs_Visual/def_exposed_edge.png" alt="Unit square with the bottom edge highlighted as the exposed set on the hyperplane y = 0"><figcaption>

<b>Exposed edge:</b> $H=\{y=0\}$ cuts the unit square in the segment $[\,(0,0),(1,0)\,]$, of affine dimension $1$

</figcaption></figure>
</div>

</div>
</div>

---
<!-- _class: section -->

<!-- SLIDE 24 | Edge Theorem -->
# Edge Theorem

---

<!-- SLIDE 25 | Assumption 6.1 -->
# Assumption 6.1

> **Assumption 6.1.**
> The sign of the leading coefficient $\delta_n$ is constant
> on $\Omega$; e.g. $\delta_n > \Delta > 0$ for all
> $\underline\delta \in \Omega$.

Every lemma and theorem below assumes it.

---

<!-- SLIDE 26 | Lemmas 6.1–6.2 — statements -->
# Lemmas 6.1–6.2 — statements
> **Lemma 6.1.**
> Let $\Omega \subset \mathbb{R}^{n+1}$ be a polytope satisfying
> Assumption 6.1. Then
> 1. If $s_r \in \mathbb{R}$ and $s_r \in R(\Omega)$,
>    then $\exists$ an exposed edge $E$ of $\Omega$ with
>    $s_r \in R(E)$;
> 2. If $s_c \in \mathbb{C}$ and
>    $s_c \in R(\Omega)$, then $\exists$ an exposed face
>    $F$ of $\Omega$ with $s_c \in R(F)$.

> **Lemma 6.2.**
> For any exposed face $F$ of $\Omega$,
> $$
> \partial R(F) \;\subseteq\; R(\partial F),
> $$
> i.e. the boundary of the root space of $F$ is contained
> in the root space of the relative boundary of $F$.


---

<!-- SLIDE 27 | Edge Theorem — statement -->
# Edge Theorem — statement
> **Theorem (Edge Theorem).**
> Let $\Omega \subset \mathbb{R}^{n+1}$ be a polytope of polynomials
> satisfying Assumption 6.1. Then the boundary of $R(\Omega)$
> is contained in the root space of the exposed edges of $\Omega$:
> $$
> \partial R(\Omega) \;\subseteq\;
> \bigcup_{E \text{ exposed edge}} R(E).
> $$

---

<!-- SLIDE 28 | Edge Theorem — proof outline -->
# Edge Theorem — proof outline
1. **Lemma 6.1.** Every $s \in R(\Omega)$ lies in $R(F)$ for some exposed face $F$ of $\Omega$; if $s = s_r \in \mathbb{R}$ then $F = E$ can be taken to be an exposed edge.
2. **Lemma 6.2.** For $F$ exposed, $\partial R(F) \subseteq R(\mathrm{rel}\,\partial F)$: a boundary root of a face is already a root on its relative boundary.
3. **Descent.** Let $s \in \partial R(\Omega)$. By (1), $s \in R(F_0)$ for $F_0$ exposed; while $s \in \partial R(F_k)$, (2) moves the root to $R(F_{k+1})$ for $F_{k+1} \subsetneq F_k$ exposed, so $\dim F_{k+1} < \dim F_k$. The dimension drops strictly at each step, hence the process terminates at an exposed edge $E$ with $s \in R(E)$.

Together: $\partial R(\Omega) \subseteq \bigcup_{E} R(E)$ over exposed edges $E$.

---
<!-- SLIDE 29 | Section 4 · Proof of Lemma 6.1, real case -->
<!-- _class: section -->
# Section 4 · Proof of Lemma 6.1, real case

---

<!-- SLIDE 30 | Lemma 6.1 (real case) — proof overview -->
# Lemma 6.1 (real case) — proof overview

<style scoped>
h1 { font-size: 1.15em; margin-bottom: 2px; }
blockquote { font-size: 0.72em; }
ol { font-size: 0.78em; }
</style>
> **Lemma 6.1.** :  Let $\Omega \subset \mathbb{R}^{n+1}$ be a polytope satisfying Assumption 6.1. Then
> 1. If $s_r \in \mathbb{R}$ and $s_r \in R(\Omega)$,
>    then $\exists$ an exposed edge $E$ of $\Omega$ with
>    $s_r \in R(E)$;
> 2. If $s_c \in \mathbb{C}$ and
>    $s_c \in R(\Omega)$, then $\exists$ an exposed face
>    $F$ of $\Omega$ with $s_c \in R(F)$.

1. **Unpack.** $s \in R(\Omega)$ with $\mathrm{Im}(s) = 0$ gives $\delta \in \Omega \cap P_{s_r}(r)$ with $s = \bar{r}$.
2. **Count.** $\dim U = n$ and $\dim\mathrm{dir} \ge 2$ give $\dim(U \cap \mathrm{dir}) \ge 1$.
3. **Escape.** Follow the nonzero direction to $\delta_{\mathrm{bound}} \in P_{s_r} \cap \partial\Omega$.
4. **Expose.** Hahn–Banach at $\delta_{\mathrm{bound}}$ gives exposed $F \ni \delta_{\mathrm{bound}}$ with $\bar{r} \in R(F)$.
5. **Descend.** $F \to G \to \cdots \to E$ with $\bar{r} \in R(E)$, $\dim E = 1$ (termination by dimension).
6. **Degenerate.** $m = 0$ is impossible; $m = 1$ makes $\Omega$ itself the edge.

---

<!-- SLIDE 31 | Step 1: Unpack the root — Lean + map -->
# Step 1: Unpack the root — Lean + map
<div class="thm">

**Claim.** Let $s \in R(\Omega)$ with $\mathrm{Im}(s) = 0$. Then $s = \bar{r}$ $\in R$ and there is $\delta \in P_{s_r}(r)$ with $\tilde P_\delta(s) = 0$.

**Proof.** $s \in R(\Omega)$ gives $\delta \in \Omega$ with $\tilde P_\delta(s) = 0$. 
 $\mathrm{Im}(s) = 0$ gives $s = \bar{r}$ ($r = \mathrm{Re}(s)$) by `Complex.ext`. 
  The root at $\bar{r}$ reads $P_\delta(r) = 0$, i.e. $\delta \in \ker(\mathrm{ev}_r) = P_{s_r}(r)$.

</div>

<div class="codeside">
<div class="lean"><div class="lean-head">Lemma61.lean:142-153</div>
<pre><span class="tok-kw">theorem</span> <span class="tok-type">lemma61_real</span> (hn : n ≥ <span class="tok-num">1</span>) (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n) (s : <span class="tok-type">ℂ</span>) (hs : s ∈ <span class="tok-type">RootSpace</span> <span class="tok-var">P</span>) :
    s.im = <span class="tok-num">0</span> → ∃ <span class="tok-var">E</span>, <span class="tok-type">IsExposedEdge</span> <span class="tok-var">P</span> <span class="tok-var">E</span> ∧ s ∈ <span class="tok-type">RootSpaceSet</span> <span class="tok-var">E</span> := <span class="tok-tac">by</span>
  <span class="tok-tac">intro</span> hreal
<span class="grp mk1"><span class="gn">1.1</span><span class="gbox">  <span class="tok-tac">unfold</span> <span class="tok-type">RootSpace</span> <span class="tok-type">RootSpaceSet</span> <span class="tok-kw">at</span> hs
  <span class="tok-tac">obtain</span> ⟨δ, hδ_in_Ω, hδ_root⟩ := hs</span></span>
<span class="grp mk1"><span class="gn">1.2</span><span class="gbox">  <span class="tok-kw">have</span> hs_real : s = ↑s.re := <span class="tok-tac">by</span>
    <span class="tok-tac">apply</span> <span class="tok-type">Complex.ext</span>
    · <span class="tok-tac">simp</span>
    · <span class="tok-tac">simp</span> [hreal]</span></span>
<span class="grp mk1"><span class="gn">1.3</span><span class="gbox">  <span class="tok-kw">have</span> hδ_in_Psr : δ ∈ (<span class="tok-type">P_sr</span> n s.re : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) := <span class="tok-tac">by</span>
    <span class="tok-tac">rw</span> [hs_real] <span class="tok-kw">at</span> hδ_root
    <span class="tok-tac">exact</span> <span class="tok-type">mem_P_sr_of_isRoot</span> s.re δ hδ_root</span></span></pre></div>
<div class="side">

### Map

| Step | Content |
|:---|:---|
| **1.1** | $s \in R(\Omega)$ gives $\delta \in \Omega$ with $\tilde P_\delta(s) = 0$ |
| **1.2** | $\mathrm{Im}(s)=0$ gives $s = \bar{r}$ with $r = \mathrm{Re}(s)$ |
| **1.3** | Root at $\bar{r}$ gives $P_\delta(r) = 0$, i.e. $\delta \in P_{s_r}(r)$ |

</div>
</div>

---

<!-- SLIDE 32 | Step 2: Dimension count — Lean + map -->
# Step 2: Dimension count — Lean + map
<div class="thm">

**Claim.** Let $U$ be linear with $\dim U = n$, $\mathrm{aff}\Omega$ affine with $\dim(\mathrm{dir}(\mathrm{aff}\Omega)) \ge 2$, and $\delta \in U \cap \mathrm{aff}\Omega$. Then $\dim(\mathrm{meetDir}) \ge 1$.

**Proof.** $\mathrm{meetDir} = \mathrm{dir}(\mathrm{aff}(U \cap \mathrm{aff}\Omega))$ by definition. 
**2.2** Put $\mathrm{Aint} = U \sqcap \mathrm{aff}\Omega$. 
**2.3** $\mathrm{dir}(\mathrm{Aint}) = U \cap \mathrm{dir}(\mathrm{aff}\Omega)$ , Since $U$, viewed as an affine subspace, has direction $U$ itself
**2.4** $\mathrm{aff}(U \cap \mathrm{aff}\Omega) = \mathrm{Aint}$. 
**2.5** Hence $\dim(\mathrm{meetDir}) = \dim(U \cap \mathrm{dir}(\mathrm{aff}\Omega))$. 
**2.6** $\dim(U \cap V) = \dim U + \dim V - \dim(U+V) \ge n + 2 - (n+1) = 1$ , where $V$ is  $\mathrm{dir}(\mathrm{aff}\Omega)$ 

</div>

<div class="codeside">
<div class="lean"><div class="lean-head">PreliminaryLemmas.lean</div>
<pre><span class="tok-kw">lemma</span> <span class="tok-type">intersection_affine_dim_ge_one</span> {n : <span class="tok-type">ℕ</span>} (<span class="tok-var">U</span> : <span class="tok-type">Submodule</span> <span class="tok-type">ℝ</span> (<span class="tok-type">CoeffVec</span> n))
    (affΩ : <span class="tok-type">AffineSubspace</span> <span class="tok-type">ℝ</span> (<span class="tok-type">CoeffVec</span> n))
    (δ : <span class="tok-type">CoeffVec</span> n) (hδU : δ ∈ <span class="tok-var">U</span>) (hδΩ : δ ∈ affΩ)
    (hU_dim : <span class="tok-type">dim</span> <span class="tok-var">U</span> = n) (haff_dim : <span class="tok-type">dim</span> affΩ.direction ≥ <span class="tok-num">2</span>) :
    <span class="tok-type">dim</span> (<span class="tok-type">meetDir</span> n <span class="tok-var">U</span> affΩ) ≥ <span class="tok-num">1</span> := <span class="tok-tac">by</span>
<span class="grp mk1"><span class="gn">2.1</span><span class="gbox">  <span class="tok-tac">unfold</span> <span class="tok-type">meetDir</span></span></span>
<span class="grp mk1"><span class="gn">2.2</span><span class="gbox">  <span class="tok-kw">let</span> <span class="tok-type">Aint</span> : <span class="tok-type">AffineSubspace</span> <span class="tok-type">ℝ</span> (<span class="tok-type">CoeffVec</span> n) := <span class="tok-type">U.toAffineSubspace</span> ⊓ affΩ</span></span>
<span class="grp mk1"><span class="gn">2.3</span><span class="gbox">  <span class="tok-kw">have</span> hA_dir : <span class="tok-type">Aint.direction</span> = <span class="tok-var">U</span> ⊓ affΩ.direction :=
    <span class="tok-type">intersection_direction_eq</span> <span class="tok-var">U</span> affΩ δ hδU hδΩ</span></span>
<span class="grp mk1"><span class="gn">2.4</span><span class="gbox">  <span class="tok-kw">have</span> hA_eq : affineSpan <span class="tok-type">ℝ</span> ((<span class="tok-var">U</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) ∩ (affΩ : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n))) = <span class="tok-type">Aint</span> := <span class="tok-tac">by</span>
    <span class="tok-tac">rw</span> [<span class="tok-type">affineSpan_inter</span> <span class="tok-var">U</span> affΩ]</span></span>
<span class="grp mk1"><span class="gn">2.5</span><span class="gbox">  <span class="tok-tac">rw</span> [hA_eq, hA_dir]</span></span>
<span class="grp mk1"><span class="gn">2.6</span><span class="gbox">  <span class="tok-tac">exact</span> <span class="tok-type">finrank_inf_ge_one</span> <span class="tok-var">U</span> affΩ.direction hU_dim haff_dim</span></span></pre></div>
<div class="side">

### Map

| Step | Content |
|:---|:---|
| **2.1** | $\mathrm{meetDir} = \mathrm{dir}(\mathrm{aff}(U \cap \mathrm{aff}\Omega))$ by definition |
| **2.2** | $\mathrm{Aint} = U \sqcap \mathrm{aff}\Omega$ (infimum of affine subspaces) |
| **2.3** | $\mathrm{dir}(\mathrm{Aint}) = U \cap \mathrm{dir}(\mathrm{aff}\Omega)$ |
| **2.4** | $\mathrm{aff}(U \cap \mathrm{aff}\Omega) = \mathrm{Aint}$ (a subspace is affine) |
| **2.5** | Hence $\dim(\mathrm{meetDir}) = \dim(U \cap \mathrm{dir}(\mathrm{aff}\Omega))$ |
| **2.6** | $\dim(U \cap V) = \dim U + \dim V - \dim(U+V) \ge n + 2 - (n+1) = 1$ ,  |

</div>
</div>

<!-- _class: fragment -->
*** Step-by-step dimension analysis: each step reveals on a new slide ***

---
<!-- SLIDE 33 | Step 3: Escape — Lean + map -->
# Step 3: Escape — Lean + map

<style scoped>
.codeside .side td, .codeside .side th { padding: 3px 6px; }
.codeside .side table { line-height: 1.25; }
.codeside .lean pre { font-size: 0.46em; line-height: 1.25; }
.thm { font-size: 0.85em; }
.thm p { margin: 0.2em 0; }
</style>
<div class="thm">

**Claim.** Let $\Omega$ be a polytope, $U$ a linear subspace, $\delta \in \Omega \cap U$, with $\dim(\mathrm{meetDir}) \ge 1$. Then $\exists\, \delta_{\mathrm{bound}} \in U \cap \partial\Omega$.

**Proof.** $\dim \ge 1$ gives $v \neq 0$ in $U \sqcap \mathrm{dir}(\mathrm{aff}\Omega)$. 
$\delta + tv \in U$ for all $t$ because $U$ is a subspace containing both $\delta$ and $v$; $\delta + tv \in \mathrm{aff}\Omega$ because an affine space contains the whole line through any of its points in any of its directions (line_in_intersection).
$\Omega$ is compact, hence bounded: all pairs lie at distance $\le C$. With $|v| > 0$ (from ①), $t_{\mathrm{out}} := (|C|+1)/|v| > 0$, and $\mathrm{dist}(\delta + t_{\mathrm{out}}v,, \delta) = |C|+1 > C$, so the point lies outside $\Omega$ (ray_escapes_of_bounded).
The segment $[\delta, \delta + t_{\mathrm{out}}v]$ meets $\partial\Omega$. 
$\delta_{\mathrm{bound}} = \delta + (c \cdot t_{\mathrm{out}})v \in U \cap \partial\Omega$.

</div>

<div class="codeside">
<div class="lean">
<pre><span class="tok-kw">lemma</span> <span class="tok-type">exists_boundary_point_in_submodule</span> {n : <span class="tok-type">ℕ</span>} (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n)
    (<span class="tok-var">U</span> : <span class="tok-type">Submodule</span> <span class="tok-type">ℝ</span> (<span class="tok-type">CoeffVec</span> n)) (δ : <span class="tok-type">CoeffVec</span> n)
    (hδ_in_Ω : δ ∈ <span class="tok-type">P.Ω</span>) (hδ_in_U : δ ∈ (<span class="tok-var">U</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)))
    (affΩ : <span class="tok-type">AffineSubspace</span> <span class="tok-type">ℝ</span> (<span class="tok-type">CoeffVec</span> n)) (hδ_aff : δ ∈ affΩ)
    (hA_dim : <span class="tok-type">dim</span> (<span class="tok-type">meetDir</span> n <span class="tok-var">U</span> affΩ) ≥ <span class="tok-num">1</span>) :
    ∃ δ_bound, δ_bound ∈ (<span class="tok-var">U</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) ∩ frontier <span class="tok-type">P.Ω</span> := <span class="tok-tac">by</span>
<span class="grp mk1"><span class="gn">①</span><span class="gbox">  <span class="tok-kw">have</span> h_dim_pos : <span class="tok-num">0</span> < dim (meetDir n U affΩ) := by omega
  haveI : Nontrivial ↥(U ⊓ affΩ.direction) :=
    intersection_nontrivial U affΩ δ hδ_in_U hδ_aff h_dim_pos
  obtain ⟨v_sub, hv_sub_nonzero⟩ := exists_ne (0 : ↑(U ⊓ affΩ.direction))</span></span>
<span class="grp mk1"><span class="gn">②</span><span class="gbox">  <span class="tok-kw">let</span> v : <span class="tok-type">CoeffVec</span> n := v_sub.val
  <span class="tok-kw">have</span> h_line_in_intersection : ∀ (t : <span class="tok-type">ℝ</span>), δ + t • v ∈ (<span class="tok-var">U</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) ∩
      (affΩ : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) :=
    <span class="tok-type">line_in_intersection</span> <span class="tok-var">U</span> affΩ δ hδ_in_U hδ_aff v_sub</span></span>
<span class="grp mk1"><span class="gn">③</span><span class="gbox">  <span class="tok-kw">have</span> hv_nonzero : v ≠ <span class="tok-num">0</span> := <span class="tok-tac">by</span>
    <span class="tok-tac">intro</span> h; <span class="tok-tac">apply</span> hv_sub_nonzero; <span class="tok-tac">exact</span> <span class="tok-type">Submodule.coe_eq_zero.mp</span> h
  <span class="tok-kw">have</span> h_escapes : ∃ (t : <span class="tok-type">ℝ</span>), <span class="tok-num">0</span> < t ∧ δ + t • v ∉ P.Ω :=
    ray_escapes_of_bounded P.isBounded δ v hδ_in_Ω hv_nonzero
  obtain ⟨t_out, ht_out_pos, ht_out⟩ := h_escapes</span></span>
<span class="grp mk1"><span class="gn">④</span><span class="gbox">  <span class="tok-tac">by_cases</span> hδ_front : δ ∈ frontier <span class="tok-type">P.Ω</span>
  · <span class="tok-tac">exact</span> ⟨δ, hδ_in_U, hδ_front⟩
  · <span class="tok-tac">obtain</span> ⟨δ_bound, h_seg, h_front⟩ :=
      <span class="tok-type">segment_boundary_intersection</span> <span class="tok-var">P</span> δ hδ_in_Ω hδ_front v hv_nonzero t_out ht_out</span></span>
<span class="grp mk1"><span class="gn">⑤</span><span class="gbox">    <span class="tok-tac">rw</span> [segment_eq_image] <span class="tok-kw">at</span> h_seg
    <span class="tok-tac">obtain</span> ⟨c, hc_in_Icc, hc_eq⟩ := h_seg
    <span class="tok-kw">have</span> h_rewrite : (<span class="tok-num">1</span> - c) • δ + c • (δ + t_out • v) = δ + (c * t_out) • v :=
      <span class="tok-type">segment_point_rewrite</span> δ v c t_out
    <span class="tok-kw">have</span> h_mem := h_line_in_intersection (c * t_out)
    <span class="tok-tac">rcases</span> h_mem <span class="tok-kw">with</span> ⟨hmem_U, hmem_aff⟩
    <span class="tok-kw">have</span> h_eq : δ_bound = δ + (c * t_out) • v := <span class="tok-tac">by</span>
      <span class="tok-kw">calc</span> δ_bound = (<span class="tok-num">1</span> - c) • δ + c • (δ + t_out • v) := <span class="tok-tac">by</span> <span class="tok-tac">rw</span> [←hc_eq]
        _ = δ + (c * t_out) • v := <span class="tok-tac">by</span> <span class="tok-tac">rw</span> [h_rewrite]
    <span class="tok-tac">exact</span> ⟨δ_bound, h_eq ▸ hmem_U, h_front⟩</span></span></pre></div>
<div class="side">

### Map

| Step | Content |
|:---|:---|
| **①** | $\dim \ge 1$ makes $U \sqcap \mathrm{dir}(\mathrm{aff}\Omega)$ nontrivial, giving $v \neq 0$ |
| **②** | $\delta + tv$ stays in $U \cap \mathrm{aff}\Omega$: $U$ is a subspace, $\mathrm{aff}\Omega$ is affine |
| **③** | Bounded $\Omega$ gives $t_{\mathrm{out}} = (\|C\|+1)/\|v\| > 0$ with $\delta + t_{\mathrm{out}}v \notin \Omega$ (distance $\|C\|+1 > C$) |
| **④** | $[\delta, \delta + t_{\mathrm{out}}v]$ meets $\partial\Omega$ (or $\delta \in \partial\Omega$); else two disjoint opens disconnect it |
| **⑤** | $\delta_{\mathrm{bound}} = \delta + (c \cdot t_{\mathrm{out}})v$: on the line from ②, hence in $U$ — and in $\partial\Omega$ by ④ |

</div>
</div>

---

<!-- SLIDE 34 | Step 3: Escape — `exists_boundary_point_in_submodule` (Lean + map) -->
# Step 3: Escape — `exists_boundary_point_in_submodule` (Lean + map)

<style scoped>
h1 { font-size: 1.05em; margin-bottom: 2px; }
.codeside .lean pre { font-size: 0.42em; line-height: 1.22; }
.thm { font-size: 0.85em; }
.thm p { margin: 0.2em 0; }
</style>

<div class="thm">

**Goal.** Let $\Omega \subset \mathbb{R}^{n+1}$ be a polytope, $U$ a linear subspace, $\delta \in \Omega \cap U$, with $\dim(\mathrm{meetDir}\,n\,U\,\mathrm{aff}\Omega) \ge 1$. Then $\exists\,\delta_{\mathrm{bound}} \in U \cap \partial\Omega$.

**Proof.** **3.1** $\dim \ge 1$ makes $U \sqcap \mathrm{dir}(\mathrm{aff}\Omega)$ nontrivial, giving $v_{\mathrm{sub}} \neq 0$. 
**3.2** With $v := v_{\mathrm{sub}}.\mathrm{val}$, the line $\delta + t \cdot v$ lies in $U \cap \mathrm{aff}\Omega$ for all $t$. 
**3.3** Boundedness of $\Omega$ gives $t_{\mathrm{out}} > 0$ with $\delta + t_{\mathrm{out}}v \notin \Omega$ (and $v \neq 0$ is inherited). 
**3.4** If $\delta \in \partial\Omega$ take $\delta_{\mathrm{bound}} = \delta$; else the segment $[\delta,\, \delta + t_{\mathrm{out}}v]$ meets $\partial\Omega$. 
**3.5** Rewriting gives $\delta_{\mathrm{bound}} = \delta + (c \cdot t_{\mathrm{out}})v \in U \cap \partial\Omega$.

</div>

<div class="codeside" style="grid-template-columns:minmax(0,1.45fr) minmax(0,1fr);">
<div class="lean"><div class="lean-head">PreliminaryLemmas.lean:336-368 — full proof, 3.1–3.5 highlighted</div>
<pre><span class="tok-kw">lemma</span> <span class="tok-type">exists_boundary_point_in_submodule</span> {n : <span class="tok-type">ℕ</span>} (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n)
    (<span class="tok-var">U</span> : <span class="tok-type">Submodule</span> <span class="tok-type">ℝ</span> (<span class="tok-type">CoeffVec</span> n)) (δ : <span class="tok-type">CoeffVec</span> n)
    (hδ_in_Ω : δ ∈ <span class="tok-type">P.Ω</span>) (hδ_in_U : δ ∈ (<span class="tok-var">U</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)))
    (affΩ : <span class="tok-type">AffineSubspace</span> <span class="tok-type">ℝ</span> (<span class="tok-type">CoeffVec</span> n)) (hδ_aff : δ ∈ affΩ)
    (hA_dim : <span class="tok-type">dim</span> (<span class="tok-type">meetDir</span> n <span class="tok-var">U</span> affΩ) ≥ <span class="tok-num">1</span>) :
    ∃ δ_bound, δ_bound ∈ (<span class="tok-var">U</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) ∩ frontier <span class="tok-type">P.Ω</span> := <span class="tok-tac">by</span>
<span class="grp mk1"><span class="gn">3.1</span><span class="gbox">  <span class="tok-kw">have</span> h_dim_pos : <span class="tok-num">0</span> < dim (meetDir n U affΩ) := by omega
  haveI : Nontrivial ↥(U ⊓ affΩ.direction) :=
    intersection_nontrivial U affΩ δ hδ_in_U hδ_aff h_dim_pos
  obtain ⟨v_sub, hv_sub_nonzero⟩ := exists_ne (0 : ↑(U ⊓ affΩ.direction))</span></span>
<span class="grp mk1"><span class="gn">3.2</span><span class="gbox">  <span class="tok-kw">let</span> v : <span class="tok-type">CoeffVec</span> n := v_sub.val
  <span class="tok-kw">have</span> h_line_in_intersection : ∀ (t : <span class="tok-type">ℝ</span>), δ + t • v ∈ (<span class="tok-var">U</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) ∩
      (affΩ : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) :=
    <span class="tok-type">line_in_intersection</span> <span class="tok-var">U</span> affΩ δ hδ_in_U hδ_aff v_sub</span></span>
<span class="grp mk1"><span class="gn">3.3</span><span class="gbox">  <span class="tok-kw">have</span> hv_nonzero : v ≠ <span class="tok-num">0</span> := <span class="tok-tac">by</span>
    <span class="tok-tac">intro</span> h; <span class="tok-tac">apply</span> hv_sub_nonzero; <span class="tok-tac">exact</span> <span class="tok-type">Submodule.coe_eq_zero.mp</span> h
  <span class="tok-kw">have</span> h_escapes : ∃ (t : <span class="tok-type">ℝ</span>), <span class="tok-num">0</span> < t ∧ δ + t • v ∉ P.Ω :=
    ray_escapes_of_bounded P.isBounded δ v hδ_in_Ω hv_nonzero
  obtain ⟨t_out, ht_out_pos, ht_out⟩ := h_escapes</span></span>
<span class="grp mk1"><span class="gn">3.4</span><span class="gbox">  <span class="tok-tac">by_cases</span> hδ_front : δ ∈ frontier <span class="tok-type">P.Ω</span>
  · <span class="tok-tac">exact</span> ⟨δ, hδ_in_U, hδ_front⟩
  · <span class="tok-tac">obtain</span> ⟨δ_bound, h_seg, h_front⟩ :=
      <span class="tok-type">segment_boundary_intersection</span> <span class="tok-var">P</span> δ hδ_in_Ω hδ_front v hv_nonzero t_out ht_out</span></span>
<span class="grp mk1"><span class="gn">3.5</span><span class="gbox">    <span class="tok-tac">rw</span> [segment_eq_image] <span class="tok-kw">at</span> h_seg
    <span class="tok-tac">obtain</span> ⟨c, hc_in_Icc, hc_eq⟩ := h_seg
    <span class="tok-kw">have</span> h_rewrite : (<span class="tok-num">1</span> - c) • δ + c • (δ + t_out • v) = δ + (c * t_out) • v :=
      <span class="tok-type">segment_point_rewrite</span> δ v c t_out
    <span class="tok-kw">have</span> h_mem := h_line_in_intersection (c * t_out)
    <span class="tok-tac">rcases</span> h_mem <span class="tok-kw">with</span> ⟨hmem_U, hmem_aff⟩
    <span class="tok-kw">have</span> h_eq : δ_bound = δ + (c * t_out) • v := <span class="tok-tac">by</span>
      <span class="tok-kw">calc</span> δ_bound = (<span class="tok-num">1</span> - c) • δ + c • (δ + t_out • v) := <span class="tok-tac">by</span> <span class="tok-tac">rw</span> [←hc_eq]
        _ = δ + (c * t_out) • v := <span class="tok-tac">by</span> <span class="tok-tac">rw</span> [h_rewrite]
    <span class="tok-tac">exact</span> ⟨δ_bound, h_eq ▸ hmem_U, h_front⟩</span></span></pre></div>

<div class="side">

### Map

| Step | Content |
|:---|:---|
|  **3.1** | `dim(meetDir) ≥ 1 → U ⊓ dir` nontrivial → nonzero `v`  |
|  **3.2** | Line `δ + t • v ⊆ U ∩ affΩ`  |
|  **3.3** | `∃ t_out > 0, δ + t_out • v ∉ Ω` (`t_out = (\|C\|+1)/‖v‖`)  |
|  **3.4** | Segment `[δ, δ + t_out • v]` crosses `∂Ω` (connectedness)  |
|  **3.5** | The witness stays in the slice: $\delta_{\mathrm{bound}}$ on the segment gives $c \in [0,1]$ with $\delta_{\mathrm{bound}} = (1-c)\delta + c(\delta + t_{\mathrm{out}}v) = \delta + (c \cdot t_{\mathrm{out}})v$ (via `segment_eq_image`, `segment_point_rewrite`), a point of the line from 3.2, hence in $U$ — and in $\partial\Omega$ by 3.4 |

</div>
</div>

---

<!-- SLIDE 35 | Step 3: Escape — `ray_escapes_of_bounded` (Lean + map) -->
# Step 3: Escape — `ray_escapes_of_bounded` (Lean + map)
<div class="codeside" style="grid-template-columns:minmax(0,1.58fr) minmax(0,1fr);">
<div class="lean"><div class="lean-head">BasicLemmas.lean:73-91 — full proof, A.1.1–A.1.4 highlighted</div>
<pre><span class="tok-kw">lemma</span> <span class="tok-type">ray_escapes_of_bounded</span> {n : <span class="tok-type">ℕ</span>} {<span class="tok-var">S</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)}
    (hB : <span class="tok-type">Bornology.IsBounded</span> <span class="tok-var">S</span>) (δ v : <span class="tok-type">CoeffVec</span> n)
    (hδ : δ ∈ <span class="tok-var">S</span>) (hv : v ≠ <span class="tok-num">0</span>) : ∃ t : <span class="tok-type">ℝ</span>, <span class="tok-num">0</span> < t ∧ δ + t • v ∉ S := by
<span class="grp mk1"><span class="gn">A.1.1</span><span class="gbox">  <span class="tok-tac">rcases</span> <span class="tok-type">Metric.isBounded_iff.mp</span> hB <span class="tok-kw">with</span> ⟨<span class="tok-var">C</span>, hC⟩</span></span>
<span class="grp mk1"><span class="gn">A.1.2</span><span class="gbox">  <span class="tok-kw">have</span> hv_norm_pos : <span class="tok-num">0</span> < ‖v‖ := norm_pos_iff.mpr hv
  refine ⟨(|C| + 1) / ‖v‖, div_pos (by positivity) hv_norm_pos, ?_⟩
  intro h_contra</span></span>
<span class="grp mk1"><span class="gn">A.1.3</span><span class="gbox">  <span class="tok-kw">have</span> ht_nonneg : (<span class="tok-num">0</span> : <span class="tok-type">ℝ</span>) ≤ (|<span class="tok-var">C</span>| + <span class="tok-num">1</span>) / ‖v‖ := (div_pos (<span class="tok-tac">by</span> <span class="tok-tac">positivity</span>) hv_norm_pos).le
  <span class="tok-kw">have</span> h_dist : dist (δ + ((|<span class="tok-var">C</span>| + <span class="tok-num">1</span>) / ‖v‖) • v) δ = ((|<span class="tok-var">C</span>| + <span class="tok-num">1</span>) / ‖v‖) * ‖v‖ := <span class="tok-tac">by</span>
    <span class="tok-tac">rw</span> [dist_eq_norm]
    <span class="tok-kw">have</span> h_sub : δ + ((|<span class="tok-var">C</span>| + <span class="tok-num">1</span>) / ‖v‖) • v - δ = ((|<span class="tok-var">C</span>| + <span class="tok-num">1</span>) / ‖v‖) • v := <span class="tok-tac">by</span> <span class="tok-tac">abel</span>
    <span class="tok-tac">rw</span> [h_sub, norm_smul, <span class="tok-type">Real.norm_eq_abs</span> _,
      abs_of_nonneg ht_nonneg]
  <span class="tok-kw">have</span> h_le : dist (δ + ((|<span class="tok-var">C</span>| + <span class="tok-num">1</span>) / ‖v‖) • v) δ ≤ <span class="tok-var">C</span> := hC h_contra hδ
  <span class="tok-kw">have</span> h_t_mul : ((|<span class="tok-var">C</span>| + <span class="tok-num">1</span>) / ‖v‖) * ‖v‖ = |<span class="tok-var">C</span>| + <span class="tok-num">1</span> :=
    div_mul_cancel₀ _ (ne_of_gt hv_norm_pos)</span></span>
<span class="grp mk1"><span class="gn">A.1.4</span><span class="gbox">  <span class="tok-tac">rw</span> [h_dist, h_t_mul] <span class="tok-kw">at</span> h_le
  <span class="tok-kw">have</span> : <span class="tok-var">C</span> ≤ |<span class="tok-var">C</span>| := le_abs_self <span class="tok-var">C</span>
  <span class="tok-tac">linarith</span></span></span></pre></div>
<div class="side">

### Map

| Step | Content |
|:---|:---|
|  **A.1.1** | Boundedness gives radius $C$: $\mathrm{dist} \le C$ on $S$  |
|  **A.1.2** | $t_{out} = (\|C\|+1)/\|v\| > 0$ witnesses the existential  |
|  **A.1.3** | Four facts:<br>(i) $t = (\|C\|+1)/\|v\| \ge 0$ — quotient of positives;<br>(ii) $\mathrm{dist}(\delta + t{\cdot}v, \delta) = t\|v\|$ — distance is a norm, $\delta$ cancels, the scalar pulls out, $\|t\| = t$;<br>(iii) that distance is $\le C$ — the boundedness hypothesis applied;<br>(iv) $t\|v\| = \|C\|+1$ — division by nonzero $\|v\|$ cancels  |
|  **A.1.4** | $\|C\|+1 \le C \le \|C\|$, impossible  |

</div>
</div>

---

<!-- SLIDE 36 | Step 3: Escape — `segment_boundary_intersection` (Lean + map) -->
# Step 3: Escape — `segment_boundary_intersection` (Lean + map)

<div class="thm">

**Claim.** Let $\delta \in P.\Omega \setminus \mathrm{frontier}\,P.\Omega$, $v \neq 0$, and $t_{\mathrm{out}}$ with $\delta + t_{\mathrm{out}} \bullet v \notin P.\Omega$. Then $\exists\,\delta_{\mathrm{bound}} \in \mathrm{segment} [ \delta\ ,(\delta + t_{\mathrm{out}} \bullet v)$ ] with $\delta_{\mathrm{bound}} \in \mathrm{frontier}\,P.\Omega$.

**Proof.** **A.2.1** Assume $\Omega$ is closed and prove by contradiction (h_no_front : ∀ δ_bound ∈ segment ℝ δ (δ + t_out • v), δ_bound ∉ frontier P.Ω , and goal becomes false)
**A.2.2** The segment is then covered by the union of the two opens $\mathrm{int}\,\Omega$ and $\mathrm{int}(\Omega^c)$. Points in $\Omega$ off the frontier are interior since $\Omega$ is closed ($\partial\Omega = \Omega \setminus \mathrm{int}\,\Omega$), and points outside $\Omega$ lie in the open complement, hence in its interior. 
**A.2.3** Both opens meet the segment: $\delta$ lies in $\mathrm{int}\,\Omega$ (in $\Omega$ yet off the frontier), and $\delta + t_{\mathrm{out}}v$ lies in $\mathrm{int}(\Omega^c)$ (outside the closed $\Omega$); moreover the two opens are disjoint, $\mathrm{int}\,\Omega \cap \mathrm{int}(\Omega^c) = \emptyset$. 
**A.2.4** Connectedness of the segment forces a point in both — inside $\emptyset$, contradiction.

</div>

<div class="codeside" style="grid-template-columns:minmax(0,1.45fr) minmax(0,1fr);">
<div class="lean"><div class="lean-head">PreliminaryLemmas.lean:273-294 — A.2.1–A.2.4 highlighted</div>
<pre><span class="tok-kw">lemma</span> <span class="tok-type">segment_boundary_intersection</span> {n : <span class="tok-type">ℕ</span>} (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n) (δ : <span class="tok-type">CoeffVec</span> n)
    (hδ_in_Ω : δ ∈ <span class="tok-type">P.Ω</span>) (hδ_not_front : δ ∉ frontier <span class="tok-type">P.Ω</span>)
    (v : <span class="tok-type">CoeffVec</span> n) (_hv_nonzero : v ≠ <span class="tok-num">0</span>) (t_out : <span class="tok-type">ℝ</span>) (ht_out : δ + t_out • v ∉ <span class="tok-type">P.Ω</span>) :
    ∃ δ_bound ∈ segment <span class="tok-type">ℝ</span> δ (δ + t_out • v), δ_bound ∈ frontier <span class="tok-type">P.Ω</span> := <span class="tok-tac">by</span>
<span class="grp mk1"><span class="gn">A.2.4</span><span class="gbox">  <span class="tok-kw">have</span> h_conn : <span class="tok-type">IsConnected</span> (segment <span class="tok-type">ℝ</span> δ (δ + t_out • v)) :=
    <span class="tok-type">segment_is_connected</span> δ v t_out</span></span>
<span class="grp mk1"><span class="gn">A.2.1</span><span class="gbox">  <span class="tok-kw">have</span> h_closed : <span class="tok-type">IsClosed</span> <span class="tok-type">P.Ω</span> := <span class="tok-type">P.isCompact.isClosed</span>
  <span class="tok-tac">by_contra</span> h_no_front
  <span class="tok-tac">push_neg</span> <span class="tok-kw">at</span> h_no_front</span></span>
<span class="grp mk1"><span class="gn">A.2.2</span><span class="gbox">  <span class="tok-kw">have</span> h_cover : segment <span class="tok-type">ℝ</span> δ (δ + t_out • v) ⊆ (interior <span class="tok-type">P.Ω</span>) ∪ interior (<span class="tok-type">P.Ωᶜ</span>) :=
    <span class="tok-type">segment_cover_by_interior_and_complement</span> <span class="tok-var">P</span> δ v t_out h_closed h_no_front</span></span>
<span class="grp mk1"><span class="gn">A.2.3</span><span class="gbox">  <span class="tok-kw">have</span> h_in_u : (segment <span class="tok-type">ℝ</span> δ (δ + t_out • v) ∩ interior <span class="tok-type">P.Ω</span>).<span class="tok-type">Nonempty</span> :=
    <span class="tok-type">segment_intersects_interior</span> <span class="tok-var">P</span> δ v t_out hδ_in_Ω hδ_not_front h_closed
  <span class="tok-kw">have</span> h_in_v : (segment <span class="tok-type">ℝ</span> δ (δ + t_out • v) ∩ interior (<span class="tok-type">P.Ωᶜ</span>)).<span class="tok-type">Nonempty</span> :=
    <span class="tok-type">segment_intersects_complement_interior</span> <span class="tok-var">P</span> δ v t_out ht_out h_closed
  <span class="tok-kw">have</span> huv_empty : interior <span class="tok-type">P.Ω</span> ∩ interior (<span class="tok-type">P.Ωᶜ</span>) = ∅ :=
    <span class="tok-type">interior_and_complement_interior_disjoint</span> <span class="tok-var">P</span></span></span>
<span class="grp mk1"><span class="gn">A.2.4</span><span class="gbox">  <span class="tok-kw">have</span> h_pre := h_conn.<span class="tok-num">2</span> (interior <span class="tok-type">P.Ω</span>) (interior (<span class="tok-type">P.Ωᶜ</span>)) isOpen_interior isOpen_interior
  <span class="tok-kw">have</span> h_inter_nonempty := h_pre h_cover h_in_u h_in_v
  <span class="tok-tac">obtain</span> ⟨x, hx_s, hx_uv⟩ := h_inter_nonempty
  <span class="tok-tac">rw</span> [huv_empty] <span class="tok-kw">at</span> hx_uv
  <span class="tok-tac">exact</span> hx_uv</span></span></pre></div>


<div class="side">

### Map

| Step | Content |
|:---|:---|
|  **A.2.1** | Assume no segment point hits the frontier; goal becomes `False`  |
|  **A.2.2** | Covered by $\mathrm{int}\,\Omega \cup \mathrm{int}(\Omega^c)$ (`frontier_eq_for_closed`)  |
|  **A.2.3** | Both opens meet the segment ($\delta \in \mathrm{int}\,\Omega$, $\delta + t_{\mathrm{out}}v \in \mathrm{int}(\Omega^c)$) and are disjoint |
|  **A.2.4** | `segment_is_connected` (`BasicLemmas.lean:46`) forces a point in both — in $\emptyset$  |

</div>
</div>

---

<!-- SLIDE 37 | Step 3: Escape — slice wrappers `Psr`/`Psc` (Lean + map) -->
# Step 3: Escape — slice wrappers `Psr`/`Psc` (Lean + map)
<div class="codeside" style="display:grid;grid-template-columns:minmax(0,35%) 1fr;column-gap:16px;align-items:start;margin-top:8px;">
<div style="min-width:0;"><div class="lean" style="margin:0;"><div class="lean-head">PreliminaryLemmas.lean:371-384</div>

<pre><span class="grp mk1"><span class="gn">A.3</span><span class="gbox"><span class="tok-kw">lemma</span> <span class="tok-type">exists_boundary_point_in_Psr</span> {n : <span class="tok-type">ℕ</span>} (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n) (r : <span class="tok-type">ℝ</span>) (δ : <span class="tok-type">CoeffVec</span> n)
    (hδ_in_Ω : δ ∈ <span class="tok-type">P.Ω</span>) (hδ_in_Psr : δ ∈ <span class="tok-type">PsrSet</span> n r)
    (affΩ : <span class="tok-type">AffineSubspace</span> <span class="tok-type">ℝ</span> (<span class="tok-type">CoeffVec</span> n)) (hδ_aff : δ ∈ affΩ)
    (hA_dim : <span class="tok-type">dim</span> (<span class="tok-type">meetDir</span> n (<span class="tok-type">P_sr</span> n r) affΩ) ≥ <span class="tok-num">1</span>) :
    ∃ δ_bound, δ_bound ∈ <span class="tok-type">PsrSet</span> n r ∩ frontier <span class="tok-type">P.Ω</span> :=
  <span class="tok-type">exists_boundary_point_in_submodule</span> <span class="tok-var">P</span> (<span class="tok-type">P_sr</span> n r) δ hδ_in_Ω hδ_in_Psr affΩ hδ_aff hA_dim</span></span>

<span class="tok-com">/-- Complex case (U = P_sc n s): thin wrapper over the generic lemma. -/</span>
<span class="grp mk1"><span class="gn">A.3</span><span class="gbox"><span class="tok-kw">lemma</span> <span class="tok-type">exists_boundary_point_in_Psc</span> {n : <span class="tok-type">ℕ</span>} (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n) (s : <span class="tok-type">ℂ</span>) (δ : <span class="tok-type">CoeffVec</span> n)
    (hδ_in_Ω : δ ∈ <span class="tok-type">P.Ω</span>) (hδ_in_Psc : δ ∈ <span class="tok-type">PscSet</span> n s)
    (affΩ : <span class="tok-type">AffineSubspace</span> <span class="tok-type">ℝ</span> (<span class="tok-type">CoeffVec</span> n)) (hδ_aff : δ ∈ affΩ)
    (hA_dim : <span class="tok-type">dim</span> (<span class="tok-type">meetDir</span> n (<span class="tok-type">P_sc</span> n s) affΩ) ≥ <span class="tok-num">1</span>) :
    ∃ δ_bound, δ_bound ∈ <span class="tok-type">PscSet</span> n s ∩ frontier <span class="tok-type">P.Ω</span> :=
  <span class="tok-type">exists_boundary_point_in_submodule</span> <span class="tok-var">P</span> (<span class="tok-type">P_sc</span> n s) δ hδ_in_Ω hδ_in_Psc affΩ hδ_aff hA_dim</span></span></pre></div>
</div>

<div class="side">

### Map

| Step | Content |
|:--|:--|
| **A.1** | `ray_escapes_of_bounded` (:73): $t_{out}$ = (\|C\|+1)/\|v\| outside $S$ |
| **A.2** | `segment_boundary_intersection` (:273): two-opens cover ⇒ $\partial\Omega$ hit (27j–27k) |
| **A.3** | `_in_Psr` / `_Psc` (:371,379): $U$ := $P_{s_r}$ / $P_{s_c}$ (this slide) |

</div>
</div>

---
<!-- SLIDE 38 | Step 4: Exposed face — Lean + map -->
# Step 4: Exposed face — Lean + map

<style scoped>
h1 { font-size: 1.05em; margin-bottom: 2px; }
.thm { font-size: 0.78em; }
.thm p { margin: 0.2em 0; }
.codeside { column-gap: 10px; margin-top: 2px; }
.codeside .lean .grp { margin: 0; }
</style>
<div class="thm">

**Claim.** Let $\delta_{\mathrm{bound}} \in \mathrm{frontier}\,P.\Omega \cap \mathrm{PsrSet}\,n\,r = =\; \{\,\delta \in \mathbb{R}^{n+1} \mid P_\delta(r) = 0\,\} \;=\; \{\,\delta \mid \delta_0 + \delta_1 r + \cdots + \delta_n r^n = 0\,\}$ with $(\mathrm{interior}\,P.\Omega).\mathrm{Nonempty}$. Then there exists $F$ with $\mathrm{IsExposedFace}\,P\,F \land \delta_{\mathrm{bound}} \in F \land (r:\mathbb{C}) \in \mathrm{RootSpaceSet}\,F$.

</div>

<div class="codeside">
<div class="lean"><div class="lean-head">ExposedFaceLemmas.lean:96-136</div>
<pre style="font-size:0.32em;line-height:1.08;padding:0 6px;"><span class="tok-kw">lemma</span> <span class="tok-type">exists_exposed_face_containing_boundary_point</span> {n : <span class="tok-type">ℕ</span>} (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n)
    (r : <span class="tok-type">ℝ</span>) (δ_bound : <span class="tok-type">CoeffVec</span> n)
    (hδ_bound_front : δ_bound ∈ frontier <span class="tok-type">P.Ω</span>)
    (hδ_bound_Psr : δ_bound ∈ <span class="tok-type">PsrSet</span> n r)
    (h_int_nonempty : (interior <span class="tok-type">P.Ω</span>).<span class="tok-type">Nonempty</span>) :
    ∃ <span class="tok-var">F</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n), <span class="tok-type">IsExposedFace</span> <span class="tok-var">P</span> <span class="tok-var">F</span> ∧ δ_bound ∈ <span class="tok-var">F</span> ∧ (r : <span class="tok-type">ℂ</span>) ∈ <span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span> := <span class="tok-tac">by</span>
<span class="grp mk1"><span class="gn">4.1</span><span class="gbox">  <span class="tok-kw">have</span> hδ_bound_in_Ω : δ_bound ∈ <span class="tok-type">P.Ω</span> := <span class="tok-type">frontier_point_in_Ω</span> <span class="tok-var">P</span> δ_bound hδ_bound_front
  <span class="tok-kw">have</span> hδ_bound_not_int : δ_bound ∉ interior <span class="tok-type">P.Ω</span> :=
    <span class="tok-type">frontier_point_not_interior</span> <span class="tok-var">P</span> δ_bound hδ_bound_front</span></span>
<span class="grp mk1"><span class="gn">4.2</span><span class="gbox">  <span class="tok-kw">have</span> h_convex : <span class="tok-type">Convex</span> <span class="tok-type">ℝ</span> <span class="tok-type">P.Ω</span> := convex_convexHull <span class="tok-type">ℝ</span> _
  <span class="tok-kw">have</span> h_int_convex : <span class="tok-type">Convex</span> <span class="tok-type">ℝ</span> (interior <span class="tok-type">P.Ω</span>) := h_convex.interior
  <span class="tok-kw">have</span> h_int_open : <span class="tok-type">IsOpen</span> (interior <span class="tok-type">P.Ω</span>) := isOpen_interior</span></span>
<span class="grp mk1"><span class="gn">4.3</span><span class="gbox">  <span class="tok-tac">obtain</span> ⟨f, hf_strict⟩ :=
    geometric_hahn_banach_open_point h_int_convex h_int_open hδ_bound_not_int</span></span>
<span class="grp mk1"><span class="gn">4.4</span><span class="gbox">  <span class="tok-kw">have</span> hf_ne : f ≠ <span class="tok-num">0</span> := <span class="tok-type">supporting_func_nonzero</span> <span class="tok-var">P</span> f δ_bound hf_strict h_int_nonempty</span></span>
<span class="grp mk1"><span class="gn">4.5</span><span class="gbox">  <span class="tok-kw">let</span> c : <span class="tok-type">ℝ</span> := f δ_bound</span></span>
<span class="grp mk1"><span class="gn">4.4</span><span class="gbox">  <span class="tok-kw">let</span> f_lin : <span class="tok-type">CoeffVec</span> n →ₗ[<span class="tok-type">ℝ</span>] <span class="tok-type">ℝ</span> := f.toLinearMap
  <span class="tok-kw">have</span> hf_lin_ne : f_lin ≠ <span class="tok-num">0</span> := <span class="tok-tac">by</span>
    <span class="tok-tac">intro</span> heq
    <span class="tok-tac">apply</span> hf_ne
    <span class="tok-tac">ext</span> x
    <span class="tok-kw">have</span> : f_lin x = <span class="tok-num">0</span> := <span class="tok-tac">by</span>
      <span class="tok-tac">rw</span> [heq]
      <span class="tok-tac">simp</span>
    <span class="tok-tac">exact</span> this</span></span>
<span class="grp mk1"><span class="gn">4.6</span><span class="gbox">  <span class="tok-kw">have</span> hc_upper : ∀ x ∈ <span class="tok-type">P.Ω</span>, f_lin x ≤ c :=
    <span class="tok-type">supporting_hyperplane_upper_bound</span> <span class="tok-var">P</span> f c hf_strict h_int_nonempty</span></span>
<span class="grp mk1"><span class="gn">4.7</span><span class="gbox">  <span class="tok-kw">let</span> hp : <span class="tok-type">SupportingHyperplane</span> <span class="tok-var">P</span> := {
    f           := f_lin
    c           := c
    nonzero     := hf_lin_ne
    upper_bound := hc_upper
    touches     := ⟨δ_bound, hδ_bound_in_Ω, <span class="tok-tac">rfl</span>⟩
  }</span></span>
<span class="grp mk1"><span class="gn">4.8</span><span class="gbox">  <span class="tok-kw">have</span> hδ_in_face : δ_bound ∈ <span class="tok-type">ExposedFace</span> hp := <span class="tok-tac">by</span>
    <span class="tok-tac">unfold</span> <span class="tok-type">ExposedFace</span>
    <span class="tok-tac">simp</span> only [<span class="tok-type">Set.mem_setOf_eq</span>]
    <span class="tok-tac">exact</span> ⟨hδ_bound_in_Ω, <span class="tok-tac">rfl</span>⟩</span></span>
<span class="grp mk1"><span class="gn">4.9</span><span class="gbox">  <span class="tok-kw">have</span> hr_in_rootspace : (r : <span class="tok-type">ℂ</span>) ∈ <span class="tok-type">RootSpaceSet</span> (<span class="tok-type">ExposedFace</span> hp) :=
    <span class="tok-type">rootspace_mem_of_eval_zero</span> r δ_bound hδ_bound_Psr (<span class="tok-type">ExposedFace</span> hp) hδ_in_face</span></span>
<span class="grp mk1"><span class="gn">4.10</span><span class="gbox">  <span class="tok-tac">exact</span> ⟨<span class="tok-type">ExposedFace</span> hp, ⟨hp, <span class="tok-tac">rfl</span>⟩, hδ_in_face, hr_in_rootspace⟩</span></span></pre></div>
<div class="side">

### Map

| Step | Content |
|:---|:---|
| **4.1** | $\delta_{\mathrm{bound}} \in \Omega \setminus \mathrm{int}\,\Omega$ (frontier points lie in $\Omega$ but never inside) |
| **4.2** | $\mathrm{int}\,\Omega$ is convex and open: the Hahn–Banach premises |
| **4.3** | Geometric Hahn–Banach (open convex set vs. outside point) gives continuous linear $f$ with $f < f(\delta_{\mathrm{bound}})$ on the interior |
| **4.4** | *Claim:* $f \neq 0$, and its underlying linear map $f_{\mathrm{lin}} : \mathbb{R}^{n+1} \to \mathbb{R}$, $f_{\mathrm{lin}}(x) := f(x)$, likewise satisfies $f_{\mathrm{lin}} \neq 0$. , so if f = 0, then we get 0 < 0 , which is a contradiction |
| **4.5** | let $c := f(\delta_{\mathrm{bound}})$ |
| **4.6** | $f < c$ on the interior gives $f \le c$ on all of $\Omega$ (closure plus closed sublevel set) |
| **4.7** | we construct the hyperplane $(f, c, \text{nonzero}, \text{upper bound}, \text{touches})$ |
| **4.8** | $\delta_{\mathrm{bound}} \in \Omega$ with $f(\delta_{\mathrm{bound}}) = c$ puts it in $F = \Omega \cap \{f = c\}$ |
| **4.9** | $(r:\mathbb{C})\in R(F)\stackrel{\text{def}}{=}\{\,s\in\mathbb{C}\mid\exists\,\delta\in F,\;P_{\delta}(s)=0\,\}$. Because the boundary point satisfies $P_{\delta_{\mathrm{bound}}}(r)=0$ (i.e. $\delta_{\mathrm{bound}}\in P_{s_r}(r)$), the witness certifies the membership, so $(r:\mathbb{C})\in R(F)$.
| **4.10** | $\delta_{\mathrm{bound}}\in F\subseteq\Omega$ and $(r:\mathbb{C})\in R(F)$. In words: the same coefficient vector that lies on the frontier of the polytope belongs to the exposed face $F$, and the complex number $r$ is an element of the root‑space set of that face.

</div>
</div>

---
<!-- SLIDE 39 | Step 5: Descend — Lean + map (1/2) -->
# Step 5: Descend — Lean + map (1/2)

<style scoped>
h1 { font-size: 1.05em; margin-bottom: 2px; }
.thm { font-size: 0.78em; }
.thm p { margin: 0.2em 0; }
.codeside { column-gap: 10px; margin-top: 2px; }
</style>
<div class="thm">

**Claim.** Let $\Omega \subset \mathbb{R}^{n+1}$ be a polytope with $n \ge 1$, and let $F \subseteq \mathbb{R}^{n+1}$ be an exposed face of $\Omega$ with $\dim \mathrm{aff}(F) \ge 2$. If $r \in \mathbb{R}$ satisfies $(r:\mathbb{C}) \in R(F)$, then there exists an exposed edge $E$ of $\Omega$ with $(r:\mathbb{C}) \in R(E)$.
</div>

<div class="codeside">
<div class="lean"><div class="lean-head">EdgeDescent.lean:691-715 — part 1, 5.1–5.6 highlighted</div>
<pre style="font-size:0.34em;line-height:1.1;padding:1px 6px;"><span class="tok-kw">lemma</span> <span class="tok-type">descend_to_exposed_edge</span> {n : <span class="tok-type">ℕ</span>} (hn : n ≥ <span class="tok-num">1</span>) (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n) (r : <span class="tok-type">ℝ</span>)
    (<span class="tok-var">F</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) (hF_exp : <span class="tok-type">IsExposedFace</span> <span class="tok-var">P</span> <span class="tok-var">F</span>)
    (hs_F : (r : <span class="tok-type">ℂ</span>) ∈ <span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span>)
    (hF_dim_ge_2 : <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">F</span>).direction ≥ <span class="tok-num">2</span>) :
    ∃ <span class="tok-var">E</span>, <span class="tok-type">IsExposedEdge</span> <span class="tok-var">P</span> <span class="tok-var">E</span> ∧ (r : <span class="tok-type">ℂ</span>) ∈ <span class="tok-type">RootSpaceSet</span> <span class="tok-var">E</span> := <span class="tok-tac">by</span>
  <span class="tok-kw">let</span> m_F := <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">F</span>).direction
  <span class="tok-tac">by_cases</span> hm_F_1 : m_F = <span class="tok-num">1</span>
  · <span class="tok-tac">refine</span> ⟨<span class="tok-var">F</span>, <span class="tok-type">isExposedEdge_of_dim_1</span> hF_exp hm_F_1, hs_F⟩
  · <span class="tok-kw">have</span> hm_F_ge_2 : m_F ≥ <span class="tok-num">2</span> := <span class="tok-tac">by</span> <span class="tok-tac">omega</span>
<span class="grp mk1"><span class="gn">5.1</span><span class="gbox">    <span class="tok-tac">obtain</span> ⟨δ_F, hδ_F_in_F, hδ_F_root⟩ :
      ∃ δ ∈ <span class="tok-var">F</span>, ((<span class="tok-type">polyOfVec</span> δ).map (algebraMap <span class="tok-type">ℝ</span> <span class="tok-type">ℂ</span>)).<span class="tok-type">IsRoot</span> (r : <span class="tok-type">ℂ</span>) := hs_F
    <span class="tok-kw">let</span> affF := affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">F</span></span></span>
<span class="grp mk1"><span class="gn">5.1</span><span class="gbox">    <span class="tok-kw">have</span> hδ_F_Psr : δ_F ∈ <span class="tok-type">PsrSet</span> n r := <span class="tok-type">mem_P_sr_of_isRoot</span> r δ_F hδ_F_root</span></span>
<span class="grp mk1"><span class="gn">5.2</span><span class="gbox">    <span class="tok-kw">have</span> h_inter_dim : <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (<span class="tok-type">meetDir</span> n (<span class="tok-type">P_sr</span> n r) affF) ≥ <span class="tok-num">1</span> :=
      <span class="tok-type">intersection_affine_dim_ge_one</span> (<span class="tok-type">P_sr</span> n r) affF δ_F hδ_F_Psr
        (subset_affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">F</span> hδ_F_in_F) (<span class="tok-type">P_sr_dimension</span> r) hm_F_ge_2</span></span>
<span class="grp mk1"><span class="gn">5.3</span><span class="gbox">    <span class="tok-tac">obtain</span> ⟨δ_bound, hδ_bound_inter, hδ_bound_front, hδ_bound_not_relint⟩ :=
      <span class="tok-type">exists_boundary_point_in_face_rootspace</span> <span class="tok-var">P</span> r δ_F <span class="tok-var">F</span> hF_exp hδ_F_in_F hδ_F_Psr h_inter_dim</span></span>
<span class="grp mk1"><span class="gn">5.5</span><span class="gbox">    <span class="tok-kw">have</span> hδ_bound_in_F : δ_bound ∈ <span class="tok-var">F</span> := hδ_bound_inter.<span class="tok-num">1</span>
    <span class="tok-kw">have</span> hδ_bound_Psr : δ_bound ∈ (<span class="tok-type">P_sr</span> n r : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) := hδ_bound_inter.<span class="tok-num">2</span></span></span>
<span class="grp mk1"><span class="gn">5.4</span><span class="gbox">    <span class="tok-tac">obtain</span> ⟨<span class="tok-var">G</span>, hG_exp, hδ_bound_in_G, hG_dim_lt⟩ :=
      exists_proper_subface_of_boundary_point <span class="tok-var">P</span> <span class="tok-var">F</span> hF_exp δ_bound
        hδ_bound_in_F hδ_bound_front hδ_bound_not_relint hm_F_ge_2</span></span>
<span class="grp mk1"><span class="gn">5.6</span><span class="gbox">    <span class="tok-kw">have</span> hs_G : (r : <span class="tok-type">ℂ</span>) ∈ <span class="tok-type">RootSpaceSet</span> <span class="tok-var">G</span> :=
      <span class="tok-type">rootspace_mem_of_eval_zero</span> r δ_bound hδ_bound_Psr <span class="tok-var">G</span> hδ_bound_in_G</span></span></pre></div>
<div class="side">

### Map

| Step | Content |
|:---|:---|
| **5.1** | $(r:\mathbb{C}) \in R(F)$ gives $\delta_F \in F$ in the zero set $U = \{\delta \mid P_{\delta}(r) = 0\}$. |
| **5.2** | $\dim U = n$ and $\dim\mathrm{aff}\,F \ge 2$ give a nonzero root-preserving direction in $\mathrm{aff}\,F$ (Grassmann). |
| **5.3** | Follow it to $\delta_{\mathrm{bound}} \in F$ with $P_{\delta_{\mathrm{bound}}}(r) = 0$ on the relative boundary. |
| **5.4** | A supporting hyperplane there cuts out a proper exposed $G \subset F$ ($\dim G < \dim F$). |
| **5.5** | $\delta_{\mathrm{bound}} \in G$ keeps the vanishing. |
| **5.6** | Hence $(r:\mathbb{C}) \in R(G)$ — the root moves to the smaller face. |

</div>
</div>

---

<!-- SLIDE 40 | Step 5: Descend — Lean + map (2/2) -->
# Step 5: Descend — Lean + map (2/2)

<style scoped>
h1 { font-size: 1.05em; margin-bottom: 2px; }
.thm { font-size: 0.78em; }
.thm p { margin: 0.2em 0; }
.codeside { column-gap: 10px; margin-top: 2px; }
</style>

<div class="codeside">
<div class="lean"><div class="lean-head">EdgeDescent.lean:716-733 — part 2, 5.7–5.10 highlighted</div>
<pre style="font-size:0.34em;line-height:1.1;padding:1px 6px;"><span class="grp mk1"><span class="gn">5.8</span><span class="gbox">    <span class="tok-tac">by_cases</span> hG_dim_ge_2 : <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">G</span>).direction ≥ <span class="tok-num">2</span>
    · <span class="tok-tac">exact</span> <span class="tok-type">descend_to_exposed_edge</span> hn <span class="tok-var">P</span> r <span class="tok-var">G</span> hG_exp hs_G hG_dim_ge_2</span></span>
<span class="grp mk1"><span class="gn">5.9</span><span class="gbox">    · <span class="tok-tac">by_cases</span> hG_dim_1 : <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">G</span>).direction = <span class="tok-num">1</span>
      · <span class="tok-tac">refine</span> ⟨<span class="tok-var">G</span>, <span class="tok-type">isExposedEdge_of_dim_1</span> hG_exp hG_dim_1, hs_G⟩</span></span>
<span class="grp mk1"><span class="gn">5.10</span><span class="gbox">      · <span class="tok-com">-- dim(G) = 0: G is the singleton {δ_bound}; get an edge through it.</span>
        <span class="tok-kw">have</span> hG_dim_0 : <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">G</span>).direction = <span class="tok-num">0</span> := <span class="tok-tac">by</span>
          <span class="tok-kw">have</span> h_not_ge_2 : ¬ <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">G</span>).direction ≥ <span class="tok-num">2</span> := hG_dim_ge_2
          <span class="tok-kw">have</span> h_not_1 : ¬ <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">G</span>).direction = <span class="tok-num">1</span> := hG_dim_1
          <span class="tok-tac">omega</span>
        <span class="tok-kw">have</span> hG_single : <span class="tok-var">G</span> = {δ_bound} :=
          <span class="tok-type">exposed_face_dim_zero_singleton</span> <span class="tok-var">G</span> hG_dim_0 δ_bound hδ_bound_in_G
        <span class="tok-tac">obtain</span> ⟨<span class="tok-var">E</span>, hE_edge, hδ_in_E⟩ :=
          <span class="tok-type">exists_exposed_edge_of_singleton</span> hn <span class="tok-var">P</span> δ_bound <span class="tok-var">G</span> hG_exp hG_single
        <span class="tok-kw">have</span> h_root_E : (r : <span class="tok-type">ℂ</span>) ∈ <span class="tok-type">RootSpaceSet</span> <span class="tok-var">E</span> :=
          <span class="tok-type">rootspace_mem_of_eval_zero</span> r δ_bound hδ_bound_Psr <span class="tok-var">E</span> hδ_in_E
        <span class="tok-tac">exact</span> ⟨<span class="tok-var">E</span>, hE_edge, h_root_E⟩</span></span>
<span class="grp mk1"><span class="gn">5.7</span><span class="gbox">  <span class="tok-kw">termination_by</span> <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">F</span>).direction
  <span class="tok-kw">decreasing_by</span> <span class="tok-tac">exact</span> hG_dim_lt</span></span></pre></div>
<div class="side">

### Map

| Step | Content |
|:---|:---|
| **5.7** | Each descent step replaces $F$ by $G$ with $\dim G < \dim F$. Hence the dimension drops by at least one at every iteration. Therefore the process can continue only finitely many times. |
| **5.8** | If $\dim G \ge 2$, then $G$ satisfies the same hypothesis as $F$. Hence the same argument applies with $F$ replaced by $G$. This is the recursive descent step. |
| **5.9** | If $\dim G = 1$, then $G$ is a segment, i.e. an exposed edge. Since $(r:\mathbb{C}) \in R(G)$ already holds, the descent stops here. Take $E = G$ to conclude. |
| **5.10** | If $\dim G = 0$, then $G$ is the singleton $\{\delta_{\mathrm{bound}}\}$. Choose an exposed edge $E$ through this vertex, so $\delta_{\mathrm{bound}} \in E$. Since $P_{\delta_{\mathrm{bound}}}(r) = 0$, the root transfers to $E$ and the proof is complete. |

</div>
</div>

---

<!-- SLIDE 41 | Step 6: Degenerate cases — Lean + map -->
# Step 6: Degenerate cases — Lean + map
<div class="thm">

**Claim.** Let $m := \dim\mathrm{aff}(\Omega)$. Then $m = 0$ is impossible ($\mathrm{int}\,\Omega \neq \emptyset$), and $m = 1$ makes $\Omega$ itself the edge.

**Proof.** **D.1** $m = 0$: `polytope_direction_dim_pos` gives $\dim \ge 1$, contradiction. **D.2** $m = 1$: `polytope_dim1_is_exposed_edge` makes $\Omega$ itself the edge; $s = \bar{r}$ moves the root witness to $E$.

</div>

<div class="codeside">
<div class="lean"><div class="lean-head">Lemma61.lean:191-203 — degenerate cases, ①② highlighted</div>
<pre><span class="grp mk1"><span class="gn">①</span><span class="gbox">  · <span class="tok-tac">by_cases</span> hm0 : m = <span class="tok-num">0</span>
    · <span class="tok-kw">have</span> h_pos : <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-type">P.Ω</span>).direction ≥ <span class="tok-num">1</span> :=
        <span class="tok-type">polytope_direction_dim_pos</span> <span class="tok-var">P</span>
      <span class="tok-tac">omega</span></span></span>
<span class="grp mk1"><span class="gn">②</span><span class="gbox">    · <span class="tok-kw">have</span> hm1 : m = <span class="tok-num">1</span> := <span class="tok-tac">by</span> <span class="tok-tac">omega</span>
      <span class="tok-kw">have</span> h_Ω_is_edge : <span class="tok-type">IsExposedEdge</span> <span class="tok-var">P</span> <span class="tok-type">P.Ω</span> :=
        <span class="tok-type">polytope_dim1_is_exposed_edge</span> hn <span class="tok-var">P</span> hm1
      <span class="tok-tac">refine</span> ⟨<span class="tok-type">P.Ω</span>, h_Ω_is_edge, ?_⟩
      <span class="tok-tac">rw</span> [hs_real]
      <span class="tok-tac">exact</span> <span class="tok-type">rootspace_mem_of_eval_zero</span> s.re δ
        (<span class="tok-type">mem_P_sr_of_isRoot</span> s.re δ (<span class="tok-tac">by</span>
          <span class="tok-tac">rw</span> [← hs_real]
          <span class="tok-tac">exact</span> hδ_root)) <span class="tok-type">P.Ω</span> hδ_in_Ω</span></span></pre></div>
<div class="side">

### Map

| Step | Content |
|:---|:---|
| **D.1 ①** | $m = 0$ contradicts nonempty interior ($\dim \ge 1$) |
| **D.2 ②** | $m = 1$: $\Omega$ itself the edge; $s = \bar{r}$ moves the root $\Omega \to E$ |

</div>
</div>

---

<!-- SLIDE 42 | Lemma 6.1 (real case) — recap -->
# Lemma 6.1 (real case) — recap
1. **Step 1** unpacked $s \in R(\Omega)$ to $\delta \in P_{s_r}(r)$ with $s = \bar{r}$.
2. **Step 2** gave $\dim(U \cap \mathrm{aff}\,\Omega) \ge 1$.
3. **Step 3** followed it to $\delta_{\mathrm{bound}} \in P_{s_r} \cap \partial\Omega$.
4. **Step 4** separated at $\delta_{\mathrm{bound}}$: exposed $F \ni \delta_{\mathrm{bound}}$ with $\bar{r} \in R(F)$.
5. **Step 5** descended $F \to G \to \cdots \to E$ with $\bar{r} \in R(E)$, $\dim E = 1$.

Degenerate cases (`lemma61_real:191-203`): $m = 0$ contradicts nonempty interior; $m = 1$ makes $\Omega$ itself the edge (`polytope_dim1_is_exposed_edge`).

---

<!-- SLIDE 43 | Lemma 6.1: complex case — what is extra -->
# Lemma 6.1: complex case — what is extra

<style scoped>
h1 { font-size: 1.15em; margin-bottom: 2px; }
</style>
<div class="columns">
<div class="col">

### Mathematics
- **Claim.** If $s \in R(\Omega)$ with $\mathrm{Im}(s) \ne 0$, then $s \in R(F)$ for an exposed face $F$ with $\dim\mathrm{aff}(F) \le 2$ — a face, not an edge.
- **Thinner slice.** $U = \{\delta \mid P_\delta(s) = 0\}$ has dimension $n - 1$: real and imaginary parts must each vanish — two equations cut twice.
- **Stronger count.** Grassmann needs direction dimension $\ge 3$ (and $n \ge 2$).
- **Weaker target.** One condition gives a line to walk to an edge; two give isolated points that cannot slide — descent stops at dimension $2$.
- **New degenerate case $n = 1$.** Linear $P_\delta$ forces $s = -\delta_0/\delta_1 \in \mathbb{R}$ unless $\delta_1 = 0$, which Assumption 6.1 forbids.

</div>
<div class="col">

### Lean
- `P_sc_dimension` (`hn : n ≥ 1`, `hs : s.im ≠ 0`): the complex slice has dimension $n - 1$ (evaluation onto $\mathbb{C}$ is surjective of real rank $2$).
- `mem_P_sc_of_isRoot`, `intersection_affine_dim_ge_one_complex` (needs direction dimension $\ge 3$), `exists_boundary_point_in_Psc`: Steps 1–3 with $P_{s_c}$ in place of $P_{s_r}$.
- `exists_exposed_face_containing_boundary_point_complex`: Step 4 for the complex slice.
- `descend_to_exposed_face_with_dim`: Step 5 stopping at dimension $\le 2$.
- Assumption 6.1 as explicit hypothesis `hleading : ∀ v ∈ P.vertices, 0 < v (Fin.last n)`, threaded through `lemma61_complex_with_dim` → `lemma61_complex` → `lemma61`; the $n = 1$ case closes by leading-coefficient positivity (`convexHull_min`).

</div>
</div>

---

<!-- SLIDE 44 | Section 5 · Lemma 6.2, real case -->
<!-- _class: section -->
# Section 5 · Lemma 6.2, real case

---

<!-- SLIDE 45 | Lemma 6.2 (real case) — overview -->
# Lemma 6.2 (real case) — overview
<div class="thm">

**Theorem (Lemma 6.2).** Let $F$ be an exposed face of $\Omega$ with $\dim\mathrm{aff}(F) = 2$. Then $\partial R(F) \subseteq R(\partial F)$: every boundary point of the root space of $F$ is a root on the relative boundary (`lemma62`, `Lemma62.lean:1446`).

</div>

The Lean proof splits on `s_star.im = 0` (`by_cases hreal`): the **real case** (`lemma62_real_case`, this section) goes through $P_{s_r}$ as in Lemma 6.1; the **complex case** (`lemma62_complex_case`) needs the $W$-matrix machinery — future work.

---

<!-- SLIDE 46 | Lemma 6.2 (real case) — goal -->
# Lemma 6.2 (real case) — goal
<div class="thm">

**Goal.** Let $F$ be exposed with $\dim\mathrm{aff}(F) = 2$ and $s^\star \in \mathrm{frontier}\,R(F)$ real ($\mathrm{Im}(s^\star) = 0$). Then $s^\star \in R(\mathrm{relativeBoundary}\,F)$ (`lemma62_real_case`, `Lemma62.lean:127`).

</div>

**Proof sketch.** **6.1–6.3** $R(F)$ is closed, so $s^\star \in R(F)$ with $s^\star = \bar{r}$. **6.4–6.5** Unpack $\delta^\star \in F$; split on relint. **6.6–6.8** Escape to $\delta_{\mathrm{bound}} \in F \cap P_{s_r}$ off the relint. **6.9–6.12** Transfer the root; close Case A the same way.

<div class="lean"><div class="lean-head">PreliminaryLemmas.lean:422-423</div>
<pre><span class="tok-kw">def</span> <span class="tok-type">relativeBoundary</span> (<span class="tok-var">F</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n) :=
  <span class="tok-var">F</span> \ intrinsicInterior <span class="tok-type">ℝ</span> <span class="tok-var">F</span></pre></div>

---

<!-- SLIDE 47 | Lemma 6.2 (real case) — walkthrough 6.1–6.6 -->
# Lemma 6.2 (real case) — walkthrough 6.1–6.6
<div class="codeside">
<div class="lean"><div class="lean-head">Lemma62.lean:127-162, 6.1–6.6 highlighted</div>
<pre style="font-size:0.52em;line-height:1.25;"><span class="tok-kw">theorem</span> <span class="tok-type">lemma62_real_case</span> {n : <span class="tok-type">ℕ</span>}  (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n)
    (<span class="tok-var">F</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) (hF_exp : <span class="tok-type">IsExposedFace</span> <span class="tok-var">P</span> <span class="tok-var">F</span>)
    (hF_dim_2 : <span class="tok-type">dim</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">F</span>).direction = <span class="tok-num">2</span>)
    (s_star : <span class="tok-type">ℂ</span>) (hs_star_front : s_star ∈ frontier (<span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span>)) (hreal : s_star.im = <span class="tok-num">0</span>) :
    s_star ∈ <span class="tok-type">RootSpaceSet</span> (<span class="tok-type">relativeBoundary</span> <span class="tok-var">F</span>) := <span class="tok-tac">by</span>
<span class="grp mk1"><span class="gn">6.1</span><span class="gbox">  <span class="tok-kw">have</span> hF_compact : <span class="tok-type">IsCompact</span> <span class="tok-var">F</span> := <span class="tok-type">isExposedFace_isCompact</span> <span class="tok-var">P</span> hF_exp
  <span class="tok-kw">have</span> hF_convex : <span class="tok-type">Convex</span> <span class="tok-type">ℝ</span> <span class="tok-var">F</span> := <span class="tok-type">isExposedFace_convex</span> <span class="tok-var">P</span> hF_exp</span></span>
<span class="grp mk1"><span class="gn">6.2</span><span class="gbox">  <span class="tok-kw">have</span> h_s_star_eq : s_star = (s_star.re : <span class="tok-type">ℂ</span>) := <span class="tok-tac">by</span>
    <span class="tok-tac">apply</span> <span class="tok-type">Complex.ext</span> <;> <span class="tok-tac">simp</span> [hreal]</span></span>
<span class="grp mk1"><span class="gn">6.3</span><span class="gbox">  <span class="tok-kw">have</span> h_root_closed : <span class="tok-type">IsClosed</span> (<span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span>) :=
    <span class="tok-type">rootSpaceSet_isClosed_of_isCompact</span> hF_compact
  <span class="tok-kw">have</span> hs_star_in_RF : s_star ∈ <span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span> := <span class="tok-tac">by</span>
    <span class="tok-kw">have</span> h_sub : frontier (<span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span>) ⊆ <span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span> := <span class="tok-tac">by</span>
      <span class="tok-kw">calc</span>
        frontier (<span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span>) ⊆ closure (<span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span>) := frontier_subset_closure
        _ = <span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span> := h_root_closed.closure_eq
    <span class="tok-tac">exact</span> h_sub hs_star_front</span></span>
<span class="grp mk1"><span class="gn">6.4</span><span class="gbox">  <span class="tok-tac">rcases</span> hs_star_in_RF <span class="tok-kw">with</span> ⟨δ_star, hδ_star_in_F, hδ_star_root⟩
  <span class="tok-kw">have</span> hδ_star_in_Psr : δ_star ∈ <span class="tok-type">PsrSet</span> n s_star.re :=
    <span class="tok-type">mem_P_sr_of_isRoot</span> s_star.re δ_star (<span class="tok-tac">by</span>
      <span class="tok-tac">rw</span> [h_s_star_eq] <span class="tok-kw">at</span> hδ_star_root
      <span class="tok-tac">exact</span> hδ_star_root)</span></span>
<span class="grp mk1"><span class="gn">6.5</span><span class="gbox">  <span class="tok-tac">by_cases</span> hδ_star_relint : δ_star ∈ intrinsicInterior <span class="tok-type">ℝ</span> <span class="tok-var">F</span>
  · <span class="tok-kw">let</span> <span class="tok-var">U</span> : <span class="tok-type">Submodule</span> <span class="tok-type">ℝ</span> (<span class="tok-type">CoeffVec</span> n) := <span class="tok-type">P_sr</span> n s_star.re
    <span class="tok-kw">let</span> <span class="tok-var">V</span> : <span class="tok-type">Submodule</span> <span class="tok-type">ℝ</span> (<span class="tok-type">CoeffVec</span> n) := (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">F</span>).direction</span></span>
<span class="grp mk1"><span class="gn">6.6</span><span class="gbox">    <span class="tok-kw">have</span> hU_dim : <span class="tok-type">dim</span> <span class="tok-var">U</span> = n := <span class="tok-type">P_sr_dimension</span> s_star.re
    <span class="tok-kw">have</span> hV_dim_ge_2 : <span class="tok-type">dim</span> <span class="tok-var">V</span> ≥ <span class="tok-num">2</span> := <span class="tok-tac">by</span> <span class="tok-tac">rw</span> [hF_dim_2]
    <span class="tok-kw">have</span> h_inter_dim_ge_1 : <span class="tok-type">dim</span> (<span class="tok-var">U</span> ⊓ <span class="tok-var">V</span>) ≥ <span class="tok-num">1</span> :=
      <span class="tok-type">finrank_inf_ge_one</span> <span class="tok-var">U</span> <span class="tok-var">V</span> hU_dim hV_dim_ge_2
    <span class="tok-kw">have</span> h_inter_finrank_pos : <span class="tok-num">0</span> < dim (U ⊓ V) := by omega
    have h_inter_nontrivial : Nontrivial ↥(U ⊓ V) :=
      Module.nontrivial_of_finrank_pos h_inter_finrank_pos
    obtain ⟨v_sub, hv_sub_ne⟩ := exists_ne (0 : ↥(U ⊓ V))
    let v : CoeffVec n := v_sub.val
    have hv_ne : v ≠ 0 := by
      intro h; apply hv_sub_ne; exact Subtype.ext h</span></span></pre></div>
<div class="side">

### Map

| Step | Content |
|:---|:---|
|  **6.1** | $F$ compact and convex from $P.\Omega$  |
|  **6.2** | $\mathrm{Im}(s^\star)=0 \implies s^\star = \bar{r}$  |
|  **6.3** | $R(F)$ closed, so $s^\star \in \mathrm{frontier}\,R(F) \subseteq R(F)$  |
|  **6.4** | $\delta^\star \in F$ with root $\implies \delta^\star \in P_{s_r}(r)$  |
|  **6.5** | Split: off-relint (Case A) vs on-relint (Case B)  |
|  **6.6** | $U = P_{s_r}$ ($\dim n$), $V = \mathrm{dir}$ ($\dim \ge 2$) give nonzero $v$  |

</div>
</div>

---
<!-- SLIDE 48 | Lemma 6.2 (real case) — walkthrough 6.7–6.9 -->
# Lemma 6.2 (real case) — walkthrough 6.7–6.9
<div class="codeside">
<div class="lean"><div class="lean-head">Lemma62.lean:163-190, 6.7–6.9 highlighted</div>
<pre style="font-size:0.52em;line-height:1.25;"><span class="grp mk1"><span class="gn">6.7</span><span class="gbox">    <span class="tok-kw">have</span> hv_U : v ∈ <span class="tok-var">U</span> := <span class="tok-tac">by</span>
      <span class="tok-kw">have</span> h := v_sub.property
      <span class="tok-tac">rw</span> [<span class="tok-type">Submodule.mem_inf</span>] <span class="tok-kw">at</span> h
      <span class="tok-tac">exact</span> h.<span class="tok-num">1</span>
    <span class="tok-kw">have</span> hv_V : v ∈ <span class="tok-var">V</span> := <span class="tok-tac">by</span>
      <span class="tok-kw">have</span> h := v_sub.property
      <span class="tok-tac">rw</span> [<span class="tok-type">Submodule.mem_inf</span>] <span class="tok-kw">at</span> h
      <span class="tok-tac">exact</span> h.<span class="tok-num">2</span>
    <span class="tok-kw">have</span> hv_affF_dir : v ∈ (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">F</span>).direction := hv_V
    <span class="tok-tac">obtain</span> ⟨t_out, ht_out_pos, ht_out⟩ :=
      <span class="tok-type">ray_escapes_of_bounded</span> hF_compact.isBounded δ_star v hδ_star_in_F hv_ne
    <span class="tok-kw">let</span> <span class="tok-var">S</span> : <span class="tok-type">Set</span> <span class="tok-type">ℝ</span> := {t | <span class="tok-num">0</span> ≤ t ∧ δ_star + t • v ∈ <span class="tok-var">F</span>}
    <span class="tok-kw">have</span> hS_nonempty : <span class="tok-type">S.Nonempty</span> := ⟨<span class="tok-num">0</span>, ⟨<span class="tok-tac">by</span> <span class="tok-tac">norm_num</span>, <span class="tok-tac">by</span> <span class="tok-tac">simpa</span> using hδ_star_in_F⟩⟩</span></span>
<span class="grp mk1"><span class="gn">6.8</span><span class="gbox">    <span class="tok-kw">have</span> hS_closed : <span class="tok-type">IsClosed</span> <span class="tok-var">S</span> := <span class="tok-tac">by</span>
      <span class="tok-kw">have</span> h_cont : <span class="tok-type">Continuous</span> (<span class="tok-kw">fun</span> (t : <span class="tok-type">ℝ</span>) => δ_star + t • v) := <span class="tok-tac">by</span>
        <span class="tok-tac">refine</span> <span class="tok-type">Continuous.add</span> continuous_const ?_
        <span class="tok-tac">exact</span> <span class="tok-type">Continuous.smul</span> continuous_id continuous_const
      <span class="tok-kw">have</span> h_preimage_closed : <span class="tok-type">IsClosed</span> {t | δ_star + t • v ∈ <span class="tok-var">F</span>} :=
        hF_compact.isClosed.preimage h_cont
      <span class="tok-kw">have</span> h_nonneg_closed : <span class="tok-type">IsClosed</span> {t : <span class="tok-type">ℝ</span> | <span class="tok-num">0</span> ≤ t} := isClosed_Ici
      <span class="tok-kw">have</span> hS_eq : <span class="tok-var">S</span> = {t | δ_star + t • v ∈ <span class="tok-var">F</span>} ∩ {t : <span class="tok-type">ℝ</span> | <span class="tok-num">0</span> ≤ t} := <span class="tok-tac">by</span>
        <span class="tok-tac">ext</span> t; <span class="tok-tac">constructor</span>
        · rintro ⟨ht_nonneg, ht_mem⟩; <span class="tok-tac">exact</span> ⟨ht_mem, ht_nonneg⟩
        · rintro ⟨ht_mem, ht_nonneg⟩; <span class="tok-tac">exact</span> ⟨ht_nonneg, ht_mem⟩
      <span class="tok-tac">rw</span> [hS_eq]
      <span class="tok-tac">exact</span> h_preimage_closed.inter h_nonneg_closed</span></span>
<span class="grp mk1"><span class="gn">6.9</span><span class="gbox">    <span class="tok-kw">have</span> h_bdd_above : <span class="tok-type">BddAbove</span> <span class="tok-var">S</span> :=
      <span class="tok-type">ray_stay_set_bddAbove</span> hF_convex hδ_star_in_F t_out ht_out_pos ht_out</span></span></pre></div>
<div class="side">

### Map

| Step | Content |
|:---|:---|
|  **6.7** | $v$ splits into slice and direction parts; $t_{out}$ escapes $F$; ray-stay set nonempty at $t = 0$  |
|  **6.8** | $S$ closed: continuous ray meets closed $F$  |
|  **6.9** | $S$ bounded above by $t_{out}$ via convexity (helper `ray_stay_set_bddAbove`)  |

</div>
</div>

---
<!-- SLIDE 49 | Lemma 6.2 (real case) — walkthrough 6.10–6.12 -->
# Lemma 6.2 (real case) — walkthrough 6.10–6.12
<div class="codeside">
<div class="lean"><div class="lean-head">Lemma62.lean:191-220, 6.10–6.12 highlighted</div>
<pre style="font-size:0.52em;line-height:1.25;"><span class="grp mk1"><span class="gn">6.10</span><span class="gbox">    <span class="tok-kw">let</span> t1 := sSup <span class="tok-var">S</span>
    <span class="tok-kw">have</span> h_max : t1 ∈ <span class="tok-var">S</span> := <span class="tok-tac">by</span>
      <span class="tok-tac">simpa</span> [t1] using hS_closed.csSup_mem hS_nonempty h_bdd_above
    <span class="tok-tac">rcases</span> h_max <span class="tok-kw">with</span> ⟨h_t1_nonneg, h_t1_mem⟩
    <span class="tok-kw">let</span> δ_bound : <span class="tok-type">CoeffVec</span> n := δ_star + t1 • v
    <span class="tok-kw">have</span> hδ_bound_in_F : δ_bound ∈ <span class="tok-var">F</span> := h_t1_mem
    <span class="tok-kw">have</span> hv_in_Psr : v ∈ (<span class="tok-type">P_sr</span> n s_star.re : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) := hv_U
    <span class="tok-kw">have</span> hδ_bound_in_Psr : δ_bound ∈ (<span class="tok-type">P_sr</span> n s_star.re : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) := <span class="tok-tac">by</span>
      <span class="tok-tac">dsimp</span> [δ_bound]
      <span class="tok-tac">apply</span> <span class="tok-type">Submodule.add_mem</span> (<span class="tok-type">P_sr</span> n s_star.re)
      · <span class="tok-tac">exact</span> hδ_star_in_Psr
      · <span class="tok-tac">exact</span> <span class="tok-type">Submodule.smul_mem</span> (<span class="tok-type">P_sr</span> n s_star.re) t1 hv_in_Psr</span></span>
<span class="grp mk1"><span class="gn">6.11</span><span class="gbox">    <span class="tok-kw">have</span> h_not_relint : δ_bound ∉ intrinsicInterior <span class="tok-type">ℝ</span> <span class="tok-var">F</span> :=
      <span class="tok-type">not_mem_intrinsicInterior_of_escapes_along_direction</span>
        <span class="tok-var">F</span> hF_convex δ_star hδ_star_in_F v hv_ne hv_affF_dir
        <span class="tok-var">S</span> <span class="tok-tac">rfl</span> hS_nonempty h_bdd_above
        t1 <span class="tok-tac">rfl</span> h_t1_nonneg h_t1_mem
        t_out ht_out_pos ht_out
    <span class="tok-kw">have</span> hδ_bound_rel_boundary : δ_bound ∈ <span class="tok-type">relativeBoundary</span> <span class="tok-var">F</span> :=
      ⟨hδ_bound_in_F, h_not_relint⟩
    <span class="tok-kw">have</span> h_r_in_RF : (s_star.re : <span class="tok-type">ℂ</span>) ∈ <span class="tok-type">RootSpaceSet</span> (<span class="tok-type">relativeBoundary</span> <span class="tok-var">F</span>) :=
      <span class="tok-type">rootspace_mem_of_eval_zero</span> s_star.re δ_bound hδ_bound_in_Psr (<span class="tok-type">relativeBoundary</span> <span class="tok-var">F</span>) hδ_bound_rel_boundary
    <span class="tok-tac">rw</span> [h_s_star_eq]
    <span class="tok-tac">exact</span> h_r_in_RF</span></span>
<span class="grp mk1"><span class="gn">6.12</span><span class="gbox">  · <span class="tok-kw">have</span> hδ_star_rel_boundary : δ_star ∈ <span class="tok-type">relativeBoundary</span> <span class="tok-var">F</span> :=
      ⟨hδ_star_in_F, hδ_star_relint⟩
    <span class="tok-kw">have</span> h_r_in_RF : (s_star.re : <span class="tok-type">ℂ</span>) ∈ <span class="tok-type">RootSpaceSet</span> (<span class="tok-type">relativeBoundary</span> <span class="tok-var">F</span>) :=
      <span class="tok-type">rootspace_mem_of_eval_zero</span> s_star.re δ_star hδ_star_in_Psr (<span class="tok-type">relativeBoundary</span> <span class="tok-var">F</span>) hδ_star_rel_boundary
    <span class="tok-tac">rw</span> [h_s_star_eq]
    <span class="tok-tac">exact</span> h_r_in_RF</span></span></pre></div>
<div class="side">

### Map

| Step | Content |
|:---|:---|
|  **6.10** | Supremum stays in closed $S$; $\delta_{\mathrm{bound}} \in F \cap P_{s_r}$  |
|  **6.11** | $\delta_{\mathrm{bound}}$ off relint; root transfers to the relative boundary  |
|  **6.12** | $\delta^\star$ itself works; same transfer  |

</div>
</div>

---

<!-- SLIDE 50 | Lemma 6.2 (real case) — proof map (1/2) -->
# Lemma 6.2 (real case) — proof map (1/2)
| Step | Content |
|:---|:---|
|  **6.1** | $F$ compact and convex  |
|  **6.2** | $s^\star = \bar{r}$  |
|  **6.3** | $R(F)$ closed $\implies s^\star \in R(F)$  |
|  **6.4** | $\delta^\star \in F \cap P_{s_r}(r)$  |
|  **6.5** | Case A (off relint) vs Case B (escape)  |
|  **6.6** | $U \sqcap V$ nontrivial $\to$ nonzero $v$  |
| helpers | Step-2 formula + ray escape | `finrank_inf_ge_one` (Step 2); `ray_escapes_of_bounded` (bounded $\Omega$ forces exit) |

---

<!-- SLIDE 51 | Lemma 6.2 (real case) — proof map (2/2) -->
# Lemma 6.2 (real case) — proof map (2/2)
| Step | Content |
|:---|:---|
|  **6.7** | Direction split, escape time, ray-stay set  |
|  **6.8** | $S$ closed (preimage $\cap$ `Ici`)  |
|  **6.9** | $S$ bounded above by $t_{out}$ (helper `ray_stay_set_bddAbove`)  |
|  **6.10** | Supremum gives $\delta_{\mathrm{bound}} \in F \cap P_{s_r}$  |
|  **6.11** | Off relint; root moves, rewrite to $s^\star$  |
|  **6.12** | $\delta^\star$ itself; same transfer  |
| dispatcher | `lemma62` (`Lemma62.lean:1446`) | Real branch $\to$ here; complex branch $\to$ next slide |
| complex twin | `lemma62_complex_case` (`Lemma62.lean:1164`) | $W$-matrix Case A/B; proof overview on the next slide |

---

<!-- SLIDE 52 | Lemma 6.2: complex case — what is extra -->
# Lemma 6.2: complex case — what is extra

<style scoped>
h1 { font-size: 1.15em; margin-bottom: 2px; }
</style>
<div class="columns">
<div class="col">

### Mathematics
- **Claim.** Same goal for non-real $s^\star$: a boundary root of $R(F)$ already lives on the relative boundary of $F$ (complex slice $P_{s_c}$ in place of $P_{s_r}$).
- **New split.** The slice $P_{s_c}(s^\star)$ and the face directions $\mathrm{dir}\,\mathrm{aff}\,F$ generically meet only in $\{0\}$ — no direction to walk. Case A shares a nonzero direction $v$; Case B ($\dim = 0$) is transverse.
- **Case A ($\dim \ge 1$).** Walk $v$ to the relative boundary and transfer the root — the real-case escape.
- **Case B ($\dim = 0$).** Non-roots $s_k \to s^\star$; Cramer on $V_0, V_1$ ($\det \ne 0$) gives $\delta_k \to \delta^\star$ in $\mathrm{aff}(F)$ carrying $s_k$.
- **Limit.** $\delta_k \notin F$ yet $\delta_k \to \delta^\star$ rules out interior — $\delta^\star$ is on the relative boundary carrying $s^\star$.

</div>
<div class="col">

<div class="figs"><figure class="fig-card"><img src="./Complex_Visual/complex_caseAB_3d.png" alt="True-3D view. Case A: the complex slice shares a direction v with the face flat; Case B: transverse slice meeting the flat only at the root witness" style="height:150px;"></figure></div>

### Lean
- Same opening via `isExposedFace_isCompact`, `rootSpaceSet_isClosed_of_isCompact`, `mem_P_sc_of_isRoot`.
- Case A: `exists_boundary_point_in_face_rootspace_complex` (via `h_inter_dim_of_meet`), then `rootspace_mem_of_isRoot` — the real-case escape replayed in $P_{s_c}$.
- Case B: `exists_seq_notin_RootSpaceSet_tendsto` (the $s_k$); `faceCols` basis with `detOf_ne_zero_of_transverse` + `tendsto_detOf` (determinant stays nonzero); Cramer corrections `lam0`/`lam1` with `hev_root` ($\delta_k$ carries $s_k$ while $\det_k \ne 0$); `hdeltak_tendsto` ($\lambda_k \to 0$); the interior assumption contradicts `hev_notF` — hence `hnot_ri`.
- Machinery: quadratic-factor perturbations `Wcol`/`Wmul` staying inside the slice (`evalAtComplex_Wcol`, `Wmul_mem_Psc`, `tendsto_Wmul`); `evalAtComplex` with `tendsto_evalAtComplex`; transverse $2 \times 2$ `detOf`.

</div>
</div>

---

<!-- SLIDE 53 | Edge Theorem — formal proof -->
# Edge Theorem — formal proof
<div class="thm">

**Theorem (Edge Theorem).** Let $\Omega \subset \mathbb{R}^{n+1}$ ($n \ge 1$) be a polytope satisfying Assumption 6.1. Then every $s \in \partial R(\Omega)$ lies in $R(E)$ for some exposed edge $E$ of $\Omega$.

</div>
<div class="columns">
<div class="col">

### Proof
1. Let $s \in \partial R(\Omega)$. Since $R(\Omega)$ is closed, $s \in R(\Omega)$ and $s \notin \mathrm{int}\,R(\Omega)$.
2. If $\mathrm{Im}(s) = 0$, Lemma 6.1 (real case) gives an exposed edge $E$ with $s \in R(E)$. Done.
3. Else $\mathrm{Im}(s) \ne 0$: Lemma 6.1 (complex case) gives an exposed face $F$ with $s \in R(F)$ and $\dim\mathrm{aff}(F) \le 2$.
4. If $\dim = 2$: $R(F)$ is closed, and $\mathrm{int}\,R(F) \subseteq \mathrm{int}\,R(\Omega) \not\ni s$, so $s \in \partial R(F)$. Lemma 6.2 moves $s$ to $R(\mathrm{relativeBoundary}\,F)$; the witness lies on the relative boundary, giving a proper exposed subface $G \subsetneq F$ ($\dim G \le 1$) with $s \in R(G)$.
5. If $\dim \le 1$: the face ($G$, resp. $F$) is already an edge ($\dim = 1$) or a singleton ($\dim = 0$), and a singleton face sits on an exposed edge through it. Either way $s \in R(E)$ for an exposed edge $E$. ∎

</div>
<div class="col">

### Lean (`EdgeTheorem.lean`)
- Closedness + unpacking: `rootSpaceSet_isClosed_of_isCompact`, `frontier_subset_closure`.
- Step 2 is `edge_real` (exactly `lemma61_real`).
- Step 3 is `lemma61_complex_with_dim` (face of dimension at most two).
- Step 4 uses `interior_mono` with $R(F) \subseteq R(\Omega)$ to land in $\partial R(F)$; Lemma 6.2 enters as `face_boundary_subset`.
- The last descent is `exists_proper_subface_of_boundary_point`, closing via `isExposedEdge_of_dim_1` or `exposed_face_dim_zero_singleton` + `exists_exposed_edge_of_singleton` (factored as `exposed_face_root_dim_le1_to_edge`).
- Assembly: `edge_theorem` (`by_cases hreal`, then `by_cases hdim2`).

</div>
</div>

---

<!-- SLIDE 54 | Edge Theorem — lemmas behind steps 1–5 -->
# Edge Theorem — lemmas behind steps 1–5

<style scoped>
p { margin: 2px 0; font-size: 0.82em; }
.lean { margin: 2px 0 6px 0; }
.lean pre { font-size: 0.6em; line-height: 1.3; }
</style>

<div class="columns">
<div class="col">

**Step 1.** Root spaces over compact sets are closed, so a boundary root is a genuine root outside the interior.
<div class="lean"><div class="lean-head">Lemma62.lean:37-38</div>
<pre><span class="tok-kw">lemma</span> <span class="tok-type">rootSpaceSet_isClosed_of_isCompact</span> {n : <span class="tok-type">ℕ</span>} {<span class="tok-var">W</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)} (hW : <span class="tok-type">IsCompact</span> <span class="tok-var">W</span>) :
    <span class="tok-type">IsClosed</span> (<span class="tok-type">RootSpaceSet</span> <span class="tok-var">W</span>)</pre></div>

**How:** Let $Z = \{(\delta, s) \in W \times \mathbb{C} : \tilde P_\delta(s) = 0\}$, the set of polynomial–root pairs. It is closed, being the zero set of the continuous evaluation map. $\pi(\delta, s) = s$ satisfies $\pi(Z) = R(W)$: indeed $s \in \pi(Z)$ iff some $\delta \in W$ vanishes at $s$. Since $W$ is compact, $\pi : W \times \mathbb{C} \to \mathbb{C}$ is a closed map, so $\pi(Z) = R(W)$ is closed.
**Step 2.** Every real root of the family already lives on an exposed edge.
<div class="lean"><div class="lean-head">EdgeTheorem.lean:37-40</div>
<pre><span class="tok-kw">theorem</span> <span class="tok-type">edge_real</span> {n : <span class="tok-type">ℕ</span>} (hn : n ≥ <span class="tok-num">1</span>) (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n) (s : <span class="tok-type">ℂ</span>)
    (hs : s ∈ <span class="tok-type">RootSpace</span> <span class="tok-var">P</span>) (hreal : s.im = <span class="tok-num">0</span>) :
    ∃ <span class="tok-var">E</span>, <span class="tok-type">IsExposedEdge</span> <span class="tok-var">P</span> <span class="tok-var">E</span> ∧ s ∈ <span class="tok-type">RootSpaceSet</span> <span class="tok-var">E</span></pre></div>

How: Lemma 6.1, real case: $s = \bar{r} \in R(\Omega)$ yields $E$ with $s \in R(E)$.

**Step 3.** Every non-real root lives on an exposed face of dimension at most two.
<div class="lean"><div class="lean-head">Lemma61.lean:208-211</div>
<pre><span class="tok-kw">theorem</span> <span class="tok-type">lemma61_complex_with_dim</span> (hn : n ≥ <span class="tok-num">1</span>) (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n) (s : <span class="tok-type">ℂ</span>) (hs : s ∈ <span class="tok-type">RootSpace</span> <span class="tok-var">P</span>)
    (hleading : ∀ v ∈ <span class="tok-type">P.vertices</span>, <span class="tok-num">0</span> &lt; v (<span class="tok-type">Fin.last</span> n)) : s.im ≠ <span class="tok-num">0</span> →
    ∃ <span class="tok-var">F</span>, <span class="tok-type">IsExposedFace</span> <span class="tok-var">P</span> <span class="tok-var">F</span> ∧ s ∈ <span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span> ∧
      <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">F</span>).direction ≤ <span class="tok-num">2</span></pre></div>

How: Steps 1–5 in the $(n-1)$-dimensional slice, descending to $\dim \le 2$ (the count requires $\dim \ge 3$); $n = 1$ excluded by the leading coefficient.

</div>
<div class="col">

**Step 4.** Boundary roots of a two-dimensional exposed face live on its relative boundary.
<div class="lean"><div class="lean-head">EdgeTheorem.lean:56-60</div>
<pre><span class="tok-kw">theorem</span> <span class="tok-type">face_boundary_subset</span> {n : <span class="tok-type">ℕ</span>} (hn : n ≥ <span class="tok-num">1</span>) (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n)
    (<span class="tok-var">F</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) (hF_exp : <span class="tok-type">IsExposedFace</span> <span class="tok-var">P</span> <span class="tok-var">F</span>)
    (hF_dim_2 : <span class="tok-type">dim</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">F</span>).direction = <span class="tok-num">2</span>) :
    frontier (<span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span>) ⊆ <span class="tok-type">RootSpaceSet</span> (<span class="tok-type">relativeBoundary</span> <span class="tok-var">F</span>)</pre></div>

How: split on $\mathrm{Im}(s^\star) = 0$ into the real and complex cases.

**Step 5.** Roots on an at-most-one-dimensional exposed face move to an exposed edge — directly at dimension one, through a singleton vertex at dimension zero.
<div class="lean"><div class="lean-head">EdgeTheorem.lean:66-70</div>
<pre><span class="tok-kw">private</span> <span class="tok-kw">theorem</span> <span class="tok-type">exposed_face_root_dim_le1_to_edge</span> {n : <span class="tok-type">ℕ</span>} (hn : n ≥ <span class="tok-num">1</span>) (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n)
    (s : <span class="tok-type">ℂ</span>) (<span class="tok-var">F</span> : <span class="tok-type">Set</span> (<span class="tok-type">CoeffVec</span> n)) (hF_exp : <span class="tok-type">IsExposedFace</span> <span class="tok-var">P</span> <span class="tok-var">F</span>)
    (hsF : s ∈ <span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span>)
    (hF_dim : <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">F</span>).direction ≤ <span class="tok-num">1</span>) :
    ∃ <span class="tok-var">E</span>, <span class="tok-type">IsExposedEdge</span> <span class="tok-var">P</span> <span class="tok-var">E</span> ∧ s ∈ <span class="tok-type">RootSpaceSet</span> <span class="tok-var">E</span></pre></div>

How: $\dim = 1$ is already an edge; $\dim = 0$ is a singleton lying on an edge through it.

</div>
</div>

---

<!-- SLIDE 55 | Edge Theorem — Lean implementation -->
# Edge Theorem — Lean implementation
<div class="lean"><div class="lean-head">EdgeTheorem.lean:82-89 — statement</div>
<pre style="font-size:0.6em;line-height:1.3;">
<span class="tok-kw">theorem</span> <span class="tok-type">edge_theorem</span> {n : <span class="tok-type">ℕ</span>} (hn : n ≥ <span class="tok-num">1</span>) (<span class="tok-var">P</span> : <span class="tok-type">Polytope</span> n) (s : <span class="tok-type">ℂ</span>)
    (hleading : ∀ v ∈ <span class="tok-type">P.vertices</span>, <span class="tok-num">0</span> &lt; v (<span class="tok-type">Fin.last</span> n))
    (hs : s ∈ frontier (<span class="tok-type">RootSpace</span> <span class="tok-var">P</span>)) :
    ∃ <span class="tok-var">E</span>, <span class="tok-type">IsExposedEdge</span> <span class="tok-var">P</span> <span class="tok-var">E</span> ∧ s ∈ <span class="tok-type">RootSpaceSet</span> <span class="tok-var">E</span> := <span class="tok-tac">by</span></pre></div>

<div class="columns">
<div class="col">
<div class="lean"><div class="lean-head">EdgeTheorem.lean:90-121 — proof (1/2)</div>
<pre style="font-size:0.5em;line-height:1.25;">  <span class="tok-kw">have</span> hroot_closed : <span class="tok-type">IsClosed</span> (<span class="tok-type">RootSpace</span> <span class="tok-var">P</span>) := <span class="tok-tac">by</span>
    <span class="tok-tac">change</span> <span class="tok-type">IsClosed</span> (<span class="tok-type">RootSpaceSet</span> <span class="tok-type">P.Ω</span>)
    <span class="tok-tac">exact</span> <span class="tok-type">rootSpaceSet_isClosed_of_isCompact</span> <span class="tok-type">P.isCompact</span>
  <span class="tok-kw">have</span> hs_mem : s ∈ <span class="tok-type">RootSpace</span> <span class="tok-var">P</span> := <span class="tok-tac">by</span>
    <span class="tok-kw">have</span> hcl : s ∈ closure (<span class="tok-type">RootSpace</span> <span class="tok-var">P</span>) := frontier_subset_closure hs
    <span class="tok-tac">rw</span> [hroot_closed.closure_eq] <span class="tok-kw">at</span> hcl
    <span class="tok-tac">exact</span> hcl
  <span class="tok-kw">have</span> hs_not_int : s ∉ interior (<span class="tok-type">RootSpace</span> <span class="tok-var">P</span>) := <span class="tok-tac">by</span>
    <span class="tok-tac">change</span> s ∈ closure (<span class="tok-type">RootSpace</span> <span class="tok-var">P</span>) \ interior (<span class="tok-type">RootSpace</span> <span class="tok-var">P</span>) <span class="tok-kw">at</span> hs
    <span class="tok-tac">exact</span> hs.<span class="tok-num">2</span>
  <span class="tok-tac">by_cases</span> hreal : s.im = <span class="tok-num">0</span>
  · <span class="tok-tac">exact</span> <span class="tok-type">edge_real</span> hn <span class="tok-var">P</span> s hs_mem hreal
  · <span class="tok-tac">obtain</span> ⟨<span class="tok-var">F</span>, hF_exp, hsF, hF_dim⟩ :=
      <span class="tok-type">lemma61_complex_with_dim</span> hn <span class="tok-var">P</span> s hs_mem hleading hreal
    <span class="tok-tac">by_cases</span> hdim2 : <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">F</span>).direction = <span class="tok-num">2</span>
    · <span class="tok-kw">have</span> hroot_closed_F : <span class="tok-type">IsClosed</span> (<span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span>) :=
        <span class="tok-type">rootSpaceSet_isClosed_of_isCompact</span> (<span class="tok-type">isExposedFace_isCompact</span> <span class="tok-var">P</span> hF_exp)
      <span class="tok-kw">have</span> hsF_not_int : s ∉ interior (<span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span>) := <span class="tok-tac">by</span>
        <span class="tok-tac">intro</span> hInt
        <span class="tok-kw">have</span> hsub : <span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span> ⊆ <span class="tok-type">RootSpace</span> <span class="tok-var">P</span> := <span class="tok-tac">by</span>
          <span class="tok-tac">intro</span> z hz
          <span class="tok-tac">obtain</span> ⟨δ, hδF, hδroot⟩ := hz
          <span class="tok-tac">exact</span> <span class="tok-type">rootspace_mem_of_isRoot</span> z δ hδroot <span class="tok-type">P.Ω</span>
            (<span class="tok-type">isExposedFace_subset_Ω</span> hF_exp hδF)
        <span class="tok-tac">exact</span> hs_not_int (interior_mono hsub hInt)
      <span class="tok-kw">have</span> hsF_front : s ∈ frontier (<span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span>) := <span class="tok-tac">by</span>
        <span class="tok-kw">have</span> hsF_mem : s ∈ closure (<span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span>) := <span class="tok-tac">by</span>
          <span class="tok-tac">rw</span> [hroot_closed_F.closure_eq]
          <span class="tok-tac">exact</span> hsF
        <span class="tok-tac">change</span> s ∈ closure (<span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span>) \ interior (<span class="tok-type">RootSpaceSet</span> <span class="tok-var">F</span>)
        <span class="tok-tac">exact</span> ⟨hsF_mem, hsF_not_int⟩</pre></div>

</div>
<div class="col">
<div class="lean"><div class="lean-head">EdgeTheorem.lean:122-151 — proof (2/2)</div>
<pre style="font-size:0.5em;line-height:1.25;">      <span class="tok-kw">have</span> hs_rel : s ∈ <span class="tok-type">RootSpaceSet</span> (<span class="tok-type">relativeBoundary</span> <span class="tok-var">F</span>) :=
        <span class="tok-type">face_boundary_subset</span> hn <span class="tok-var">P</span> <span class="tok-var">F</span> hF_exp hdim2 hsF_front
      <span class="tok-tac">obtain</span> ⟨δ, hδrel, hδroot⟩ := hs_rel
      <span class="tok-kw">have</span> hδF : δ ∈ <span class="tok-var">F</span> := hδrel.<span class="tok-num">1</span>
      <span class="tok-kw">have</span> hδ_not_relint : δ ∉ intrinsicInterior <span class="tok-type">ℝ</span> <span class="tok-var">F</span> := hδrel.<span class="tok-num">2</span>
      <span class="tok-kw">have</span> hF_compact : <span class="tok-type">IsCompact</span> <span class="tok-var">F</span> := <span class="tok-type">isExposedFace_isCompact</span> <span class="tok-var">P</span> hF_exp
      <span class="tok-kw">have</span> hδ_not_int : δ ∉ interior <span class="tok-var">F</span> := <span class="tok-tac">by</span>
        <span class="tok-tac">intro</span> hInt
        <span class="tok-tac">exact</span> hδ_not_relint
          (interior_subset_intrinsicInterior (𝕜 := <span class="tok-type">ℝ</span>) (s := <span class="tok-var">F</span>) hInt)
      <span class="tok-kw">have</span> hδ_front : δ ∈ frontier <span class="tok-var">F</span> := <span class="tok-tac">by</span>
        <span class="tok-tac">rw</span> [<span class="tok-type">frontier_eq_for_closed</span> <span class="tok-var">F</span> hF_compact.isClosed]
        <span class="tok-tac">exact</span> ⟨hδF, hδ_not_int⟩
      <span class="tok-tac">obtain</span> ⟨<span class="tok-var">G</span>, hG_exp, hδG, hG_dim_lt⟩ :=
        exists_proper_subface_of_boundary_point <span class="tok-var">P</span> <span class="tok-var">F</span> hF_exp δ hδF hδ_front
          hδ_not_relint (<span class="tok-tac">by</span> <span class="tok-tac">omega</span>)
      <span class="tok-kw">have</span> hsG : s ∈ <span class="tok-type">RootSpaceSet</span> <span class="tok-var">G</span> :=
        <span class="tok-type">rootspace_mem_of_isRoot</span> s δ hδroot <span class="tok-var">G</span> hδG
      <span class="tok-tac">by_cases</span> hG1 : <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">G</span>).direction = <span class="tok-num">1</span>
      · <span class="tok-tac">exact</span> ⟨<span class="tok-var">G</span>, <span class="tok-type">isExposedEdge_of_dim_1</span> hG_exp hG1, hsG⟩
      · <span class="tok-kw">have</span> hG0 : <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">G</span>).direction = <span class="tok-num">0</span> := <span class="tok-tac">by</span> <span class="tok-tac">omega</span>
        <span class="tok-tac">obtain</span> ⟨δ', hδ'G, hδ'root⟩ := hsG
        <span class="tok-kw">have</span> hG_single : <span class="tok-var">G</span> = {δ'} :=
          <span class="tok-type">exposed_face_dim_zero_singleton</span> <span class="tok-var">G</span> hG0 δ' hδ'G
        <span class="tok-tac">obtain</span> ⟨<span class="tok-var">E</span>, hE, hδ'E⟩ :=
          <span class="tok-type">exists_exposed_edge_of_singleton</span> hn <span class="tok-var">P</span> δ' <span class="tok-var">G</span> hG_exp hG_single
        <span class="tok-tac">exact</span> ⟨<span class="tok-var">E</span>, hE, <span class="tok-type">rootspace_mem_of_isRoot</span> s δ' hδ'root <span class="tok-var">E</span> hδ'E⟩
    · <span class="tok-com">-- In dimension zero or one, the exposed face itself is a singleton or edge.</span>
      <span class="tok-kw">have</span> hdim_le1 : <span class="tok-type">Module.finrank</span> <span class="tok-type">ℝ</span> (affineSpan <span class="tok-type">ℝ</span> <span class="tok-var">F</span>).direction ≤ <span class="tok-num">1</span> := <span class="tok-tac">by</span> <span class="tok-tac">omega</span>
      <span class="tok-tac">exact</span> <span class="tok-type">exposed_face_root_dim_le1_to_edge</span> hn <span class="tok-var">P</span> s <span class="tok-var">F</span> hF_exp hsF hdim_le1</pre></div>

</div>
</div>

---

 