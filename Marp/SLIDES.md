### 1. Edge Theorem in Lean 4 (Lemma 6.1, real case)
- Title slide (`_class: lead`): placeholder title, subtitle "polytopic families and exposed edges", "TODO: Author Name · Institute".

### 1b. What is a control system?
- Quote-block definition (thermostat to industrial processes); two columns with continuous-time ($\dot{x} = Ax + Bu$, $y = Cx + Du$) and discrete-time ($x[k+1] = A_d x[k] + B_d u[k]$, $y[k] = C_d x[k] + D_d u[k]$) state-space models; Where-paragraph ($x$ state, $y$ output, $u$ input, $A,B,C,D$ matrices).

### 1c. From state-space to transfer function
- 4-step Laplace derivation under $x(0) = 0$ (transform, isolate $X(s)$, substitute, factor $U(s)$); boxed result $G(s) = Y(s)/U(s) = C(sI-A)^{-1}B + D$.

### 1d. Example: mass-spring-damper
- $m=1$, $c=2$, $k=3$ ($u$ force, $y$ displacement); ODE $\ddot{y}+2\dot{y}+3y=u$; states $x_1=y$, $x_2=\dot{y}$; matrices $A=[[0,1],[-3,-2]]$, $B=[0,1]^T$, $C=[1,0]$, $D=0$; boxed $G(s)=1/(s^2+2s+3)$ via the adjugate.

### 1e. Poles and stability
- Quote-block criterion (stable iff all poles strictly LHP; unstable if some pole has positive real part); example $G(s)=1/(s^2+2s+3)$ gives $p_{1,2}=-1\pm j\sqrt2$ with real parts $-1<0$ — stable.

### 1f. Kharitonov's theorem
- Theorem box: interval family plus the four min/max vertex polynomials $K_1$–$K_4$ and the Hurwitz equivalence; example paragraph (primary $m_1,k_1,c_1$ + TMD $m_2,k_2,c_2$ in intervals; fourth-order $p(s)$ with $a_i\in[\underline{a}_i,\bar{a}_i]$); `Intro_Visual/tmd.png` schematic (wall–k1/c1–m1–k2/c2–m2, $u(t)$ drive, $y(t)$ output).

### 1g. Kharitonov vs Edge Theorem (discrete systems)
- two columns: why Kharitonov fails (half-plane-only symmetry, bilinear map tangles intervals, real models dependent) / verified numeric counterexample (cubic box; four $K_i$ Schur with max moduli $0.83,0.79,0.98,0.82$; vertex $0.9z^3+1.3z^2+0.3z+0.5$ has root modulus $1.47$); green takeaway line.

### 1h. The Edge Theorem at work (discrete)
- theorem box (fixed-degree polytope; boundary root space on exposed edges; stability iff edges stable; one-parameter edges); worked Ex. 6.2 in plain words (box, $12$ corner-joining edges, disc, robust Schur stability); `Intro_Visual/edge_example_62.png` two-panel figure from `edge_example_62.py` (3D coefficient box colored by varying coefficient + unit disc with the $12$ edge root loci, max $|z|=0.50$).

### 2. Outline
- `_class: list`. Eight parts: 1 Background (control systems through Edge-at-work); 2 Preliminaries; 3 Exposed faces and edges; 4 Edge Theorem; 5 Lemma 6.1 real case + complex extra; 6 Lemma 6.2 real case + helper + complex extra; 7 Edge Theorem assembled (formal proof, lemmas, implementation); 8 Future work.

### 3. Section 1 · Preliminaries
- Section divider (`_class: section`), no content beyond the title.

### 4. Polytopic family of polynomials
- Prose definition: $P(s)=\lambda_1P_1(s)+\cdots+\lambda_nP_n(s)$ with $\lambda_i\ge0$, $\sum\lambda_i=1$; motivation (convex hull of finitely many polynomials). Quote-block "Definition (Po…)".

### 5. Coefficient vectors (`CoeffVec`)
- Lean panel: `EdgeTheoremDefs.lean` (`abbrev CoeffVec (ℕ) := Fin (n+1) → ℝ`, `polyOfVec`); highlighted span `EdgeTheoremDefs.lean:95-99`. Blocks: Restatement / Lean / Example.

### 6. Polytope: Lean formalization
- Figure `Defs_Visual/def_polytope.png`. Lean panel `EdgeTheoremDefs.lean`: `structure Polytope`, `Polytope.Ω`, `additionally`; snippet ends at `convexHull ℝ (P.vertices : Set (CoeffVec n))`.

### 7. Affine span, direction, dimension — definition
- Prose definitions: affine set (closed under lines, $A=p+V$), affine span $\mathrm{aff}(S)$, direction $\mathrm{dir}(A)$, dimension. Starts a "Lean" lead paragraph.

### 8. Affine span, direction, dimension — Lean
- Lean panel `EdgeTheoremDefs.lean:341-354`: `abbrev meetDir`, `dim`, snippet ends `Module.finrank ℝ U`.

### 9. Supporting hyperplane
- Two columns: prose definition ($H=\{x: f(x)=c\}$ supports convex $\Omega$ iff (i) $f\le c$ on $\Omega$, (ii) $f(x_0)=c$ for some $x_0\in\Omega$) on the left; worked example on the right ($f(x,y)=-y$, $c=0$, $H=x$-axis; exposed set = bottom edge) with figure `Defs_Visual/def_supporting_example.png`.

### 11. Supporting hyperplane: Lean
- Lean panel `EdgeTheoremDefs.lean`: `structure SupportingHyperplane`, statement ends `touches : ∃ x ∈ P.Ω, f x = c`.

### 12. Root spaces
- Section divider (`_class: section`).

### 13. Root space — definition
- Notation for $R(\Omega)$ (roots of $P_\delta$). Lean panel `EdgeTheoremDefs.lean`: `RootSpaceSet`, `RootSpace`; snippet ends `RootSpaceSet P.Ω`.

### 14. Exposed faces and edges
- Section divider (`_class: section`).

### 15. Boundary and exposed faces — definition
- Prose definitions: closure $\overline{S}$, boundary $\partial S=\overline{S}\setminus\mathrm{int}(S)$; exposed face $F=\Omega\cap H$ for supporting $H$; edge when $\dim\mathrm{aff}(F)=1$.

### 16. Boundary and exposed faces — Lean
- Lean panel `EdgeTheoremDefs.lean:140-151`: `ExposedFace`, `IsExposedEdge`; doc comment `/-- The exposed face of P for hp`, ends `Module.finrank ℝ (affineSpan ℝ (ExposedFace hp)).direction = 1`.

### 17. Boundary and exposed edge — example
- Two-column examples with figures `Defs_Visual/def_boundary.png`, `Defs_Visual/def_exposed_edge.png`: disk boundary $\{|s|=1\}$; unit square with $H=\{-y=0\}$ exposing the bottom edge.

### 18. Edge Theorem
- Section divider (`_class: section`).

### 19. Assumption 6.1
- Statement: sign of the leading coefficient $\delta_n$ is constant on $\Omega$ (e.g. $\delta_n>\Delta>0$ for all $\underline\delta\in\Omega$); assumed by every lemma and theorem below.

### 20. Lemmas 6.1–6.2 — statements
- Lemma 6.1 (real root in $R(\Omega)$ ⇒ exposed edge; complex root ⇒ exposed face) and Lemma 6.2 (boundary roots of a face ⇒ relative boundary of the face).

### 21. Edge Theorem — statement
- Statement: $\partial R(\Omega)\subseteq\bigcup_{E\ \text{exposed edge}} R(E)$ for polytopes satisfying Assumption 6.1.

### 22. Edge Theorem — proof outline
- Three-step assembly: Lemma 6.1 puts roots on exposed faces/edges; Lemma 6.2 pushes face-boundary roots to $\partial F$; dimension descent reaches edges.

### 23. Section 4 · Proof of Lemma 6.1, real case
- Section divider (`_class: section`).

### 24. Lemma 6.1 (real case) — proof overview
- Numbered plan: 1 unpack the root (pass to slice $\mathcal{P}_{s_r}$/$\mathcal{P}_{s_c}$); 2 dimension count; 3 escape to the boundary; 4 exposed face; 5 descend to an edge; 6 Lemma 6.2.

### 25. Step 1: Unpack the root — Lean + map

### 26. Step 2: Dimension count — Lean + map

### 27. Step 3: Escape — Lean + map
- Full master-lemma proof (`PreliminaryLemmas.lean:336-368`) with grouped boxes ①–⑤ + two-column formal Map.
- Full `intersection_affine_dim_ge_one` proof with grouped boxes 2.1–2.6 + two-column formal Map.
- Codeside `Lemma61.lean:142-153` with grouped boxes 1.1–1.3 + two-column formal Map.
### 44. Step 4: Exposed face — Lean + map

### 45. Step 5: Descend — Lean + map (1/2)
- First half of `descend_to_exposed_edge` (`EdgeDescent.lean:691-715`): claim + code 5.1–5.6 + Map rows 5.1–5.6 (one concise sentence each).

### 45b. Step 5: Descend — Lean + map (2/2)
- Second half (`EdgeDescent.lean:716-733`): code 5.7 (`termination_by`/`decreasing_by`)–5.10 + Map rows 5.7–5.10.
- Full proof (`ExposedFaceLemmas.lean:96-136`) with grouped boxes 4.1–4.10 + two-column formal Map (Hahn–Banach folded into 4.3).
- Intro paragraph ("Wrappers", `PreliminaryLemmas.lean:371,379`) + `.codeside`: Lean panel `PreliminaryLemmas.lean:371-384` with two boxes badge **A.3** (Psr lemma, Psc lemma); right "### Map" table rows A.1–A.3 (where each appendix lemma is used).

### 46. Step 6: Degenerate cases — Lean + map
- Codeside `Lemma61.lean:191-203` with grouped boxes ①/② + two-column formal Map (D.1/D.2 rows).
### 72. Lemma 6.1 (real case) — recap
- numbered list only: 1 Step 1 unpacked $s\in R(\Omega)$ to $\delta\in P_{s_r}(r)$, $s=\bar r$; 2 Step 2 gave $\dim(U\cap\mathrm{aff}\,\Omega)\ge1$; 3 Step 3 reached $\delta_{\mathrm{bound}}\in P_{s_r}\cap\partial\Omega$; 4 Step 4 exposed $F\ni\delta_{\mathrm{bound}}$ with $\bar r\in R(F)$; 5 Step 5 descends to an edge.

### 72b. Lemma 6.1: complex case — what is extra
- two columns (Mathematics / Lean): thinner slice ($\dim n-1$, two real conditions), stronger count ($\ge 3$ direction dimension, $n \ge 2$), weaker target ($\dim \le 2$ face: one condition gives a line to walk to an edge, two conditions give isolated points that cannot slide), $n = 1$ via Assumption 6.1; Lean parallels (`P_sc_dimension`, `intersection_affine_dim_ge_one_complex`, `exists_boundary_point_in_Psc`, `..._complex`, `descend_to_exposed_face_with_dim`, `hleading`).

### 73. Section 5 · Lemma 6.2, real case
- Section divider (`_class: section`).

### 74. Lemma 6.2 (real case) — overview
- Theorem box: $F$ exposed, $\dim\mathrm{aff}(F)=2$ ⇒ $\partial R(F)\subseteq R(\partial F)$; every boundary point of $R(F)$ lies in the root space of $\partial F$.

### 75. Lemma 6.2 (real case) — goal
- Goal box: $F$ exposed, $\dim\mathrm{aff}(F)=2$, real $s^\star\in\mathrm{frontier}\,R(F)$ ⇒ $s^\star\in R(\mathrm{rel}\,\partial F)$; Lean panel `PreliminaryLemmas.lean:422-423` (`def relativeBoundary`, ends `F \ intrinsicInterior ℝ F`); "Proof sketch." paragraphs.

### 76-77. Lemma 6.2 (real case) — math proof (1/2), (2/2)
- REMOVED (with the helper slide below): the 6.1–6.12 math exposition now lives in the lecture notes; the deck jumps from the goal slide to the walkthroughs.

### 78-84. Lemma 6.2 (real case) — Lean (1/7)–(7/7)
- REMOVED: the full-code slides were dropped; the proof lives in `lemma62_real_case` (`Lemma62.lean:127-220`) and is shown via the helper + walkthrough slides below.

### 84b. Lemma 6.2 (real case) — helper `ray_stay_set_bddAbove` (Lean)
- REMOVED: slide dropped; the lemma itself (`Lemma62.lean:91-121`) still exists and is still called by the one-line 6.9 box on the walkthrough slide.

### 85. Lemma 6.2 (real case) — walkthrough 6.1–6.6
- `.codeside`: `Lemma62.lean:127-162` with boxes **6.1–6.6**; right "### Map" table rows 6.1–6.6.

### 86. Lemma 6.2 (real case) — walkthrough 6.7–6.9
- `.codeside`: `Lemma62.lean:163-190` with boxes **6.7–6.9** (6.9 is the one-line helper call); right "### Map" table rows 6.7–6.9.

### 87. Lemma 6.2 (real case) — walkthrough 6.10–6.12
- `.codeside`: `Lemma62.lean:191-220` with boxes **6.10–6.12**; right "### Map" table rows 6.10–6.12.

### 92. Lemma 6.2 (real case) — proof map (1/2)
- Table rows 6.1–6.6 (Lean line + mathematical content).

### 93. Lemma 6.2 (real case) — proof map (2/2)
- Table rows 6.7–6.12.

### 93b. Lemma 6.2: complex case — what is extra
- two columns (Mathematics / Lean): same claim/opening with $P_{s_c}$; new split on transversality ($\dim \ge 1$ vs $= 0$); Case A replays the escape; Case B approximates ($s_k \to s^\star$, Cramer $\lambda_k \to 0$, $\delta_k \to \delta^\star$) and the limit forces the relative boundary; Lean parallels (`exists_boundary_point_in_face_rootspace_complex`, `exists_seq_notin_RootSpaceSet_tendsto`, `faceCols`/`detOf`, `lam0`/`lam1`, `Wcol`/`Wmul`); Lean column topped by `Complex_Visual/complex_caseAB_3d.png` (true-3D shared-direction vs transverse figure; flat TikZ version kept as `complex_caseAB.png`; interactive 3D version: `Complex_Visual/caseAB_viewer.py`).

### 93c. Edge Theorem — formal proof
- theorem box (formal statement with Assumption 6.1); two columns: Proof 1–5 (closedness unpacking; real case by Lemma 6.1; complex face of dim $\le 2$; dim-$2$ case via closedness + `interior_mono` into Lemma 6.2 then proper subface; dim-$\le 1$ closes at an edge) / Lean mapping (`edge_real`, `lemma61_complex_with_dim`, `face_boundary_subset`, `exposed_face_root_dim_le1_to_edge`, `edge_theorem` in `EdgeTheorem.lean`).

### 93d. Edge Theorem — lemmas behind steps 1–5
- five statement panels, each with a what-sentence and a one-line how-proven note (no proofs): `rootSpaceSet_isClosed_of_isCompact` (closed zero set + closed projection), `edge_real` (one application of `lemma61_real`), `lemma61_complex_with_dim` (Steps 1–5 in the complex slice + $n=1$ case), `face_boundary_subset` (one application of `lemma62`), `exposed_face_root_dim_le1_to_edge` (dimension split: edge vs singleton); steps 1–3 left column, 4–5 right column.

### 93e. Edge Theorem — Lean implementation
- full `edge_theorem` statement (`EdgeTheorem.lean:82-89`) + complete proof in two columns (`:90-121` and `:122-151`, one blank source line dropped for HTML-block safety).

### 94. Future work — outlook
- Numbered list: 1 Lemma 6.2 complex case (`lemma62_complex_case`); 2 Lemma 6.1 complex case (`lemma61_complex`); 3 assembling the full Edge Theorem in Lean (`EdgeTheorem.lean`).
