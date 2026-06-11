# Lemma 6.1 (Real Case) — Formal Proof & Lean Formalization

## Statement

Let `Ω = P.Ω` be a polytope in `ℝ^{n+1}` (convex hull of finitely many points) with
nonempty interior. If a real number `s ∈ ℝ` satisfies `s ∈ R(Ω)` (i.e. there exists
`δ ∈ Ω` such that `δ(s) = 0`), then there exists an **exposed edge** `E` of `Ω` such
that `s ∈ R(E)`.

---

## Step 1 — Root witness

**Math.** Since `s ∈ R(Ω)`, there exists `δ ∈ Ω` such that `δ(s) = 0`.

**Lean.** The hypothesis `hs : s ∈ RootSpace P` unfolds to:

```lean4
-- RootSpace P = RootSpaceSet P.Ω = {s | ∃ δ ∈ P.Ω, ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s}
obtain ⟨δ, hδ_in_Ω, hδ_root⟩ := hs
```

---

## Step 2 — Vector space of polys with root `s`

**Math.** The set `P_s := {δ ∈ ℝ^{n+1} | δ(s) = 0}` is a vector subspace of
dimension `n` in the ambient space `ℝ^{n+1}` (the space of all real polynomials
of degree ≤ `n`).

**Lean.**

```lean4
-- P_sr n r = (evalLinear r).ker = {δ | eval r (polyOfVec δ) = 0}
-- Its ℝ-dimension is n:
have hdim_Psr : Module.finrank ℝ (P_sr n s.re) = n := P_sr_dimension s.re
```

`P_sr_dimension` (line 32 of `Edge2.lean`) proves this using rank-nullity on
`evalLinear r : CoeffVec n →ₗ[ℝ] ℝ`, whose image has dimension 1.

---

## Step 3 — Base case: `Ω` is already 1-dimensional

**Math.** Let `m = dim(aff(Ω))`. If `m = 1` then `Ω` itself is a line segment —
an exposed edge — and we are done.

**Lean.**

```lean4
let m := Module.finrank ℝ (affineSpan ℝ P.Ω).direction
if hm0 : m = 0 then
  -- impossible: polytope with nonempty interior has dim ≥ 1
  have h_pos : m ≥ 1 := polytope_direction_dim_pos P
  omega
else if hm1 : m = 1 then
  have h_Ω_is_edge : IsExposedEdge P P.Ω :=
    polytope_dim1_is_exposed_edge hn P hm1
  refine ⟨P.Ω, h_Ω_is_edge, ...⟩
```

`polytope_dim1_is_exposed_edge` (line 2013 of `Edge2.lean`) constructs a
supporting hyperplane that exposes the whole polytope when `dim = 1`.

---

## Step 4 — When `m ≥ 2`, the intersection `P_s ∩ aff(Ω)` has dimension ≥ 1

**Math.** By the Grassmann formula:

```
dim(P_s ∩ aff(Ω)) = dim(P_s) + dim(aff(Ω)) − dim(ℝ^{n+1})
                 = n + m − (n+1)
                 = m − 1
                 ≥ 1       (since m ≥ 2)
```

**Lean.**

```lean4
let U : Submodule ℝ (CoeffVec n) := P_sr n s.re
let affΩ : AffineSubspace ℝ (CoeffVec n) := affineSpan ℝ P.Ω
have hdim_Psr : Module.finrank ℝ U = n := P_sr_dimension s.re
have hδ_aff : δ ∈ affΩ := subset_affineSpan ℝ P.Ω hδ_in_Ω

let dir' := (affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction
have hA_dim : Module.finrank ℝ (↥dir') ≥ 1 :=
  intersection_affine_dim_ge_one U affΩ δ hδ_in_Psr hδ_aff hdim_Psr hm
```

The key lemma `intersection_affine_dim_ge_one` (line 108 of `Edge2.lean`)
uses the submodular inequality for finrank:

```lean4
private lemma finrank_inf_ge_one {n : ℕ} (U W : Submodule ℝ (CoeffVec n))
    (hU : Module.finrank ℝ U = n) (hW : Module.finrank ℝ W ≥ 2) :
    Module.finrank ℝ ↥(U ⊓ W) ≥ 1 := by
  have h_sum_le : Module.finrank ℝ ↥(U ⊔ W) ≤ n + 1 := ...
  have hformula : Module.finrank ℝ ↥(U ⊔ W) + Module.finrank ℝ ↥(U ⊓ W) =
    Module.finrank ℝ U + Module.finrank ℝ W :=
    Submodule.finrank_sup_add_finrank_inf_eq U W
  omega
```

---

## Step 5 — The intersection contains a non-zero direction

**Math.** Since `dim(P_s ∩ aff(Ω)) ≥ 1`, there exists a non-zero vector `v` in
`(P_s ∩ aff(Ω))`. Moreover, `δ + tv ∈ P_s ∩ aff(Ω)` for all `t ∈ ℝ` (since
`P_s` and `aff(Ω)` are affine subspaces).

**Lean.** The direction space `dir'` (computed above) has dimension ≥ 1, so
it is nontrivial:

```lean4
have h_dir_nontrivial : Nontrivial (↥dir') :=
  direction_nontrivial_from_dim_ge_1 hA_dim

obtain ⟨v_sub, hv_sub_ne⟩ := exists_ne (0 : ↥dir')
let v : CoeffVec n := v_sub.val
have hv_ne : v ≠ 0 := by
  intro h; apply hv_sub_ne; exact Subtype.ext h
have hv_dir : v ∈ dir' := v_sub.property
```

Then `v ∈ P_s` and `v ∈ affΩ.direction` by construction (dir' is contained in
both direction spaces).

---

## Step 6 — The ray `δ + tv` must exit `Ω`

**Math.** Since `Ω` is compact (closed and bounded), the line `δ + ℝ·v` cannot stay
inside `Ω` forever. There exists `t_out > 0` such that `δ + t_out·v ∉ Ω`.

**Lean.**

```lean4
have h_escapes : ∃ (t : ℝ), δ + t • v ∉ P.Ω :=
  ray_escapes_polytope P δ v hδ_in_Ω hv_ne
```

`ray_escapes_polytope` (in `EdgeTheoremDefs.lean:239`) uses boundedness:
pick `t = (|C|+1)/‖v‖` where `C` is the diameter bound.

---

## Step 7 — Find the exit point on the frontier of `Ω`

**Math.** On the segment `[δ, δ + t_out·v]`, the endpoints are respectively
inside and outside `Ω`. By connectedness of the segment, there must be a
point `δ_bound` on the segment that lies on the topological frontier
`∂Ω = closure(Ω) \ int(Ω)`.

If `δ ∉ ∂Ω` (i.e. `δ ∈ int(Ω)`), then the segment exits for the first time
at some `δ_bound ∈ ∂Ω`. If `δ ∈ ∂Ω` already, we take `δ_bound = δ`.

**Lean.** This is `segment_boundary_intersection` (line 178 of `Edge2.lean`):

```lean4
obtain ⟨δ_bound, h_seg, h_front⟩ :=
  segment_boundary_intersection P δ hδ_in_Ω hδ_not_front v hv_ne t_out ht_out
```

The proof: the segment is connected and covered by `interior(Ω) ∪ interior(Ωᶜ)`.
Since both parts are nonempty open sets in the segment, their union covering the
segment forces the existence of a boundary point where the segment exits `Ω`.

The combined result `exists_boundary_point_in_Psr` (line 247) packages steps 5–7:

```lean4
have h_boundary_root : ∃ δ_bound, δ_bound ∈ (P_sr n s.re : Set (CoeffVec n)) ∩ frontier P.Ω :=
  exists_boundary_point_in_Psr P s.re δ hδ_in_Ω hδ_in_Psr affΩ hδ_aff hA_dim
```

---

## Step 8 — The boundary point lies on an exposed face

**Math.** Since `δ_bound ∈ ∂Ω`, there exists a supporting hyperplane `H` of `Ω`
at `δ_bound`. The intersection `F = Ω ∩ H` is an exposed face containing
`δ_bound`. Since `δ_bound ∈ P_s`, we have `s ∈ R(F)`.

**Lean.**

```lean4
have h_int_nonempty : (interior P.Ω).Nonempty := P.interior_nonempty
obtain ⟨F, hF_exposed, hδ_in_F, hs_in_RF⟩ :=
  exists_exposed_face_containing_boundary_point P s.re δ_bound hδ_bound_front hδ_bound_Psr
    h_int_nonempty
```

`exists_exposed_face_containing_boundary_point` (line 356):

1. Uses `geometric_hahn_banach_open_point` to separate `δ_bound` from
   `interior P.Ω`, obtaining a continuous linear functional `f` with
   `f(x) < f(δ_bound)` for all `x ∈ interior P.Ω`.

2. Constructs `hp : SupportingHyperplane P` from `f` and `c = f(δ_bound)`.

3. Defines `F = ExposedFace hp = {x ∈ P.Ω | f(x) = f(δ_bound)}`.

4. Proves `δ_bound ∈ F` and `s ∈ RootSpaceSet F` (since `δ_bound ∈ P_s`).

---

## Step 9 — Iterative descent to an exposed edge

**Math.** We now have an exposed face `F` with `s ∈ R(F)`. If `dim(F) = 1`,
then `F` is itself an exposed edge. If `dim(F) ≥ 2`, we can find a **proper**
exposed subface `G ⊊ F` with `δ_bound ∈ G`, `s ∈ R(G)`, and
`1 ≤ dim(G) < dim(F)`. Repeating this process, we eventually reach a face of
dimension exactly 1 — an exposed edge.

**Lean.** The descent is `descend_to_exposed_edge` (line 1958):

```lean4
let m_F := Module.finrank ℝ (affineSpan ℝ F).direction
by_cases hm_F_ge_2 : m_F ≥ 2
· obtain ⟨E, hE_edge, h_edge_re⟩ :=
    descend_to_exposed_edge P s.re F hF_exposed hs_in_RF hm_F_ge_2
  use E, hE_edge
  ...
· by_cases hm_F_1 : m_F = 1
  · refine ⟨F, isExposedEdge_of_dim_1 hF_exposed hm_F_1, ...⟩
  · -- dim(F) = 0 — vertex case (see Step 10)
```

`descend_to_exposed_edge` works by well-founded recursion on the dimension:

```lean4
private lemma descend_to_exposed_edge {n : ℕ} (P : Polytope n) (r : ℝ)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hs_F : (r : ℂ) ∈ RootSpaceSet F)
    (hF_dim_ge_2 : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 2) :
    ∃ E, IsExposedEdge P E ∧ (r : ℂ) ∈ RootSpaceSet E := by
  ...
  obtain ⟨δ_bound, hδ_bound_inter, hδ_bound_front, hδ_bound_not_relint⟩ :=
    exists_boundary_point_in_face_rootspace P r δ_F F hF_exp hδ_F_in_F hδ_F_Psr h_inter_dim
  obtain ⟨G, hG_exp, hδ_bound_in_G, hG_dim_lt, hG_dim_ge_1⟩ :=
    exists_proper_subface_of_boundary_point P F hF_exp δ_bound ... hm_F_ge_2
  have hs_G : (r : ℂ) ∈ RootSpaceSet G := ...
  -- recurse if dim(G) ≥ 2, otherwise G is the edge
```

The recursion uses `termination_by Module.finrank ℝ (affineSpan ℝ F).direction`
and `decreasing_by exact hG_dim_lt`.

The core step `exists_proper_subface_of_boundary_point` (line 1378) constructs
a proper exposed subface `G` with `dim(G) < dim(F)` and `dim(G) ≥ 1` using
a Hahn–Banach separation argument.

---

## ⚠️ Step 10 — Vertex case: `dim(F) = 0` [GAP]

**Math (book).** The proof in the book avoids this case because the intersection
`P_s ∩ aff(Ω)` has dimension ≥ 1 (Step 4), and an affine subspace of dimension
≥ 1 that contains a point of `Ω` **must** exit `Ω` through an `(m-1)`-dimensional
exposed face, not through a vertex (0-dimensional face). This is a general-position
argument: a 1-dimensional affine subspace hitting a compact convex set of
dimension ≥ 2 cannot exit only at a single vertex — it must cross a facet of
codimension 1.

**Lean (gap).** In the current code, when `hF_exposed` gives an exposed face F
of dimension 0 (i.e. `m_F = 0`, a vertex), we cannot descend further. The code
arrives at line 2163 with a `sorry`:

```lean4
· -- F has dim 0 (vertex case): δ_bound is a vertex of P.Ω and we need an exposed
  -- edge containing it.
  sorry
```

**What's needed.** We need to construct an exposed edge `E` of `P.Ω` that
contains the vertex `δ_bound` and satisfies `s ∈ R(E)`. A strategy:

1. Since `dim(aff(Ω)) = m ≥ 2`, pick another vertex `δ' ≠ δ_bound` of `P.Ω`.
2. The segment `[δ_bound, δ']` is an edge of the polytope.
3. Find a supporting hyperplane that exposes exactly this edge (i.e. a
   functional `f` vanishing on `δ_bound` and `δ'` and negative elsewhere).
4. Since `δ_bound ∈ P_s`, we need `s` to also be a root of `δ'`. The
   book proof ensures this by noting that the entire intersection
   `P_s ∩ aff(Ω)` contains a line, and this line passes through `δ_bound`
   and some other point `δ' ∈ Ω`. We can take `δ'` to be where this line
   hits the boundary of `Ω`, giving `δ' ∈ P_s` automatically.

In other words, the book's construction **guarantees** that the boundary
point we find in Step 7 lies on an `(m-1)`-dimensional exposed face, not on
a vertex. The Lean code bypasses this by using a general Hahn–Banach
functional at any boundary point, which can produce a 0-dimensional exposed
face. The fix is either:

- **Option A:** In `exists_boundary_point_in_Psr`, use the direction `v`
  (which lies in `P_s`) to track which supporting hyperplane to construct,
  ensuring the resulting exposed face has dimension ≥ 1.
- **Option B:** Fill the vertex case using a forward ray from `δ_bound`
  along the direction `v`, which must exit `Ω` at another boundary point
  `δ'' ∈ P_s`. The segment `[δ_bound, δ'']` is then the required exposed edge.

---

## Summary of the formalization state

| Step | Description | Lean lemma | Status |
|------|-------------|------------|--------|
| 1 | Root witness `δ ∈ Ω` with `δ(s) = 0` | `RootSpace P` (hypothesis) | ✓ |
| 2 | `dim(P_s) = n` | `P_sr_dimension r` (Edge2.lean:32) | ✓ |
| 3 | Base: `dim(affΩ) = 1 ⇒` Ω is edge | `polytope_dim1_is_exposed_edge` (Edge2.lean:2013) | ✓ |
| 4 | `dim(P_s ∩ affΩ) ≥ 1` when `m ≥ 2` | `intersection_affine_dim_ge_one` (Edge2.lean:108) | ✓ |
| 5 | Nonzero direction `v ∈ P_s ∩ affΩ` | `direction_nontrivial_from_dim_ge_1` (Edge2.lean:1609) | ✓ |
| 6 | Ray escapes `Ω` (boundedness) | `ray_escapes_polytope` (EdgeDefs.lean:239) | ✓ |
| 7 | Exit point on `frontier Ω` | `segment_boundary_intersection` (Edge2.lean:178) | ✓ |
| 7' | Combined: boundary point in `P_s ∩ ∂Ω` | `exists_boundary_point_in_Psr` (Edge2.lean:247) | ✓ |
| 8 | Boundary point → exposed face containing `s` | `exists_exposed_face_containing_boundary_point` (Edge2.lean:356) | ✓ |
| 9 | Iterative descent to dimension 1 | `descend_to_exposed_edge` (Edge2.lean:1958) | ✓ |
| 9a | Proper subface construction (dim ≥ 1, `< dim(F)`) | `exists_proper_subface_of_boundary_point` (Edge2.lean:1378) | Partial¹ |
| 10 | Vertex case: edge through a vertex | Gap at Edge2.lean:2163 | ❌ `sorry` |

¹ `exists_proper_subface_of_boundary_point` has one `sorry` in Case A (`hG_dim_ge_1`)
  and the entire Case B (`g_Ω` constant on F) is `sorry`.
  A complete version of Case B exists in the commented-out block (lines 1141–1375)
  and needs to be reintegrated.
