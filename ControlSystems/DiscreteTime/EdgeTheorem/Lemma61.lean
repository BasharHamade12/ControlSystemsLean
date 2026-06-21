module

public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeTheoremDefs
public import ControlSystems.DiscreteTime.EdgeTheorem.BasicLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.PreliminaryLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.ExposedFaceLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.SubfaceConstruction
public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeDescent


@[expose] public section

open Polynomial Affine FiniteDimensional LinearMap Set

namespace CoeffBox

/-! # Lemma 6.1: Root Spaces Meet Exposed Edges/Faces

**Statement (Lemma 6.1):** Let `Ω ⊆ ℝⁿ⁺¹` be a polytope (convex hull of finitely many
vertices, with nonempty interior).  For any `s ∈ ℂ` with `s ∈ R(Ω)` (the root space of
`Ω` – i.e. `s` is a root of some polynomial whose coefficient vector lies in `Ω`):

  • **Real case** (`s.im = 0`):  There exists an **exposed edge** `E` of `Ω` such that
    `s ∈ R(E)`.
  • **Complex case** (`s.im ≠ 0`):  There exists an **exposed face** `F` of `Ω` such that
    `s ∈ R(F)`.

This file implements `lemma61_real` (the real case) and provides a deferred stub for
`lemma61_complex` (the complex case).  The full theorem `lemma61` bundles both.

---

## Proof Structure of `lemma61_real`

### Overview

The proof uses a **dimension descent** argument.  Let `m := dim(aff(Ω))` be the
dimension of the affine hull of `Ω`.

  • If `m = 0`, the result is impossible because `Ω` has nonempty interior
    (`polytope_direction_dim_pos`).
  • If `m = 1`, then `Ω` itself is already an exposed edge
    (`polytope_dim1_is_exposed_edge`).
  • If `m ≥ 2`, we carry out the following steps:

### Step 1 – Obtain a root vector `δ ∈ Ω`

Unfold the definition of `RootSpace` and extract a coefficient vector `δ ∈ Ω`
whose polynomial has `s` as a root:
```lean4
obtain ⟨δ, hδ_in_Ω, hδ_root⟩ := hs
```

### Step 2 – Place `δ` in `P_sr` (the kernel of evaluation at `s.re`)

Because `s` is real (`s.im = 0`), we have `s = (s.re : ℂ)`.  The condition that
`δ`'s polynomial has root `s` translates to `δ` belonging to the subspace
`P_sr n s.re := ker(evalLinear s.re)`.  This is a linear subspace of codimension 1,
hence `dim(P_sr) = n`.
```lean4
have hδ_in_Psr : δ ∈ (P_sr n s.re : Set (CoeffVec n)) :=
  mem_P_sr_of_isRoot s.re δ hδ_root
```

### Step 3 – Lower bound on the intersection dimension

Let `U = P_sr` and `affΩ = aff(Ω)`.  Consider
`S := aff( U ∩ affΩ )`, the affine hull of the intersection.  Using the dimension
formula for the intersection of a linear subspace and an affine subspace
(`intersection_affine_dim_ge_one`), we get:
```lean4
have hA_dim : Module.finrank ℝ (↥dir') ≥ 1 :=
  intersection_affine_dim_ge_one U affΩ δ hδ_in_Psr hδ_aff hdim_Psr hm
```
**(Uses `P_sr_dimension` – a lemma from `PreliminaryLemmas` proving `dim(P_sr) = n`.)**

### Step 4 – Find a boundary point `δ_bound ∈ P_sr ∩ frontier(Ω)`

Because `S` contains a line through `δ` (from `dim(S) ≥ 1`) and `Ω` is bounded,
that line must exit `Ω`, so it crosses the frontier.  The key lemma
`exists_boundary_point_in_Psr` produces a point `δ_bound` belonging to both
`P_sr` and `frontier P.Ω`.
```lean4
have h_boundary_root : ∃ δ_bound, δ_bound ∈ (P_sr n s.re : Set (CoeffVec n)) ∩ frontier P.Ω :=
  exists_boundary_point_in_Psr P s.re δ hδ_in_Ω hδ_in_Psr affΩ hδ_aff hA_dim
```

### Step 5 – Construct an exposed face `F` containing `δ_bound`

Apply `exists_exposed_face_containing_boundary_point` (from `ExposedFaceLemmas`).
This uses the Hahn–Banach separation theorem (`geometric_hahn_banach_open_point`) to
strictly separate `δ_bound` from `interior P.Ω`, then extends the resulting functional
to a supporting hyperplane.  The exposed face `F` is the intersection of `Ω` with that
hyperplane.
```lean4
obtain ⟨F, hF_exposed, hδ_in_F, hs_in_RF⟩ :=
  exists_exposed_face_containing_boundary_point P s.re δ_bound hδ_bound_front hδ_bound_Psr
    h_int_nonempty
```
**(Uses `frontier_point_not_interior`, `frontier_point_in_Ω`, and
`rootspace_mem_of_eval_zero` from `ExposedFaceLemmas`.)**

### Step 6 – Dimension descent on `F`

Let `m_F := dim(aff(F))`.

  • **If `m_F ≥ 2`**:  Recursively descend (`descend_to_exposed_edge` from
    `EdgeDescent`).  This lemma finds a boundary point `δ_bound` on the *relative*
    boundary of `F` (guaranteed not to be in `intrinsicInterior ℝ F`), constructs a
    **proper** exposed subface `G ⊂ F` with strictly smaller dimension, and recurses.
  • **If `m_F = 1`**:  `F` is already an exposed edge; we are done
    (`isExposedEdge_of_dim_1` from `EdgeDescent`).
  • **If `m_F = 0`** (a vertex):  Use `exists_exposed_edge_through_vertex` (from
    `EdgeDescent`), which relies on the axiom `vertex_incident_to_exposed_edge`
    (stated in `EdgeTheoremDefs`).

The recursive descent terminates because the dimension strictly decreases at each
step and is bounded below by 0.

### Step 7 – Wrap up

The final exposed edge `E` satisfies `IsExposedEdge P E` and `s ∈ RootSpaceSet E`
(as required).

---

## Key Lemmas Referenced (by source file)

| Lemma | File | Role |
|-------|------|------|
| `mem_P_sr_of_isRoot` | `ExposedFaceLemmas` | Step 2 |
| `P_sr_dimension` | `PreliminaryLemmas` | Step 3 |
| `intersection_affine_dim_ge_one` | `PreliminaryLemmas` | Step 3 |
| `exists_boundary_point_in_Psr` | `PreliminaryLemmas` | Step 4 |
| `exists_exposed_face_containing_boundary_point` | `ExposedFaceLemmas` | Step 5 |
| `frontier_point_not_interior` | `ExposedFaceLemmas` | Step 5 |
| `frontier_point_in_Ω` | `ExposedFaceLemmas` | Step 5 |
| `rootspace_mem_of_eval_zero` | `ExposedFaceLemmas` | Steps 5–6 |
| `descend_to_exposed_edge` | `EdgeDescent` | Step 6 |
| `isExposedEdge_of_dim_1` | `EdgeDescent` | Step 6 |
| `exists_exposed_edge_through_vertex` | `EdgeDescent` | Step 6 |
| `vertex_incident_to_exposed_edge` | `EdgeTheoremDefs` | Step 6 (axiom) |
| `polytope_direction_dim_pos` | This file | Edge case `m=0` |
| `polytope_dim1_is_exposed_edge` | This file | Edge case `m=1` |

---

## Complex Case (`lemma61_complex`)

The complex case is **deferred** (body is `sorry`).  It will be proved after the
real case is fully stable and will follow a similar strategy but without the
dimensional descent to an edge (the complex root space lives on a face of
arbitrary dimension).

-/

/-- A polytope with nonempty interior has affine dimension ≥ 1,
    so m = 0 is impossible given interior_nonempty. -/
lemma polytope_direction_dim_pos {n : ℕ} (P : Polytope n) :
    Module.finrank ℝ (affineSpan ℝ P.Ω).direction ≥ 1 := by
  have h_convex : Convex ℝ P.Ω := convex_convexHull ℝ _
  have h_findim : FiniteDimensional ℝ (CoeffVec n) := by infer_instance
  have h_span_eq_top : affineSpan ℝ P.Ω = ⊤ :=
    ((Convex.interior_nonempty_iff_affineSpan_eq_top h_convex).mp (by
      simpa using P.interior_nonempty))
  have h_finrank : Module.finrank ℝ (affineSpan ℝ P.Ω).direction =
      Module.finrank ℝ (CoeffVec n) := by
    rw [h_span_eq_top, AffineSubspace.direction_top, finrank_top]
  rw [h_finrank, finrank_CoeffVec]
  omega

/-- If the affine dimension of P.Ω equals 1, then P.Ω is itself an exposed edge.
    Requires n ≥ 1 because IsExposedEdge is impossible when n = 0. -/
lemma polytope_dim1_is_exposed_edge {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (hm : Module.finrank ℝ (affineSpan ℝ P.Ω).direction = 1) :
    IsExposedEdge P P.Ω := by
  have h_pos : 0 < Module.finrank ℝ (affineSpan ℝ P.Ω).direction := by
    rw [hm]; omega
  have h_nontriv_dir : Nontrivial (affineSpan ℝ P.Ω).direction :=
    Module.nontrivial_of_finrank_pos h_pos
  have h_nonzero_dir : ∃ d : (affineSpan ℝ P.Ω).direction, d ≠ 0 := by
    exact exists_ne (0 : (affineSpan ℝ P.Ω).direction)
  obtain ⟨d, hd⟩ := h_nonzero_dir
  let d_val : CoeffVec n := d.val
  have hd_val_ne_zero : d_val ≠ 0 := Subtype.coe_ne_coe.mpr hd
  have h_two : n + 1 ≥ 2 := by omega
  have h_exists_k : ∃ k : Fin (n+1), d_val k ≠ 0 := by
    by_contra h_no_k
    push_neg at h_no_k
    apply hd_val_ne_zero
    ext i
    exact h_no_k i
  obtain ⟨k, hk⟩ := h_exists_k
  have h_exists_j : ∃ j : Fin (n+1), j ≠ k := by
    have hNontriv : Nontrivial (Fin (n+1)) := by
      have h0ne1 : (0 : Fin (n+1)) ≠ 1 := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      exact ⟨⟨0, 1, h0ne1⟩⟩
    exact exists_ne k
  obtain ⟨j, hj⟩ := h_exists_j
  let f : CoeffVec n →ₗ[ℝ] ℝ :=
    if h_dj : d_val j = 0 then LinearMap.proj j
    else (d_val j) • LinearMap.proj k - (d_val k) • LinearMap.proj j
  have hf_d_val : f d_val = 0 := by
    dsimp [f]
    by_cases h_dj : d_val j = 0
    · simp [h_dj]
    · simp [h_dj, LinearMap.proj_apply]; ring
  have hf_nonzero : f ≠ 0 := by
    by_cases h_dj : d_val j = 0
    · intro hzero
      have h := congrArg (fun g : CoeffVec n →ₗ[ℝ] ℝ =>
        g (fun i : Fin (n+1) => if i = j then 1 else 0)) hzero
      have hval : (1 : ℝ) = 0 := by
        simpa [f, h_dj, LinearMap.proj_apply] using h
      linarith
    · intro hzero
      have h := congrArg (fun g : CoeffVec n →ₗ[ℝ] ℝ =>
        g (fun i : Fin (n+1) => if i = k then 1 else 0)) hzero
      have hval : d_val j = 0 := by
        simpa [f, h_dj, LinearMap.proj_apply, hj] using h
      exact h_dj hval
  have hf_dir : ∀ v ∈ (affineSpan ℝ P.Ω).direction, f v = 0 := by
    intro v hv
    have h_dir_span : (affineSpan ℝ P.Ω).direction = Submodule.span ℝ {d_val} := by
      refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
      · exact (Submodule.span_singleton_le_iff_mem d_val (affineSpan ℝ P.Ω).direction).mpr d.2
      · rw [hm, finrank_span_singleton hd_val_ne_zero]
    rw [h_dir_span] at hv
    rcases Submodule.mem_span_singleton.mp hv with ⟨μ, hμ⟩
    rw [← hμ, map_smul, hf_d_val, smul_zero]
  obtain ⟨δ0, hδ0_in_int⟩ := P.interior_nonempty
  have hδ0_in_Ω : δ0 ∈ P.Ω := interior_subset hδ0_in_int
  have hf_const : ∀ x ∈ affineSpan ℝ P.Ω, f x = f δ0 := by
    intro x hx
    have hδ0_span : δ0 ∈ affineSpan ℝ P.Ω := subset_affineSpan ℝ P.Ω hδ0_in_Ω
    have h_diff : (x -ᵥ δ0 : CoeffVec n) ∈ (affineSpan ℝ P.Ω).direction :=
      AffineSubspace.vsub_mem_direction hx hδ0_span
    calc
      f x = f ((x - δ0) + δ0) := by abel_nf
      _ = f (x - δ0) + f δ0 := by simp
      _ = f (x -ᵥ δ0) + f δ0 := by rw [vsub_eq_sub]
      _ = 0 + f δ0 := by rw [hf_dir (x -ᵥ δ0) h_diff]
      _ = f δ0 := by simp
  let c := f δ0
  have h_touches : ∃ x ∈ P.Ω, f x = c := ⟨δ0, hδ0_in_Ω, rfl⟩
  have h_upper_bound : ∀ x ∈ P.Ω, f x ≤ c := by
    intro x hx
    have hx_span : x ∈ affineSpan ℝ P.Ω := subset_affineSpan ℝ P.Ω hx
    have : f x = c := hf_const x hx_span
    rw [this]
  let hp : SupportingHyperplane P :=
    { f := f
      c := c
      nonzero := hf_nonzero
      upper_bound := h_upper_bound
      touches := h_touches
    }
  have h_exposed : P.Ω = ExposedFace hp := by
    ext x; constructor
    · intro hx; refine ⟨hx, ?_⟩
      have hx_span : x ∈ affineSpan ℝ P.Ω := subset_affineSpan ℝ P.Ω hx
      exact hf_const x hx_span
    · intro hx; exact hx.1
  have h_dir_finrank : Module.finrank ℝ (affineSpan ℝ (ExposedFace hp)).direction = 1 := by
    rw [← h_exposed, hm]
  exact ⟨hp, h_exposed, h_dir_finrank⟩

/-- Real case of Lemma 6.1: If `s` is a real root of `P` (i.e., `s.im = 0`), then there exists an exposed edge `E` of `P` such that `s ∈ RootSpaceSet E`. -/
theorem lemma61_real (hn : n ≥ 1) (P : Polytope n) (s : ℂ) (hs : s ∈ RootSpace P) :
    s.im = 0 → ∃ E, IsExposedEdge P E ∧ s ∈ RootSpaceSet E := by
  intro hreal
  unfold RootSpace RootSpaceSet at hs
  obtain ⟨δ, hδ_in_Ω, hδ_root⟩ := hs
  have hs_real : s = ↑s.re := by
    apply Complex.ext
    · simp
    · simp [hreal]
  have hδ_in_Psr : δ ∈ (P_sr n s.re : Set (CoeffVec n)) := by
    rw [hs_real] at hδ_root
    exact mem_P_sr_of_isRoot s.re δ hδ_root
  let m := Module.finrank ℝ (affineSpan ℝ (P.Ω)).direction
  by_cases hm : m ≥ 2
  · let U : Submodule ℝ (CoeffVec n) := P_sr n s.re
    let affΩ : AffineSubspace ℝ (CoeffVec n) := affineSpan ℝ (P.Ω)
    have hdim_Psr : Module.finrank ℝ U = n := P_sr_dimension s.re
    have hδ_aff : δ ∈ affΩ := subset_affineSpan ℝ P.Ω hδ_in_Ω
    let dir' := (affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction
    have hA_dim : Module.finrank ℝ (↥dir') ≥ 1 :=
      intersection_affine_dim_ge_one U affΩ δ hδ_in_Psr hδ_aff hdim_Psr hm
    have h_boundary_root : ∃ δ_bound, δ_bound ∈ (P_sr n s.re : Set (CoeffVec n)) ∩ frontier P.Ω :=
      exists_boundary_point_in_Psr P s.re δ hδ_in_Ω hδ_in_Psr affΩ hδ_aff hA_dim
    obtain ⟨δ_bound, hδ_bound⟩ := h_boundary_root
    have hδ_bound_front : δ_bound ∈ frontier P.Ω := hδ_bound.2
    have hδ_bound_Psr : δ_bound ∈ (P_sr n s.re : Set (CoeffVec n)) := hδ_bound.1
    have h_int_nonempty : (interior P.Ω).Nonempty := P.interior_nonempty
    obtain ⟨F, hF_exposed, hδ_in_F, hs_in_RF⟩ :=
      exists_exposed_face_containing_boundary_point P s.re δ_bound hδ_bound_front hδ_bound_Psr
        h_int_nonempty
    let m_F := Module.finrank ℝ (affineSpan ℝ F).direction
    by_cases hm_F_ge_2 : m_F ≥ 2
    · obtain ⟨E, hE_edge, h_edge_re⟩ :=
        descend_to_exposed_edge P s.re F hF_exposed hs_in_RF hm_F_ge_2
      use E, hE_edge
      rw [← hs_real] at h_edge_re
      exact h_edge_re
    · by_cases hm_F_1 : m_F = 1
      · refine ⟨F, isExposedEdge_of_dim_1 hF_exposed hm_F_1, ?_⟩
        rw [hs_real]
        exact hs_in_RF
      · -- F has dim 0: δ_bound is a vertex. Fall back to exists_exposed_edge_through_vertex.
        have hδ_bound_in_Ω : δ_bound ∈ P.Ω :=
          frontier_point_in_Ω P δ_bound hδ_bound_front
        obtain ⟨E, hE_edge, hs_re_RF⟩ :=
          exists_exposed_edge_through_vertex P s.re δ_bound hδ_bound_in_Ω hδ_bound_front hδ_bound_Psr
        use E, hE_edge
        rw [hs_real]
        exact hs_re_RF
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

/-- Complex case of Lemma 6.1: If `s` has nonzero imaginary part, then there exists an exposed face `F` of `P` such that `s ∈ RootSpaceSet F`. (Proof deferred.) -/
theorem lemma61_complex (hn : n ≥ 1) (P : Polytope n) (s : ℂ) (hs : s ∈ RootSpace P) :
    s.im ≠ 0 → ∃ F, IsExposedFace P F ∧ s ∈ RootSpaceSet F := by
  intro hcomplex
  -- to be done after the real case is totally done
  sorry

/-- Lemma 6.1: For a polytope `P` and a root `s` of `P`, either `s` is real (in which case there exists an exposed edge with `s` in its root space set) or `s` is complex (in which case there exists an exposed face with `s` in its root space set). -/
theorem lemma61 (hn : n ≥ 1) (P : Polytope n) (s : ℂ) (hs : s ∈ RootSpace P) :
    (s.im = 0 → ∃ E, IsExposedEdge P E ∧ s ∈ RootSpaceSet E) ∧
    (s.im ≠ 0 → ∃ F, IsExposedFace P F ∧ s ∈ RootSpaceSet F) :=
  ⟨lemma61_real hn P s hs, lemma61_complex hn P s hs⟩

end CoeffBox
