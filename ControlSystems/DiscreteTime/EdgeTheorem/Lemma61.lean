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

/-! # Lemma 6.1 (edgetheorem.md, Lemma 6.1)

Real `s` in `R(Omega)` lies in `R(E)` for an exposed edge `E`;
non-real `s` lies in `R(F)` for an exposed face `F` (Assumption 6.1:
positive leading coefficient on vertices).

Proof idea: `P_sr` has dim n, `P_sc` dim n-1; each meets `aff(Omega)`
in positive dimension, giving a boundary point; Hahn-Banach yields an
exposed face; descent (`EdgeDescent`) lowers `dim aff(F)` to 1 (real)
or at most 2 (complex). See `lemma61_real`, `lemma61_complex`, `lemma61`.
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
    let dir' := meetDir n U affΩ
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
        descend_to_exposed_edge hn P s.re F hF_exposed hs_in_RF hm_F_ge_2
      use E, hE_edge
      rw [← hs_real] at h_edge_re
      exact h_edge_re
    · by_cases hm_F_1 : m_F = 1
      · refine ⟨F, isExposedEdge_of_dim_1 hF_exposed hm_F_1, ?_⟩
        rw [hs_real]
        exact hs_in_RF
      · -- F has dim 0: singleton face. Fall back to exists_exposed_edge_through_vertex.
        have hδ_bound_in_Ω : δ_bound ∈ P.Ω :=
          frontier_point_in_Ω P δ_bound hδ_bound_front
        obtain ⟨E, hE_edge, hs_re_RF⟩ :=
          exists_exposed_edge_through_vertex hn P s.re δ_bound hδ_bound_in_Ω hδ_bound_front hδ_bound_Psr
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

/-- Complex case of Lemma 6.1: If `s` has nonzero imaginary part and `P` satisfies Assumption 6.1
  (all vertices have positive leading coefficient), then there exists an exposed face `F` of `P`
  such that `s ∈ RootSpaceSet F`. -/
theorem lemma61_complex_with_dim (hn : n ≥ 1) (P : Polytope n) (s : ℂ) (hs : s ∈ RootSpace P)
    (hleading : ∀ v ∈ P.vertices, 0 < v (Fin.last n)) : s.im ≠ 0 →
    ∃ F, IsExposedFace P F ∧ s ∈ RootSpaceSet F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction ≤ 2 := by
  intro hcomplex
  by_cases hn2 : n ≥ 2
  · unfold RootSpace RootSpaceSet at hs
    obtain ⟨δ, hδ_in_Ω, hδ_root⟩ := hs
    have hδ_in_Psc : δ ∈ (P_sc n s : Set (CoeffVec n)) :=
      mem_P_sc_of_isRoot s δ hδ_root
    let m := Module.finrank ℝ (affineSpan ℝ (P.Ω)).direction
    have hm_ge_3 : m ≥ 3 := by
      dsimp [m]
      have h_span_top : affineSpan ℝ P.Ω = ⊤ :=
        ((Convex.interior_nonempty_iff_affineSpan_eq_top (convex_convexHull ℝ _)).mp
          (by simpa using P.interior_nonempty))
      rw [h_span_top, AffineSubspace.direction_top, finrank_top, finrank_CoeffVec]
      omega
    let affΩ : AffineSubspace ℝ (CoeffVec n) := affineSpan ℝ (P.Ω)
    have hdim_Psc : Module.finrank ℝ (P_sc n s) = n - 1 :=
      P_sc_dimension hn s hcomplex
    have hδ_aff : δ ∈ affΩ := subset_affineSpan ℝ P.Ω hδ_in_Ω
    let dir' := meetDir n (P_sc n s) affΩ
    have hA_dim : Module.finrank ℝ (↥dir') ≥ 1 :=
      intersection_affine_dim_ge_one_complex (P_sc n s) affΩ δ hδ_in_Psc hδ_aff
        hdim_Psc hm_ge_3
    obtain ⟨δ_bound, hδ_bound⟩ :=
      exists_boundary_point_in_Psc P s δ hδ_in_Ω hδ_in_Psc affΩ hδ_aff hA_dim
    have hδ_bound_front : δ_bound ∈ frontier P.Ω := hδ_bound.2
    have hδ_bound_Psc : δ_bound ∈ (P_sc n s : Set (CoeffVec n)) := hδ_bound.1
    have h_int_nonempty : (interior P.Ω).Nonempty := P.interior_nonempty
    obtain ⟨F, hF_exposed, hδ_in_F, hs_in_RF⟩ :=
      exists_exposed_face_containing_boundary_point_complex P s δ_bound
        hδ_bound_front hδ_bound_Psc h_int_nonempty
    let m_F := Module.finrank ℝ (affineSpan ℝ F).direction
    by_cases hm_F_ge_3 : m_F ≥ 3
    · exact descend_to_exposed_face_with_dim hn P s hcomplex F hF_exposed hs_in_RF hm_F_ge_3
    · exact ⟨F, hF_exposed, hs_in_RF, by omega⟩
  · -- n = 1. By Assumption 6.1 (P.leading_pos), all vertices have positive leading
    -- coefficient, thus so does every δ ∈ P.Ω. Hence (δ 1 : ℂ) ≠ 0, forcing s to be
    -- real, contradicting hcomplex.
    have hn1 : n = 1 := by omega
    subst hn1
    unfold RootSpace RootSpaceSet at hs
    obtain ⟨δ, hδ_in_Ω, hδ_root⟩ := hs
    have h_eval : ((polyOfVec δ).map (algebraMap ℝ ℂ)).eval s = (δ 0 : ℂ) + (δ 1 : ℂ) * s := by
      simp [polyOfVec, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_mul, Polynomial.map_add]
    have h_eval_zero : ((polyOfVec δ).map (algebraMap ℝ ℂ)).eval s = 0 := hδ_root
    rw [h_eval] at h_eval_zero
    have h_sum : (δ 0 : ℂ) + (δ 1 : ℂ) * s = 0 := h_eval_zero
    by_cases hδ1_ne_zero : (δ 1 : ℂ) ≠ 0
    · have h_mul : (δ 1 : ℂ) * s = -(δ 0 : ℂ) := by
        calc
          (δ 1 : ℂ) * s = -(δ 0 : ℂ) + (δ 0 : ℂ) + (δ 1 : ℂ) * s := by ring
          _ = -(δ 0 : ℂ) + ((δ 0 : ℂ) + (δ 1 : ℂ) * s) := by ring
          _ = -(δ 0 : ℂ) + 0 := by rw [h_sum]
          _ = -(δ 0 : ℂ) := by simp
      have hs_eq : s = -((δ 0 : ℂ) / (δ 1 : ℂ)) := by
        field_simp [hδ1_ne_zero]
        calc
          s * (δ 1 : ℂ) = (δ 1 : ℂ) * s := mul_comm _ _
          _ = -(δ 0 : ℂ) := h_mul
      have hs_real : s.im = 0 := by
        rw [hs_eq]
        simp
      exact absurd hs_real hcomplex
    · -- δ 1 = 0. Show this contradicts hleading.
      have h_δ1_pos : 0 < δ 1 := by
        have h_mem_conv : δ ∈ convexHull ℝ (P.vertices : Set (CoeffVec 1)) := hδ_in_Ω
        have h_vertices_pos : (P.vertices : Set (CoeffVec 1)) ⊆ {x | 0 < x 1} := by
          intro v hv
          have h := hleading v hv
          simpa [Fin.last] using h
        have h_convex : Convex ℝ {x : CoeffVec 1 | 0 < x 1} := by
          intro x hx y hy a b ha hb hab
          have hx1 : 0 < x 1 := hx
          have hy1 : 0 < y 1 := hy
          have ha_nonneg : 0 ≤ a := ha
          have hb_nonneg : 0 ≤ b := hb
          have hcalc : (a • x + b • y) 1 = a * (x 1) + b * (y 1) := by simp
          have hpos : 0 < a * (x 1) + b * (y 1) := by
            by_cases ha0 : a = 0
            · subst ha0
              have hb1 : b = 1 := by linarith
              subst hb1
              simpa
            · have ha_pos : 0 < a := by
                by_contra! h
                have ha0' : a = 0 := by nlinarith
                exact ha0 ha0'
              have ha_x1_pos : 0 < a * (x 1) := mul_pos ha_pos hx1
              have hb_y1_nonneg : 0 ≤ b * (y 1) := mul_nonneg hb_nonneg (by linarith)
              nlinarith
          simpa [hcalc]
        have h_subset : convexHull ℝ (P.vertices : Set (CoeffVec 1)) ⊆ {x | 0 < x 1} :=
          convexHull_min h_vertices_pos h_convex
        exact h_subset h_mem_conv
      have h_δ1_ne_zero' : (δ 1 : ℂ) ≠ 0 := by exact_mod_cast h_δ1_pos.ne.symm
      exact absurd h_δ1_ne_zero' hδ1_ne_zero

/-- Lemma 6.1's complex case without the additional dimension information. -/
theorem lemma61_complex (hn : n ≥ 1) (P : Polytope n) (s : ℂ) (hs : s ∈ RootSpace P)
    (hleading : ∀ v ∈ P.vertices, 0 < v (Fin.last n)) : s.im ≠ 0 →
    ∃ F, IsExposedFace P F ∧ s ∈ RootSpaceSet F := by
  intro hcomplex
  obtain ⟨F, hF, hsF, _⟩ := lemma61_complex_with_dim hn P s hs hleading hcomplex
  exact ⟨F, hF, hsF⟩

/-- Lemma 6.1: For a polytope `P` satisfying Assumption 6.1 (all vertices have positive leading
  coefficient) and a root `s` of `P`, either `s` is real (in which case there exists an exposed edge
  with `s` in its root space set) or `s` is complex (in which case there exists an exposed face with
  `s` in its root space set). -/
theorem lemma61 (hn : n ≥ 1) (P : Polytope n) (s : ℂ) (hs : s ∈ RootSpace P)
    (hleading : ∀ v ∈ P.vertices, 0 < v (Fin.last n)) :
    (s.im = 0 → ∃ E, IsExposedEdge P E ∧ s ∈ RootSpaceSet E) ∧
    (s.im ≠ 0 → ∃ F, IsExposedFace P F ∧ s ∈ RootSpaceSet F) :=
  ⟨lemma61_real hn P s hs, lemma61_complex hn P s hs hleading⟩

end CoeffBox
