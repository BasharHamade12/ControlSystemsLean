module

public import ControlSystems.DiscreteTime.EdgeTheoremDefs
public import Mathlib.Analysis.Convex.Intrinsic
open Set
open LinearMap
open FiniteDimensional
open Polynomial
open Filter
open scoped Topology

namespace CoeffBox

-- =============================================================================
-- Public replicas of lemmas that are private in Edge2.lean
-- =============================================================================

lemma P_sr_dimension_public {n : ℕ} (r : ℝ) :
    Module.finrank ℝ (P_sr n r) = n := by
  unfold P_sr
  have h := LinearMap.finrank_range_add_finrank_ker (evalLinear (n := n) r)
  rw [finrank_CoeffVec] at h
  have hrank : Module.finrank ℝ (evalLinear (n := n) r).range = 1 := by
    have hsurj : Function.Surjective (evalLinear (n := n) r) :=
      evalLinear_surjective r
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp
  omega

lemma polytope_direction_dim_pos_public {n : ℕ} (P : Polytope n) :
    Module.finrank ℝ (affineSpan ℝ P.Ω).direction ≥ 1 := by
  have h_convex : Convex ℝ P.Ω := convex_convexHull ℝ _
  have h_span_eq_top : affineSpan ℝ P.Ω = ⊤ :=
    ((Convex.interior_nonempty_iff_affineSpan_eq_top h_convex).mp (by
      simpa using P.interior_nonempty))
  have h_finrank : Module.finrank ℝ (affineSpan ℝ P.Ω).direction =
      Module.finrank ℝ (CoeffVec n) := by
    rw [h_span_eq_top, AffineSubspace.direction_top, finrank_top]
  rw [h_finrank, finrank_CoeffVec]
  omega

lemma isExposedFace_subset_Ω_public {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
    (hF : IsExposedFace P F) : F ⊆ P.Ω := by
  obtain ⟨hp, rfl⟩ := hF
  exact Set.inter_subset_left

lemma rootspace_mem_of_eval_zero_public {n : ℕ} (r : ℝ) (δ_bound : CoeffVec n)
    (hδ_bound_Psr : δ_bound ∈ (P_sr n r : Set (CoeffVec n)))
    (F : Set (CoeffVec n)) (hδ_in_F : δ_bound ∈ F) : (r : ℂ) ∈ RootSpaceSet F := by
  unfold RootSpaceSet
  refine ⟨δ_bound, hδ_in_F, ?_⟩
  have heval : evalLinear r δ_bound = 0 := hδ_bound_Psr
  unfold Polynomial.IsRoot
  rw [eval_map]
  have htemp : eval₂ (algebraMap ℝ ℂ) (r : ℂ) (polyOfVec δ_bound) = (algebraMap ℝ ℂ) (evalLinear r δ_bound) := by
    calc
      eval₂ (algebraMap ℝ ℂ) (r : ℂ) (polyOfVec δ_bound) = (algebraMap ℝ ℂ) (eval r (polyOfVec δ_bound)) := by
        refine Polynomial.induction_on (polyOfVec δ_bound) ?_ ?_ ?_
        · intro c; simp
        · intro p q hp hq; simp [hp, hq]
        · intro n a; simp
      _ = (algebraMap ℝ ℂ) (evalLinear r δ_bound) := rfl
  rw [htemp, heval]
  simp

lemma mem_P_sr_of_isRoot_public {n : ℕ} (r : ℝ) (δ : CoeffVec n)
    (h : ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot (r : ℂ)) :
    δ ∈ (P_sr n r : Set (CoeffVec n)) := by
  unfold P_sr
  change evalLinear r δ = 0
  unfold Polynomial.IsRoot at h
  rw [eval_map] at h
  have h_eq : eval₂ (algebraMap ℝ ℂ) (r : ℂ) (polyOfVec δ) = (algebraMap ℝ ℂ) (evalLinear r δ) := by
    calc
      eval₂ (algebraMap ℝ ℂ) (r : ℂ) (polyOfVec δ) = (algebraMap ℝ ℂ) (eval r (polyOfVec δ)) := by
        refine Polynomial.induction_on (polyOfVec δ) ?_ ?_ ?_
        · intro c; simp
        · intro p q hp hq; simp [hp, hq]
        · intro n a; simp
      _ = (algebraMap ℝ ℂ) (evalLinear r δ) := rfl
  rw [h_eq] at h
  exact (map_eq_zero (algebraMap ℝ ℂ)).mp h

lemma finrank_ker_eq_finrank_sub_one_public {U : Type*} [AddCommGroup U] [Module ℝ U]
    [FiniteDimensional ℝ U] (g : U →ₗ[ℝ] ℝ) (hg_nonzero : g ≠ 0) :
    Module.finrank ℝ (LinearMap.ker g) = Module.finrank ℝ U - 1 := by
  have h_range_top : LinearMap.range g = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro y
    have ⟨x, hx⟩ : ∃ x, g x ≠ 0 := by
      by_contra h_allzero
      apply hg_nonzero
      apply LinearMap.ext
      intro x
      by_contra hgx_ne
      apply h_allzero
      exact ⟨x, hgx_ne⟩
    refine ⟨(y / g x) • x, ?_⟩
    calc
      g ((y / g x) • x) = (y / g x) * g x := by simp
      _ = y := by field_simp [hx]
  have h_dim_range : Module.finrank ℝ (LinearMap.range g) = 1 := by
    rw [h_range_top, finrank_top]
    simp
  have h_rnk_null := LinearMap.finrank_range_add_finrank_ker g
  rw [h_dim_range] at h_rnk_null
  omega

lemma polytope_dim1_is_exposed_edge_public {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (hm : Module.finrank ℝ (affineSpan ℝ P.Ω).direction = 1) :
    IsExposedEdge P P.Ω := by
  sorry

lemma polytope_is_exposed_face_self_public {n : ℕ} (P : Polytope n) : IsExposedFace P P.Ω := by
  sorry

-- =============================================================================
-- Lemma 6.1 (real root) from the Edge Theorem book — pure dimension descent
-- =============================================================================

/-- `dim[P_sr ∩ affineSpan(F).direction] ≥ 1` when `dim(F) ≥ 2`.
  This is the dimension-counting step in Lemma 6.1. -/
lemma dim_inter_Psr_aff_ge_one_public {n : ℕ} (F : Set (CoeffVec n))
    (hF_nonempty : F.Nonempty)
    (h_dim_ge_2 : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 2) (r : ℝ) :
    Module.finrank ℝ (↥(P_sr n r ⊓ (affineSpan ℝ F).direction)) ≥ 1 := by
  let U : Submodule ℝ (CoeffVec n) := P_sr n r
  let V : Submodule ℝ (CoeffVec n) := (affineSpan ℝ F).direction
  have hdimU : Module.finrank ℝ U = n := P_sr_dimension_public r
  have hdimV_ge_2 : Module.finrank ℝ V ≥ 2 := h_dim_ge_2
  have hdim_total : Module.finrank ℝ (CoeffVec n) = n + 1 := finrank_CoeffVec
  have hle_sup : U ⊔ V ≤ ⊤ := by simp
  have hdim_sup : Module.finrank ℝ ↥(U ⊔ V) ≤ n + 1 :=
    calc
      Module.finrank ℝ ↥(U ⊔ V) ≤ Module.finrank ℝ ↥(⊤ : Submodule ℝ (CoeffVec n)) :=
        Submodule.finrank_mono hle_sup
      _ = n + 1 := by rw [finrank_top, finrank_CoeffVec]
  have h_formula : Module.finrank ℝ ↥(U ⊔ V) + Module.finrank ℝ ↥(U ⊓ V) =
      Module.finrank ℝ U + Module.finrank ℝ V :=
    Submodule.finrank_sup_add_finrank_inf_eq U V
  have hsum : Module.finrank ℝ U + Module.finrank ℝ V = n + Module.finrank ℝ V := by
    rw [hdimU]
  have hdim_inf_pos : Module.finrank ℝ ↥(U ⊓ V) > 0 := by
    by_contra! hzero
    have hzero_eq : Module.finrank ℝ ↥(U ⊓ V) = 0 := by omega
    have hsup_eq : Module.finrank ℝ ↥(U ⊔ V) = n + Module.finrank ℝ V := by
      omega
    have : Module.finrank ℝ ↥(U ⊔ V) > n + 1 := by
      rw [hsup_eq]
      omega
    have h_contra : Module.finrank ℝ ↥(U ⊔ V) ≤ n + 1 := hdim_sup
    omega
  have hgoal : Module.finrank ℝ (↥(U ⊓ V)) ≥ 1 := by omega
  simpa [U, V] using hgoal

-- =============================================================================
-- Helper lemmas for the piercing argument
-- =============================================================================

/-- If `F` is an exposed face of `P` defined by `hp`, then `hp.f` is constant
  on the affine span of `F`. -/
lemma affine_const_on_exposed_face_public {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
    (hp : SupportingHyperplane P) (hF_eq : F = ExposedFace hp) :
    ∀ x ∈ affineSpan ℝ F, hp.f x = hp.c := by
  let H : AffineSubspace ℝ (CoeffVec n) :=
    { carrier := {x | hp.f x = hp.c}
      smul_vsub_vadd_mem := by
        intro a b c d hb hc hd
        have hb' : hp.f b = hp.c := hb
        have hc' : hp.f c = hp.c := hc
        have hd' : hp.f d = hp.c := hd
        have : hp.f (a • (b - c) + d) = hp.c := by
          calc
            hp.f (a • (b - c) + d) = hp.f (a • (b - c)) + hp.f d := by rw [map_add]
            _ = a • hp.f (b - c) + hp.c := by rw [map_smul, hd']
            _ = a • (hp.f b - hp.f c) + hp.c := by rw [map_sub]
            _ = a • (hp.c - hp.c) + hp.c := by rw [hb', hc']
            _ = a • 0 + hp.c := by rw [sub_self]
            _ = 0 + hp.c := by rw [smul_zero]
            _ = hp.c := by rw [zero_add]
        simpa [Set.mem_setOf_eq, vsub_eq_sub, vadd_eq_add] using this
    }
  have hF_sub : (F : Set (CoeffVec n)) ⊆ (H : Set (CoeffVec n)) := by
    intro y hy; rw [hF_eq] at hy; exact hy.2
  have h_span_sub : affineSpan ℝ F ≤ H := affineSpan_le.mpr hF_sub
  intro x hx; simpa using h_span_sub hx

/-- For a direction `v` in the direction space of an exposed face `F`, the
  supporting functional `hp.f` vanishes on `v`. -/
lemma exposed_face_direction_kills_vector_public {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
    (hp : SupportingHyperplane P) (hF_eq : F = ExposedFace hp) (δ : CoeffVec n) (v : CoeffVec n)
    (hδ_in_F : δ ∈ F) (hv_in_dir : v ∈ (affineSpan ℝ F).direction) : hp.f v = 0 := by
  have h_aff_const : ∀ x ∈ affineSpan ℝ F, hp.f x = hp.c :=
    affine_const_on_exposed_face_public hp hF_eq
  have hδ_f : hp.f δ = hp.c := by
    rw [hF_eq] at hδ_in_F
    exact hδ_in_F.2
  have h_δ_plus_v : δ + v ∈ affineSpan ℝ F := by
    have h_vadd : v +ᵥ δ ∈ affineSpan ℝ F :=
      AffineSubspace.vadd_mem_of_mem_direction hv_in_dir (subset_affineSpan ℝ F hδ_in_F)
    simpa [vadd_eq_add, add_comm] using h_vadd
  have hsum : hp.f (δ + v) = hp.f δ + hp.f v := by simp
  rw [h_aff_const (δ + v) h_δ_plus_v, h_aff_const δ (subset_affineSpan ℝ F hδ_in_F)] at hsum
  linarith

/-- Construct an exposed face from the intersection of two supporting hyperplanes.
  Given a supporting hyperplane `hpF`, a functional `g_lin` that is ≤ at `δ_bound`,
  a direction `v` killed by `hpF.f` and where `g_lin` is strictly positive, the set
  `{x | x ∈ P.Ω ∧ (hpF.f + g_lin) x = hpF.c + g_lin δ_bound}` is an exposed face of `P`. -/
lemma sum_supporting_hyperplane_exposed_face_public {n : ℕ} {P : Polytope n}
    (hpF : SupportingHyperplane P) (g_lin : CoeffVec n →ₗ[ℝ] ℝ) (v δ_bound : CoeffVec n)
    (hδ_bound_in_Ω : δ_bound ∈ P.Ω) (h_fδ_bound : hpF.f δ_bound = hpF.c)
    (hc_upper : ∀ x ∈ P.Ω, g_lin x ≤ g_lin δ_bound)
    (h_fv_zero : hpF.f v = 0) (h_gv_pos : g_lin v > 0) :
    IsExposedFace P {x | x ∈ P.Ω ∧ (hpF.f + g_lin) x = hpF.c + g_lin δ_bound} := by
  let g_new := hpF.f + g_lin
  have h_new_upper : ∀ x ∈ P.Ω, (hpF.f + g_lin) x ≤ hpF.c + g_lin δ_bound := by
    intro x hx
    have hfx : hpF.f x ≤ hpF.c := hpF.upper_bound x hx
    have hgx : g_lin x ≤ g_lin δ_bound := hc_upper x hx
    simpa [Pi.add_apply] using add_le_add hfx hgx
  have h_new_touches : ∃ x ∈ P.Ω, g_new x = hpF.c + g_lin δ_bound :=
    ⟨δ_bound, hδ_bound_in_Ω, by simp [g_new, h_fδ_bound]⟩
  have h_new_nonzero : g_new ≠ 0 := by
    intro hzero
    have : g_lin v = 0 := by
      calc
        g_lin v = g_new v := by simp [g_new, h_fv_zero]
        _ = (0 : CoeffVec n →ₗ[ℝ] ℝ) v := by rw [hzero]
        _ = 0 := by simp
    linarith
  exact ⟨{
    f := g_new
    c := hpF.c + g_lin δ_bound
    nonzero := h_new_nonzero
    upper_bound := h_new_upper
    touches := h_new_touches
  }, rfl⟩

/-- The set `P_sr ∩ aff(F)` intersects the relative boundary of `F`.
  Because `dim(P_sr ∩ aff(F)) ≥ 1`, there exists a direction `v` in the intersection.
  The ray `δ_F + t·v` must leave `P.Ω` (by `ray_escapes_polytope`), and the first exit
  point `δ_bound` lies on an exposed proper subface `G` of `F` with `dim(G) < dim(F)`,
  `dim(G) ≥ 1`, and `(r : ℂ) ∈ RootSpaceSet G`.  This is the book's "piercing" argument. -/
lemma exists_facet_pierced_by_Psr_public {n : ℕ} (P : Polytope n) (F : Set (CoeffVec n))
    (hF_exp : IsExposedFace P F) (r : ℝ) (h_root : (r : ℂ) ∈ RootSpaceSet F)
    (h_dim_ge_2 : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 2) :
    ∃ (G : Set (CoeffVec n)), IsExposedFace P G ∧ (r : ℂ) ∈ RootSpaceSet G ∧
      Module.finrank ℝ (affineSpan ℝ G).direction <
        Module.finrank ℝ (affineSpan ℝ F).direction ∧
      Module.finrank ℝ (affineSpan ℝ G).direction ≥ 1 := by
  obtain ⟨δ_F, hδ_F_in_F, hδ_F_root⟩ := h_root
  have hδ_F_Psr : δ_F ∈ (P_sr n r : Set (CoeffVec n)) :=
    mem_P_sr_of_isRoot_public r δ_F hδ_F_root
  let A_dir : Submodule ℝ (CoeffVec n) := P_sr n r ⊓ (affineSpan ℝ F).direction
  have hA_dim_ge_1 : Module.finrank ℝ A_dir ≥ 1 :=
    dim_inter_Psr_aff_ge_one_public F ⟨δ_F, hδ_F_in_F⟩ h_dim_ge_2 r
  have hA_has_nonzero_element : ∃ (v : CoeffVec n), v ∈ A_dir ∧ v ≠ 0 := by
    by_contra! hallzero
    have hA_eq_bot : A_dir = ⊥ := by
      ext v
      constructor
      · intro hv; exact hallzero v hv
      · intro hv; simp at hv; subst hv; exact A_dir.zero_mem
    have : Module.finrank ℝ A_dir = 0 := by
      rw [hA_eq_bot]; simp
    omega
  rcases hA_has_nonzero_element with ⟨v, hv_mem, hv_nonzero⟩
  have hv_in_Psr : v ∈ P_sr n r := hv_mem.1
  have hv_in_aff_dir : v ∈ (affineSpan ℝ F).direction := hv_mem.2
  have hδ_F_in_Ω : δ_F ∈ P.Ω := isExposedFace_subset_Ω_public hF_exp hδ_F_in_F

  have h_escapes : ∃ (t : ℝ), 0 < t ∧ δ_F + t • v ∉ P.Ω :=
    ray_escapes_polytope P δ_F v hδ_F_in_Ω hv_nonzero
  rcases h_escapes with ⟨t_exit, ht_exit_pos, ht_exit⟩

  have h_closed_PΩ : IsClosed P.Ω := P.isCompact.isClosed
  have h_cont : Continuous (fun (t : ℝ) => δ_F + t • v) := by continuity
  let S : Set ℝ := {t | δ_F + t • v ∈ P.Ω} ∩ Set.Icc 0 t_exit
  have hS_nonempty : S.Nonempty := by
    refine ⟨0, ⟨?_, ⟨by norm_num, ht_exit_pos.le⟩⟩⟩
    simpa using hδ_F_in_Ω
  have hS_isClosed : IsClosed S := by
    have h_closed_pre : IsClosed {t | δ_F + t • v ∈ P.Ω} :=
      h_closed_PΩ.preimage h_cont
    have h_closed_Icc : IsClosed (Set.Icc 0 t_exit) := isClosed_Icc
    exact h_closed_pre.inter h_closed_Icc
  have hS_isCompact : IsCompact S :=
    IsCompact.of_isClosed_subset isCompact_Icc hS_isClosed (by
      rintro x ⟨hx_pre, hx_Icc⟩; exact hx_Icc)
  rcases hS_isCompact.exists_isMaxOn hS_nonempty continuous_id.continuousOn with
    ⟨t_bound, ht_bound, ht_max⟩
  have hδ_bound_in_Ω : δ_F + t_bound • v ∈ P.Ω := ht_bound.1
  have ht_bound_0 : 0 ≤ t_bound := ht_bound.2.1
  have ht_bound_le_exit : t_bound ≤ t_exit := ht_bound.2.2
  let δ_bound := δ_F + t_bound • v
  have ht_bound_lt_exit : t_bound < t_exit := by
    by_contra! hge
    have : t_bound = t_exit := le_antisymm ht_bound_le_exit hge
    subst this; exact ht_exit hδ_bound_in_Ω

  -- Show δ_bound is NOT in the interior (hence on the boundary).
  have hδ_bound_not_int : δ_bound ∉ interior P.Ω := by
    intro h_int
    rcases Metric.isOpen_iff.mp isOpen_interior δ_bound h_int with ⟨ε, hε_pos, h_ball_int⟩
    have h_tendsto : Filter.Tendsto (fun (t : ℝ) => δ_F + t • v) (𝓝 t_bound) (𝓝 δ_bound) :=
      h_cont.continuousAt.tendsto
    have h_mem_nhds : Metric.ball δ_bound ε ∈ 𝓝 δ_bound := Metric.ball_mem_nhds δ_bound hε_pos
    have h_preimage_nhds : (fun (t : ℝ) => δ_F + t • v) ⁻¹' (Metric.ball δ_bound ε) ∈ 𝓝 t_bound :=
      h_tendsto h_mem_nhds
    rcases Metric.mem_nhds_iff.mp h_preimage_nhds with ⟨δ, hδ_pos, h_ball_nhd⟩
    let δ' := min δ (t_exit - t_bound)
    have hδ'_pos : 0 < δ' := lt_min_iff.mpr ⟨hδ_pos, sub_pos.mpr ht_bound_lt_exit⟩
    let t' := t_bound + δ' / 2
    have hδ'_le_δ : δ' ≤ δ := min_le_left _ _
    have hδ'_le_exit_sub : δ' ≤ t_exit - t_bound := min_le_right _ _
    have h_t'_ball_t : t' ∈ Metric.ball t_bound δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      have h_diff : t' - t_bound = δ' / 2 := by ring
      have h_abs : |t' - t_bound| = δ' / 2 := by
        rw [h_diff, abs_of_pos (by nlinarith)]
      rw [h_abs]
      nlinarith
    have h_t'_pre : t' ∈ (fun (t : ℝ) => δ_F + t • v) ⁻¹' (Metric.ball δ_bound ε) :=
      h_ball_nhd h_t'_ball_t
    have h_t'_img_ball : δ_F + t' • v ∈ Metric.ball δ_bound ε := h_t'_pre
    have h_t'_in_int : δ_F + t' • v ∈ interior P.Ω := h_ball_int h_t'_img_ball
    have h_t'_in_Ω : δ_F + t' • v ∈ P.Ω := interior_subset h_t'_in_int
    have ht'_Icc : t' ∈ Set.Icc 0 t_exit := by
      have h_nonneg : 0 ≤ t' := by
        dsimp [t']; nlinarith [ht_bound_0, hδ'_pos]
      have h_le_exit : t' ≤ t_exit := by
        calc
          t' = t_bound + δ' / 2 := rfl
          _ ≤ t_bound + (t_exit - t_bound) / 2 := by nlinarith
          _ = (t_bound + t_exit) / 2 := by ring
          _ ≤ t_exit := by nlinarith
      exact ⟨h_nonneg, h_le_exit⟩
    have h_t'_in_S : t' ∈ S := ⟨h_t'_in_Ω, ht'_Icc⟩
    have h_t'_le_t_bound : t_bound ≥ t' := ht_max h_t'_in_S
    have h_contra : δ' ≤ 0 := by
      dsimp [t'] at h_t'_le_t_bound
      nlinarith
    nlinarith

  -- δ_bound ∈ P_sr (by linearity of evalLinear)
  have hδ_bound_Psr : δ_bound ∈ (P_sr n r : Set (CoeffVec n)) := by
    dsimp [δ_bound]
    have h_smul : t_bound • v ∈ P_sr n r := Submodule.smul_mem (P_sr n r) t_bound hv_in_Psr
    exact Submodule.add_mem (P_sr n r) hδ_F_Psr h_smul

  -- Separate δ_bound from the interior of P.Ω using Hahn–Banach.
  have h_int_nonempty : (interior P.Ω).Nonempty := P.interior_nonempty
  have h_int_convex : Convex ℝ (interior P.Ω) := (convex_convexHull ℝ _).interior
  obtain ⟨f, hf_strict⟩ :=
    geometric_hahn_banach_open_point h_int_convex isOpen_interior hδ_bound_not_int
  let g : CoeffVec n →ₗ[ℝ] ℝ := f.toLinearMap
  have hg_strict : ∀ x ∈ interior P.Ω, g x < g δ_bound := hf_strict
  have hg_support : ∀ x ∈ P.Ω, g x ≤ g δ_bound := by
    intro x hx
    have h_closed_half : IsClosed {y | g y ≤ g δ_bound} :=
      isClosed_Iic.preimage (LinearMap.continuous_of_finiteDimensional g)
    have h_convex_Ω : Convex ℝ P.Ω := convex_convexHull ℝ _
    have h_subset : P.Ω ⊆ {y | g y ≤ g δ_bound} := by
      calc
        P.Ω = closure P.Ω := (P.isCompact.isClosed.closure_eq).symm
        _ = closure (interior P.Ω) :=
          (h_convex_Ω.closure_interior_eq_closure_of_nonempty_interior h_int_nonempty).symm
        _ ⊆ closure {y | g y ≤ g δ_bound} :=
          closure_mono fun y hy => le_of_lt (hg_strict y hy)
        _ = {y | g y ≤ g δ_bound} := h_closed_half.closure_eq
    exact h_subset hx

  -- Show g v ≥ 0  (using convexity of P.Ω)
  have h_interval_in_Ω : ∀ t, t ∈ Set.Icc (0 : ℝ) t_bound → δ_F + t • v ∈ P.Ω := by
    intro t ⟨ht0, htbound⟩
    have h_conv_Ω : Convex ℝ P.Ω := convex_convexHull ℝ _
    let h_linear : ℝ →ₗ[ℝ] CoeffVec n :=
      { toFun := fun t => t • v
        map_add' := fun a b => by simp [add_smul]
        map_smul' := fun r x => by simp [smul_smul] }
    let f : ℝ →ᵃ[ℝ] CoeffVec n :=
      { toFun := fun t => δ_F + t • v
        linear := h_linear
        map_vadd' := by
          intro a b; simp [h_linear, add_smul, vadd_eq_add, add_comm, add_assoc] }
    have h_conv_pre : Convex ℝ {t | δ_F + t • v ∈ P.Ω} :=
      h_conv_Ω.affine_preimage f
    have h0 : (0 : ℝ) ∈ {t | δ_F + t • v ∈ P.Ω} := by simpa using hδ_F_in_Ω
    have ht_bound_mem : t_bound ∈ {t | δ_F + t • v ∈ P.Ω} := hδ_bound_in_Ω
    have h_ord_conn : OrdConnected {t | δ_F + t • v ∈ P.Ω} :=
      (convex_iff_ordConnected.mp h_conv_pre)
    have h_sub : Set.Icc (0 : ℝ) t_bound ⊆ {t | δ_F + t • v ∈ P.Ω} :=
      h_ord_conn.out h0 ht_bound_mem
    exact h_sub (Set.mem_Icc.mpr ⟨ht0, htbound⟩)

  have hg_v_nonneg : g v ≥ 0 := by
    -- Not strictly needed: handled in Case A (g v > 0) or Case B (g v ≤ 0)
    sorry

  -- Decompose hF_exp and obtain hp.
  obtain ⟨hp, hF_eq⟩ := hF_exp
  have hp_f_v_zero : hp.f v = 0 :=
    exposed_face_direction_kills_vector_public hp hF_eq δ_F v hδ_F_in_F hv_in_aff_dir

  -- Case A: g v > 0  (generic case).  Construct G using sum_supporting_hyperplane.
  by_cases hg_v_pos : g v > 0
  · have hp_f_δ_bound : hp.f δ_bound = hp.c := by
      have hδ_bound_in_aff_F : δ_bound ∈ affineSpan ℝ F := by
        have h_δ_F_in_aff : δ_F ∈ affineSpan ℝ F := subset_affineSpan ℝ F hδ_F_in_F
        have h_vadd : (t_bound • v) +ᵥ δ_F ∈ affineSpan ℝ F :=
          AffineSubspace.vadd_mem_of_mem_direction
            (Submodule.smul_mem (affineSpan ℝ F).direction t_bound hv_in_aff_dir) h_δ_F_in_aff
        simpa [δ_bound, vadd_eq_add, add_comm] using h_vadd
      exact affine_const_on_exposed_face_public hp hF_eq δ_bound hδ_bound_in_aff_F

    let G : Set (CoeffVec n) := {x | x ∈ P.Ω ∧ (hp.f + g) x = hp.c + g δ_bound}
    have hG_exposed : IsExposedFace P G :=
      sum_supporting_hyperplane_exposed_face_public hp g v δ_bound hδ_bound_in_Ω hp_f_δ_bound
        hg_support hp_f_v_zero hg_v_pos
    have hδ_bound_in_G : δ_bound ∈ G := by
      refine ⟨hδ_bound_in_Ω, ?_⟩
      simp [hp_f_δ_bound]
    have h_root_G : (r : ℂ) ∈ RootSpaceSet G :=
      rootspace_mem_of_eval_zero_public r δ_bound hδ_bound_Psr G hδ_bound_in_G

    -- Prove dim(G) < dim(F) and dim(G) ≥ 1
    have hG_sub_F : G ⊆ F := by
      intro x hx
      rcases hx with ⟨hx_Ω, hx_sum⟩
      have h_fx_le : hp.f x ≤ hp.c := hp.upper_bound x hx_Ω
      have h_gx_le : g x ≤ g δ_bound := hg_support x hx_Ω
      have h_fx_eq : hp.f x = hp.c := by
        simp [LinearMap.add_apply] at hx_sum
        nlinarith
      rw [hF_eq]
      exact ⟨hx_Ω, h_fx_eq⟩

    have hg_const_on_G : ∀ x ∈ G, g x = g δ_bound := by
      intro x hx
      have hx_F : x ∈ F := hG_sub_F hx
      have hx_sum : (hp.f + g) x = hp.c + g δ_bound := hx.2
      have hx_f : hp.f x = hp.c := by
        rw [hF_eq] at hx_F
        exact hx_F.2
      simp [LinearMap.add_apply] at hx_sum
      nlinarith

    have hG_sub_g_const : G ⊆ {x | g x = g δ_bound} := hg_const_on_G

    let V := (affineSpan ℝ F).direction
    have hgV_nonzero : g.domRestrict V ≠ 0 := by
      intro hzero
      have hv_in_V : v ∈ V := hv_in_aff_dir
      have hzero_on_v : g v = 0 := by
        have : g.domRestrict V ⟨v, hv_in_V⟩ = 0 := by
          simpa using congrArg (fun φ => φ ⟨v, hv_in_V⟩) hzero
        simpa using this
      linarith

    have h_dim_ker : Module.finrank ℝ (LinearMap.ker (g.domRestrict V)) = Module.finrank ℝ V - 1 :=
      finrank_ker_eq_finrank_sub_one_public (g.domRestrict V) hgV_nonzero

    have h_dir_le_V : (affineSpan ℝ G).direction ≤ V :=
      AffineSubspace.direction_le (affineSpan_mono (k := ℝ) hG_sub_F)

    have h_dir_le_ker_g : (affineSpan ℝ G).direction ≤ LinearMap.ker g := by
      intro w hw
      have h_spanG_nonempty : ((affineSpan ℝ G : Set (CoeffVec n)).Nonempty) :=
        ⟨δ_bound, subset_affineSpan ℝ G hδ_bound_in_G⟩
      rcases (AffineSubspace.mem_direction_iff_eq_vsub h_spanG_nonempty w).mp hw with ⟨x, hx, y, hy, hxy⟩
      let H : AffineSubspace ℝ (CoeffVec n) :=
        { carrier := {x | g x = g δ_bound}
          smul_vsub_vadd_mem := by
            intro c p₁ p₂ p₃ hp₁ hp₂ hp₃
            have h1 : g p₁ = g δ_bound := hp₁
            have h2 : g p₂ = g δ_bound := hp₂
            have h3 : g p₃ = g δ_bound := hp₃
            calc
              g (c • (p₁ -ᵥ p₂) +ᵥ p₃) = g (c • (p₁ - p₂) + p₃) := by simp
              _ = g (c • (p₁ - p₂)) + g p₃ := by simp
              _ = c • g (p₁ - p₂) + g p₃ := by simp
              _ = c • (g p₁ - g p₂) + g p₃ := by simp
              _ = c • (g δ_bound - g δ_bound) + g δ_bound := by rw [h1, h2, h3]
              _ = c • 0 + g δ_bound := by ring
              _ = g δ_bound := by simp }
      have hG_sub_H : (G : Set (CoeffVec n)) ⊆ (H : Set (CoeffVec n)) := hg_const_on_G
      have h_spanG_sub_H : (affineSpan ℝ G : Set (CoeffVec n)) ⊆ (H : Set (CoeffVec n)) :=
        SetLike.coe_subset_coe.mpr (affineSpan_le.mpr hG_sub_H)
      have hx_g : g x = g δ_bound := h_spanG_sub_H hx
      have hy_g : g y = g δ_bound := h_spanG_sub_H hy
      have : g w = 0 := by
        calc
          g w = g (x - y) := by rw [hxy, vsub_eq_sub]
          _ = g x - g y := by simp
          _ = g δ_bound - g δ_bound := by rw [hx_g, hy_g]
          _ = 0 := by ring
      exact this

    have h_dir_in_ker_gV_map : (affineSpan ℝ G).direction ≤
      Submodule.map (Submodule.subtype V) (LinearMap.ker (g.domRestrict V)) := by
      intro w hw
      have hwV : w ∈ V := h_dir_le_V hw
      have hw_ker_g : g w = 0 := h_dir_le_ker_g hw
      have h_ker_mem : g.domRestrict V ⟨w, hwV⟩ = 0 := by simp [hw_ker_g]
      refine Submodule.mem_map.mpr ⟨⟨w, hwV⟩, h_ker_mem, rfl⟩

    have h_dim_lt : Module.finrank ℝ (affineSpan ℝ G).direction < Module.finrank ℝ V := by
      calc
        Module.finrank ℝ (affineSpan ℝ G).direction ≤
          Module.finrank ℝ (Submodule.map (Submodule.subtype V) (LinearMap.ker (g.domRestrict V))) :=
          Submodule.finrank_mono h_dir_in_ker_gV_map
        _ ≤ Module.finrank ℝ (LinearMap.ker (g.domRestrict V)) :=
          Submodule.finrank_map_le (Submodule.subtype V) (LinearMap.ker (g.domRestrict V))
        _ = Module.finrank ℝ V - 1 := h_dim_ker
        _ < Module.finrank ℝ V := by
          have : Module.finrank ℝ V ≥ 2 := h_dim_ge_2
          omega

    have h_dim_ge_1 : Module.finrank ℝ (affineSpan ℝ G).direction ≥ 1 := by
      sorry

    exact ⟨G, hG_exposed, h_root_G, h_dim_lt, h_dim_ge_1⟩

  · -- Case B: g v ≤ 0
    sorry

/-- Lemma 6.1 (real root) following the book's descent.
  Uses `exists_facet_pierced_by_Psr_public` repeatedly to reduce dimension by at least 1
  each step, starting from `dim(P.Ω) = m ≥ 2` and stopping at dimension 1 (an edge). -/
lemma lemma61_real_descent_public {n : ℕ} (hn : n ≥ 1) (P : Polytope n) (s_r : ℝ)
    (hs_r : (s_r : ℂ) ∈ RootSpace P) :
    ∃ E, IsExposedEdge P E ∧ (s_r : ℂ) ∈ RootSpaceSet E := by
  sorry

end CoeffBox
