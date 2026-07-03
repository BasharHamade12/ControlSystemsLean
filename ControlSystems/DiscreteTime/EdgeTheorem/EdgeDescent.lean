module

public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeTheoremDefs
public import ControlSystems.DiscreteTime.EdgeTheorem.BasicLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.PreliminaryLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.ExposedFaceLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.SubfaceConstruction
public import Mathlib.Algebra.Module.SpanRank


@[expose] public section

open Polynomial Affine FiniteDimensional LinearMap Set

namespace CoeffBox

/-- An exposed face of a polytope whose affine span has dimension 1 is an exposed edge. -/
lemma isExposedEdge_of_dim_1 {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
    (hF_exposed : IsExposedFace P F)
    (h_dim : Module.finrank ℝ (affineSpan ℝ F).direction = 1) : IsExposedEdge P F := by
  obtain ⟨hp, hF_eq⟩ := hF_exposed
  exact ⟨hp, hF_eq, hF_eq ▸ h_dim⟩

/-- If the direction of the affine span of `F` has dimension at least 1, then it is nontrivial. -/
private lemma direction_nontrivial_from_dim_ge_1 {n : ℕ} {F : Set (CoeffVec n)}
    (h_finrank : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 1) :
    Nontrivial ↥(affineSpan ℝ F).direction := by
  have h_pos : 0 < Module.finrank ℝ (affineSpan ℝ F).direction :=
    Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h_finrank
  exact Module.nontrivial_of_finrank_pos h_pos

/--
Find a point δ_bound on the *relative* boundary of F that also lies in P_sr n r.
Unlike the earlier version, this guarantees δ_bound is NOT in intrinsicInterior ℝ F
(i.e., it is on the genuine relative boundary of F, not just the ambient frontier).
-/
private lemma exists_boundary_point_in_face_rootspace {n : ℕ} (P : Polytope n) (r : ℝ)
    (δ_F : CoeffVec n) (F : Set (CoeffVec n)) (hF_exposed : IsExposedFace P F)
    (hδ_F_in_F : δ_F ∈ F) (hδ_F_root : δ_F ∈ (P_sr n r : Set (CoeffVec n)))
    (h_inter_dim : Module.finrank ℝ ↥(affineSpan ℝ
      (((P_sr n r : Set (CoeffVec n)) ∩ (affineSpan ℝ F : Set (CoeffVec n))))).direction ≥ 1) :
    ∃ δ_bound, δ_bound ∈ F ∩ (P_sr n r : Set (CoeffVec n))
    ∧ δ_bound ∈ frontier F ∧ δ_bound ∉ intrinsicInterior ℝ F := by
  let affF := affineSpan ℝ F
  let hF_compact := isExposedFace_isCompact P hF_exposed
  let hF_subset := isExposedFace_subset_Ω hF_exposed
  let hF_convex : Convex ℝ F := isExposedFace_convex P hF_exposed
  let hδ_F_in_Psr : δ_F ∈ (P_sr n r : Set (CoeffVec n)) := hδ_F_root
  let hδ_F_affF := subset_affineSpan ℝ F hδ_F_in_F
  have hδ_F_inter : δ_F ∈ F ∩ (P_sr n r : Set (CoeffVec n)) := Set.mem_inter hδ_F_in_F hδ_F_in_Psr
  let L := affineSpan ℝ (↑(P_sr n r) ∩ (affF : Set (CoeffVec n)))
  have h_dir_nontrivial : Nontrivial L.direction :=
    direction_nontrivial_from_dim_ge_1 h_inter_dim
  obtain ⟨v_sub, hv_sub_ne⟩ := exists_ne (0 : ↥L.direction)
  let v : CoeffVec n := v_sub.val
  have hv_ne : v ≠ 0 := by
    intro h; apply hv_sub_ne; exact Subtype.ext h
  have hv_dir : v ∈ L.direction := v_sub.property
  have h_escapes : ∃ (t : ℝ) (ht_pos : 0 < t), δ_F + t • v ∉ F := by
    rcases Metric.isBounded_iff.mp hF_compact.isBounded with ⟨C, hC⟩
    have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
    let t := (|C| + 1) / ‖v‖
    have ht_pos : 0 < t := div_pos (by positivity) (by positivity)
    refine ⟨t, ht_pos, ?_⟩
    intro h_contra
    have ht_nonneg : 0 ≤ t := by positivity
    have h_dist : dist (δ_F + t • v) δ_F = t * ‖v‖ := by
      rw [dist_eq_norm]; have h_sub : δ_F + t • v - δ_F = t • v := by abel
      rw [h_sub, norm_smul, Real.norm_eq_abs t, abs_of_nonneg ht_nonneg]
    have h_t_mul : t * ‖v‖ = |C| + 1 := by
      dsimp [t]; field_simp
    have h_le : dist (δ_F + t • v) δ_F ≤ C := by
      apply hC
      · exact h_contra
      · exact hδ_F_in_F
    have h_C_abs : C ≤ |C| := le_abs_self C
    nlinarith
  obtain ⟨t_out, ht_out_pos, ht_out⟩ := h_escapes
  have hL_le_affF : L ≤ affF := affineSpan_le.mpr Set.inter_subset_right
  have hv_affF_dir : v ∈ affF.direction := AffineSubspace.direction_le hL_le_affF hv_dir
  have ht_out_P : δ_F + t_out • v ∉ P.Ω :=
    escapes_P_via_exposed_face hF_exposed δ_F v t_out hδ_F_in_F hv_affF_dir ht_out
  by_cases hδ_front_Ω : δ_F ∉ frontier P.Ω
  · -- δ_F is NOT on the frontier of P.Ω → start the segment directly from δ_F
    obtain ⟨δ_bound, h_seg, h_front_P⟩ :=
      segment_boundary_intersection P δ_F (hF_subset hδ_F_in_F) hδ_front_Ω v hv_ne t_out ht_out_P
    have h_δ_bound_in_F : δ_bound ∈ F := by
      obtain ⟨hp, hF_expr⟩ := hF_exposed; rw [hF_expr]
      refine ⟨?_, ?_⟩
      · have h_closed : IsClosed P.Ω := P.isCompact.isClosed
        have h_front_sub : frontier P.Ω ⊆ P.Ω :=
          calc
            frontier P.Ω ⊆ closure P.Ω := frontier_subset_closure
            _ = P.Ω := h_closed.closure_eq
        exact h_front_sub h_front_P
      · obtain ⟨c, hc_Icc, rfl⟩ := segment_eq_image ℝ δ_F (δ_F + t_out • v) ▸ h_seg
        have hf_v : hp.f v = 0 :=
          exposed_face_direction_kills_vector hp hF_expr δ_F v hδ_F_in_F hv_affF_dir
        have hδ_F_val : hp.f δ_F = hp.c := (hF_expr ▸ hδ_F_in_F).2
        have h_eq : (1 - c) • δ_F + c • (δ_F + t_out • v) = δ_F + (c * t_out) • v := by
          calc
            (1 - c) • δ_F + c • (δ_F + t_out • v) = (1 - c) • δ_F +
              (c • δ_F + c • (t_out • v)) := by rw [smul_add]
            _ = ((1 - c) • δ_F + c • δ_F) + c • (t_out • v) := by abel
            _ = ((1 - c + c) • δ_F) + (c * t_out) • v := by rw [add_smul, smul_smul]
            _ = 1 • δ_F + (c * t_out) • v := by
              have h : (1 : ℝ) - c + c = 1 := by ring
              simp [h]
            _ = δ_F + (c * t_out) • v := by simp
        calc
          hp.f ((1 - c) • δ_F + c • (δ_F + t_out • v)) = hp.f (δ_F + (c * t_out) • v) := by
            rw [h_eq]
          _ = hp.c := by simp [hδ_F_val, hf_v, map_add, map_smul]
    have h_δ_bound_not_relint : δ_bound ∉ intrinsicInterior ℝ F := by
      have h_front_P_Ω : δ_bound ∈ frontier P.Ω := h_front_P
      have h_not_int_Ω : δ_bound ∉ interior P.Ω :=
        frontier_point_not_interior P δ_bound h_front_P_Ω
      -- In case 1, δ_F ∉ frontier P.Ω and δ_F ∈ P.Ω, so δ_F ∈ interior P.Ω.
      have hδ_F_int_Ω : δ_F ∈ interior P.Ω := by
        have hδ_F_Ω : δ_F ∈ P.Ω := hF_subset hδ_F_in_F
        have hfront_diff : δ_F ∉ P.Ω \ interior P.Ω := by
          rwa [← frontier_eq_for_closed P.Ω P.isCompact.isClosed]
        by_contra h_not_int
        exact hfront_diff ⟨hδ_F_Ω, h_not_int⟩
      -- We derive a contradiction: F is an exposed face of P.Ω, so F ⊆ H where
      -- H = {x | hp.f x = hp.c} and hp.f ≠ 0. δ_F ∈ F ∩ interior P.Ω, so
      -- there's a ball B(δ_F, ε) ⊆ P.Ω. On this ball, hp.f ≤ hp.c. At δ_F,
      -- hp.f = hp.c. For any unit u, both δ_F ± (ε/2)•u ∈ B, so hp.f (δ_F + (ε/2)•u)
      -- = hp.c + (ε/2)*hp.f u ≤ hp.c, giving hp.f u ≤ 0. Similarly hp.f u ≥ 0.
      -- Hence hp.f u = 0 for all unit u, so hp.f = 0, contradicting hp.f ≠ 0.
      obtain ⟨hp, hF_expr⟩ := hF_exposed
      have hF_sub : F ⊆ {x | hp.f x = hp.c} := fun x hx => (hF_expr ▸ hx).2
      have hδ_F_val : hp.f δ_F = hp.c := hF_sub hδ_F_in_F
      have hF_le : ∀ x ∈ P.Ω, hp.f x ≤ hp.c := hp.upper_bound
      have h_ball : ∃ ε > 0, Metric.ball δ_F ε ⊆ interior P.Ω :=
        Metric.isOpen_iff.mp isOpen_interior δ_F hδ_F_int_Ω
      obtain ⟨ε, hε, hB_sub⟩ := h_ball
      have h_unit_zero : ∀ u : CoeffVec n, ‖u‖ = 1 → hp.f u = 0 := by
        intro u hu
        -- Both δ_F + (ε/2) • u and δ_F - (ε/2) • u are in B(δ_F, ε) ⊆ P.Ω
        have h_pos_pt : dist (δ_F + (ε/2) • u) δ_F < ε := by
          rw [dist_eq_norm]
          have h1 : (δ_F + (ε/2) • u) - δ_F = (ε/2) • u := by abel
          rw [h1, norm_smul]
          rw [Real.norm_of_nonneg (by positivity : 0 ≤ ε / 2), hu]
          simp; linarith
        have h_neg_pt : dist (δ_F + (-(ε/2)) • u) δ_F < ε := by
          rw [dist_eq_norm]
          have h1 : (δ_F + (-(ε/2)) • u) - δ_F = (-(ε/2)) • u := by abel
          rw [h1, norm_smul, norm_neg]
          rw [Real.norm_of_nonneg (by positivity : 0 ≤ ε / 2), hu]
          simp; linarith
        have h_pos : hp.f (δ_F + (ε/2) • u) ≤ hp.c :=
          hF_le _ (hB_sub.trans interior_subset h_pos_pt)
        have h_neg : hp.f (δ_F + (-(ε/2)) • u) ≤ hp.c :=
          hF_le _ (hB_sub.trans interior_subset h_neg_pt)
        have h_val_pos : hp.f (δ_F + (ε/2) • u) = hp.c + (ε/2) * hp.f u := by
          rw [map_add, map_smul, hδ_F_val, smul_eq_mul]
        have h_val_neg : hp.f (δ_F + (-(ε/2)) • u) = hp.c - (ε/2) * hp.f u := by
          rw [map_add, map_smul, hδ_F_val, smul_eq_mul, neg_mul, sub_eq_add_neg]
        have h_pos_le : hp.c + (ε/2) * hp.f u ≤ hp.c := by rw [← h_val_pos]; exact h_pos
        have h_neg_le : hp.c - (ε/2) * hp.f u ≤ hp.c := by rw [← h_val_neg]; exact h_neg
        -- From h_pos_le: (ε/2) * hp.f u ≤ 0, so hp.f u ≤ 0 (since ε/2 > 0)
        -- From h_neg_le: -(ε/2) * hp.f u ≤ 0, so hp.f u ≥ 0
        -- Hence hp.f u = 0
        have h1 : hp.f u ≤ 0 := by nlinarith [h_pos_le, h_neg_le, hε]
        have h2 : hp.f u ≥ 0 := by nlinarith [h_pos_le, h_neg_le, hε]
        linarith
      have hp_f_zero : hp.f = 0 := by
        apply LinearMap.ext
        intro w
        by_cases hw : w = 0
        · subst hw
          simp [LinearMap.map_zero]
        · have hnorm : ‖w‖ ≠ 0 := fun h => hw (norm_eq_zero.mp h)
          have hmul_cancel : (‖w‖ : ℝ) * (‖w‖ : ℝ)⁻¹ = 1 := by field_simp [hnorm]
          have h_unit : ‖(‖w‖⁻¹ : ℝ) • w‖ = 1 := by
            rw [norm_smul, norm_inv]
            field_simp [hnorm]
            simp
          -- hp.f w = ‖w‖ • hp.f (‖w‖⁻¹ • w) by linearity
          have h_w : hp.f w = ‖w‖ • hp.f (‖w‖⁻¹ • w) := by
            have h_w_eq : w = ‖w‖ • (‖w‖⁻¹ • w) := by
              calc
                w = 1 • w := by simp
                _ = ((‖w‖ : ℝ) * (‖w‖ : ℝ)⁻¹) • w := by
                    rw [hmul_cancel]
                    simp
                _ = ‖w‖ • (‖w‖⁻¹ • w) := by rw [smul_smul]
            nth_rewrite 1 [h_w_eq]
            rw [hp.f.map_smul]
          have h_u_zero : hp.f (‖w‖⁻¹ • w) = 0 := h_unit_zero _ h_unit
          rw [h_w, h_u_zero]
          simp
      exact absurd hp_f_zero hp.nonzero
    have hv_in_Psr : v ∈ (P_sr n r : Submodule ℝ (CoeffVec n)) := by
      have hL_dir_le_Psr_dir : L.direction ≤ (P_sr n r : Submodule ℝ (CoeffVec n)) := by
        have hL_as_sub : L ≤ (P_sr n r : Submodule ℝ (CoeffVec n)).toAffineSubspace :=
          affineSpan_le.mpr (by
            rintro x ⟨hx_Psr, _⟩
            simpa [Submodule.mem_toAffineSubspace] using hx_Psr)
        have hdir : L.direction ≤ ((P_sr n r : Submodule ℝ (CoeffVec n)).toAffineSubspace).direction :=
          AffineSubspace.direction_le hL_as_sub
        simpa using hdir
      exact hL_dir_le_Psr_dir hv_dir
    have hδ_bound_in_Psr : δ_bound ∈ (P_sr n r : Set (CoeffVec n)) := by
      obtain ⟨c, hc_Icc, hc_eq⟩ := segment_eq_image ℝ δ_F (δ_F + t_out • v) ▸ h_seg
      have h_eq : δ_bound = δ_F + (c * t_out) • v := by
        calc
          δ_bound = (1 - c) • δ_F + c • (δ_F + t_out • v) := by
            simpa using hc_eq.symm
          _ = δ_F + (c * t_out) • v := segment_point_rewrite δ_F v c t_out
      rw [h_eq]
      apply Submodule.add_mem (P_sr n r)
      · exact hδ_F_root
      · apply Submodule.smul_mem (P_sr n r) (c * t_out)
        exact hv_in_Psr
    have hδ_bound_frontier_F : δ_bound ∈ frontier F := by
      rw [frontier_eq_for_closed F hF_compact.isClosed]
      refine ⟨h_δ_bound_in_F, ?_⟩
      intro h_int
      apply h_δ_bound_not_relint
      exact (interior_subset_intrinsicInterior (𝕜 := ℝ) (s := F)) h_int
    refine ⟨δ_bound, ⟨h_δ_bound_in_F, hδ_bound_in_Psr⟩, hδ_bound_frontier_F, h_δ_bound_not_relint⟩
  · -- δ_F IS on the frontier of P.Ω → find boundary point along the ray
    have hδ_F_front_Ω : δ_F ∈ frontier P.Ω := by
      by_contra h; exact hδ_front_Ω h
    by_cases hδ_F_relint : δ_F ∈ intrinsicInterior ℝ F
    · -- δ_F is in the relative interior of F; find boundary point along direction v
      let S : Set ℝ := {t | 0 ≤ t ∧ δ_F + t • v ∈ F}
      have hS_nonempty : S.Nonempty := ⟨0, by simp [S, hδ_F_in_F]⟩
      have hS_closed : IsClosed S := by
        have h_cont : Continuous (fun (t : ℝ) => δ_F + t • v) := by
          continuity
        have h_preimage_closed : IsClosed {t | δ_F + t • v ∈ F} :=
          hF_compact.isClosed.preimage h_cont
        have h_nonneg_closed : IsClosed {t : ℝ | 0 ≤ t} := isClosed_Ici
        have hS_eq : S = {t | δ_F + t • v ∈ F} ∩ {t : ℝ | 0 ≤ t} := by
          ext t; constructor
          · rintro ⟨ht_nonneg, ht_mem⟩; exact ⟨ht_mem, ht_nonneg⟩
          · rintro ⟨ht_mem, ht_nonneg⟩; exact ⟨ht_nonneg, ht_mem⟩
        rw [hS_eq]
        exact h_preimage_closed.inter h_nonneg_closed
      have h_bdd_above : BddAbove S := by
        refine ⟨t_out, ?_⟩
        rintro t ⟨ht_nonneg, ht_mem⟩
        by_contra! h_gt
        have ha_nonneg : 0 ≤ t_out / t := div_nonneg (by linarith) (by linarith)
        have hdiv : t_out / t ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
        have hb_nonneg : 0 ≤ 1 - t_out / t := by linarith
        have hsum : (t_out / t : ℝ) + (1 - t_out / t) = 1 := by ring
        have h_conv : ((t_out / t : ℝ) • (δ_F + t • v) + (1 - t_out / t) • δ_F) = δ_F + t_out • v := by
          calc
            (t_out / t : ℝ) • (δ_F + t • v) + (1 - t_out / t) • δ_F
                = (t_out / t) • δ_F + (t_out / t) • (t • v) + (1 - t_out / t) • δ_F := by rw [smul_add]
            _ = ((t_out / t) • δ_F + (1 - t_out / t) • δ_F) + (t_out / t) • (t • v) := by abel
            _ = ((t_out / t + (1 - t_out / t)) • δ_F) + ((t_out / t) * t) • v := by
              simp [smul_smul]
            _ = (1 • δ_F) + (t_out • v) := by
              have h_t_ne_zero : t ≠ 0 := by linarith
              have h_sum : t_out / t + (1 - t_out / t) = 1 := by ring
              have h_mul : (t_out / t) * t = t_out := by field_simp [h_t_ne_zero]
              simp [h_sum, h_mul]
            _ = δ_F + t_out • v := by simp
        have hstar : StarConvex ℝ (δ_F + t • v) F := hF_convex ht_mem
        have h_mem_conv : (t_out / t : ℝ) • (δ_F + t • v) + (1 - t_out / t) • δ_F ∈ F :=
          hstar hδ_F_in_F ha_nonneg hb_nonneg hsum
        have h_mem : δ_F + t_out • v ∈ F := by
          rw [← h_conv]
          exact h_mem_conv
        exact ht_out h_mem
      let t1 := sSup S
      have h_max : t1 ∈ S := by
        simpa [t1] using hS_closed.csSup_mem hS_nonempty h_bdd_above
      rcases h_max with ⟨h_t1_nonneg, h_t1_mem⟩
      let δ_bound : CoeffVec n := δ_F + t1 • v
      have hv_in_Psr : v ∈ (P_sr n r : Submodule ℝ (CoeffVec n)) := by
        have hL_dir_le_Psr_dir : L.direction ≤ (P_sr n r : Submodule ℝ (CoeffVec n)) := by
          have hL_as_sub : L ≤ (P_sr n r : Submodule ℝ (CoeffVec n)).toAffineSubspace :=
            affineSpan_le.mpr (by
              rintro x ⟨hx_Psr, _⟩
              simpa [Submodule.mem_toAffineSubspace] using hx_Psr)
          have hdir : L.direction ≤ ((P_sr n r : Submodule ℝ (CoeffVec n)).toAffineSubspace).direction :=
            AffineSubspace.direction_le hL_as_sub
          simpa using hdir
        exact hL_dir_le_Psr_dir hv_dir
      have hδ_bound_in_Psr : δ_bound ∈ (P_sr n r : Set (CoeffVec n)) := by
        dsimp [δ_bound]
        apply Submodule.add_mem (P_sr n r)
        · exact hδ_F_root
        · apply Submodule.smul_mem (P_sr n r) t1 hv_in_Psr
      have h_not_relint : δ_bound ∉ intrinsicInterior ℝ F :=
        not_mem_intrinsicInterior_of_escapes_along_direction
          F hF_convex δ_F hδ_F_in_F v hv_ne hv_affF_dir
          S rfl hS_nonempty h_bdd_above
          t1 rfl h_t1_nonneg h_t1_mem
          t_out ht_out_pos ht_out

      have hδ_bound_frontier_F : δ_bound ∈ frontier F := by
        rw [frontier_eq_for_closed F hF_compact.isClosed]
        refine ⟨h_t1_mem, ?_⟩
        intro h_int
        apply h_not_relint
        exact (interior_subset_intrinsicInterior (𝕜 := ℝ) (s := F)) h_int

      refine ⟨δ_bound, ⟨h_t1_mem, hδ_bound_in_Psr⟩, hδ_bound_frontier_F, h_not_relint⟩
    · -- δ_F is not in the relative interior → already on the boundary
      use δ_F
      have hδ_F_frontier_F : δ_F ∈ frontier F := by
        rw [frontier_eq_for_closed F hF_compact.isClosed]
        refine ⟨hδ_F_in_F, ?_⟩
        intro h_int
        apply hδ_F_relint
        exact (interior_subset_intrinsicInterior (𝕜 := ℝ) (s := F)) h_int
      exact ⟨⟨hδ_F_in_F, hδ_F_root⟩, hδ_F_frontier_F, hδ_F_relint⟩

/-- Complex analogue of `exists_boundary_point_in_face_rootspace`:
  finds a point on the relative boundary of `F` that also lies in `P_sc n s`. -/
private lemma exists_boundary_point_in_face_rootspace_complex {n : ℕ} (P : Polytope n) (s : ℂ)
    (δ_F : CoeffVec n) (F : Set (CoeffVec n)) (hF_exposed : IsExposedFace P F)
    (hδ_F_in_F : δ_F ∈ F) (hδ_F_root : δ_F ∈ (P_sc n s : Set (CoeffVec n)))
    (h_inter_dim : Module.finrank ℝ ↥(affineSpan ℝ
      (((P_sc n s : Set (CoeffVec n)) ∩ (affineSpan ℝ F : Set (CoeffVec n))))).direction ≥ 1) :
    ∃ δ_bound, δ_bound ∈ F ∩ (P_sc n s : Set (CoeffVec n))
    ∧ δ_bound ∈ frontier F ∧ δ_bound ∉ intrinsicInterior ℝ F := by
  let affF := affineSpan ℝ F
  let hF_compact := isExposedFace_isCompact P hF_exposed
  let hF_subset := isExposedFace_subset_Ω hF_exposed
  let hF_convex : Convex ℝ F := isExposedFace_convex P hF_exposed
  let hδ_F_in_Psc : δ_F ∈ (P_sc n s : Set (CoeffVec n)) := hδ_F_root
  let hδ_F_affF := subset_affineSpan ℝ F hδ_F_in_F
  have hδ_F_inter : δ_F ∈ F ∩ (P_sc n s : Set (CoeffVec n)) := Set.mem_inter hδ_F_in_F hδ_F_in_Psc
  let L := affineSpan ℝ (↑(P_sc n s) ∩ (affF : Set (CoeffVec n)))
  have h_dir_nontrivial : Nontrivial L.direction :=
    direction_nontrivial_from_dim_ge_1 h_inter_dim
  obtain ⟨v_sub, hv_sub_ne⟩ := exists_ne (0 : ↥L.direction)
  let v : CoeffVec n := v_sub.val
  have hv_ne : v ≠ 0 := by
    intro h; apply hv_sub_ne; exact Subtype.ext h
  have hv_dir : v ∈ L.direction := v_sub.property
  have h_escapes : ∃ (t : ℝ) (ht_pos : 0 < t), δ_F + t • v ∉ F := by
    rcases Metric.isBounded_iff.mp hF_compact.isBounded with ⟨C, hC⟩
    have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
    let t := (|C| + 1) / ‖v‖
    have ht_pos : 0 < t := div_pos (by positivity) (by positivity)
    refine ⟨t, ht_pos, ?_⟩
    intro h_contra
    have ht_nonneg : 0 ≤ t := by positivity
    have h_dist : dist (δ_F + t • v) δ_F = t * ‖v‖ := by
      rw [dist_eq_norm]; have h_sub : δ_F + t • v - δ_F = t • v := by abel
      rw [h_sub, norm_smul, Real.norm_eq_abs t, abs_of_nonneg ht_nonneg]
    have h_t_mul : t * ‖v‖ = |C| + 1 := by
      dsimp [t]; field_simp
    have h_le : dist (δ_F + t • v) δ_F ≤ C := by
      apply hC
      · exact h_contra
      · exact hδ_F_in_F
    have h_C_abs : C ≤ |C| := le_abs_self C
    nlinarith
  obtain ⟨t_out, ht_out_pos, ht_out⟩ := h_escapes
  have hL_le_affF : L ≤ affF := affineSpan_le.mpr Set.inter_subset_right
  have hv_affF_dir : v ∈ affF.direction := AffineSubspace.direction_le hL_le_affF hv_dir
  have ht_out_P : δ_F + t_out • v ∉ P.Ω :=
    escapes_P_via_exposed_face hF_exposed δ_F v t_out hδ_F_in_F hv_affF_dir ht_out
  by_cases hδ_front_Ω : δ_F ∉ frontier P.Ω
  · -- δ_F is NOT on the frontier of P.Ω → start the segment directly from δ_F
    obtain ⟨δ_bound, h_seg, h_front_P⟩ :=
      segment_boundary_intersection P δ_F (hF_subset hδ_F_in_F) hδ_front_Ω v hv_ne t_out ht_out_P
    have h_δ_bound_in_F : δ_bound ∈ F := by
      obtain ⟨hp, hF_expr⟩ := hF_exposed; rw [hF_expr]
      refine ⟨?_, ?_⟩
      · have h_closed : IsClosed P.Ω := P.isCompact.isClosed
        have h_front_sub : frontier P.Ω ⊆ P.Ω :=
          calc
            frontier P.Ω ⊆ closure P.Ω := frontier_subset_closure
            _ = P.Ω := h_closed.closure_eq
        exact h_front_sub h_front_P
      · obtain ⟨c, hc_Icc, rfl⟩ := segment_eq_image ℝ δ_F (δ_F + t_out • v) ▸ h_seg
        have hf_v : hp.f v = 0 :=
          exposed_face_direction_kills_vector hp hF_expr δ_F v hδ_F_in_F hv_affF_dir
        have hδ_F_val : hp.f δ_F = hp.c := (hF_expr ▸ hδ_F_in_F).2
        have h_eq : (1 - c) • δ_F + c • (δ_F + t_out • v) = δ_F + (c * t_out) • v := by
          calc
            (1 - c) • δ_F + c • (δ_F + t_out • v) = (1 - c) • δ_F +
              (c • δ_F + c • (t_out • v)) := by rw [smul_add]
            _ = ((1 - c) • δ_F + c • δ_F) + c • (t_out • v) := by abel
            _ = ((1 - c + c) • δ_F) + (c * t_out) • v := by rw [add_smul, smul_smul]
            _ = 1 • δ_F + (c * t_out) • v := by
              have h : (1 : ℝ) - c + c = 1 := by ring
              simp [h]
            _ = δ_F + (c * t_out) • v := by simp
        calc
          hp.f ((1 - c) • δ_F + c • (δ_F + t_out • v)) = hp.f (δ_F + (c * t_out) • v) := by
            rw [h_eq]
          _ = hp.c := by simp [hδ_F_val, hf_v, map_add, map_smul]
    have h_δ_bound_not_relint : δ_bound ∉ intrinsicInterior ℝ F := by
      have h_front_P_Ω : δ_bound ∈ frontier P.Ω := h_front_P
      have h_not_int_Ω : δ_bound ∉ interior P.Ω :=
        frontier_point_not_interior P δ_bound h_front_P_Ω
      have hδ_F_int_Ω : δ_F ∈ interior P.Ω := by
        have hδ_F_Ω : δ_F ∈ P.Ω := hF_subset hδ_F_in_F
        have hfront_diff : δ_F ∉ P.Ω \ interior P.Ω := by
          rwa [← frontier_eq_for_closed P.Ω P.isCompact.isClosed]
        by_contra h_not_int
        exact hfront_diff ⟨hδ_F_Ω, h_not_int⟩
      obtain ⟨hp, hF_expr⟩ := hF_exposed
      have hF_sub : F ⊆ {x | hp.f x = hp.c} := fun x hx => (hF_expr ▸ hx).2
      have hδ_F_val : hp.f δ_F = hp.c := hF_sub hδ_F_in_F
      have hF_le : ∀ x ∈ P.Ω, hp.f x ≤ hp.c := hp.upper_bound
      have h_ball : ∃ ε > 0, Metric.ball δ_F ε ⊆ interior P.Ω :=
        Metric.isOpen_iff.mp isOpen_interior δ_F hδ_F_int_Ω
      obtain ⟨ε, hε, hB_sub⟩ := h_ball
      have h_unit_zero : ∀ u : CoeffVec n, ‖u‖ = 1 → hp.f u = 0 := by
        intro u hu
        have h_pos_pt : dist (δ_F + (ε/2) • u) δ_F < ε := by
          rw [dist_eq_norm]
          have h1 : (δ_F + (ε/2) • u) - δ_F = (ε/2) • u := by abel
          rw [h1, norm_smul]
          rw [Real.norm_of_nonneg (by positivity : 0 ≤ ε / 2), hu]
          simp; linarith
        have h_neg_pt : dist (δ_F + (-(ε/2)) • u) δ_F < ε := by
          rw [dist_eq_norm]
          have h1 : (δ_F + (-(ε/2)) • u) - δ_F = (-(ε/2)) • u := by abel
          rw [h1, norm_smul, norm_neg]
          rw [Real.norm_of_nonneg (by positivity : 0 ≤ ε / 2), hu]
          simp; linarith
        have h_pos : hp.f (δ_F + (ε/2) • u) ≤ hp.c :=
          hF_le _ (hB_sub.trans interior_subset h_pos_pt)
        have h_neg : hp.f (δ_F + (-(ε/2)) • u) ≤ hp.c :=
          hF_le _ (hB_sub.trans interior_subset h_neg_pt)
        have h_val_pos : hp.f (δ_F + (ε/2) • u) = hp.c + (ε/2) * hp.f u := by
          rw [map_add, map_smul, hδ_F_val, smul_eq_mul]
        have h_val_neg : hp.f (δ_F + (-(ε/2)) • u) = hp.c - (ε/2) * hp.f u := by
          rw [map_add, map_smul, hδ_F_val, smul_eq_mul, neg_mul, sub_eq_add_neg]
        have h_pos_le : hp.c + (ε/2) * hp.f u ≤ hp.c := by rw [← h_val_pos]; exact h_pos
        have h_neg_le : hp.c - (ε/2) * hp.f u ≤ hp.c := by rw [← h_val_neg]; exact h_neg
        have h1 : hp.f u ≤ 0 := by nlinarith [h_pos_le, h_neg_le, hε]
        have h2 : hp.f u ≥ 0 := by nlinarith [h_pos_le, h_neg_le, hε]
        linarith
      have hp_f_zero : hp.f = 0 := by
        apply LinearMap.ext
        intro w
        by_cases hw : w = 0
        · subst hw
          simp [LinearMap.map_zero]
        · have hnorm : ‖w‖ ≠ 0 := fun h => hw (norm_eq_zero.mp h)
          have hmul_cancel : (‖w‖ : ℝ) * (‖w‖ : ℝ)⁻¹ = 1 := by field_simp [hnorm]
          have h_unit : ‖(‖w‖⁻¹ : ℝ) • w‖ = 1 := by
            rw [norm_smul, norm_inv]
            field_simp [hnorm]
            simp
          have h_w : hp.f w = ‖w‖ • hp.f (‖w‖⁻¹ • w) := by
            have h_w_eq : w = ‖w‖ • (‖w‖⁻¹ • w) := by
              calc
                w = 1 • w := by simp
                _ = ((‖w‖ : ℝ) * (‖w‖ : ℝ)⁻¹) • w := by
                    rw [hmul_cancel]
                    simp
                _ = ‖w‖ • (‖w‖⁻¹ • w) := by rw [smul_smul]
            nth_rewrite 1 [h_w_eq]
            rw [hp.f.map_smul]
          have h_u_zero : hp.f (‖w‖⁻¹ • w) = 0 := h_unit_zero _ h_unit
          rw [h_w, h_u_zero]
          simp
      exact absurd hp_f_zero hp.nonzero
    have hv_in_Psc : v ∈ (P_sc n s : Submodule ℝ (CoeffVec n)) := by
      have hL_dir_le_Psc_dir : L.direction ≤ (P_sc n s : Submodule ℝ (CoeffVec n)) := by
        have hL_as_sub : L ≤ (P_sc n s : Submodule ℝ (CoeffVec n)).toAffineSubspace :=
          affineSpan_le.mpr (by
            rintro x ⟨hx_Psc, _⟩
            simpa [Submodule.mem_toAffineSubspace] using hx_Psc)
        have hdir : L.direction ≤ ((P_sc n s : Submodule ℝ (CoeffVec n)).toAffineSubspace).direction :=
          AffineSubspace.direction_le hL_as_sub
        simpa using hdir
      exact hL_dir_le_Psc_dir hv_dir
    have hδ_bound_in_Psc : δ_bound ∈ (P_sc n s : Set (CoeffVec n)) := by
      obtain ⟨c, hc_Icc, hc_eq⟩ := segment_eq_image ℝ δ_F (δ_F + t_out • v) ▸ h_seg
      have h_eq : δ_bound = δ_F + (c * t_out) • v := by
        calc
          δ_bound = (1 - c) • δ_F + c • (δ_F + t_out • v) := by
            simpa using hc_eq.symm
          _ = δ_F + (c * t_out) • v := segment_point_rewrite δ_F v c t_out
      rw [h_eq]
      apply Submodule.add_mem (P_sc n s)
      · exact hδ_F_root
      · apply Submodule.smul_mem (P_sc n s) (c * t_out)
        exact hv_in_Psc
    have hδ_bound_frontier_F : δ_bound ∈ frontier F := by
      rw [frontier_eq_for_closed F hF_compact.isClosed]
      refine ⟨h_δ_bound_in_F, ?_⟩
      intro h_int
      apply h_δ_bound_not_relint
      exact (interior_subset_intrinsicInterior (𝕜 := ℝ) (s := F)) h_int
    refine ⟨δ_bound, ⟨h_δ_bound_in_F, hδ_bound_in_Psc⟩, hδ_bound_frontier_F, h_δ_bound_not_relint⟩
  · -- δ_F IS on the frontier of P.Ω → find boundary point along the ray
    have hδ_F_front_Ω : δ_F ∈ frontier P.Ω := by
      by_contra h; exact hδ_front_Ω h
    by_cases hδ_F_relint : δ_F ∈ intrinsicInterior ℝ F
    · -- δ_F is in the relative interior of F; find boundary point along direction v
      let S : Set ℝ := {t | 0 ≤ t ∧ δ_F + t • v ∈ F}
      have hS_nonempty : S.Nonempty := ⟨0, by simp [S, hδ_F_in_F]⟩
      have hS_closed : IsClosed S := by
        have h_cont : Continuous (fun (t : ℝ) => δ_F + t • v) := by
          continuity
        have h_preimage_closed : IsClosed {t | δ_F + t • v ∈ F} :=
          hF_compact.isClosed.preimage h_cont
        have h_nonneg_closed : IsClosed {t : ℝ | 0 ≤ t} := isClosed_Ici
        have hS_eq : S = {t | δ_F + t • v ∈ F} ∩ {t : ℝ | 0 ≤ t} := by
          ext t; constructor
          · rintro ⟨ht_nonneg, ht_mem⟩; exact ⟨ht_mem, ht_nonneg⟩
          · rintro ⟨ht_mem, ht_nonneg⟩; exact ⟨ht_nonneg, ht_mem⟩
        rw [hS_eq]
        exact h_preimage_closed.inter h_nonneg_closed
      have h_bdd_above : BddAbove S := by
        refine ⟨t_out, ?_⟩
        rintro t ⟨ht_nonneg, ht_mem⟩
        by_contra! h_gt
        have ha_nonneg : 0 ≤ t_out / t := div_nonneg (by linarith) (by linarith)
        have hdiv : t_out / t ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
        have hb_nonneg : 0 ≤ 1 - t_out / t := by linarith
        have hsum : (t_out / t : ℝ) + (1 - t_out / t) = 1 := by ring
        have h_conv : ((t_out / t : ℝ) • (δ_F + t • v) + (1 - t_out / t) • δ_F) = δ_F + t_out • v := by
          calc
            (t_out / t : ℝ) • (δ_F + t • v) + (1 - t_out / t) • δ_F
                = (t_out / t) • δ_F + (t_out / t) • (t • v) + (1 - t_out / t) • δ_F := by rw [smul_add]
            _ = ((t_out / t) • δ_F + (1 - t_out / t) • δ_F) + (t_out / t) • (t • v) := by abel
            _ = ((t_out / t + (1 - t_out / t)) • δ_F) + ((t_out / t) * t) • v := by
              simp [smul_smul]
            _ = (1 • δ_F) + (t_out • v) := by
              have h_t_ne_zero : t ≠ 0 := by linarith
              have h_sum : t_out / t + (1 - t_out / t) = 1 := by ring
              have h_mul : (t_out / t) * t = t_out := by field_simp [h_t_ne_zero]
              simp [h_sum, h_mul]
            _ = δ_F + t_out • v := by simp
        have hstar : StarConvex ℝ (δ_F + t • v) F := hF_convex ht_mem
        have h_mem_conv : (t_out / t : ℝ) • (δ_F + t • v) + (1 - t_out / t) • δ_F ∈ F :=
          hstar hδ_F_in_F ha_nonneg hb_nonneg hsum
        have h_mem : δ_F + t_out • v ∈ F := by
          rw [← h_conv]
          exact h_mem_conv
        exact ht_out h_mem
      let t1 := sSup S
      have h_max : t1 ∈ S := by
        simpa [t1] using hS_closed.csSup_mem hS_nonempty h_bdd_above
      rcases h_max with ⟨h_t1_nonneg, h_t1_mem⟩
      let δ_bound : CoeffVec n := δ_F + t1 • v
      have hv_in_Psc : v ∈ (P_sc n s : Submodule ℝ (CoeffVec n)) := by
        have hL_dir_le_Psc_dir : L.direction ≤ (P_sc n s : Submodule ℝ (CoeffVec n)) := by
          have hL_as_sub : L ≤ (P_sc n s : Submodule ℝ (CoeffVec n)).toAffineSubspace :=
            affineSpan_le.mpr (by
              rintro x ⟨hx_Psc, _⟩
              simpa [Submodule.mem_toAffineSubspace] using hx_Psc)
          have hdir : L.direction ≤ ((P_sc n s : Submodule ℝ (CoeffVec n)).toAffineSubspace).direction :=
            AffineSubspace.direction_le hL_as_sub
          simpa using hdir
        exact hL_dir_le_Psc_dir hv_dir
      have hδ_bound_in_Psc : δ_bound ∈ (P_sc n s : Set (CoeffVec n)) := by
        dsimp [δ_bound]
        apply Submodule.add_mem (P_sc n s)
        · exact hδ_F_root
        · apply Submodule.smul_mem (P_sc n s) t1 hv_in_Psc
      have h_not_relint : δ_bound ∉ intrinsicInterior ℝ F :=
        not_mem_intrinsicInterior_of_escapes_along_direction
          F hF_convex δ_F hδ_F_in_F v hv_ne hv_affF_dir
          S rfl hS_nonempty h_bdd_above
          t1 rfl h_t1_nonneg h_t1_mem
          t_out ht_out_pos ht_out
      have hδ_bound_frontier_F : δ_bound ∈ frontier F := by
        rw [frontier_eq_for_closed F hF_compact.isClosed]
        refine ⟨h_t1_mem, ?_⟩
        intro h_int
        apply h_not_relint
        exact (interior_subset_intrinsicInterior (𝕜 := ℝ) (s := F)) h_int
      refine ⟨δ_bound, ⟨h_t1_mem, hδ_bound_in_Psc⟩, hδ_bound_frontier_F, h_not_relint⟩
    · -- δ_F is not in the relative interior → already on the boundary
      use δ_F
      have hδ_F_frontier_F : δ_F ∈ frontier F := by
        rw [frontier_eq_for_closed F hF_compact.isClosed]
        refine ⟨hδ_F_in_F, ?_⟩
        intro h_int
        apply hδ_F_relint
        exact (interior_subset_intrinsicInterior (𝕜 := ℝ) (s := F)) h_int
      exact ⟨⟨hδ_F_in_F, hδ_F_root⟩, hδ_F_frontier_F, hδ_F_relint⟩

/--
If an exposed face `G` of a polytope `P` has affine dimension 0,
then any point `x` in `G` must be one of the vertices of `P`.
-/
lemma exposed_face_dim_zero_mem_vertices {n : ℕ} (P : Polytope n) (G : Set (CoeffVec n))
    (hG_exp : IsExposedFace P G) (hG_dim_0 : Module.finrank ℝ (affineSpan ℝ G).direction = 0)
    (x : CoeffVec n) (hx_in_G : x ∈ G) : x ∈ P.vertices := by
  obtain ⟨hp, hG_eq⟩ := hG_exp
  have hx_in_Ω : x ∈ P.Ω := (hG_eq ▸ hx_in_G).1
  have hx_f : hp.f x = hp.c := (hG_eq ▸ hx_in_G).2

  -- Step 1: Prove G = {x} (since it has dimension 0 and contains x)
  have hG_singleton : G = {x} := by
    ext y
    constructor
    · intro hy_in_G
      have h_sub : y - x ∈ (affineSpan ℝ G).direction := by
        apply AffineSubspace.vsub_mem_direction
        · exact subset_affineSpan ℝ G hy_in_G
        · exact subset_affineSpan ℝ G hx_in_G
      have h_dir_eq_bot : (affineSpan ℝ G).direction = ⊥ :=
        (Submodule.finrank_eq_zero (R := ℝ) (M := CoeffVec n)).mp hG_dim_0
      rw [h_dir_eq_bot] at h_sub
      have h_y_sub_x_zero : y - x = 0 := by simpa [Submodule.mem_bot] using h_sub
      exact sub_eq_zero.mp h_y_sub_x_zero
    · intro hy_eq
      rw [hy_eq]
      exact hx_in_G

  -- Step 2: Prove there exists a vertex v where hp.f v = hp.c
  have h_exists_v : ∃ v ∈ P.vertices, hp.f v = hp.c := by
    by_contra h_no_vertex_eq
    push_neg at h_no_vertex_eq
    -- If no vertex achieves the max, then all vertices are strictly less than hp.c
    have hv_le_c : ∀ v ∈ P.vertices, hp.f v ≤ hp.c := by
      intro v hv
      exact hp.upper_bound v (subset_convexHull ℝ (P.vertices : Set (CoeffVec n)) hv)
    have h_vert_nonempty : P.vertices.Nonempty := P.nonempty
    let f_vals : Finset ℝ := P.vertices.image (fun v => hp.f v)
    have hf_vals_nonempty : f_vals.Nonempty := Finset.image_nonempty.mpr h_vert_nonempty
    let M := f_vals.max' hf_vals_nonempty
    have hM_lt_c : M < hp.c := by
      have hM_mem : M ∈ f_vals := Finset.max'_mem f_vals hf_vals_nonempty
      rcases Finset.mem_image.mp hM_mem with ⟨v, hv, _h_eq⟩
      rw [← _h_eq]
      have h_le : hp.f v ≤ hp.c := hv_le_c v hv
      have h_ne : hp.f v ≠ hp.c := h_no_vertex_eq v hv
      exact lt_of_le_of_ne h_le h_ne
    have hv_le_M : ∀ v ∈ P.vertices, hp.f v ≤ M := by
      intro v hv
      exact Finset.le_max' f_vals (hp.f v) (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    -- The half-space H = {y | hp.f y ≤ M} is convex and contains all vertices
    let H : Set (CoeffVec n) := {y | hp.f y ≤ M}
    have hH_convex : Convex ℝ H := by
      intro y hy z hz a b ha hb hab
      simp only [Set.mem_setOf_eq, smul_eq_mul] at *
      calc
        hp.f (a • y + b • z) = a * hp.f y + b * hp.f z := by simp [map_add, map_smul, smul_eq_mul]
        _ ≤ a * M + b * M := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hy ha
          · exact mul_le_mul_of_nonneg_left hz hb
        _ = (a + b) * M := by rw [← add_mul]
        _ = M := by simp [hab]
    have h_verts_sub_H : (P.vertices : Set (CoeffVec n)) ⊆ H := by
      intro v hv; dsimp [H]; exact hv_le_M v hv
    -- Therefore, the entire convex hull P.Ω is contained in H
    have hΩ_sub_H : P.Ω ⊆ H := by
      unfold Polytope.Ω
      exact convexHull_min h_verts_sub_H hH_convex
    have hx_in_H : x ∈ H := hΩ_sub_H hx_in_Ω
    dsimp [H] at hx_in_H
    -- But x achieves hp.c, meaning hp.c ≤ M, contradicting M < hp.c
    have h_contra : hp.c ≤ M := by rwa [hx_f] at hx_in_H
    exact (not_lt.mpr h_contra) hM_lt_c

  -- Step 3: Conclude x is that vertex
  obtain ⟨v, hv, hv_f⟩ := h_exists_v
  have hv_in_Ω : v ∈ P.Ω := subset_convexHull ℝ (P.vertices : Set (CoeffVec n)) hv
  have hv_in_G : v ∈ G := by
    rw [hG_eq]
    exact ⟨hv_in_Ω, hv_f⟩
  have hv_eq_x : v = x := by
    have hv_in_singleton : v ∈ ({x} : Set (CoeffVec n)) := by
      rw [← hG_singleton]
      exact hv_in_G
    exact Set.mem_singleton_iff.mp hv_in_singleton
  rw [← hv_eq_x]
  exact hv

/-- Given an exposed face `F` of `P` with `(r : ℂ) ∈ RootSpaceSet F` and dimension ≥ 2, recursively descend to a proper exposed subface until reaching dimension 0 or 1, then extract an exposed edge. -/
lemma descend_to_exposed_edge {n : ℕ} (P : Polytope n) (r : ℝ)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hs_F : (r : ℂ) ∈ RootSpaceSet F)
    (hF_dim_ge_2 : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 2) :
    ∃ E, IsExposedEdge P E ∧ (r : ℂ) ∈ RootSpaceSet E := by
  let m_F := Module.finrank ℝ (affineSpan ℝ F).direction
  by_cases hm_F_1 : m_F = 1
  · refine ⟨F, isExposedEdge_of_dim_1 hF_exp hm_F_1, hs_F⟩
  · have hm_F_ge_2 : m_F ≥ 2 := by omega
    obtain ⟨δ_F, hδ_F_in_F, hδ_F_root⟩ :
      ∃ δ ∈ F, ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot (r : ℂ) := hs_F
    let affF := affineSpan ℝ F
    have hδ_F_Psr : δ_F ∈ (P_sr n r : Set (CoeffVec n)) := mem_P_sr_of_isRoot r δ_F hδ_F_root
    let dir := (affineSpan ℝ (((P_sr n r : Set (CoeffVec n)) ∩
      (affF : Set (CoeffVec n))))).direction
    have h_inter_dim : Module.finrank ℝ (↥dir) ≥ 1 :=
      intersection_affine_dim_ge_one (P_sr n r) affF δ_F hδ_F_Psr
        (subset_affineSpan ℝ F hδ_F_in_F) (P_sr_dimension r) hm_F_ge_2
    obtain ⟨δ_bound, hδ_bound_inter, hδ_bound_front, hδ_bound_not_relint⟩ :=
      exists_boundary_point_in_face_rootspace P r δ_F F hF_exp hδ_F_in_F hδ_F_Psr h_inter_dim
    have hδ_bound_in_F : δ_bound ∈ F := hδ_bound_inter.1
    have hδ_bound_Psr : δ_bound ∈ (P_sr n r : Set (CoeffVec n)) := hδ_bound_inter.2
    obtain ⟨G, hG_exp, hδ_bound_in_G, hG_dim_lt⟩ :=
      exists_proper_subface_of_boundary_point P F hF_exp δ_bound
        hδ_bound_in_F hδ_bound_front hδ_bound_not_relint hm_F_ge_2
    have hs_G : (r : ℂ) ∈ RootSpaceSet G :=
      rootspace_mem_of_eval_zero r δ_bound hδ_bound_Psr G hδ_bound_in_G
    by_cases hG_dim_ge_2 : Module.finrank ℝ (affineSpan ℝ G).direction ≥ 2
    · exact descend_to_exposed_edge P r G hG_exp hs_G hG_dim_ge_2
    · by_cases hG_dim_1 : Module.finrank ℝ (affineSpan ℝ G).direction = 1
      · refine ⟨G, isExposedEdge_of_dim_1 hG_exp hG_dim_1, hs_G⟩
      · -- dim(G) = 0: δ_bound is a vertex; use the vertex_adjacent_edge axiom.
        have hG_dim_0 : Module.finrank ℝ (affineSpan ℝ G).direction = 0 := by
          have h_not_ge_2 : ¬ Module.finrank ℝ (affineSpan ℝ G).direction ≥ 2 := hG_dim_ge_2
          have h_not_1 : ¬ Module.finrank ℝ (affineSpan ℝ G).direction = 1 := hG_dim_1
          omega
        have hδ_is_vertex : δ_bound ∈ P.vertices :=
          exposed_face_dim_zero_mem_vertices P G hG_exp hG_dim_0 δ_bound hδ_bound_in_G
        obtain ⟨E, hE_edge, hδ_in_E⟩ := vertex_incident_to_exposed_edge P δ_bound hδ_is_vertex
        have h_root_E : (r : ℂ) ∈ RootSpaceSet E :=
          rootspace_mem_of_eval_zero r δ_bound hδ_bound_Psr E hδ_in_E
        exact ⟨E, hE_edge, h_root_E⟩
  termination_by Module.finrank ℝ (affineSpan ℝ F).direction
  decreasing_by exact hG_dim_lt

/-- Complex descent: given an exposed face `F` of `P` with `s ∈ RootSpaceSet F` and `dim(F) ≥ 3`,
  recursively descend to a proper exposed subface of dimension at most 2. -/
lemma descend_to_exposed_face {n : ℕ} (hn : n ≥ 1) (P : Polytope n) (s : ℂ)
    (hcomplex : s.im ≠ 0) (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hs_F : s ∈ RootSpaceSet F)
    (hF_dim_ge_3 : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 3) :
    ∃ F', IsExposedFace P F' ∧ s ∈ RootSpaceSet F' := by
  obtain ⟨δ_F, hδ_F_in_F, hδ_F_root⟩ : ∃ δ ∈ F, ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s :=
    hs_F
  let affF := affineSpan ℝ F
  have hδ_F_Psc : δ_F ∈ (P_sc n s : Set (CoeffVec n)) :=
    mem_P_sc_of_isRoot s δ_F hδ_F_root
  let dir := (affineSpan ℝ (((P_sc n s : Set (CoeffVec n)) ∩
    (affF : Set (CoeffVec n))))).direction
  have hdim_Psc : Module.finrank ℝ (P_sc n s) = n - 1 :=
    P_sc_dimension hn s hcomplex
  have h_inter_dim : Module.finrank ℝ (↥dir) ≥ 1 :=
    intersection_affine_dim_ge_one_complex (P_sc n s) affF δ_F hδ_F_Psc
      (subset_affineSpan ℝ F hδ_F_in_F) hdim_Psc hF_dim_ge_3
  obtain ⟨δ_bound, hδ_bound_inter, hδ_bound_front, hδ_bound_not_relint⟩ :=
    exists_boundary_point_in_face_rootspace_complex P s δ_F F hF_exp hδ_F_in_F hδ_F_Psc h_inter_dim
  have hδ_bound_in_F : δ_bound ∈ F := hδ_bound_inter.1
  have hδ_bound_Psc : δ_bound ∈ (P_sc n s : Set (CoeffVec n)) := hδ_bound_inter.2
  obtain ⟨G, hG_exp, hδ_bound_in_G, hG_dim_lt⟩ :=
    exists_proper_subface_of_boundary_point P F hF_exp δ_bound
      hδ_bound_in_F hδ_bound_front hδ_bound_not_relint (by omega)
  have hs_G : s ∈ RootSpaceSet G :=
    rootspace_mem_of_isRoot s δ_bound (by
      have hzero : evalAtComplex s δ_bound = 0 := hδ_bound_Psc
      simpa [evalAtComplex] using hzero) G hδ_bound_in_G
  by_cases hG_dim_ge_3 : Module.finrank ℝ (affineSpan ℝ G).direction ≥ 3
  · exact descend_to_exposed_face hn P s hcomplex G hG_exp hs_G hG_dim_ge_3
  · exact ⟨G, hG_exp, hs_G⟩
  termination_by Module.finrank ℝ (affineSpan ℝ F).direction
  decreasing_by exact hG_dim_lt

/-- Given a boundary point δ_bound ∈ P.Ω that lies in P_sr, find an exposed edge E
  of P.Ω such that (r : ℂ) ∈ RootSpaceSet E.

  Wires `exists_exposed_face_containing_boundary_point` to get an exposed face F,
  then dispatches by dimension.  For dim(F) ≥ 2 it delegates to
  `descend_to_exposed_edge`.  For dim(F) = 1 the face is already an edge.
  For dim(F) = 0 (a vertex) the `vertex_adjacent_edge` gap remains.
-/
lemma exists_exposed_edge_through_vertex {n : ℕ} (P : Polytope n) (r : ℝ) (δ_bound : CoeffVec n)
    (hδ_bound_in_Ω : δ_bound ∈ P.Ω) (hδ_bound_front : δ_bound ∈ frontier P.Ω)
    (hδ_bound_Psr : δ_bound ∈ (P_sr n r : Set (CoeffVec n))) :
    ∃ E, IsExposedEdge P E ∧ (r : ℂ) ∈ RootSpaceSet E := by
  have h_int_nonempty : (interior P.Ω).Nonempty := P.interior_nonempty
  obtain ⟨F, hF_exposed, hδ_in_F, hs_in_RF⟩ :=
    exists_exposed_face_containing_boundary_point P r δ_bound hδ_bound_front hδ_bound_Psr h_int_nonempty
  let m_F := Module.finrank ℝ (affineSpan ℝ F).direction
  by_cases hm_F_ge_2 : m_F ≥ 2
  · exact descend_to_exposed_edge P r F hF_exposed hs_in_RF hm_F_ge_2
  · by_cases hm_F_1 : m_F = 1
    · refine ⟨F, isExposedEdge_of_dim_1 hF_exposed hm_F_1, hs_in_RF⟩
    · have hm_F_0 : m_F = 0 := by omega
      have hδ_is_vertex : δ_bound ∈ P.vertices :=
        exposed_face_dim_zero_mem_vertices P F hF_exposed hm_F_0 δ_bound hδ_in_F
      obtain ⟨E, hE_edge, hδ_in_E⟩ := vertex_incident_to_exposed_edge P δ_bound hδ_is_vertex
      have h_root_E : (r : ℂ) ∈ RootSpaceSet E :=
        rootspace_mem_of_eval_zero r δ_bound hδ_bound_Psr E hδ_in_E
      exact ⟨E, hE_edge, h_root_E⟩

end CoeffBox
