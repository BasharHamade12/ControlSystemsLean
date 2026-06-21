module

public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeTheoremDefs
public import Mathlib.Analysis.Convex.Intrinsic
public import ControlSystems.DiscreteTime.EdgeTheorem.BasicLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.ExposedFaceLemmas


@[expose] public section

open Polynomial Affine FiniteDimensional LinearMap Set

namespace CoeffBox

lemma not_mem_intrinsicInterior_of_escapes_along_direction {n : ℕ}
    (F : Set (CoeffVec n))
    (hF_convex : Convex ℝ F)
    (δ_F : CoeffVec n) (hδ_F_in_F : δ_F ∈ F)
    (v : CoeffVec n) (hv_ne : v ≠ 0) (hv_affF_dir : v ∈ (affineSpan ℝ F).direction)
    (S : Set ℝ) (hS_def : S = {t | 0 ≤ t ∧ δ_F + t • v ∈ F})
    (hS_nonempty : S.Nonempty) (h_bdd_above : BddAbove S)
    (t1 : ℝ) (ht1_t1_is_sup : t1 = sSup S) (ht1_nonneg : 0 ≤ t1)
    (hδ_bound_in_F : (δ_F + t1 • v) ∈ F)
    (t_out : ℝ) (ht_out_pos : 0 < t_out) (ht_out : δ_F + t_out • v ∉ F) :
    (δ_F + t1 • v) ∉ intrinsicInterior ℝ F := by
  let δ_bound : CoeffVec n := δ_F + t1 • v
  let affF : AffineSubspace ℝ (CoeffVec n) := affineSpan ℝ F
  have h_upper_bound : ∀ x ∈ S, x ≤ t_out := by
    intro x hx
    rw [hS_def] at hx
    rcases hx with ⟨hx_nonneg, hx_mem⟩
    by_contra! h_gt
    have hdiv_nonneg : 0 ≤ t_out / x := div_nonneg (by linarith) (by linarith)
    have hdiv_le_one : t_out / x ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have hb_nonneg : 0 ≤ 1 - t_out / x := by linarith
    have hsum : (t_out / x : ℝ) + (1 - t_out / x) = 1 := by ring
    have hstar : StarConvex ℝ (δ_F + x • v) F := hF_convex hx_mem
    have h_mem_conv : (t_out / x : ℝ) • (δ_F + x • v) + (1 - t_out / x) • δ_F ∈ F :=
      hstar hδ_F_in_F hdiv_nonneg hb_nonneg hsum
    have h_conv : (t_out / x : ℝ) • (δ_F + x • v) + (1 - t_out / x) • δ_F = δ_F + t_out • v := by
      calc
        (t_out / x : ℝ) • (δ_F + x • v) + (1 - t_out / x) • δ_F
            = (t_out / x) • δ_F + (t_out / x) • (x • v) + (1 - t_out / x) • δ_F := by rw [smul_add]
        _ = ((t_out / x) • δ_F + (1 - t_out / x) • δ_F) + (t_out / x) • (x • v) := by abel
        _ = ((t_out / x + (1 - t_out / x)) • δ_F) + ((t_out / x) * x) • v := by
          simp [smul_smul]
        _ = (1 • δ_F) + (t_out • v) := by
          have h_x_ne_zero : x ≠ 0 := by linarith
          have h_sum : t_out / x + (1 - t_out / x) = 1 := by ring
          have h_mul : (t_out / x) * x = t_out := by field_simp [h_x_ne_zero]
          simp [h_sum, h_mul]
        _ = δ_F + t_out • v := by simp
    rw [h_conv] at h_mem_conv
    exact ht_out h_mem_conv
  have h_t1_le_t_out : t1 ≤ t_out := by
    rw [ht1_t1_is_sup]
    exact csSup_le hS_nonempty h_upper_bound
  have ht_out_gt_t1 : t1 < t_out := by
    by_contra! h_ge
    have h_eq : t1 = t_out := le_antisymm h_t1_le_t_out h_ge
    have h_t_out_mem_F : δ_F + t_out • v ∈ F := by
      rw [← h_eq]
      exact hδ_bound_in_F
    exact ht_out h_t_out_mem_F
  by_contra h_relint
  rcases h_relint with ⟨x, hx_int, hx_eq⟩
  have hx_val : (x : CoeffVec n) = δ_bound := hx_eq
  have h_open_int : IsOpen (interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF)) :=
    isOpen_interior
  haveI : Nonempty affF := ⟨⟨δ_F, subset_affineSpan ℝ F hδ_F_in_F⟩⟩
  let v_dir : (affineSpan ℝ F).direction := ⟨v, hv_affF_dir⟩
  have h_cont_ambient : Continuous (fun (t : ℝ) => (t • v : CoeffVec n) + (x : CoeffVec n)) := by
    continuity
  have h_mem_affF : ∀ (t : ℝ), (t • v : CoeffVec n) + (x : CoeffVec n) ∈ affF := by
    intro t
    simpa using
      AffineSubspace.vadd_mem_of_mem_direction (s := affF) (hv := affF.direction.smul_mem t hv_affF_dir)
        (hp := x.property)
  have h_cont : Continuous (fun (t : ℝ) => (t • v_dir) +ᵥ (x : affF)) := by
    have h_eq : (fun (t : ℝ) => ((t • v_dir) +ᵥ (x : affF) : CoeffVec n)) =
      (fun (t : ℝ) => (t • v : CoeffVec n) + (x : CoeffVec n)) := by
      ext t
      simp [v_dir, vadd_eq_add]
    have h_cont' : Continuous (fun (t : ℝ) => ((t • v_dir) +ᵥ (x : affF) : CoeffVec n)) := by
      simpa [h_eq] using h_cont_ambient
    exact h_cont'.subtype_mk (fun t => h_mem_affF t)
  have h_preimage_open : IsOpen ((fun (t : ℝ) => (t • v_dir) +ᵥ (x : affF))⁻¹'
      (interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF))) :=
    h_open_int.preimage h_cont
  have h_zero_mem : (0 : ℝ) ∈ (fun (t : ℝ) => (t • v_dir) +ᵥ (x : affF))⁻¹'
      (interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF)) := by
    show (0 • v_dir) +ᵥ (x : affF) ∈ interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF)
    simpa using hx_int
  have h_nhds : (fun (t : ℝ) => (t • v_dir) +ᵥ (x : affF))⁻¹'
      (interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF)) ∈ nhds (0 : ℝ) :=
    h_preimage_open.mem_nhds h_zero_mem
  rcases Metric.mem_nhds_iff.mp h_nhds with ⟨ε, hε_pos, h_ball⟩
  let t_small := min (ε / 2) ((t_out - t1) / 2)
  have ht_small_pos : 0 < t_small := by
    refine lt_min_iff.mpr ⟨by nlinarith, by nlinarith⟩
  have h_ball_mem : t_small ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have ht_small_lt_ε : t_small < ε := by
      have h1 : t_small ≤ ε / 2 := min_le_left _ _
      have h2 : ε / 2 < ε := by nlinarith
      linarith
    calc
      |t_small| = t_small := abs_of_pos ht_small_pos
      _ < ε := ht_small_lt_ε
  have h_mem_interior : t_small • v_dir +ᵥ (x : affF) ∈
      interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF) :=
    h_ball h_ball_mem
  have h_mem_preimage : t_small • v_dir +ᵥ (x : affF) ∈
      (Subtype.val : affF → CoeffVec n)⁻¹' F :=
    interior_subset h_mem_interior
  have h_mem_F : ((t_small • v_dir +ᵥ (x : affF) : affF) : CoeffVec n) ∈ F :=
    h_mem_preimage
  have h_coord : ((t_small • v_dir +ᵥ (x : affF) : affF) : CoeffVec n) =
      δ_F + (t1 + t_small) • v := by
    calc
      ((t_small • v_dir +ᵥ (x : affF) : affF) : CoeffVec n) = (t_small • v : CoeffVec n) + (x : CoeffVec n) := by
        simp [v_dir, vadd_eq_add]
      _ = (t_small • v : CoeffVec n) + δ_bound := by rw [hx_val]
      _ = t_small • v + (δ_F + t1 • v) := by simp [δ_bound]
      _ = δ_F + t1 • v + t_small • v := by abel
      _ = δ_F + (t1 + t_small) • v := by
        simp [add_smul]
        abel
  rw [h_coord] at h_mem_F
  have h_contra : δ_F + (t1 + t_small) • v ∉ F := by
    intro hF
    have hS : (t1 + t_small) ∈ S := by
      rw [hS_def]
      exact ⟨by nlinarith, hF⟩
    have h_sup_le : t1 + t_small ≤ sSup S := le_csSup h_bdd_above hS
    rw [ht1_t1_is_sup] at h_sup_le
    nlinarith
  exact h_contra h_mem_F

private lemma exists_proper_subface_caseB1 {n : ℕ} (P : Polytope n)
    (F : Set (CoeffVec n)) (hp : SupportingHyperplane P) (hF_eq : F = ExposedFace hp)
    (δ_bound : CoeffVec n)
    (hδ_in_Ω : δ_bound ∈ P.Ω) (hδ_f_val : hp.f δ_bound = hp.c)
    (hδ_affF : δ_bound ∈ affineSpan ℝ F)
    (hF_dim : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 2)
    (w_base : CoeffVec n →ₗ[ℝ] ℝ) (c_w : ℝ) (hδ_cw : w_base δ_bound = c_w)
    (h_nonconst : ∃ x ∈ F, w_base x < c_w)
    (hS_empty : P.vertices.filter (fun v => w_base v > c_w) = ∅) :
    ∃ (G : Set (CoeffVec n)), IsExposedFace P G ∧ δ_bound ∈ G ∧
    Module.finrank ℝ (affineSpan ℝ G).direction < Module.finrank ℝ (affineSpan ℝ F).direction := by
  let S_verts : Finset (CoeffVec n) := P.vertices.filter fun v => w_base v > c_w
  let lam : ℝ := 1
  have hlam_pos : 0 < lam := by norm_num
  let f_new := hp.f + lam • w_base
  let c_new := hp.c + lam * c_w
  have h_support : ∀ x ∈ P.Ω, f_new x ≤ c_new := by
    intro x hx
    unfold Polytope.Ω at hx
    rcases (f_new.convexOn convex_univ).exists_ge_of_mem_convexHull (by simp) hx with ⟨v, hv, h_le⟩
    have hv_w : w_base v ≤ c_w := by
      by_contra! hgt
      have : v ∈ S_verts := by
        dsimp [S_verts]
        exact Finset.mem_filter.mpr ⟨hv, hgt⟩
      simpa [S_verts, hS_empty] using this
    simp [f_new, c_new, LinearMap.add_apply, LinearMap.smul_apply] at h_le ⊢
    nlinarith [hp.upper_bound v ((subset_convexHull ℝ _) hv), hlam_pos, hv_w]
  have h_touches : ∃ x ∈ P.Ω, f_new x = c_new := by
    refine ⟨δ_bound, hδ_in_Ω, ?_⟩
    dsimp [f_new, c_new]
    simp [hδ_f_val, hδ_cw]
  have h_nonzero : f_new ≠ 0 := by
    intro hzero
    rcases h_nonconst with ⟨y, hyF, hyw⟩
    have hy_f : hp.f y = hp.c := (hF_eq ▸ hyF).2
    have h_y : hp.c + lam * w_base y = 0 := by simpa [f_new, hy_f] using congrArg (fun f => f y) hzero
    have h_δ : hp.c + lam * c_w = 0 := by simpa [f_new, hδ_f_val, hδ_cw] using congrArg (fun f => f δ_bound) hzero
    have h_eq : lam * w_base y = lam * c_w := by linarith
    have hw_eq : w_base y = c_w := by
      apply mul_left_cancel₀ (ne_of_gt hlam_pos)
      simpa [mul_comm] using h_eq
    rw [hw_eq] at hyw; exact lt_irrefl _ hyw
  let G : Set (CoeffVec n) := {x | x ∈ P.Ω ∧ f_new x = c_new}
  have hG_exposed : IsExposedFace P G :=
    ⟨{ f := f_new, c := c_new, nonzero := h_nonzero, upper_bound := h_support, touches := h_touches }, rfl⟩
  have hδ_in_G : δ_bound ∈ G := by
    refine ⟨hδ_in_Ω, ?_⟩
    dsimp [f_new, c_new]
    simp [hδ_f_val, hδ_cw]

  have hG_sub_F : G ⊆ F := by
    intro x hx
    have hx_Ω : x ∈ P.Ω := hx.1
    have hx_eq : f_new x = c_new := hx.2
    by_contra hx_not_F
    have hx_hull : x ∈ convexHull ℝ (P.vertices : Set (CoeffVec n)) := by
      unfold Polytope.Ω at hx_Ω; exact hx_Ω
    rw [Finset.convexHull_eq] at hx_hull
    rcases hx_hull with ⟨w_poly, hw_nonneg, hw_sum, hx_cm⟩
    have h_v_le : ∀ v ∈ P.vertices, f_new v ≤ c_new := by
      intro v hv
      simp [f_new, c_new, LinearMap.add_apply, LinearMap.smul_apply]
      have hv_w : w_base v ≤ c_w := by
        by_contra! hgt
        have hv_Sverts : v ∈ S_verts := by
          dsimp [S_verts]
          exact Finset.mem_filter.mpr ⟨hv, hgt⟩
        have : v ∈ (∅ : Finset (CoeffVec n)) := by
          simpa [S_verts, hS_empty] using hv_Sverts
        simp at this
      nlinarith [hp.upper_bound v ((subset_convexHull ℝ _) hv), hlam_pos]
    have h_exists_v_not_F : ∃ v ∈ P.vertices, w_poly v > 0 ∧ v ∉ F := by
      by_contra h_all_in_F
      push_neg at h_all_in_F
      have h_x_in_F : x ∈ F := by
        classical
        have hF_convex' : Convex ℝ F := isExposedFace_convex P ⟨hp, hF_eq⟩
        have h_sum_F : ∑ v ∈ P.vertices.filter (fun v => v ∈ F), w_poly v = 1 := by
          calc ∑ v ∈ P.vertices.filter (fun v => v ∈ F), w_poly v
            = ∑ v ∈ P.vertices, if v ∈ F then w_poly v else 0 := by simp [Finset.sum_filter]
            _ = ∑ v ∈ P.vertices, w_poly v := by
              refine Finset.sum_congr rfl fun v hv => ?_
              by_cases hvF : v ∈ F
              · simp [hvF]
              · have : w_poly v = 0 := by
                  by_contra h_ne
                  have h_pos : w_poly v > 0 :=
                    lt_of_le_of_ne (hw_nonneg v hv) (Ne.symm h_ne)
                  exact hvF (h_all_in_F v hv h_pos)
                simp [this]
            _ = 1 := hw_sum
        have h_mem : x ∈ convexHull ℝ (P.vertices.filter (fun v => v ∈ F) : Set (CoeffVec n)) := by
          rw [Finset.convexHull_eq]
          refine ⟨w_poly, ?_, h_sum_F, ?_⟩
          · intro y hy; exact hw_nonneg y ((Finset.mem_filter.mp hy).1)
          · calc
              (P.vertices.filter (fun v => v ∈ F)).centerMass w_poly (fun x => x) =
                P.vertices.centerMass w_poly (fun x => x) := by
                apply Finset.centerMass_subset (fun x => x) (Finset.filter_subset _ _)
                intro v hv hnv
                have hv_notF : v ∉ F := by
                  intro h; apply hnv; exact Finset.mem_filter.mpr ⟨hv, h⟩
                by_cases hpos : w_poly v > 0
                · exfalso; exact hv_notF (h_all_in_F v hv hpos)
                · have : w_poly v = 0 := by linarith [hw_nonneg v hv]
                  simp [this]
              _ = x := hx_cm
        exact convexHull_min (fun v hv => (Finset.mem_filter.mp hv).2) hF_convex' h_mem
      exact hx_not_F h_x_in_F
    rcases h_exists_v_not_F with ⟨v, hv, hw_pos, hv_not_F⟩
    have h_v_strict : f_new v < c_new := by
      dsimp [f_new, c_new]
      have hv_f_strict : hp.f v < hp.c := by
        by_contra h_eq
        have h_le : hp.f v ≤ hp.c := hp.upper_bound v ((subset_convexHull ℝ _) hv)
        have h_eq' : hp.f v = hp.c := le_antisymm h_le (not_lt.mp h_eq)
        exact hv_not_F (hF_eq ▸ ⟨(subset_convexHull ℝ _) hv, h_eq'⟩)
      have hv_w_le : w_base v ≤ c_w := by
        by_contra! hgt
        have hv_Sverts : v ∈ S_verts := by
          dsimp [S_verts]
          exact Finset.mem_filter.mpr ⟨hv, hgt⟩
        have : v ∈ (∅ : Finset (CoeffVec n)) := by simpa [S_verts, hS_empty] using hv_Sverts
        simp at this
      nlinarith
    have h_sum_strict : ∑ v ∈ P.vertices, w_poly v * f_new v < c_new := by
      have h_lt : ∑ v ∈ P.vertices, w_poly v * f_new v < ∑ v ∈ P.vertices, w_poly v * c_new := by
        apply Finset.sum_lt_sum
        · intro i hi; exact mul_le_mul_of_nonneg_left (h_v_le i hi) (hw_nonneg i hi)
        · use v
          constructor
          ·
            exact hv
          · exact mul_lt_mul_of_pos_left h_v_strict hw_pos



      have h_eq : ∑ v ∈ P.vertices, w_poly v * c_new = c_new := by
        simp [← Finset.sum_mul, hw_sum]


      linarith
    have h_eq_sum : f_new x = ∑ v ∈ P.vertices, w_poly v * f_new v := by
      rw [← hx_cm]; simp only [Finset.centerMass, map_sum, LinearMap.map_smul, smul_eq_mul]; rw [hw_sum]; simp
    rw [h_eq_sum] at hx_eq; linarith

  have h_dim_lt : Module.finrank ℝ (affineSpan ℝ G).direction <
      Module.finrank ℝ (affineSpan ℝ F).direction := by
    let V_dirF := (affineSpan ℝ F).direction
    have h_dir_le : (affineSpan ℝ G).direction ≤ V_dirF :=
      AffineSubspace.direction_le (affineSpan_mono (k := ℝ) hG_sub_F)
    have h_const_on_G : ∀ x ∈ G, w_base x = c_w := by
      intro x hx
      have hx_Ω : x ∈ P.Ω := hx.1
      have hx_eq : f_new x = c_new := hx.2
      have hx_F : x ∈ F := hG_sub_F hx
      have hx_hp : hp.f x = hp.c := (hF_eq ▸ hx_F).2
      dsimp [f_new, c_new] at hx_eq
      have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
      have h_eq : lam * w_base x = lam * c_w := by linarith
      exact mul_left_cancel₀ hlam_ne h_eq
    have h_dir_sub_ker : (affineSpan ℝ G).direction ≤ LinearMap.ker w_base := by
      intro v hv
      have h_base : δ_bound ∈ affineSpan ℝ G := subset_affineSpan ℝ G hδ_in_G
      have h_plus : δ_bound + v ∈ affineSpan ℝ G := by
        have h_vadd : v +ᵥ δ_bound ∈ affineSpan ℝ G :=
          AffineSubspace.vadd_mem_of_mem_direction hv h_base
        simpa [vadd_eq_add, add_comm] using h_vadd
      have h_const : ∀ x ∈ affineSpan ℝ G, w_base x = c_w := by
        intro x hx
        refine affineSpan_induction hx (fun p hp => h_const_on_G p hp) ?_
        intro a u v w hu hv hw
        rw [vsub_eq_sub, vadd_eq_add]
        simp [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_sub, hu, hv, hw]
      have h_val_base : w_base δ_bound = c_w := h_const δ_bound h_base
      have h_val_plus : w_base (δ_bound + v) = c_w := h_const (δ_bound + v) h_plus
      rw [← h_val_base] at h_val_plus
      simpa using h_val_plus
    have h_dir_le_inter : (affineSpan ℝ G).direction ≤ V_dirF ⊓ LinearMap.ker w_base :=
      le_inf h_dir_le h_dir_sub_ker
    let w_V : V_dirF →ₗ[ℝ] ℝ := w_base.comp V_dirF.subtype
    have hw_V_nonzero : w_V ≠ 0 := by
      intro hzero
      rcases h_nonconst with ⟨y, hyF, hyw⟩
      have hv : (y - δ_bound) ∈ V_dirF :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ F hyF) hδ_affF
      have h_val : w_V ⟨y - δ_bound, hv⟩ = w_base (y - δ_bound) := by
        simp [w_V, LinearMap.comp_apply, Submodule.subtype_apply]
      have h_w_y : w_base y = w_base (y - δ_bound) + w_base δ_bound := by simp
      have h_w_y_lt : w_base y < c_w := hyw
      have h_w_diff_lt : w_base (y - δ_bound) < 0 := by
        rw [h_w_y] at h_w_y_lt
        have hδ_cw_symm : w_base δ_bound = c_w := hδ_cw
        linarith
      have h_zero : w_V ⟨y - δ_bound, hv⟩ = 0 := by
        simp [hzero]
      have : w_base (y - δ_bound) = 0 := by
        simpa [h_val] using h_zero
      linarith
    haveI : FiniteDimensional ℝ (↥V_dirF) := by infer_instance
    have h_dim_ker : Module.finrank ℝ (LinearMap.ker w_V) = Module.finrank ℝ (↥V_dirF) - 1 := by
      have hg_surj : LinearMap.range w_V = ⊤ := by
        apply LinearMap.range_eq_top.mpr
        intro y
        have ⟨x, hx⟩ : ∃ x, w_V x ≠ 0 := by
          by_contra h_allzero
          apply hw_V_nonzero
          apply LinearMap.ext
          simpa using not_exists.mp h_allzero
        refine ⟨(y / w_V x) • x, ?_⟩
        simp [LinearMap.map_smul, smul_eq_mul, hx, mul_comm]
        grind
      have h_finrank_range : Module.finrank ℝ (LinearMap.range w_V) = 1 := by
        rw [hg_surj]; simp
      have h_total : Module.finrank ℝ (LinearMap.range w_V) + Module.finrank ℝ (LinearMap.ker w_V) =
        Module.finrank ℝ (↥V_dirF) := LinearMap.finrank_range_add_finrank_ker w_V
      rw [h_finrank_range] at h_total
      omega
    have h_V_finrank : Module.finrank ℝ (↥V_dirF) = Module.finrank ℝ V_dirF := rfl
    have h_iso : Module.finrank ℝ (LinearMap.ker w_V) = Module.finrank ℝ (↥(V_dirF ⊓ LinearMap.ker w_base)) := by
      let φ : LinearMap.ker w_V ≃ₗ[ℝ] ↥(V_dirF ⊓ LinearMap.ker w_base) := {
        toFun := fun x => ⟨x.1.1, ⟨x.1.2, by
          have h_ker : w_V x.1 = 0 := x.2
          simp
          rw [LinearMap.comp_apply] at h_ker
          simpa [Submodule.subtype_apply] using h_ker

          ⟩⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, by
          simpa [w_V, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.mem_ker] using y.2.2⟩
        left_inv := fun x => by ext; simp
        right_inv := fun y => by ext; simp
        map_add' := fun x y => by ext; simp
        map_smul' := fun a x => by ext; simp
      }
      exact LinearEquiv.finrank_eq φ
    have h_dim_inter : Module.finrank ℝ (↥(V_dirF ⊓ LinearMap.ker w_base)) = Module.finrank ℝ (↥V_dirF) - 1 := by
      rw [← h_iso, h_dim_ker]
    calc Module.finrank ℝ (affineSpan ℝ G).direction
      ≤ Module.finrank ℝ (↥(V_dirF ⊓ LinearMap.ker w_base)) := Submodule.finrank_mono h_dir_le_inter
      _ = Module.finrank ℝ (↥V_dirF) - 1 := h_dim_inter
      _ = Module.finrank ℝ V_dirF - 1 := rfl
      _ < Module.finrank ℝ V_dirF := by
        have h_V_ge_2 : Module.finrank ℝ V_dirF ≥ 2 := hF_dim
        omega

  exact ⟨G, hG_exposed, hδ_in_G, h_dim_lt⟩

/-- Case B2 of `exists_proper_subface_of_boundary_point`: when some vertex has `w_base v > c_w`, choose `λ` small enough via ratios so that `hp.f + λ • w_base` yields a proper subface `G` of `F` containing `δ_bound`. -/
private lemma exists_proper_subface_caseB2 {n : ℕ} (P : Polytope n)
    (F : Set (CoeffVec n)) (hp : SupportingHyperplane P) (hF_eq : F = ExposedFace hp)
    (δ_bound : CoeffVec n)
    (hδ_in_Ω : δ_bound ∈ P.Ω) (hδ_f_val : hp.f δ_bound = hp.c)
    (hδ_affF : δ_bound ∈ affineSpan ℝ F)
    (hF_dim : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 2)
    (w_base : CoeffVec n →ₗ[ℝ] ℝ) (c_w : ℝ) (hδ_cw : w_base δ_bound = c_w)
    (hw_nonpos_F : ∀ x ∈ F, w_base x ≤ c_w)
    (h_nonconst : ∃ x ∈ F, w_base x < c_w)
    (hS_empty : P.vertices.filter (fun v => w_base v > c_w) ≠ ∅) :
    ∃ (G : Set (CoeffVec n)), IsExposedFace P G ∧ δ_bound ∈ G ∧
    Module.finrank ℝ (affineSpan ℝ G).direction < Module.finrank ℝ (affineSpan ℝ F).direction := by
  let S_verts : Finset (CoeffVec n) := P.vertices.filter fun v => w_base v > c_w
  have hS_nonempty : S_verts.Nonempty := by rw [Finset.nonempty_iff_ne_empty]; exact hS_empty
  let allRatios : Finset ℝ := S_verts.image fun v => (hp.c - hp.f v) / (w_base v - c_w)
  have hallRatios_nonempty : allRatios.Nonempty := hS_nonempty.image _
  have h_all_pos : ∀ r ∈ allRatios, 0 < r := by
    intro r hr; rcases Finset.mem_image.mp hr with ⟨v, hvS, rfl⟩
    have hv_Ω : v ∈ P.Ω := (subset_convexHull ℝ _) (Finset.mem_filter.mp hvS).1
    have hvS_mem := Finset.mem_filter.mp hvS
    have h_num : 0 < hp.c - hp.f v := by
      have hb := hp.upper_bound v hv_Ω
      have hne : hp.f v ≠ hp.c := by
        intro heq
        have hvF : v ∈ F := hF_eq ▸ ⟨hv_Ω, heq⟩
        have := hw_nonpos_F v hvF
        nlinarith
      have h_lt : hp.f v < hp.c := lt_of_le_of_ne hb hne
      nlinarith
    have h_den : 0 < w_base v - c_w := by nlinarith [hvS_mem.2]
    exact div_pos h_num h_den
  let lam := allRatios.min' hallRatios_nonempty / 2
  have hlam_pos : 0 < lam := by
    dsimp [lam]
    have hmin := allRatios.min'_mem hallRatios_nonempty
    have hmin_pos := h_all_pos _ hmin
    nlinarith
  let f_new := hp.f + lam • w_base
  let c_new := hp.c + lam * c_w
  have h_support : ∀ x ∈ P.Ω, f_new x ≤ c_new := by
    intro x hx
    unfold Polytope.Ω at hx
    rcases (f_new.convexOn convex_univ).exists_ge_of_mem_convexHull (by simp) hx with ⟨v, hv, h_le⟩
    have hv_new : f_new v ≤ c_new := by
      have h_hp : hp.f v ≤ hp.c := hp.upper_bound v ((subset_convexHull ℝ _) hv)
      by_cases hw_gt : w_base v > c_w
      · have h_mem : v ∈ S_verts := by
          simp [S_verts, Finset.mem_filter, hv, hw_gt]
          simp at hv
          exact hv
        have h_ratio : (hp.c - hp.f v) / (w_base v - c_w) ∈ allRatios :=
          Finset.mem_image.mpr ⟨v, h_mem, rfl⟩
        have h_min : allRatios.min' hallRatios_nonempty ≤ (hp.c - hp.f v) / (w_base v - c_w) :=
          Finset.min'_le _ _ h_ratio
        have h_lam_le_ratio : lam ≤ (hp.c - hp.f v) / (w_base v - c_w) := by
          dsimp [lam]
          have h_nonneg : 0 ≤ allRatios.min' hallRatios_nonempty :=
            le_of_lt (h_all_pos _ (allRatios.min'_mem hallRatios_nonempty))
          calc
            allRatios.min' hallRatios_nonempty / 2 ≤ allRatios.min' hallRatios_nonempty := by nlinarith
            _ ≤ (hp.c - hp.f v) / (w_base v - c_w) := h_min
        have h_pos_den : 0 < w_base v - c_w := by nlinarith
        have h_ineq : lam * (w_base v - c_w) ≤ hp.c - hp.f v :=
          (le_div_iff₀ h_pos_den).mp h_lam_le_ratio
        dsimp [f_new, c_new]; nlinarith
      · push_neg at hw_gt
        dsimp [f_new, c_new]; nlinarith
    linarith
  have h_touches : ∃ x ∈ P.Ω, f_new x = c_new := by
    refine ⟨δ_bound, hδ_in_Ω, ?_⟩
    dsimp [f_new, c_new]
    simp [hδ_f_val, hδ_cw]
  have h_nonzero : f_new ≠ 0 := by
    intro hzero
    rcases h_nonconst with ⟨y, hyF, hyw⟩
    have hy_f : hp.f y = hp.c := (hF_eq ▸ hyF).2
    have h_y : f_new y = 0 := by simpa [f_new, hy_f] using congrArg (fun f => f y) hzero
    have h_δ : f_new δ_bound = 0 := by
      simpa [f_new, hδ_f_val, hδ_cw] using congrArg (fun f => f δ_bound) hzero
    dsimp [f_new, c_new] at h_y h_δ
    have h_eq_lam : lam * w_base y = lam * c_w := by nlinarith
    have h_wy_eq_cw : w_base y = c_w := mul_left_cancel₀ (ne_of_gt hlam_pos) h_eq_lam
    rw [h_wy_eq_cw] at hyw; exact lt_irrefl _ hyw
  let G : Set (CoeffVec n) := {x | x ∈ P.Ω ∧ f_new x = c_new}
  have hG_exposed : IsExposedFace P G :=
    ⟨{ f := f_new, c := c_new, nonzero := h_nonzero, upper_bound := h_support, touches := h_touches }, rfl⟩
  have hδ_in_G : δ_bound ∈ G := by
    refine ⟨hδ_in_Ω, ?_⟩
    dsimp [f_new, c_new]
    simp [hδ_f_val, hδ_cw]
  have h_v_strict_not_F : ∀ v ∈ P.vertices, v ∉ F → f_new v < c_new := by
    intro v hv hv_notF
    have hv_f_strict : hp.f v < hp.c := by
      by_contra h_eq
      have h_le : hp.f v ≤ hp.c := hp.upper_bound v ((subset_convexHull ℝ _) hv)
      have h_eq' : hp.f v = hp.c := le_antisymm h_le (not_lt.mp h_eq)
      exact hv_notF (hF_eq ▸ ⟨(subset_convexHull ℝ _) hv, h_eq'⟩)
    by_cases hw_gt : w_base v > c_w
    · have h_mem : v ∈ S_verts := by simp [S_verts, Finset.mem_filter, hv, hw_gt]
      have h_ratio : (hp.c - hp.f v) / (w_base v - c_w) ∈ allRatios :=
        Finset.mem_image.mpr ⟨v, h_mem, rfl⟩
      have h_min : allRatios.min' hallRatios_nonempty ≤ (hp.c - hp.f v) / (w_base v - c_w) :=
        Finset.min'_le _ _ h_ratio
      have h_pos_den : 0 < w_base v - c_w := by nlinarith
      have h_lam_lt_ratio : lam < (hp.c - hp.f v) / (w_base v - c_w) := by
        dsimp [lam]
        have h_pos : 0 < allRatios.min' hallRatios_nonempty :=
          h_all_pos _ (allRatios.min'_mem hallRatios_nonempty)
        calc
          allRatios.min' hallRatios_nonempty / 2 < allRatios.min' hallRatios_nonempty := by nlinarith
          _ ≤ (hp.c - hp.f v) / (w_base v - c_w) := h_min
      have h_ineq_strict : lam * (w_base v - c_w) < hp.c - hp.f v :=
        (lt_div_iff₀ h_pos_den).mp h_lam_lt_ratio
      dsimp [f_new, c_new]; nlinarith
    · push_neg at hw_gt
      dsimp [f_new, c_new]; nlinarith
  have hG_sub_F : G ⊆ F := by
    intro x hx
    have hx_Ω : x ∈ P.Ω := hx.1
    have hx_eq : f_new x = c_new := hx.2
    by_contra hx_not_F
    have hx_hull : x ∈ convexHull ℝ (P.vertices : Set (CoeffVec n)) := by
      unfold Polytope.Ω at hx_Ω; exact hx_Ω
    rw [Finset.convexHull_eq] at hx_hull
    rcases hx_hull with ⟨w_poly, hw_nonneg, hw_sum, hx_cm⟩
    have h_exists_v_not_F : ∃ v ∈ P.vertices, w_poly v > 0 ∧ v ∉ F := by
      by_contra h_all_in_F
      push_neg at h_all_in_F
      have h_x_in_F : x ∈ F := by
        classical
        have hF_convex' : Convex ℝ F := isExposedFace_convex P ⟨hp, hF_eq⟩
        have h_sum_F : ∑ v ∈ P.vertices.filter (fun v => v ∈ F), w_poly v = 1 := by
          calc ∑ v ∈ P.vertices.filter (fun v => v ∈ F), w_poly v
            = ∑ v ∈ P.vertices, if v ∈ F then w_poly v else 0 := by simp [Finset.sum_filter]
            _ = ∑ v ∈ P.vertices, w_poly v := by
              refine Finset.sum_congr rfl fun v hv => ?_
              by_cases hvF : v ∈ F
              · simp [hvF]
              · have : w_poly v = 0 := by
                  by_contra h_ne
                  have h_pos : w_poly v > 0 :=
                    lt_of_le_of_ne (hw_nonneg v hv) (Ne.symm h_ne)
                  exact hvF (h_all_in_F v hv h_pos)
                simp [this]
            _ = 1 := hw_sum
        have h_mem : x ∈ convexHull ℝ (P.vertices.filter (fun v => v ∈ F) : Set (CoeffVec n)) := by
          rw [Finset.convexHull_eq]
          refine ⟨w_poly, ?_, h_sum_F, ?_⟩
          · intro y hy; exact hw_nonneg y ((Finset.mem_filter.mp hy).1)
          · calc
              (P.vertices.filter (fun v => v ∈ F)).centerMass w_poly (fun x => x) =
                P.vertices.centerMass w_poly (fun x => x) := by
                apply Finset.centerMass_subset (fun x => x) (Finset.filter_subset _ _)
                intro v hv hnv
                have hv_notF : v ∉ F := by
                  intro h; apply hnv; exact Finset.mem_filter.mpr ⟨hv, h⟩
                by_cases hpos : w_poly v > 0
                · exfalso; exact hv_notF (h_all_in_F v hv hpos)
                · have : w_poly v = 0 := by linarith [hw_nonneg v hv]
                  simp [this]
              _ = x := hx_cm
        exact convexHull_min (fun v hv => (Finset.mem_filter.mp hv).2) hF_convex' h_mem
      exact hx_not_F h_x_in_F
    rcases h_exists_v_not_F with ⟨v, hv, hw_pos, hv_not_F⟩
    have h_v_strict : f_new v < c_new := h_v_strict_not_F v hv hv_not_F
    have h_sum_strict : ∑ v ∈ P.vertices, w_poly v * f_new v < c_new := by
      have h_lt : ∑ v ∈ P.vertices, w_poly v * f_new v < ∑ v ∈ P.vertices, w_poly v * c_new := by
        apply Finset.sum_lt_sum
        · intro i hi; exact mul_le_mul_of_nonneg_left (h_support i
            ((subset_convexHull ℝ _) hi)) (hw_nonneg i hi)
        · refine ⟨v, hv, ?_⟩
          nlinarith
      have h_eq : ∑ v ∈ P.vertices, w_poly v * c_new = c_new := by
        simp [← Finset.sum_mul, hw_sum]
      linarith
    have h_eq_sum : f_new x = ∑ v ∈ P.vertices, w_poly v * f_new v := by
      rw [← hx_cm]; simp only [Finset.centerMass, map_sum, LinearMap.map_smul, smul_eq_mul]
      rw [hw_sum]; simp
    rw [h_eq_sum] at hx_eq; linarith
  have h_dim_lt : Module.finrank ℝ (affineSpan ℝ G).direction <
      Module.finrank ℝ (affineSpan ℝ F).direction := by
    let V_dirF := (affineSpan ℝ F).direction
    have h_dir_le : (affineSpan ℝ G).direction ≤ V_dirF :=
      AffineSubspace.direction_le (affineSpan_mono (k := ℝ) hG_sub_F)
    have h_const_on_G : ∀ x ∈ G, w_base x = c_w := by
      intro x hx
      have hx_Ω : x ∈ P.Ω := hx.1
      have hx_eq : f_new x = c_new := hx.2
      have hx_F : x ∈ F := hG_sub_F hx
      have hx_hp : hp.f x = hp.c := (hF_eq ▸ hx_F).2
      dsimp [f_new, c_new] at hx_eq
      have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
      have h_eq : lam * w_base x = lam * c_w := by nlinarith
      exact mul_left_cancel₀ hlam_ne h_eq
    have h_dir_sub_ker : (affineSpan ℝ G).direction ≤ LinearMap.ker w_base := by
      intro v hv
      have h_base : δ_bound ∈ affineSpan ℝ G := subset_affineSpan ℝ G hδ_in_G
      have h_plus : δ_bound + v ∈ affineSpan ℝ G := by
        have h_vadd : v +ᵥ δ_bound ∈ affineSpan ℝ G :=
          AffineSubspace.vadd_mem_of_mem_direction hv h_base
        simpa [vadd_eq_add, add_comm] using h_vadd
      have h_const : ∀ x ∈ affineSpan ℝ G, w_base x = c_w := by
        intro x hx
        refine affineSpan_induction hx (fun p hp => h_const_on_G p hp) ?_
        intro a u v w hu hv hw
        rw [vsub_eq_sub, vadd_eq_add]
        simp [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_sub, hu, hv, hw]
      have h_val_base : w_base δ_bound = c_w := h_const δ_bound h_base
      have h_val_plus : w_base (δ_bound + v) = c_w := h_const (δ_bound + v) h_plus
      rw [← h_val_base] at h_val_plus
      simpa using h_val_plus
    have h_dir_le_inter : (affineSpan ℝ G).direction ≤ V_dirF ⊓ LinearMap.ker w_base :=
      le_inf h_dir_le h_dir_sub_ker
    let w_V : V_dirF →ₗ[ℝ] ℝ := w_base.comp V_dirF.subtype
    haveI : FiniteDimensional ℝ (↥V_dirF) := by infer_instance
    have hw_V_nonzero : w_V ≠ 0 := by
      intro hzero
      rcases h_nonconst with ⟨y, hyF, hyw⟩
      have hv : (y - δ_bound) ∈ V_dirF :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ F hyF) hδ_affF
      have h_val : w_V ⟨y - δ_bound, hv⟩ = w_base (y - δ_bound) := by
        simp [w_V, LinearMap.comp_apply, Submodule.subtype_apply]
      have h_w_y : w_base y = w_base (y - δ_bound) + w_base δ_bound := by simp
      have h_w_diff_lt : w_base (y - δ_bound) < 0 := by
        rw [h_w_y] at hyw
        have hδ_cw_symm : w_base δ_bound = c_w := hδ_cw
        nlinarith
      have h_zero : w_V ⟨y - δ_bound, hv⟩ = 0 := by
        simp [hzero]
      have : w_base (y - δ_bound) = 0 := by
        simpa [h_val] using h_zero
      nlinarith
    have h_dim_ker : Module.finrank ℝ (LinearMap.ker w_V) = Module.finrank ℝ (↥V_dirF) - 1 := by
      have hg_surj : LinearMap.range w_V = ⊤ := by
        apply LinearMap.range_eq_top.mpr
        intro y
        have ⟨x, hx⟩ : ∃ x, w_V x ≠ 0 := by
          by_contra h_allzero
          apply hw_V_nonzero
          apply LinearMap.ext
          simpa using not_exists.mp h_allzero
        refine ⟨(y / w_V x) • x, ?_⟩
        simp [LinearMap.map_smul, smul_eq_mul, hx, mul_comm]
        grind

      have h_finrank_range : Module.finrank ℝ (LinearMap.range w_V) = 1 := by
        rw [hg_surj]; simp
      have h_total : Module.finrank ℝ (LinearMap.range w_V) + Module.finrank ℝ (LinearMap.ker w_V) =
        Module.finrank ℝ (↥V_dirF) := LinearMap.finrank_range_add_finrank_ker w_V
      rw [h_finrank_range] at h_total
      omega
    have h_V_finrank : Module.finrank ℝ (↥V_dirF) = Module.finrank ℝ V_dirF := rfl
    have h_iso : Module.finrank ℝ (LinearMap.ker w_V) = Module.finrank ℝ (↥(V_dirF ⊓ LinearMap.ker w_base)) := by
      let φ : LinearMap.ker w_V ≃ₗ[ℝ] ↥(V_dirF ⊓ LinearMap.ker w_base) := {
        toFun := fun x => ⟨x.1.1, ⟨x.1.2,  by
          have h_ker : w_V x.1 = 0 := x.2
          simp
          rw [LinearMap.comp_apply] at h_ker
          simpa [Submodule.subtype_apply] using h_ker
          ⟩⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, by
          simpa [w_V, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.mem_ker] using y.2.2⟩
        left_inv := fun x => by ext; simp
        right_inv := fun y => by ext; simp
        map_add' := fun x y => by ext; simp
        map_smul' := fun a x => by ext; simp
      }
      exact LinearEquiv.finrank_eq φ
    have h_dim_inter : Module.finrank ℝ (↥(V_dirF ⊓ LinearMap.ker w_base)) = Module.finrank ℝ (↥V_dirF) - 1 := by
      rw [← h_iso, h_dim_ker]
    calc Module.finrank ℝ (affineSpan ℝ G).direction
      ≤ Module.finrank ℝ (↥(V_dirF ⊓ LinearMap.ker w_base)) := Submodule.finrank_mono h_dir_le_inter
      _ = Module.finrank ℝ (↥V_dirF) - 1 := h_dim_inter
      _ = Module.finrank ℝ V_dirF - 1 := rfl
      _ < Module.finrank ℝ V_dirF := by
        have h_V_ge_2 : Module.finrank ℝ V_dirF ≥ 2 := hF_dim
        omega
  exact ⟨G, hG_exposed, hδ_in_G, h_dim_lt⟩

public lemma exists_proper_subface_of_boundary_point {n : ℕ} (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F) (δ_bound : CoeffVec n)
    (hδ_bound_in_F : δ_bound ∈ F) (hδ_bound_front : δ_bound ∈ frontier F)
    (hδ_bound_not_relint : δ_bound ∉ intrinsicInterior ℝ F)
    (hF_dim : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 2) :
    ∃ (G : Set (CoeffVec n)), IsExposedFace P G ∧ δ_bound ∈ G ∧
    Module.finrank ℝ (affineSpan ℝ G).direction < Module.finrank ℝ (affineSpan ℝ F).direction := by
  -- ----------------------------------------------------------------
  -- SETUP: Extract the supporting hyperplane and basic facts about F
  -- ----------------------------------------------------------------
  obtain ⟨hp, hF_eq⟩ := hF_exp
  have hF_compact : IsCompact F :=
    isExposedFace_isCompact P ⟨hp, hF_eq⟩
  have hF_convex : Convex ℝ F :=
    isExposedFace_convex P ⟨hp, hF_eq⟩
  have hF_sub_Ω : F ⊆ P.Ω :=
    isExposedFace_subset_Ω ⟨hp, hF_eq⟩
  have hF_closed : IsClosed F :=
    hF_compact.isClosed
  have hδ_in_ExF : δ_bound ∈ ExposedFace hp :=
    hF_eq ▸ hδ_bound_in_F
  have hδ_in_Ω : δ_bound ∈ P.Ω :=
    hF_sub_Ω hδ_bound_in_F
  have hδ_f_val : hp.f δ_bound = hp.c :=
    hδ_in_ExF.2
  have h_int_nonempty : (interior P.Ω).Nonempty :=
    P.interior_nonempty
  have hΩ_convex : Convex ℝ P.Ω :=
    convex_convexHull ℝ _
  have hΩ_closed : IsClosed P.Ω :=
    P.isCompact.isClosed
  -- ----------------------------------------------------------------
  -- STEP 1: δ_bound is not in the relative interior of F
  -- ----------------------------------------------------------------
  have hδ_not_relint : δ_bound ∉ interior F := by
    rw [frontier_eq_for_closed F hF_closed] at hδ_bound_front
    exact hδ_bound_front.2
  -- ----------------------------------------------------------------
  -- STEP 2: F has nonempty relative interior
  -- Since F is a compact convex set with affine dimension ≥ 2,
  -- its relative interior is nonempty.
  -- ----------------------------------------------------------------
  have hF_relint_nonempty : (intrinsicInterior ℝ F).Nonempty :=
    Set.Nonempty.intrinsicInterior (isExposedFace_convex P ⟨hp, hF_eq⟩)
      ⟨δ_bound, hδ_bound_in_F⟩
  -- ----------------------------------------------------------------
  -- STEP 3: δ_bound is on the frontier of P.Ω
  -- Any point on the relative boundary of F lies on the boundary of Ω
  -- ----------------------------------------------------------------
  have hδ_in_front_Ω : δ_bound ∈ frontier P.Ω :=
    frontier_of_exposed_face_implies_frontier_of_polytope P F hp hF_eq δ_bound
      hδ_bound_in_F hδ_bound_front
  have hδ_not_int_Ω : δ_bound ∉ interior P.Ω :=
    frontier_point_not_interior P δ_bound hδ_in_front_Ω
  -- ----------------------------------------------------------------
  -- STEP 4: Find g_Ω via Hahn-Banach separation of int(Ω) from δ_bound
  -- Since δ_bound ∉ int(Ω) and int(Ω) is convex open nonempty,
  -- there exists a continuous linear functional strictly separating them.
  -- ----------------------------------------------------------------
  have hΩ_int_convex : Convex ℝ (interior P.Ω) :=
    hΩ_convex.interior
  obtain ⟨f_Ω, hf_Ω_strict⟩ :=
    geometric_hahn_banach_open_point
      hΩ_int_convex isOpen_interior hδ_not_int_Ω
  let g_Ω : CoeffVec n →ₗ[ℝ] ℝ := f_Ω.toLinearMap
  have hg_Ω_strict : ∀ x ∈ interior P.Ω, g_Ω x < g_Ω δ_bound :=
    hf_Ω_strict
  -- ----------------------------------------------------------------
  -- STEP 5: g_Ω is an upper bound for all of Ω at δ_bound
  -- By density of int(Ω) in Ω (convexity + nonempty interior),
  -- the strict inequality extends to a weak inequality on Ω.
  -- ----------------------------------------------------------------
  let g_c : ℝ := g_Ω δ_bound
  have hg_Ω_support : ∀ x ∈ P.Ω, g_Ω x ≤ g_Ω δ_bound := by
    intro x hx
    have h_closed_le : IsClosed {y : CoeffVec n | g_Ω y ≤ g_Ω δ_bound} :=
      isClosed_Iic.preimage
        (LinearMap.continuous_of_finiteDimensional g_Ω)
    have h_int_sub : interior P.Ω ⊆ {y | g_Ω y ≤ g_Ω δ_bound} :=
      fun y hy => le_of_lt (hg_Ω_strict y hy)
    have h_closure_Ω : closure (interior P.Ω) = P.Ω :=
      calc
        closure (interior P.Ω) = closure P.Ω :=
          hΩ_convex.closure_interior_eq_closure_of_nonempty_interior h_int_nonempty
        _ = P.Ω := hΩ_closed.closure_eq
    have h_Ω_sub : P.Ω ⊆ {y | g_Ω y ≤ g_Ω δ_bound} := by
      calc P.Ω = closure (interior P.Ω) := h_closure_Ω.symm
        _ ⊆ closure {y | g_Ω y ≤ g_Ω δ_bound} := closure_mono h_int_sub
        _ = {y | g_Ω y ≤ g_Ω δ_bound} := h_closed_le.closure_eq
    exact h_Ω_sub hx
  -- ----------------------------------------------------------------
  -- STEP 6: Check if g_Ω is non-constant on F.
  -- If yes, use the existing construction to get a proper subface.
  -- If g_Ω is constant on F, use a Hahn-Banach separation in affF to construct
  -- a proper subface of dim ≥ 1.
  -- ----------------------------------------------------------------

  by_cases hg_Ω_nonconst : ∃ x₀ ∈ ExposedFace hp, g_Ω x₀ < g_Ω δ_bound
  · -- Case A: g_Ω is non-constant on F → use the existing construction
    -- ----------------------------------------------------------------
    -- STEP 7: g_Ω is nonzero
    -- ----------------------------------------------------------------
    have hg_Ω_nonzero : g_Ω ≠ 0 := by
      obtain ⟨x₀, _, hx₀_lt⟩ := hg_Ω_nonconst
      intro h_zero
      simp [g_Ω, h_zero] at hx₀_lt
    -- ----------------------------------------------------------------
    -- STEP 8: Find a direction v ∈ dir(F) with g_Ω v > 0
    -- ----------------------------------------------------------------
    obtain ⟨x₀_F, hx₀_in_ExF, hx₀_lt⟩ := hg_Ω_nonconst
    have hx₀_in_F : x₀_F ∈ F := hF_eq ▸ hx₀_in_ExF
    let v_dir : CoeffVec n := δ_bound - x₀_F
    have hv_in_dir : v_dir ∈ (affineSpan ℝ (ExposedFace hp)).direction :=
      AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ _ hδ_in_ExF) (subset_affineSpan ℝ _ hx₀_in_ExF)
    have hgv_pos : g_Ω v_dir > 0 := by
      simp only [v_dir, map_sub]
      linarith
    -- ----------------------------------------------------------------
    -- STEP 9: hp.f kills the direction v_dir
    -- ----------------------------------------------------------------
    have hfv_zero : hp.f v_dir = 0 :=
      exposed_face_direction_kills_vector hp rfl δ_bound v_dir hδ_in_ExF hv_in_dir
    -- ----------------------------------------------------------------
    -- STEP 10: Construct G as the exposed face defined by hp.f + g_Ω
    -- ----------------------------------------------------------------
    let G : Set (CoeffVec n) :=
      {x | x ∈ P.Ω ∧ (hp.f + g_Ω) x = hp.c + g_c}
    have hG_exposed : IsExposedFace P G :=
      sum_supporting_hyperplane_exposed_face hp g_Ω v_dir δ_bound
        hδ_in_Ω hδ_f_val hg_Ω_support hfv_zero hgv_pos
    -- ----------------------------------------------------------------
    -- STEP 11: δ_bound ∈ G
    -- ----------------------------------------------------------------
    have hδ_in_G : δ_bound ∈ G := by
      refine ⟨hδ_in_Ω, ?_⟩
      simp only [G, Pi.add_apply, LinearMap.add_apply]
      linarith [hδ_f_val]
    -- ----------------------------------------------------------------
    -- STEP 12: G ⊆ ExposedFace hp  (i.e., G ⊆ F)
    -- ----------------------------------------------------------------
    have hG_sub_ExF : G ⊆ ExposedFace hp := by
      intro x ⟨hx_Ω, hx_sum⟩
      have h_fx_le : hp.f x ≤ hp.c := hp.upper_bound x hx_Ω
      have h_gx_le : g_Ω x ≤ g_c := hg_Ω_support x hx_Ω
      have h_fx_eq : hp.f x = hp.c := by
        simp only [Pi.add_apply, LinearMap.add_apply] at hx_sum
        linarith
      exact ⟨hx_Ω, h_fx_eq⟩
    -- ----------------------------------------------------------------
    -- STEP 13: dim(G) < dim(F)
    -- ----------------------------------------------------------------
    have hG_dim_lt : Module.finrank ℝ (affineSpan ℝ G).direction <
        Module.finrank ℝ (affineSpan ℝ F).direction := by
      have hG_dir_le_ker :
          (affineSpan ℝ G).direction ≤
          LinearMap.ker (hp.f + g_Ω : CoeffVec n →ₗ[ℝ] ℝ) := by
        have h_const_on_G : ∀ x ∈ G, (hp.f + g_Ω) x = hp.c + g_c :=
          fun x hx => hx.2
        exact direction_sub_ker_of_exposed_intersection hp g_Ω δ_bound G
          hδ_in_G h_const_on_G
      have hG_dir_le_F_dir :
          (affineSpan ℝ G).direction ≤
          (affineSpan ℝ (ExposedFace hp)).direction :=
        AffineSubspace.direction_le (affineSpan_mono (k := ℝ) hG_sub_ExF)
      have hv_not_ker :
          v_dir ∉ LinearMap.ker (hp.f + g_Ω : CoeffVec n →ₗ[ℝ] ℝ) := by
        simp only [LinearMap.mem_ker, Pi.add_apply, LinearMap.add_apply,
          hfv_zero, zero_add]
        linarith
      have hv_not_dirG :
          v_dir ∉ (affineSpan ℝ G).direction :=
        fun h => hv_not_ker (hG_dir_le_ker h)
      have h_dir_ne :
          (affineSpan ℝ G).direction ≠
          (affineSpan ℝ (ExposedFace hp)).direction :=
        fun h_eq => hv_not_dirG (h_eq ▸ hv_in_dir)
      have h_dir_strict :
          (affineSpan ℝ G).direction <
          (affineSpan ℝ (ExposedFace hp)).direction :=
        lt_of_le_of_ne hG_dir_le_F_dir h_dir_ne
      have h_lt_ExF :=
        Submodule.finrank_lt_finrank_of_lt h_dir_strict
      rw [hF_eq]
      exact h_lt_ExF
    exact ⟨G, hG_exposed, hδ_in_G, hG_dim_lt⟩
  · -- Case B: g_Ω is constant on F. Since δ_bound ∉ ri(F) (hδ_bound_not_relint),
    -- there exists a supporting functional of P.Ω at δ_bound not in the normal cone of F.
    -- The exposed face is then a strict subface of F containing δ_bound.
    have hg_const_on_F : ∀ x ∈ F, g_Ω x = g_c := by
      intro x hx
      have hx_in_Ω : x ∈ P.Ω := hF_sub_Ω hx
      have h_gx_le_gc : g_Ω x ≤ g_c := hg_Ω_support x hx_in_Ω
      have h_gx_ge_gc : g_Ω x ≥ g_c := by
        by_contra h_lt
        apply hg_Ω_nonconst
        refine ⟨x, hF_eq ▸ hx, ?_⟩
        simpa [g_c] using h_lt
      exact le_antisymm h_gx_le_gc h_gx_ge_gc
    -- Step B: Separate δ_bound from intrinsicInterior ℝ F within affF.
    -- This constructs a functional w_base that is strictly larger at δ_bound
    -- than at any point of intrinsicInterior ℝ F.
    let V_dir : Submodule ℝ (CoeffVec n) := (affineSpan ℝ F).direction
    let affF := affineSpan ℝ F
    have hδ_affF : δ_bound ∈ affF := subset_affineSpan ℝ F hδ_bound_in_F

    -- Transport the problem to V_dir using τ : V_dir ≃ₜ affF (affine homeomorphism)
    let τ : V_dir ≃ₜ affF := {
      toFun := fun v => ⟨δ_bound +ᵥ (v : CoeffVec n), by
        have h := AffineSubspace.vadd_mem_of_mem_direction v.2 hδ_affF
        simpa [vadd_eq_add, add_comm] using h⟩
      invFun := fun p => ⟨(p : CoeffVec n) - δ_bound,
        AffineSubspace.vsub_mem_direction p.property hδ_affF⟩
      left_inv := by intro v; ext; simp [vadd_vsub]
      right_inv := by intro p; ext; simp [vsub_vadd]
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ ?_
        · exact (continuous_const.add continuous_subtype_val : Continuous (fun (v : V_dir) => δ_bound + (v : CoeffVec n)))
    }

    let A : Set V_dir := τ ⁻¹' ((Subtype.val : affF → CoeffVec n) ⁻¹' F)
    let intF_preimage : Set (affineSpan ℝ F) :=
      (Subtype.val : (affineSpan ℝ F) → CoeffVec n) ⁻¹' (intrinsicInterior ℝ F)
    let C : Set V_dir := τ ⁻¹' intF_preimage
    -- Define the coercion from the affine subspace to the ambient space
    -- let val : affF → CoeffVec n := Subtype.val

    -- Restrict F to the affine span explicitly
    -- let F_aff : Set affF := val ⁻¹' F

    -- let A : Set V_dir := τ ⁻¹' F_aff
    -- let C : Set V_dir := τ ⁻¹' (intrinsicInterior ℝ F_aff)

    have h_int_eq :
      (Subtype.val : affF → CoeffVec n) ⁻¹' (intrinsicInterior ℝ F) =
      interior ((Subtype.val : affF → CoeffVec n) ⁻¹' F : Set affF) := by
      rw [intrinsicInterior]
      rw [Set.preimage_image_eq _ Subtype.coe_injective]


    have hC_eq_interior_A : C = interior A := by
      -- Step 1: Unfold C to show it equals τ⁻¹' (val⁻¹' (intrinsicInterior ℝ F))

      have hC_def : C = τ ⁻¹' ((Subtype.val : affF → CoeffVec n) ⁻¹' (intrinsicInterior ℝ F)) := by
        ext x
        simp only [C, intF_preimage, Set.mem_preimage]





      -- Step 2: Replace intrinsicInterior with interior of preimage using h_int_eq
      have h_step2 : τ ⁻¹' ((Subtype.val : affF → CoeffVec n) ⁻¹' (intrinsicInterior ℝ F)) =
                    τ ⁻¹' (interior ((Subtype.val : affF → CoeffVec n) ⁻¹' F)) := by
        rw [h_int_eq]

      -- Step 3: Pull τ⁻¹' inside interior using homeomorphism property
      have h_step3 : τ ⁻¹' (interior ((Subtype.val : affF → CoeffVec n) ⁻¹' F)) =
                    interior (τ ⁻¹' ((Subtype.val : affF → CoeffVec n) ⁻¹' F)) := by
        rw [τ.preimage_interior]

      -- Step 4: Show that τ⁻¹' (val⁻¹' F) = A
      have hA_def : τ ⁻¹' ((Subtype.val : affF → CoeffVec n) ⁻¹' F) = A := by
        ext x
        simp only [A, τ]

      -- Chain all equalities together
      rw [hC_def, h_step2, h_step3, hA_def]


    have hA_convex : Convex ℝ A := by
      dsimp [A]
      let φ : V_dir →ᵃ[ℝ] CoeffVec n :=
        AffineMap.const ℝ V_dir δ_bound + (Submodule.subtype (V_dir : Submodule ℝ (CoeffVec n))).toAffineMap
      have hF_convex' : Convex ℝ F := by
        trivial

      have h_equiv : τ ⁻¹' ((Subtype.val : affF → CoeffVec n)⁻¹' F) = φ⁻¹' F := by
        ext v; simp [τ, φ, vadd_eq_add]
      rw [h_equiv]
      exact hF_convex'.affine_preimage φ
    have hC_convex : Convex ℝ (C : Set V_dir) := by
      rw [hC_eq_interior_A]; exact hA_convex.interior
    have hC_open : IsOpen (C : Set V_dir) := by
      rw [hC_eq_interior_A]; exact isOpen_interior
    have h0_notin_C : (0 : V_dir) ∉ C := by
      intro h
      have hτ0 : (τ 0 : CoeffVec n) = δ_bound := by
        simp [τ, vadd_eq_add]
      have h_mem_ambient : δ_bound ∈ intrinsicInterior ℝ F := by
        simpa [C, intF_preimage, hτ0, Set.mem_preimage] using h
      exact hδ_bound_not_relint h_mem_ambient

    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hC_convex hC_open h0_notin_C
    have hf_zero : f (0 : V_dir) = 0 := by simp
    let f_lin : V_dir →ₗ[ℝ] ℝ := f.toLinearMap
    obtain ⟨w_base, hw_base⟩ := LinearMap.exists_extend (p := V_dir) f_lin
    let c_w := w_base δ_bound

    have h_on_intF : ∀ y ∈ intrinsicInterior ℝ F, w_base y < c_w := by
      intro y hy
      have hv : (y - δ_bound) ∈ V_dir :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ F (intrinsicInterior_subset hy)) hδ_affF
      set v : V_dir := ⟨y - δ_bound, hv⟩ with hv_def
      have hv_C : v ∈ C := by
        dsimp [C, intF_preimage, v]
        simpa [τ, vadd_eq_add, Set.mem_preimage] using hy
      have hf_lt : f v < f 0 := hf v hv_C
      calc
        w_base y = w_base (y - δ_bound) + w_base δ_bound := by simp
        _ = w_base (v : CoeffVec n) + c_w := by
            simp [v, c_w]
        _ = (w_base.comp V_dir.subtype) v + c_w := rfl
        _ = f_lin v + c_w := by rw [hw_base]
        _ = f v + c_w := rfl
        _ < 0 + c_w := by linarith
        _ = c_w := by simp

    have h_closure_intF : closure (intrinsicInterior ℝ F) = F := by
      apply subset_antisymm
      · exact closure_minimal intrinsicInterior_subset hF_compact.isClosed
      · intro x hx
        rcases Set.Nonempty.intrinsicInterior hF_convex ⟨δ_bound, hδ_bound_in_F⟩ with ⟨y, hy⟩
        have h_cont : Continuous (fun (t : ℝ) => (1 - t) • x + t • y) := by
          refine Continuous.add ?_ ?_
          · -- (1 - t) • x is continuous in t
            refine (continuous_const.sub continuous_id).smul continuous_const
          · -- t • y is continuous in t
            exact continuous_id.smul continuous_const

        have h_tendsto' : Filter.Tendsto (fun (t : ℝ) => (1 - t) • x + t • y) (nhds (0 : ℝ)) (nhds x) := by
          simpa using h_cont.tendsto (0 : ℝ)
        have h_tendsto : Filter.Tendsto (fun (t : ℝ) => (1 - t) • x + t • y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds x) :=
          h_tendsto'.mono_left nhdsWithin_le_nhds
        have h_nhd : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          refine ⟨Set.Ioo (-1 : ℝ) 1, IsOpen.mem_nhds isOpen_Ioo (by norm_num), ?_⟩
          rintro x ⟨⟨hx1, hx2⟩, hxpos⟩
          exact ⟨hxpos, hx2⟩
        have h_event : Filter.Eventually (fun t => (1 - t) • x + t • y ∈ intrinsicInterior ℝ F) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
          refine Filter.mem_of_superset h_nhd ?_
          intro t ht
          exact mem_intrinsicInterior_add_smul F hF_convex hx hy ht.1 ht.2
        haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := by infer_instance
        exact mem_closure_of_tendsto h_tendsto h_event

    have hw_nonpos_F : ∀ x ∈ F, w_base x ≤ c_w := by
      intro x hx
      have hx_closure : x ∈ closure (intrinsicInterior ℝ F) := by
        rw [h_closure_intF]; exact hx
      have h_closed_le : IsClosed {y | w_base y ≤ c_w} :=
        isClosed_Iic.preimage (LinearMap.continuous_of_finiteDimensional w_base)
      have h_mem : x ∈ closure {y | w_base y ≤ c_w} :=
        closure_mono (fun y hy => le_of_lt (h_on_intF y hy)) hx_closure
      rwa [h_closed_le.closure_eq] at h_mem

    have h_nonconst : ∃ x ∈ F, w_base x < c_w := by
      rcases Set.Nonempty.intrinsicInterior hF_convex ⟨δ_bound, hδ_bound_in_F⟩ with ⟨y, hy⟩
      exact ⟨y, intrinsicInterior_subset hy, h_on_intF y hy⟩

    -- Step C: Choose λ > 0 to ensure hp.f + λ • w_base supports P.Ω at δ_bound.
    let S_verts : Finset (CoeffVec n) := P.vertices.filter fun v => w_base v > c_w
    by_cases hS_empty : S_verts = ∅
    · -- Case B1: w_base ≤ c_w on all vertices → λ = 1 works
      exact exists_proper_subface_caseB1 P F hp hF_eq δ_bound
        hδ_in_Ω hδ_f_val hδ_affF hF_dim
        w_base c_w rfl h_nonconst hS_empty
    · -- Case B2: Some vertex has w_base v > c_w → choose λ small enough via ratios
      exact exists_proper_subface_caseB2 P F hp hF_eq δ_bound
        hδ_in_Ω hδ_f_val hδ_affF hF_dim
        w_base c_w rfl hw_nonpos_F h_nonconst hS_empty

end CoeffBox
