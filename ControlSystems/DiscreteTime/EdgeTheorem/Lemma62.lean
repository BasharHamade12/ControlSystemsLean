module

public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeTheoremDefs
public import ControlSystems.DiscreteTime.EdgeTheorem.BasicLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.PreliminaryLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.ExposedFaceLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.SubfaceConstruction
public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeDescent
public import ControlSystems.DiscreteTime.EdgeTheorem.Lemma61

@[expose] public section

open Polynomial Affine FiniteDimensional LinearMap Set Complex
open Filter Topology

namespace CoeffBox

/--
The relative boundary of a set `F` (with respect to its affine hull).
For a convex set, this is `F \ intrinsicInterior ℝ F`.

Notation: `relativeBoundary F` can be used via `relativeBoundary F`.
-/
def relativeBoundary (F : Set (CoeffVec n)) : Set (CoeffVec n) :=
  F \ intrinsicInterior ℝ F


/-- If `W` is compact, then `RootSpaceSet W` is closed in ℂ.
Proof: `evalAtComplex s δ = ((polyOfVec δ).map (algebraMap ℝ ℂ)).eval s` is jointly continuous
in `(δ, s)`, so its zero set intersected with `W × ℂ` is closed. Projecting to ℂ via `snd`
preserves closedness because `W` is compact. -/
lemma rootSpaceSet_isClosed_of_isCompact {n : ℕ} {W : Set (CoeffVec n)} (hW : IsCompact W) :
    IsClosed (RootSpaceSet W) := by
  haveI : CompactSpace (Subtype W) := isCompact_iff_compactSpace.mp hW
  have h_closed_map : IsClosedMap (Prod.snd : (Subtype W) × ℂ → ℂ) :=
    isClosedMap_snd_of_compactSpace
  let Z : Set ((Subtype W) × ℂ) := { p | ((polyOfVec p.1.val).map (algebraMap ℝ ℂ)).eval p.2 = 0 }
  have hZ_closed : IsClosed Z := by
    have h_cont : Continuous (fun (p : (Subtype W) × ℂ) => ((polyOfVec p.1.val).map (algebraMap ℝ ℂ)).eval p.2) := by
      have h_eq : ∀ (δ : CoeffVec n) (s : ℂ), ((polyOfVec δ).map (algebraMap ℝ ℂ)).eval s =
        ∑ j : Fin (n+1), (algebraMap ℝ ℂ : ℝ → ℂ) (δ j) * (s ^ (j.val : ℕ)) := by
        intro δ s
        calc
          ((polyOfVec δ).map (algebraMap ℝ ℂ)).eval s = (polyOfVec δ).eval₂ (algebraMap ℝ ℂ) s := by
            simp [Polynomial.eval_map]
          _ = (∑ j : Fin (n+1), Polynomial.monomial j.val (δ j)).eval₂ (algebraMap ℝ ℂ) s := rfl
          _ = ∑ j : Fin (n+1), ((Polynomial.monomial j.val (δ j)).eval₂ (algebraMap ℝ ℂ) s) := by
            simp [Polynomial.eval₂_finset_sum]
          _ = ∑ j : Fin (n+1), (algebraMap ℝ ℂ : ℝ → ℂ) (δ j) * (s ^ (j.val : ℕ)) := by
            simp [Polynomial.eval₂_monomial]
      have h_sum : Continuous (λ (p : (Subtype W) × ℂ) =>
        ∑ j : Fin (n+1), (algebraMap ℝ ℂ : ℝ → ℂ) (p.1.val j) * (p.2 ^ (j.val : ℕ))) := by
        refine continuous_finset_sum _ (λ j _ => ?_)
        refine Continuous.mul ?_ ?_
        · refine (continuous_algebraMap ℝ ℂ).comp ?_
          refine ((continuous_apply j).comp continuous_subtype_val).comp continuous_fst
        · exact continuous_snd.pow (j.val : ℕ)
      -- rewrite using h_eq
      have h_rewrite : (fun (p : (Subtype W) × ℂ) => ((polyOfVec p.1.val).map (algebraMap ℝ ℂ)).eval p.2) =
        (fun (p : (Subtype W) × ℂ) => ∑ j : Fin (n+1), (algebraMap ℝ ℂ : ℝ → ℂ) (p.1.val j) * (p.2 ^ (j.val : ℕ))) := by
        ext p; exact h_eq p.1.val p.2
      rw [h_rewrite]
      exact h_sum
    exact (isClosed_singleton.preimage h_cont)
  have h_image : Prod.snd '' Z = RootSpaceSet W := by
    ext s; constructor
    · rintro ⟨a, ha, ha_eq⟩
      rcases a with ⟨x, s'⟩
      have h_s'_eq_s : s' = s := by simpa using ha_eq
      have hzero : ((polyOfVec x.val).map (algebraMap ℝ ℂ)).eval s = 0 := by
        rw [← h_s'_eq_s]
        exact ha
      rw [RootSpaceSet, Set.mem_setOf_eq]
      refine ⟨x.val, x.property, ?_⟩
      rw [Polynomial.IsRoot, hzero]
    · rintro ⟨δ, hδ, hroot⟩
      let x : Subtype W := ⟨δ, hδ⟩
      refine ⟨(x, s), ?_, rfl⟩
      rw [Polynomial.IsRoot] at hroot
      exact hroot
  rw [← h_image]
  exact h_closed_map Z hZ_closed

/-- If `F` is a compact convex set, then any ray starting from a point in `F`
    along a nonzero direction eventually exits `F`. -/
lemma ray_escapes_compact_convex {n : ℕ} {F : Set (CoeffVec n)} (hF_compact : IsCompact F)
    (_hF_convex : Convex ℝ F) (δ : CoeffVec n) (hδ_in_F : δ ∈ F) (v : CoeffVec n)
    (hv_ne : v ≠ 0) : ∃ (t : ℝ), 0 < t ∧ δ + t • v ∉ F := by
  rcases Metric.isBounded_iff.mp hF_compact.isBounded with ⟨C, hC⟩
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  let t := (|C| + 1) / ‖v‖
  have ht_pos : 0 < t := div_pos (by have : 0 ≤ |C| := abs_nonneg C; linarith) hv_norm_pos
  by_cases h_contra : δ + t • v ∈ F
  · exfalso
    have h_dist : dist (δ + t • v) δ = t * ‖v‖ := by
      rw [dist_eq_norm]
      have h_sub : δ + t • v - δ = t • v := by abel
      have ht_nonneg : 0 ≤ t := ht_pos.le
      rw [h_sub, norm_smul, Real.norm_eq_abs t, abs_of_nonneg ht_nonneg]
    have h_le : dist (δ + t • v) δ ≤ C := by
      apply hC
      · exact h_contra
      · exact hδ_in_F
    have h_C_lt : C < |C| + 1 := by have : C ≤ |C| := le_abs_self C; linarith
    rw [h_dist] at h_le
    have h_t_mul : t * ‖v‖ = |C| + 1 := div_mul_cancel₀ (|C| + 1) (ne_of_gt hv_norm_pos)
    rw [h_t_mul] at h_le
    linarith
  · exact ⟨t, ht_pos, h_contra⟩

/-- Real case of Lemma 6.2:
    If `s*` is a real point on the frontier of `RootSpaceSet F` (where `F` is an
    exposed face of dimension 2), then `s*` is a root of a coefficient vector
    on the relative boundary of `F`. -/
theorem lemma62_real_case {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hF_dim_2 : Module.finrank ℝ (affineSpan ℝ F).direction = 2)
    (s_star : ℂ) (hs_star_front : s_star ∈ frontier (RootSpaceSet F)) (hreal : s_star.im = 0) :
    s_star ∈ RootSpaceSet (relativeBoundary F) := by
  have hF_compact : IsCompact F := isExposedFace_isCompact P hF_exp
  have hF_convex : Convex ℝ F := isExposedFace_convex P hF_exp
  have h_s_star_eq : s_star = (s_star.re : ℂ) := by
    apply Complex.ext <;> simp [hreal]
  have h_root_closed : IsClosed (RootSpaceSet F) :=
    rootSpaceSet_isClosed_of_isCompact hF_compact
  have hs_star_in_RF : s_star ∈ RootSpaceSet F := by
    have h_sub : frontier (RootSpaceSet F) ⊆ RootSpaceSet F := by
      calc
        frontier (RootSpaceSet F) ⊆ closure (RootSpaceSet F) := frontier_subset_closure
        _ = RootSpaceSet F := h_root_closed.closure_eq
    exact h_sub hs_star_front
  rcases hs_star_in_RF with ⟨δ_star, hδ_star_in_F, hδ_star_root⟩
  have hδ_star_in_Psr : δ_star ∈ (P_sr n s_star.re : Set (CoeffVec n)) :=
    mem_P_sr_of_isRoot s_star.re δ_star (by
      rw [h_s_star_eq] at hδ_star_root
      exact hδ_star_root)
  by_cases hδ_star_relint : δ_star ∈ intrinsicInterior ℝ F
  · let U : Submodule ℝ (CoeffVec n) := P_sr n s_star.re
    let V : Submodule ℝ (CoeffVec n) := (affineSpan ℝ F).direction
    have hU_dim : Module.finrank ℝ U = n := P_sr_dimension s_star.re
    have hV_dim_ge_2 : Module.finrank ℝ V ≥ 2 := by rw [hF_dim_2]
    have h_inter_dim_ge_1 : Module.finrank ℝ (↥(U ⊓ V)) ≥ 1 :=
      finrank_inf_ge_one U V hU_dim hV_dim_ge_2
    have h_inter_finrank_pos : 0 < Module.finrank ℝ (↥(U ⊓ V)) := by omega
    have h_inter_nontrivial : Nontrivial ↥(U ⊓ V) :=
      Module.nontrivial_of_finrank_pos h_inter_finrank_pos
    obtain ⟨v_sub, hv_sub_ne⟩ := exists_ne (0 : ↥(U ⊓ V))
    let v : CoeffVec n := v_sub.val
    have hv_ne : v ≠ 0 := by
      intro h; apply hv_sub_ne; exact Subtype.ext h
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
      ray_escapes_compact_convex hF_compact hF_convex δ_star hδ_star_in_F v hv_ne
    let S : Set ℝ := {t | 0 ≤ t ∧ δ_star + t • v ∈ F}
    have hS_nonempty : S.Nonempty := ⟨0, ⟨by norm_num, by simpa using hδ_star_in_F⟩⟩
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
    have h_bdd_above : BddAbove S := by
      refine ⟨t_out, ?_⟩
      rintro t ⟨ht_nonneg, ht_mem⟩
      by_contra! h_gt
      have ha_nonneg : 0 ≤ t_out / t := div_nonneg (by linarith) (by linarith)
      have hdiv : t_out / t ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      have hb_nonneg : 0 ≤ 1 - t_out / t := by linarith
      have hsum : (t_out / t : ℝ) + (1 - t_out / t) = 1 := by ring
      have hstar : StarConvex ℝ (δ_star + t • v) F := hF_convex ht_mem
      have h_conv : ((t_out / t : ℝ) • (δ_star + t • v) + (1 - t_out / t) • δ_star) = δ_star + t_out • v := by
        calc
          (t_out / t : ℝ) • (δ_star + t • v) + (1 - t_out / t) • δ_star
              = (t_out / t) • δ_star + (t_out / t) • (t • v) + (1 - t_out / t) • δ_star := by rw [smul_add]
          _ = ((t_out / t) • δ_star + (1 - t_out / t) • δ_star) + (t_out / t) • (t • v) := by abel
          _ = ((t_out / t + (1 - t_out / t)) • δ_star) + ((t_out / t) * t) • v := by
            simp [smul_smul]
          _ = (1 • δ_star) + (t_out • v) := by
            have h_t_ne_zero : t ≠ 0 := by linarith
            have h_sum : t_out / t + (1 - t_out / t) = 1 := by ring
            have h_mul : (t_out / t) * t = t_out := by field_simp [h_t_ne_zero]
            simp [h_sum, h_mul]
          _ = δ_star + t_out • v := by simp
      have h_mem_conv : (t_out / t : ℝ) • (δ_star + t • v) + (1 - t_out / t) • δ_star ∈ F :=
        hstar hδ_star_in_F ha_nonneg hb_nonneg hsum
      have h_mem : δ_star + t_out • v ∈ F := by
        rw [← h_conv]
        exact h_mem_conv
      exact ht_out h_mem
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
  · have hδ_star_rel_boundary : δ_star ∈ relativeBoundary F :=
      ⟨hδ_star_in_F, hδ_star_relint⟩
    have h_r_in_RF : (s_star.re : ℂ) ∈ RootSpaceSet (relativeBoundary F) :=
      rootspace_mem_of_eval_zero s_star.re δ_star hδ_star_in_Psr (relativeBoundary F) hδ_star_rel_boundary
    rw [h_s_star_eq]
    exact h_r_in_RF

/-- Complex case of Lemma 6.2:
    If `s*` is a non-real point on the frontier of `RootSpaceSet F` (where `F` is an
    exposed face of dimension 2), then `s*` is a root of a coefficient vector
    on the relative boundary of `F`. -/
theorem lemma62_complex_case {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hF_dim_2 : Module.finrank ℝ (affineSpan ℝ F).direction = 2)
    (s_star : ℂ) (hs_star_front : s_star ∈ frontier (RootSpaceSet F)) (hcomplex : s_star.im ≠ 0) :
    s_star ∈ RootSpaceSet (relativeBoundary F) := by
  have h_polytope : IsPolytopeSet F := isExposedFace_isPolytopeSet P hF_exp
  sorry

/--
**Lemma 6.2:** Let `F` be an exposed face of a polytope `P` (satisfying Assumption 6.1)
with `dim(aff(F)) = 2`. Then the relative boundary of the root space set of `F` is
contained in the root space set of the relative boundary of `F`:

∂ R(F) ⊆ R(relativeBoundary F)

where `∂ X` on the left is the topological frontier in ℂ, and `relativeBoundary F` on the right is
the relative boundary `F \ intrinsicInterior ℝ F`.
-/
theorem lemma62 {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hF_dim_2 : Module.finrank ℝ (affineSpan ℝ F).direction = 2) :
    frontier (RootSpaceSet F) ⊆ RootSpaceSet (relativeBoundary F) := by
  intro s_star hs_star_front
  by_cases hreal : s_star.im = 0
  · exact lemma62_real_case hn P F hF_exp hF_dim_2 s_star hs_star_front hreal
  · exact lemma62_complex_case hn P F hF_exp hF_dim_2 s_star hs_star_front hreal

end CoeffBox
