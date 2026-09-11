module

public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeTheoremDefs
public import ControlSystems.DiscreteTime.EdgeTheorem.BasicLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.PreliminaryLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.ExposedFaceLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.SubfaceConstruction
public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeDescent
public import ControlSystems.DiscreteTime.EdgeTheorem.Lemma61
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

open Polynomial Affine FiniteDimensional LinearMap Set Complex
open Filter Topology

namespace CoeffBox

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
theorem lemma62_real_case {n : ℕ}  (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2)
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
  have hδ_star_in_Psr : δ_star ∈ PsrSet n s_star.re :=
    mem_P_sr_of_isRoot s_star.re δ_star (by
      rw [h_s_star_eq] at hδ_star_root
      exact hδ_star_root)
  by_cases hδ_star_relint : δ_star ∈ intrinsicInterior ℝ F
  · let U : Submodule ℝ (CoeffVec n) := P_sr n s_star.re
    let V : Submodule ℝ (CoeffVec n) := (affineSpan ℝ F).direction
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

/-! ### Complex-case building blocks -/

/-- Positive dimension of the linear intersection
`P_sc n s ⊓ (affineSpan ℝ F).direction` transfers to positive dimension of
the direction of `affineSpan ℝ (↑(P_sc n s) ∩ ↑(affineSpan ℝ F))`. -/
private lemma h_inter_dim_of_meet {n : ℕ} (F : Set (CoeffVec n)) (s : ℂ)
    (δ : CoeffVec n) (hδU : δ ∈ PscSet n s) (hδF : δ ∈ F)
    (h : dim (P_sc n s ⊓ (affineSpan ℝ F).direction) ≥ 1) :
    dim (meetDir n (P_sc n s) (affineSpan ℝ F)) ≥ 1 := by
  unfold meetDir
  have hδA : δ ∈ affineSpan ℝ F := subset_affineSpan ℝ F hδF
  have hA : affineSpan ℝ (PscSet n s ∩ (affineSpan ℝ F : Set (CoeffVec n))) =
      (P_sc n s).toAffineSubspace ⊓ affineSpan ℝ F := by
    rw [affineSpan_inter (P_sc n s) (affineSpan ℝ F)]
  have hD : ((P_sc n s).toAffineSubspace ⊓ affineSpan ℝ F).direction =
      P_sc n s ⊓ (affineSpan ℝ F).direction :=
    intersection_direction_eq (P_sc n s) (affineSpan ℝ F) δ hδU hδA
  rw [hA, hD]
  exact h

/-- Evaluation at a complex point expanded as a finite power sum in the point. -/
lemma evalAtComplex_eq_sum (δ : CoeffVec n) (s : ℂ) :
    evalAtComplex (n := n) s δ =
      ∑ j : Fin (n + 1), (algebraMap ℝ ℂ) (δ j) * (s ^ (j.val : ℕ)) := by
  have h : ((polyOfVec δ).map (algebraMap ℝ ℂ)).eval s =
      ∑ j : Fin (n + 1), (algebraMap ℝ ℂ) (δ j) * (s ^ (j.val : ℕ)) := by
    calc
      ((polyOfVec δ).map (algebraMap ℝ ℂ)).eval s = (polyOfVec δ).eval₂ (algebraMap ℝ ℂ) s := by
        rw [Polynomial.eval_map]
      _ = (∑ j : Fin (n+1), Polynomial.monomial j.val (δ j)).eval₂ (algebraMap ℝ ℂ) s := rfl
      _ = ∑ j : Fin (n+1), ((Polynomial.monomial j.val (δ j)).eval₂ (algebraMap ℝ ℂ) s) := by
        simp [Polynomial.eval₂_finset_sum]
      _ = ∑ j : Fin (n+1), (algebraMap ℝ ℂ : ℝ → ℂ) (δ j) * (s ^ (j.val : ℕ)) := by
        simp [Polynomial.eval₂_monomial]
  simpa [evalAtComplex] using h

/-- For fixed `δ`, the map `s ↦ evalAtComplex s δ` is continuous. -/
lemma continuous_evalAtComplex (δ : CoeffVec n) :
    Continuous fun s : ℂ => evalAtComplex (n := n) s δ := by
  have h_fun : (fun s : ℂ => evalAtComplex (n := n) s δ) =
      (fun s : ℂ => ∑ j : Fin (n + 1), (algebraMap ℝ ℂ) (δ j) * s ^ (j.val : ℕ)) :=
    funext fun s => evalAtComplex_eq_sum δ s
  rw [h_fun]
  refine continuous_finset_sum _ (fun j _ => ?_)
  exact continuous_const.mul ((continuous_id).pow (j.val : ℕ))

/-- Sequential form of `continuous_evalAtComplex`. -/
lemma tendsto_evalAtComplex {α : Type*} [TopologicalSpace α] {l : Filter α}
    {s : α → ℂ} {s₀ : ℂ} (hs : Tendsto s l (𝓝 s₀)) (δ : CoeffVec n) :
    Tendsto (fun x => evalAtComplex (n := n) (s x) δ) l
      (𝓝 (evalAtComplex (n := n) s₀ δ)) :=
  ((continuous_evalAtComplex (n := n) δ).tendsto s₀).comp hs

/-! ### Affine parametrization of the face -//-- A basis of the direction of `affineSpan ℝ F` indexed by `Fin 2`, from
`hF_dim_2` via `Module.finBasisOfFinrankEq`. -/
noncomputable def faceDirBasis {n : ℕ} (F : Set (CoeffVec n))
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2) :
    Module.Basis (Fin 2) ℝ (affineSpan ℝ F).direction :=
  Module.finBasisOfFinrankEq ℝ _ hF_dim_2

/-- The two basis vectors as ambient coefficient vectors. -/
noncomputable def faceCols {n : ℕ} (F : Set (CoeffVec n))
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2) :
    Fin 2 → CoeffVec n :=
  fun i => ((faceDirBasis F hF_dim_2 i : (affineSpan ℝ F).direction).val)

/-- Each basis vector lies in the direction. -/
lemma faceCols_mem_dir {n : ℕ} (F : Set (CoeffVec n))
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2)
    (i : Fin 2) : faceCols F hF_dim_2 i ∈ (affineSpan ℝ F).direction :=
  (faceDirBasis F hF_dim_2 i).property

/-- The two basis vectors span the whole direction. -/
lemma faceCols_span_eq {n : ℕ} (F : Set (CoeffVec n))
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2) :
    Submodule.span ℝ (Set.range (faceCols F hF_dim_2)) =
      (affineSpan ℝ F).direction := by
  have hspan : Submodule.span ℝ
      (Set.range (faceDirBasis F hF_dim_2)) = ⊤ :=
    Module.Basis.span_eq (faceDirBasis F hF_dim_2)
  have himg : (affineSpan ℝ F).direction.subtype ''
      (Set.range (faceDirBasis F hF_dim_2)) =
      Set.range (faceCols F hF_dim_2) := by
    rw [← Set.range_comp]
    rfl
  have hmap_top : Submodule.map (affineSpan ℝ F).direction.subtype ⊤ =
      (affineSpan ℝ F).direction := by
    ext v
    simp only [Submodule.mem_map, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨w, _, rfl⟩
      exact w.property
    · intro hv
      exact ⟨⟨v, hv⟩, rfl⟩
  have hmap := congrArg (Submodule.map (affineSpan ℝ F).direction.subtype) hspan
  rw [Submodule.map_span, himg, hmap_top] at hmap
  exact hmap

/-- Every direction vector is a combination `λ₀•V₀ + λ₁•V₁`. -/
lemma dir_eq_faceCols_combo {n : ℕ} (F : Set (CoeffVec n))
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2)
    (v : (affineSpan ℝ F).direction) :
    ∃ lam : Fin 2 → ℝ, (v : CoeffVec n) =
      lam 0 • faceCols F hF_dim_2 0 + lam 1 • faceCols F hF_dim_2 1 := by
  let b : Module.Basis (Fin 2) ℝ (affineSpan ℝ F).direction :=
    faceDirBasis F hF_dim_2
  have hrepr : ∑ i, b.repr v i • b i = v := Module.Basis.sum_repr b v
  have h2 : (∑ i, b.repr v i • b i) =
      b.repr v 0 • b 0 + b.repr v 1 • b 1 := Fin.sum_univ_two _
  rw [h2] at hrepr
  refine ⟨b.repr v, ?_⟩
  have hcongr : ((b.repr v 0 • b 0 + b.repr v 1 • b 1 : (affineSpan ℝ F).direction)
      : CoeffVec n) =
      b.repr v 0 • faceCols F hF_dim_2 0 + b.repr v 1 • faceCols F hF_dim_2 1 := by
    simp [faceCols, b, Submodule.coe_add]
  have hcast : (v : CoeffVec n) =
      ((b.repr v 0 • b 0 + b.repr v 1 • b 1 : (affineSpan ℝ F).direction)
        : CoeffVec n) := by
    have h := congrArg (⇑((affineSpan ℝ F).direction.subtype)) hrepr.symm
    simpa using h
  calc (v : CoeffVec n)
      = (((b.repr v 0 • b 0 + b.repr v 1 • b 1 : (affineSpan ℝ F).direction))
        : CoeffVec n) := hcast
    _ = b.repr v 0 • faceCols F hF_dim_2 0 + b.repr v 1 • faceCols F hF_dim_2 1 :=
        hcongr

/-- Membership in `aff(F)`: relative to a base point `δ_star ∈ aff(F)`,
every `x ∈ aff(F)` is `δ_star + λ₀•V₀ + λ₁•V₁`. -/
lemma mem_affineSpan_iff_faceCols {n : ℕ} (F : Set (CoeffVec n))
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2)
    (δ_star : CoeffVec n) (hδ : δ_star ∈ affineSpan ℝ F) (x : CoeffVec n) :
    x ∈ affineSpan ℝ F ↔
      ∃ lam : Fin 2 → ℝ, x =
        δ_star + (lam 0 • faceCols F hF_dim_2 0 + lam 1 • faceCols F hF_dim_2 1) := by
  constructor
  · intro hx
    have hdir : (x -ᵥ δ_star : CoeffVec n) ∈ (affineSpan ℝ F).direction := by
      have h := (AffineSubspace.vsub_right_mem_direction_iff_mem hδ x).mpr hx
      simpa [vsub_eq_sub] using h
    obtain ⟨lam, hlam⟩ := dir_eq_faceCols_combo F hF_dim_2 ⟨_, hdir⟩
    refine ⟨lam, ?_⟩
    have hsub : (x - δ_star : CoeffVec n) =
        lam 0 • faceCols F hF_dim_2 0 + lam 1 • faceCols F hF_dim_2 1 := by
      simpa [vsub_eq_sub] using hlam
    calc x = δ_star + (x - δ_star) := by abel
      _ = δ_star + (lam 0 • faceCols F hF_dim_2 0 +
          lam 1 • faceCols F hF_dim_2 1) := by rw [hsub]
  · rintro ⟨lam, rfl⟩
    have hcombo : lam 0 • faceCols F hF_dim_2 0 +
        lam 1 • faceCols F hF_dim_2 1 ∈ (affineSpan ℝ F).direction := by
      apply Submodule.add_mem _ (Submodule.smul_mem _ _ (faceCols_mem_dir F hF_dim_2 0))
      exact Submodule.smul_mem _ _ (faceCols_mem_dir F hF_dim_2 1)
    have := AffineSubspace.vadd_mem_of_mem_direction hcombo hδ
    simpa [vadd_eq_add, add_comm] using this

/-- Translates `δ_star + Vλ` stay in `aff(F)`. -/
lemma add_faceCols_mem_affineSpan {n : ℕ} (F : Set (CoeffVec n))
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2)
    (δ_star : CoeffVec n) (hδ : δ_star ∈ affineSpan ℝ F)
    (lam : Fin 2 → ℝ) :
    δ_star + (lam 0 • faceCols F hF_dim_2 0 + lam 1 • faceCols F hF_dim_2 1) ∈
      affineSpan ℝ F :=
  (mem_affineSpan_iff_faceCols F hF_dim_2 δ_star hδ _).mpr ⟨lam, rfl⟩

/-! ### The `W` matrix

For non-real `s`, every polynomial vanishing at `s` is divisible by the real
quadratic `s² + αs + β` with `α = -2 Re s`, `β = |s|²`. In coefficient space,
multiplication by `s² + αs + β` is the `(n+1)×(n-1)` Toeplitz matrix `W`:
column `j` has `β` at row `j`, `α` at row `j+1`, `1` at row `j+2`. -/

/-- `α = -2 Re s`, the linear coefficient of the quadratic factor. -/
def quadAlpha (s : ℂ) : ℝ := -2 * s.re

/-- `β = |s|²`, the constant coefficient of the quadratic factor. -/
def quadBeta (s : ℂ) : ℝ := Complex.normSq s

/-- The quadratic factor `s² + αs + β` vanishes at `s`. -/
lemma quadFactor_vanishes (s : ℂ) :
    s ^ 2 + (algebraMap ℝ ℂ) (quadAlpha s) * s
      + (algebraMap ℝ ℂ) (quadBeta s) = 0 := by
  have hs : s = (algebraMap ℝ ℂ) s.re + (algebraMap ℝ ℂ) s.im * Complex.I :=
    (Complex.re_add_im s).symm
  have hns : (algebraMap ℝ ℂ) (quadBeta s) =
      (algebraMap ℝ ℂ) s.re * (algebraMap ℝ ℂ) s.re +
      (algebraMap ℝ ℂ) s.im * (algebraMap ℝ ℂ) s.im := by
    simp only [quadBeta, Complex.normSq_apply, map_add, map_mul]
  have hα : (algebraMap ℝ ℂ) (quadAlpha s) =
      -2 * (algebraMap ℝ ℂ) s.re := by
    simp [quadAlpha]
  rw [hns, hα, hs]
  have key : (((algebraMap ℝ ℂ) s.re + (algebraMap ℝ ℂ) s.im * Complex.I) ^ 2
      + (-2 * (algebraMap ℝ ℂ) s.re)
        * ((algebraMap ℝ ℂ) s.re + (algebraMap ℝ ℂ) s.im * Complex.I)
      + ((algebraMap ℝ ℂ) s.re * (algebraMap ℝ ℂ) s.re +
        (algebraMap ℝ ℂ) s.im * (algebraMap ℝ ℂ) s.im))
      = ((algebraMap ℝ ℂ) s.im * (algebraMap ℝ ℂ) s.im)
        * (Complex.I * Complex.I + 1) := by
    ring
  rw [Complex.I_mul_I] at key
  simpa using key

/-- Column `j` of `W`: `β` at row `j`, `α` at row `j+1`, `1` at row `j+2`. -/
def Wcol {n : ℕ} (α β : ℝ) (j : Fin (n - 1)) : CoeffVec n :=
  fun i => (if i.val = j.val then β else 0) +
    (if i.val = j.val + 1 then α else 0) + (if i.val = j.val + 2 then 1 else 0)

/-- `W` applied to `μ`: the coefficient vector of `(s²+αs+β)·(∑ μⱼsʲ)`. -/
def Wmul {n : ℕ} (α β : ℝ) (μ : Fin (n - 1) → ℝ) : CoeffVec n :=
  ∑ j, μ j • Wcol (n := n) α β j

/-- Summing an indicator over `Fin (n+1)` picks out the indicated value. -/
private lemma sum_ite_val_eq {n c : ℕ} (hc : c < n + 1) (g : Fin (n + 1) → ℂ) :
    (∑ i : Fin (n + 1), (if i.val = c then g i else 0)) = g ⟨c, hc⟩ := by
  rw [Finset.sum_eq_single ⟨c, hc⟩]
  · exact if_pos rfl
  · intro b _ hb
    have hne : b.val ≠ c := fun h => hb (Fin.ext h)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Summing a scaled indicator against powers of `s`. -/
private lemma sum_ite_val_mul {n c : ℕ} (hc : c < n + 1) (k s : ℂ) :
    (∑ i : Fin (n + 1), (if i.val = c then k else 0) * s ^ (i.val : ℕ))
      = k * s ^ c := by
  have hpt : ∀ i : Fin (n + 1),
      ((if i.val = c then k else 0) * s ^ (i.val : ℕ)) =
        (if i.val = c then k * s ^ c else 0) := by
    intro i
    by_cases h : i.val = c <;> simp [h]
  simp_rw [hpt]
  have hsum := sum_ite_val_eq hc (fun _ : Fin (n + 1) => k * s ^ c)
  simpa using hsum

/-- Evaluation of a `W` column factors through the quadratic factor. -/
lemma evalAtComplex_Wcol {n : ℕ} (s : ℂ) (α β : ℝ) (j : Fin (n - 1)) :
    evalAtComplex (n := n) s (Wcol (n := n) α β j) =
      (s ^ j.val) * (s ^ 2 + (algebraMap ℝ ℂ) α * s
        + (algebraMap ℝ ℂ) β) := by
  have hj0 : j.val < n + 1 := by have := j.isLt; omega
  have hj1 : j.val + 1 < n + 1 := by have := j.isLt; omega
  have hj2 : j.val + 2 < n + 1 := by have := j.isLt; omega
  rw [evalAtComplex_eq_sum]
  have step1 : (∑ i : Fin (n + 1),
        (algebraMap ℝ ℂ) (Wcol (n := n) α β j i) * s ^ (i.val : ℕ))
      = (∑ i : Fin (n + 1),
          ((if i.val = j.val then (algebraMap ℝ ℂ) β else 0)
            * s ^ (i.val : ℕ)))
        + (∑ i : Fin (n + 1),
          ((if i.val = j.val + 1 then (algebraMap ℝ ℂ) α else 0)
            * s ^ (i.val : ℕ)))
        + (∑ i : Fin (n + 1),
          ((if i.val = j.val + 2 then 1 else 0) * s ^ (i.val : ℕ))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have e0 : (algebraMap ℝ ℂ) (if i.val = j.val then β else 0) =
        if i.val = j.val then (algebraMap ℝ ℂ) β else 0 := by
      by_cases h : i.val = j.val <;> simp [h]
    have e1 : (algebraMap ℝ ℂ) (if i.val = j.val + 1 then α else 0) =
        if i.val = j.val + 1 then (algebraMap ℝ ℂ) α else 0 := by
      by_cases h : i.val = j.val + 1 <;> simp [h]
    have e2 : (algebraMap ℝ ℂ) (if i.val = j.val + 2 then 1 else 0) =
        if i.val = j.val + 2 then 1 else 0 := by
      by_cases h : i.val = j.val + 2 <;> simp [h]
    simp only [Wcol, map_add, e0, e1, e2, add_mul]
  rw [step1, sum_ite_val_mul hj0, sum_ite_val_mul hj1, sum_ite_val_mul hj2]
  ring

/-- Every `δ* + Wμ` vanishes at `s*`: the reverse direction of the
`𝒫_{s*} = δ* + range W` characterization. -/
lemma Wmul_mem_Psc {n : ℕ} (s_star : ℂ) (δ_star : CoeffVec n)
    (h_star : δ_star ∈ P_sc n s_star) (μ : Fin (n - 1) → ℝ) :
    δ_star + Wmul (quadAlpha s_star) (quadBeta s_star) μ
      ∈ P_sc n s_star := by
  have h0 : evalAtComplex (n := n) s_star δ_star = 0 := by
    unfold P_sc at h_star
    exact LinearMap.mem_ker.mp h_star
  have hW : evalAtComplex (n := n) s_star
      (Wmul (quadAlpha s_star) (quadBeta s_star) μ) = 0 := by
    unfold Wmul
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [map_smul, evalAtComplex_Wcol, Algebra.smul_def,
      quadFactor_vanishes s_star]
    simp
  unfold P_sc
  rw [LinearMap.mem_ker, map_add, h0, hW, add_zero]

/-! ### Case B, B1: the approximating sequence (6.11) -/

/-- Continuity of `quadAlpha` in the point. -/
lemma continuous_quadAlpha : Continuous (quadAlpha : ℂ → ℝ) := by
  unfold quadAlpha
  exact continuous_const.mul Complex.continuous_re

/-- Continuity of `quadBeta` in the point. -/
lemma continuous_quadBeta : Continuous (quadBeta : ℂ → ℝ) := by
  have h : (quadBeta : ℂ → ℝ) = fun s => s.re * s.re + s.im * s.im := by
    funext s
    simp [quadBeta, Complex.normSq_apply]
  rw [h]
  exact Complex.continuous_re.mul Complex.continuous_re
    |>.add (Complex.continuous_im.mul Complex.continuous_im)

/-- From `s* ∈ R(F)` and `s* ∈ closure((R(F))ᶜ)` extract a sequence
`s_seq` with `s_seq k ∉ R(F)`, `s_seq k ≠ s*`, converging to `s*`
(textbook (6.11) setup, radii `1/(k+1)`). -/
lemma exists_seq_notin_RootSpaceSet_tendsto {n : ℕ} {F : Set (CoeffVec n)}
    {s_star : ℂ} (hs_in : s_star ∈ RootSpaceSet F)
    (h : s_star ∈ closure (RootSpaceSet F)ᶜ) :
    ∃ s_seq : ℕ → ℂ, (∀ k, s_seq k ∉ RootSpaceSet F) ∧
      (∀ k, s_seq k ≠ s_star) ∧ Tendsto s_seq atTop (𝓝 s_star) := by
  have h1 : ∀ k : ℕ, ∃ y, y ∉ RootSpaceSet F ∧ dist s_star y < 1 / (k + 1) := by
    intro k
    have hpos : (0:ℝ) < 1 / (k + 1) := by positivity
    obtain ⟨y, hy, hdy⟩ := Metric.mem_closure_iff.mp h _ hpos
    exact ⟨y, hy, hdy⟩
  choose s_seq hs_out hdist using h1
  refine ⟨s_seq, hs_out, ?_, ?_⟩
  · intro k hEq
    exact hs_out k (by rw [hEq]; exact hs_in)
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ :=
      Metric.tendsto_atTop.mp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ε hε
    refine ⟨N, fun k hk => ?_⟩
    have hmono : 1 / (k + 1) ≤ 1 / ((N:ℝ) + 1) :=
      (one_div_le_one_div (by positivity) (by positivity)).mpr (by
        have h1 : ((N:ℕ) + 1 : ℕ) ≤ (k + 1 : ℕ) := Nat.succ_le_succ hk
        exact_mod_cast h1)
    have h1N : 1 / ((N:ℝ) + 1) < ε := by
      have hN0 := hN N (le_refl N)
      rw [dist_zero_right, Real.norm_eq_abs,
        abs_of_pos (show (0:ℝ) < 1 / (N + 1) by positivity)] at hN0
      exact hN0
    have hd : dist s_star (s_seq k) < 1 / (k + 1) := hdist k
    rw [dist_comm]
    linarith

/-- (6.11): `α_k = -2 Re s_k → α = -2 Re s*` along any convergent sequence. -/
lemma tendsto_quadAlpha {α : Type*} [TopologicalSpace α] {l : Filter α}
    {s : α → ℂ} {s₀ : ℂ} (hs : Tendsto s l (𝓝 s₀)) :
    Tendsto (fun x => quadAlpha (s x)) l (𝓝 (quadAlpha s₀)) :=
  (continuous_quadAlpha.tendsto s₀).comp hs

/-- (6.11): `β_k = |s_k|² → β = |s*|²` along any convergent sequence. -/
lemma tendsto_quadBeta {α : Type*} [TopologicalSpace α] {l : Filter α}
    {s : α → ℂ} {s₀ : ℂ} (hs : Tendsto s l (𝓝 s₀)) :
    Tendsto (fun x => quadBeta (s x)) l (𝓝 (quadBeta s₀)) :=
  (continuous_quadBeta.tendsto s₀).comp hs

/-- Complex case of Lemma 6.2:
    If `s*` is a non-real point on the frontier of `RootSpaceSet F` (where `F` is an
    exposed face of dimension 2), then `s*` is a root of a coefficient vector
    on the relative boundary of `F`. -/
theorem lemma62_complex_case {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2)
    (s_star : ℂ) (hs_star_front : s_star ∈ frontier (RootSpaceSet F)) (hcomplex : s_star.im ≠ 0) :
    s_star ∈ RootSpaceSet (relativeBoundary F) := by
  have hF_compact : IsCompact F := isExposedFace_isCompact P hF_exp
  have h_root_closed : IsClosed (RootSpaceSet F) :=
    rootSpaceSet_isClosed_of_isCompact hF_compact
  have hs_star_in_RF : s_star ∈ RootSpaceSet F := by
    have h_sub : frontier (RootSpaceSet F) ⊆ RootSpaceSet F := by
      calc
        frontier (RootSpaceSet F) ⊆ closure (RootSpaceSet F) := frontier_subset_closure
        _ = RootSpaceSet F := h_root_closed.closure_eq
    exact h_sub hs_star_front
  rcases hs_star_in_RF with ⟨δ_star, hδ_star_in_F, hδ_star_root⟩
  have hδ_star_Psc : δ_star ∈ PscSet n s_star :=
    mem_P_sc_of_isRoot s_star δ_star hδ_star_root
  by_cases hA : dim (P_sc n s_star ⊓ (affineSpan ℝ F).direction) ≥ 1
  · obtain ⟨δ_hat, ⟨hδ_hat_F, hδ_hat_Psc⟩, _, hδ_hat_notrelint⟩ :=
      exists_boundary_point_in_face_rootspace_complex P s_star δ_star F hF_exp
        hδ_star_in_F hδ_star_Psc
        (h_inter_dim_of_meet F s_star δ_star hδ_star_Psc hδ_star_in_F hA)
    have hk : evalAtComplex (n := n) s_star δ_hat = 0 := by
      have h := hδ_hat_Psc
      simp only [PscSet, P_sc, LinearMap.mem_ker] at h
      exact h
    have hroot : ((polyOfVec δ_hat).map (algebraMap ℝ ℂ)).IsRoot s_star := by
      rw [Polynomial.IsRoot]
      have h_eval : ((polyOfVec δ_hat).map (algebraMap ℝ ℂ)).eval s_star
          = evalAtComplex (n := n) s_star δ_hat := rfl
      rw [h_eval, hk]
    exact rootspace_mem_of_isRoot s_star δ_hat hroot (relativeBoundary F)
      ⟨hδ_hat_F, hδ_hat_notrelint⟩
  · -- Case B
    have hc : s_star ∈ closure (RootSpaceSet F)ᶜ := by
      rw [frontier_eq_closure_inter_closure] at hs_star_front
      exact hs_star_front.2
    obtain ⟨s_seq, hs_out, _hs_ne, hs_tendsto⟩ :=
      exists_seq_notin_RootSpaceSet_tendsto
        (rootspace_mem_of_isRoot s_star δ_star hδ_star_root F hδ_star_in_F) hc
    sorry

/--
**Lemma 6.2:** for an exposed face `F` of a polytope `P` with
`dim(aff(F)) = 2`, the boundary of the root locus of `F` is contained in the
root locus of the relative boundary of `F`:

∂ R(F) ⊆ R(relativeBoundary F)
-/
theorem lemma62 {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2) :
    frontier (RootSpaceSet F) ⊆ RootSpaceSet (relativeBoundary F) := by
  intro s_star hs_star_front
  by_cases hreal : s_star.im = 0
  · exact lemma62_real_case  P F hF_exp hF_dim_2 s_star hs_star_front hreal
  · exact lemma62_complex_case hn P F hF_exp hF_dim_2 s_star hs_star_front hreal

end CoeffBox
