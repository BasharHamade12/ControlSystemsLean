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
public import Mathlib.Analysis.Complex.Polynomial.Basic

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

/-! ### Case B, B2–B3 (entry): the running matrix `Wₖ` and `Wₖ → W` -/

/-- `W` at running parameters `(α_k, β_k)`: the book's `Wₙ`. -/
def Wk {n : ℕ} (s_seq : ℕ → ℂ) (k : ℕ) (μ : Fin (n - 1) → ℝ) : CoeffVec n :=
  Wmul (quadAlpha (s_seq k)) (quadBeta (s_seq k)) μ

/-- A `W` column as a fixed real combination of the parameters: the
indicators depend only on the fixed indices `i, j`. -/
lemma Wcol_eq_const_mul {n : ℕ} (α β : ℝ) (j : Fin (n - 1)) (i : Fin (n + 1)) :
    Wcol (n := n) α β j i =
      (if i.val = j.val then (1:ℝ) else 0) * β +
      (if i.val = j.val + 1 then (1:ℝ) else 0) * α +
      (if i.val = j.val + 2 then (1:ℝ) else 0) := by
  unfold Wcol
  by_cases h0 : i.val = j.val <;> by_cases h1 : i.val = j.val + 1
    <;> by_cases h2 : i.val = j.val + 2 <;> simp [h0, h1, h2]

/-- Entrywise convergence `Wmul α_k β_k μ → Wmul α β μ` from convergence
of the parameters (textbook (6.14), matrix part). -/
lemma tendsto_Wmul {n : ℕ} {α : Type*} [TopologicalSpace α] {l : Filter α}
    (μ : Fin (n - 1) → ℝ) {α' : α → ℝ} {α₀ : ℝ} (hα : Tendsto α' l (𝓝 α₀))
    {β' : α → ℝ} {β₀ : ℝ} (hβ : Tendsto β' l (𝓝 β₀)) :
    Tendsto (fun x => Wmul (α' x) (β' x) μ) l (𝓝 (Wmul α₀ β₀ μ)) := by
  have hcoord : ∀ (a b : ℝ) (i : Fin (n + 1)),
      (Wmul a b μ) i = ∑ j, μ j * (Wcol (n := n) a b j i) := by
    intro a b i
    unfold Wmul
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [tendsto_pi_nhds]
  intro i
  simp_rw [hcoord]
  apply tendsto_finset_sum
  intro j _
  simp_rw [Wcol_eq_const_mul]
  have h1 : Tendsto (fun x => (if i.val = j.val then (1:ℝ) else 0) * β' x) l
      (𝓝 ((if i.val = j.val then (1:ℝ) else 0) * β₀)) :=
    tendsto_const_nhds.mul hβ
  have h2 : Tendsto (fun x => (if i.val = j.val + 1 then (1:ℝ) else 0) * α' x) l
      (𝓝 ((if i.val = j.val + 1 then (1:ℝ) else 0) * α₀)) :=
    tendsto_const_nhds.mul hα
  have h3 : Tendsto (fun _ => (if i.val = j.val + 2 then (1:ℝ) else 0)) l
      (𝓝 (if i.val = j.val + 2 then (1:ℝ) else 0)) :=
    tendsto_const_nhds
  exact tendsto_const_nhds.mul ((h1.add h2).add h3)

/-- `Wₖ μ → W μ` along the approximating sequence (B1 + entrywise). -/
lemma tendsto_Wk {n : ℕ} (s_seq : ℕ → ℂ) (μ : Fin (n - 1) → ℝ) {s_star : ℂ}
    (hs : Tendsto s_seq atTop (𝓝 s_star)) :
    Tendsto (fun k => Wk s_seq k μ) atTop
      (𝓝 (Wmul (quadAlpha s_star) (quadBeta s_star) μ)) :=
  tendsto_Wmul μ (tendsto_quadAlpha hs) (tendsto_quadBeta hs)

/-! ### Case B, B2b: quotient polynomial, νₖ, and membership in P_sc n sₖ

From textbook (6.12)–(6.13): since `δ* ∈ P_sc n s*` and `s*` is non-real,
`polyOfVec δ*` is divisible by the real quadratic `X² − C(2 Re s*) X + C(|s*|²)`.  The quotient
`d(x)` has degree ≤ n−2 and its coefficients form the two columns of `D`.
The offset `νₖ = (αₖ−α)·D₀ + (βₖ−β)·D₁` satisfies `δ*+νₖ ∈ P_sc n sₖ`. -/

/-- `aeval s (polyOfVec δ) = evalAtComplex s δ`. -/
lemma aeval_eq_evalAtComplex {n : ℕ} (s : ℂ) (δ : CoeffVec n) :
    aeval s (polyOfVec δ) = evalAtComplex s δ := by
  rw [aeval_def, evalAtComplex, eval₂_eq_eval_map]; rfl

/-- The quadratic factor divides `polyOfVec δ*` when `δ*` vanishes at non-real `s*`.
    Uses Mathlib form `X² − C(2 Re s) X + C(|s|²)`. -/
lemma quadratic_dvd_polyOfVec {n : ℕ} (s_star : ℂ) (δ_star : CoeffVec n)
    (h0 : evalAtComplex s_star δ_star = 0) (hcomplex : s_star.im ≠ 0) :
    X ^ 2 - C (2 * s_star.re) * X + C (‖s_star‖ ^ 2) ∣ polyOfVec δ_star := by
  have h0' : aeval s_star (polyOfVec δ_star) = 0 := by
    rw [aeval_eq_evalAtComplex]; exact h0
  exact Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero _ h0' hcomplex

/-- The quotient polynomial from dividing `polyOfVec δ*` by the quadratic factor. -/
noncomputable def quotientPoly {n : ℕ} (s_star : ℂ) (δ_star : CoeffVec n)
    (h0 : evalAtComplex s_star δ_star = 0) (hcomplex : s_star.im ≠ 0) : ℝ[X] :=
  Classical.choose (quadratic_dvd_polyOfVec s_star δ_star h0 hcomplex)

/-- The division identity: `(X² − C(2Re s*) X + C(|s*|²)) · d = polyOfVec δ*`. -/
lemma quotientPoly_spec {n : ℕ} (s_star : ℂ) (δ_star : CoeffVec n)
    (h0 : evalAtComplex s_star δ_star = 0) (hcomplex : s_star.im ≠ 0) :
    (X ^ 2 - C (2 * s_star.re) * X + C (‖s_star‖ ^ 2)) *
      quotientPoly s_star δ_star h0 hcomplex = polyOfVec δ_star :=
  (Classical.choose_spec (quadratic_dvd_polyOfVec s_star δ_star h0 hcomplex)).symm

/-- natDegree of `polyOfVec δ` is at most `n`. -/
lemma polyOfVec_natDegree_le {n : ℕ} (δ : CoeffVec n) :
    (polyOfVec δ).natDegree ≤ n := by
  unfold polyOfVec
  apply le_trans (Polynomial.natDegree_sum_le _ _)
  apply Finset.sup_le
  intro i _
  exact le_trans (Polynomial.natDegree_monomial_le (δ i)) (Nat.le_of_lt_succ i.isLt)

/-- The quadratic factor `X² − C(2 Re s) X + C(|s|²)` has natDegree 2. -/
private lemma quadratic_natDegree {s : ℂ} :
    (X ^ 2 - C (2 * s.re) * X + C ((‖s‖ : ℝ) ^ 2) : ℝ[X]).natDegree = 2 := by
  have hq2 : (X ^ 2 : ℝ[X]).degree = 2 := Polynomial.degree_X_pow 2
  have hc1 : ((C (2 * s.re) * X) : ℝ[X]).degree ≤ 1 := Polynomial.degree_C_mul_X_le _
  have hc0 : ((C ((‖s‖ : ℝ) ^ 2) : ℝ[X])).degree ≤ 0 := Polynomial.degree_C_le
  have hsub : ((X ^ 2 - C (2 * s.re) * X : ℝ[X])).degree = 2 := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt (p := X ^ 2)]
    · exact hq2
    · refine lt_of_le_of_lt hc1 ?_
      rw [hq2]; exact WithBot.coe_lt_coe.2 (by norm_num : (1:ℕ) < 2)
  have hdeg : (X ^ 2 - C (2 * s.re) * X + C ((‖s‖ : ℝ) ^ 2) : ℝ[X]).degree = 2 := by
    rw [Polynomial.degree_add_eq_left_of_degree_lt (p := X ^ 2 - C (2 * s.re) * X)]
    · exact hsub
    · refine lt_of_le_of_lt hc0 ?_
      rw [hsub]; exact WithBot.coe_lt_coe.2 (by norm_num : (0:ℕ) < 2)
  exact Polynomial.natDegree_eq_of_degree_eq_some hdeg

/-- The quotient has natDegree ≤ n − 2 (when n ≥ 2). -/
lemma quotientPoly_natDegree_le {n : ℕ} (hn : n ≥ 2) (s_star : ℂ) (δ_star : CoeffVec n)
    (h0 : evalAtComplex s_star δ_star = 0) (hcomplex : s_star.im ≠ 0) :
    (quotientPoly s_star δ_star h0 hcomplex).natDegree ≤ n - 2 := by
  have hQ2 : (X ^ 2 - C (2 * s_star.re) * X + C ((‖s_star‖ : ℝ) ^ 2) : ℝ[X]).natDegree = 2 :=
    quadratic_natDegree
  have hQne : (X ^ 2 - C (2 * s_star.re) * X + C ((‖s_star‖ : ℝ) ^ 2) : ℝ[X]) ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hQ2; norm_num at hQ2
  by_cases hqz : quotientPoly s_star δ_star h0 hcomplex = 0
  · rw [hqz, Polynomial.natDegree_zero]; omega
  · have h2 := polyOfVec_natDegree_le δ_star
    rw [← quotientPoly_spec s_star δ_star h0 hcomplex] at h2
    rw [Polynomial.natDegree_mul hQne hqz, hQ2] at h2
    omega

/-- Convert polynomial to coefficient vector (zero-padded to length n+1). -/
noncomputable def polyToVec {n : ℕ} (p : ℝ[X]) : CoeffVec n :=
  fun i => p.coeff i.val

/-- Evaluation of `polyToVec` equals the polynomial evaluation. -/
lemma evalAtComplex_polyToVec {n : ℕ} (p : ℝ[X]) (s : ℂ) (hp : p.natDegree ≤ n) :
    evalAtComplex (n := n) s (polyToVec p) = (p.map (algebraMap ℝ ℂ)).eval s := by
  classical
  have key : polyOfVec (n := n) (polyToVec (n := n) p) = p := by
    ext m
    rw [polyOfVec, Polynomial.finset_sum_coeff]
    simp only [polyToVec]
    have hsum : (∑ x : Fin (n + 1), (Polynomial.monomial x.val (p.coeff x.val)).coeff m)
        = (∑ x : Fin (n + 1), if x.val = m then p.coeff x.val else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Polynomial.coeff_monomial]
    rw [hsum]
    by_cases hmn : m ≤ n
    · have h1 : (∑ x : Fin (n + 1), if x.val = m then p.coeff x.val else 0)
          = ∑ x ∈ Finset.filter (fun x : Fin (n + 1) => x.val = m) Finset.univ, p.coeff x.val := by
        rw [Finset.sum_filter]
      rw [h1]
      have hflt : Finset.filter (fun x : Fin (n + 1) => x.val = m) Finset.univ =
          {(⟨m, by omega⟩ : Fin (n + 1))} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.ext_iff]
      rw [hflt, Finset.sum_singleton]
    · have hc : p.coeff m = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by have h := hp; omega)
      rw [hc,
        show (∑ x : Fin (n + 1), if x.val = m then p.coeff x.val else 0) = 0 from
          Finset.sum_eq_zero (fun x _ => by
            have hlt : x.val < n + 1 := x.isLt
            have hx : ¬(x.val = m) := by
              intro hc2
              have h2 := hmn
              omega
            simp [hx])]
  show ((polyOfVec (n := n) (polyToVec (n := n) p)).map (algebraMap ℝ ℂ)).eval s = _
  rw [key]

/-- `evalAtComplex s (polyToVec (X * q)) = s * evalAtComplex s (polyToVec q)`. -/
lemma evalAtComplex_polyToVec_X_mul {n : ℕ} (hn1 : 1 ≤ n) (q : ℝ[X]) (s : ℂ)
    (hq_le : q.natDegree ≤ n - 2) :
    evalAtComplex (n := n) s (polyToVec (X * q)) =
      s * evalAtComplex (n := n) s (polyToVec q) := by
  have hq : q.natDegree ≤ n := by omega
  have hXq : (X * q).natDegree ≤ n := by
    calc (X * q).natDegree ≤ X.natDegree + q.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 1 + (n - 2) := Nat.add_le_add Polynomial.natDegree_X_le hq_le
      _ ≤ n := by omega
  rw [evalAtComplex_polyToVec _ _ hXq, evalAtComplex_polyToVec _ _ hq]
  rw [Polynomial.map_mul, Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_X]

/-- The offset νₖ: linear in (αₖ−α, βₖ−β) with columns from d and X·d.
    Textbook (6.12)–(6.13). -/
noncomputable def nuk {n : ℕ} (s_seq : ℕ → ℂ) (s_star : ℂ) (δ_star : CoeffVec n)
    (h0 : evalAtComplex s_star δ_star = 0) (hcomplex : s_star.im ≠ 0) (k : ℕ) :
    CoeffVec n :=
  let q := quotientPoly s_star δ_star h0 hcomplex
  let α := quadAlpha s_star
  let β := quadBeta s_star
  let αk := quadAlpha (s_seq k)
  let βk := quadBeta (s_seq k)
  (αk - α) • polyToVec (X * q) + (βk - β) • polyToVec q

/-- `δ* + νₖ ∈ P_sc n sₖ`. Core identity: the quadratic factor vanishes at `sₖ`,
so the offset cancels the residual evaluation. -/
lemma delta_plus_nuk_mem_Psc {n : ℕ} (hn1 : n ≥ 1) (s_seq : ℕ → ℂ) (s_star : ℂ)
    (δ_star : CoeffVec n) (h0 : evalAtComplex s_star δ_star = 0)
    (hcomplex : s_star.im ≠ 0) (k : ℕ) :
    δ_star + nuk s_seq s_star δ_star h0 hcomplex k ∈ P_sc n (s_seq k) := by
  set sk := s_seq k with hsk
  set q := quotientPoly s_star δ_star h0 hcomplex with hqdef
  have hq_le : q.natDegree ≤ n - 2 := by
    by_cases hn2 : n ≥ 2
    · simpa [hqdef] using quotientPoly_natDegree_le hn2 s_star δ_star h0 hcomplex
    · have hn1' : n = 1 := by omega
      subst hn1'
      by_cases hqz : q = 0
      · rw [hqz, Polynomial.natDegree_zero]
      · exfalso
        have hQ2 : (X ^ 2 - C (2 * s_star.re) * X + C ((‖s_star‖ : ℝ) ^ 2) : ℝ[X]).natDegree =
            2 := quadratic_natDegree
        have hQne : (X ^ 2 - C (2 * s_star.re) * X + C ((‖s_star‖ : ℝ) ^ 2) : ℝ[X]) ≠ 0 := by
          intro h; rw [h, Polynomial.natDegree_zero] at hQ2; norm_num at hQ2
        have h2 := polyOfVec_natDegree_le δ_star
        have hsp := quotientPoly_spec s_star δ_star h0 hcomplex
        rw [← hqdef] at hsp
        rw [← hsp] at h2
        rw [Polynomial.natDegree_mul hQne hqz, quadratic_natDegree] at h2
        omega
  -- First term: evalAtComplex sₖ δ* via the factorization Q·q = polyOfVec δ*.
  have hb1 : evalAtComplex (n := n) sk δ_star =
      (sk ^ 2 + (algebraMap ℝ ℂ) (quadAlpha s_star) * sk
          + (algebraMap ℝ ℂ) (quadBeta s_star)) * ((q.map (algebraMap ℝ ℂ)).eval sk) := by
    have hsp := quotientPoly_spec s_star δ_star h0 hcomplex
    rw [← hqdef] at hsp
    show ((polyOfVec (n := n) δ_star).map (algebraMap ℝ ℂ)).eval sk = _
    rw [← hsp, Polynomial.map_mul, Polynomial.eval_mul]
    have key :
        (((X ^ 2 : ℝ[X]) - C (2 * s_star.re) * X + C (‖s_star‖ ^ 2)).map
            (algebraMap ℝ ℂ)).eval sk
          = sk ^ 2 + (algebraMap ℝ ℂ) (quadAlpha s_star) * sk
            + (algebraMap ℝ ℂ) (quadBeta s_star) := by
      simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, quadAlpha, quadBeta,
        Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [key]
  -- Second term: evalAtComplex sₖ νₖ from the two polyToVec evaluations.
  have hb2 : evalAtComplex (n := n) sk (nuk s_seq s_star δ_star h0 hcomplex k) =
      ((algebraMap ℝ ℂ) (quadAlpha sk) - (algebraMap ℝ ℂ) (quadAlpha s_star)) * sk *
          ((q.map (algebraMap ℝ ℂ)).eval sk) +
        ((algebraMap ℝ ℂ) (quadBeta sk) - (algebraMap ℝ ℂ) (quadBeta s_star)) *
          ((q.map (algebraMap ℝ ℂ)).eval sk) := by
    show evalAtComplex (n := n) sk (((quadAlpha sk - quadAlpha s_star : ℝ) •
        polyToVec (n := n) (X * q) + (quadBeta sk - quadBeta s_star : ℝ) •
        polyToVec (n := n) q)) = _
    have hqn : q.natDegree ≤ n := by omega
    rw [map_add, LinearMap.map_smul, LinearMap.map_smul,
      evalAtComplex_polyToVec_X_mul hn1 q sk hq_le,
      evalAtComplex_polyToVec q sk hqn]
    simp only [Algebra.smul_def, map_sub]
    ring
  -- Assemble: the sum factors as (sₖ² + αₖ sₖ + βₖ)·q(sₖ) = 0.
  unfold P_sc
  rw [LinearMap.mem_ker, map_add, hb1, hb2]
  have heuristics : (sk ^ 2
        + (algebraMap ℝ ℂ) (quadAlpha s_star) * sk
        + (algebraMap ℝ ℂ) (quadBeta s_star)) * ((q.map (algebraMap ℝ ℂ)).eval sk) +
      (((algebraMap ℝ ℂ) (quadAlpha sk) - (algebraMap ℝ ℂ) (quadAlpha s_star)) * sk *
          ((q.map (algebraMap ℝ ℂ)).eval sk) +
        ((algebraMap ℝ ℂ) (quadBeta sk) - (algebraMap ℝ ℂ) (quadBeta s_star)) *
          ((q.map (algebraMap ℝ ℂ)).eval sk))
      = (sk ^ 2 + (algebraMap ℝ ℂ) (quadAlpha sk) * sk
          + (algebraMap ℝ ℂ) (quadBeta sk)) * ((q.map (algebraMap ℝ ℂ)).eval sk) := by
    ring
  rw [heuristics, quadFactor_vanishes sk, zero_mul]

/-- νₖ → 0 along the approximating sequence (textbook (6.14), offset part). -/
lemma tendsto_nuk {n : ℕ} (s_seq : ℕ → ℂ) (s_star : ℂ) (δ_star : CoeffVec n)
    (h0 : evalAtComplex s_star δ_star = 0) (hcomplex : s_star.im ≠ 0)
    (hs : Tendsto s_seq atTop (𝓝 s_star)) :
    Tendsto (fun k => nuk s_seq s_star δ_star h0 hcomplex k) atTop (𝓝 0) := by
  rw [tendsto_pi_nhds]; intro i
  simp only [nuk, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.zero_apply]
  have hα : Tendsto (fun k => quadAlpha (s_seq k) - quadAlpha s_star) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => quadAlpha (s_seq k)) atTop (𝓝 (quadAlpha s_star)) :=
      tendsto_quadAlpha hs
    have h2 : Tendsto (fun _ : ℕ => quadAlpha s_star) atTop (𝓝 (quadAlpha s_star)) :=
      tendsto_const_nhds
    have h3 := Filter.Tendsto.sub h1 h2
    simp only [sub_self] at h3; exact h3
  have hβ : Tendsto (fun k => quadBeta (s_seq k) - quadBeta s_star) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => quadBeta (s_seq k)) atTop (𝓝 (quadBeta s_star)) :=
      tendsto_quadBeta hs
    have h2 : Tendsto (fun _ : ℕ => quadBeta s_star) atTop (𝓝 (quadBeta s_star)) :=
      tendsto_const_nhds
    have h3 := Filter.Tendsto.sub h1 h2
    simp only [sub_self] at h3; exact h3
  have hc1 : Tendsto (fun _ : ℕ => polyToVec (X * quotientPoly s_star δ_star h0 hcomplex) i)
      atTop (𝓝 (polyToVec (X * quotientPoly s_star δ_star h0 hcomplex) i)) :=
    tendsto_const_nhds
  have hc2 : Tendsto (fun _ : ℕ => polyToVec (quotientPoly s_star δ_star h0 hcomplex) i)
      atTop (𝓝 (polyToVec (quotientPoly s_star δ_star h0 hcomplex) i)) :=
    tendsto_const_nhds
  have hprod1 := Filter.Tendsto.mul hα hc1
  have hprod2 := Filter.Tendsto.mul hβ hc2
  have hadd := Filter.Tendsto.add hprod1 hprod2
  simp only [zero_mul, add_zero] at hadd
  exact hadd

/-! ### Case B, B4: the joint matrix `[V, −Wₖ]` (textbook (6.15)–(6.16)) -/

/-- `Wmul (quadAlpha s) (quadBeta s) μ` vanishes at `s`: the kernel version of
`evalAtComplex_Wcol`. -/
lemma evalAtComplex_Wmul {n : ℕ} (s : ℂ) (μ : Fin (n - 1) → ℝ) :
    evalAtComplex (n := n) s (Wmul (quadAlpha s) (quadBeta s) μ) = 0 := by
  unfold Wmul
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_smul, evalAtComplex_Wcol, Algebra.smul_def, quadFactor_vanishes s]
  simp

/-- The `W`-translate member: `Wmul` at the parameters of `s` lies in `P_sc n s`. -/
lemma Wmul_mem_Psc_zero {n : ℕ} (s : ℂ) (μ : Fin (n - 1) → ℝ) :
    Wmul (n := n) (quadAlpha s) (quadBeta s) μ ∈ P_sc n s := by
  unfold P_sc; rw [LinearMap.mem_ker]; exact evalAtComplex_Wmul s μ

/-- Indicator column sum over `Fin (n - 1)`: picks out the `c`-th value when it exists. -/
private lemma sum_ite_val_fin {n c : ℕ} (g : Fin (n - 1) → ℝ) :
    (∑ j : Fin (n - 1), (if j.val = c then g j else 0)) =
      if h : c < n - 1 then g ⟨c, h⟩ else 0 := by
  classical
  by_cases hc : c < n - 1
  · simp only [dif_pos hc]
    rw [← Finset.sum_filter]
    have hflt : Finset.filter (fun j : Fin (n - 1) => j.val = c) Finset.univ = {(⟨c, hc⟩ : Fin (n - 1))} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hj; exact Fin.ext hj
      · intro hj; subst hj; simp
    rw [hflt, Finset.sum_singleton]
  · simp only [dif_neg hc]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro hEq
    have hj := j.isLt
    omega

/-- Evaluation of `Wmul` at a row: unfolds to a weighted sum of `Wcol` entries.
Used directly by `Wmul_injective` without a closed-form dite formula
(to avoid truncated-subtraction edge cases at rows 0 and 1). -/
private lemma Wmul_apply_eq_sum {n : ℕ} (α β : ℝ) (μ : Fin (n - 1) → ℝ)
    (i : Fin (n + 1)) :
    (Wmul (n := n) α β μ) i =
      ∑ j : Fin (n - 1), μ j * (Wcol (n := n) α β j i) := by
  unfold Wmul
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The `W` operator is injective: `Wmul α β μ = 0` implies `μ = 0`.
Read `μ` off anti-diagonally from the top: the entry of the largest nonzero index at row
`val + 2` is uncancelled. -/
private lemma Wmul_injective {n : ℕ} {α β : ℝ} {μ : Fin (n - 1) → ℝ}
    (h : Wmul (n := n) α β μ = 0) : μ = 0 := by
  classical
  refine funext fun j => by_contra fun hμ => ?_
  have hfne : (Finset.univ.filter (fun k : Fin (n - 1) => μ k ≠ 0)).Nonempty := by
    rw [Finset.filter_nonempty_iff]
    exact ⟨j, Finset.mem_univ _, hμ⟩
  obtain ⟨jm, hjm_mem, hmax⟩ :=
    Finset.exists_max_image
      (Finset.univ.filter (fun k : Fin (n - 1) => μ k ≠ 0)) (fun k => (k : ℕ)) hfne
  have him : μ jm ≠ 0 := (Finset.mem_filter.mp hjm_mem).2
  have hle : ∀ k : Fin (n - 1), μ k ≠ 0 → k.val ≤ jm.val := by
    intro k hk
    have hkmem : k ∈ Finset.univ.filter (fun k : Fin (n - 1) => μ k ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    exact hmax k hkmem
  have hgt : ∀ k : Fin (n - 1), jm.val < k.val → μ k = 0 := by
    intro k hk
    by_contra hkne
    have := hle k hkne
    omega
  have hi_lt : jm.val + 2 < n + 1 := by have h := jm.isLt; omega
  have hzero : (Wmul (n := n) α β μ) ⟨jm.val + 2, hi_lt⟩ = 0 :=
    congrFun h _
  rw [Wmul_apply_eq_sum] at hzero
  -- Each summand vanishes except at `j = jm`, where it equals `μ jm`.
  have hsum : (∑ j : Fin (n - 1), μ j * (Wcol (n := n) α β j ⟨jm.val + 2, hi_lt⟩))
      = μ jm := by
    rw [Finset.sum_eq_single jm]
    · simp [Wcol]
    · intro k _ hkne
      by_cases hkj : k.val = jm.val + 2
      · -- then `k.val > jm.val`, so `μ k = 0`
        have hkgt : jm.val < k.val := by omega
        rw [hgt k hkgt, zero_mul]
      · by_cases hkj1 : k.val + 1 = jm.val + 2
        · have hkgt : jm.val < k.val := by omega
          rw [hgt k hkgt, zero_mul]
        · by_cases hkj2 : k.val + 2 = jm.val + 2
          · exfalso; apply hkne; ext; omega
          · simp only [Wcol]
            rw [if_neg (by omega : ¬ (jm.val + 2 = k.val)),
              if_neg (by omega : ¬ (jm.val + 2 = k.val + 1)),
              if_neg (by omega : ¬ (jm.val + 2 = k.val + 2))]
            ring
    · intro hcontra
      exfalso
      exact hcontra (Finset.mem_univ jm)
  rw [hsum] at hzero
  exact him hzero

/-- A `faceCols` combination that vanishes has all coefficients zero (basis independence). -/
private lemma eq_zero_of_faceCols_combo {n : ℕ} (F : Set (CoeffVec n))
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2) (lam : Fin 2 → ℝ)
    (hh : (lam 0 • faceCols F hF_dim_2 0 + lam 1 • faceCols F hF_dim_2 1) = 0) :
    ∀ k : Fin 2, lam k = 0 := by
  classical
  let b := faceDirBasis F hF_dim_2
  have hw : (lam 0 • b 0 + lam 1 • b 1 : (affineSpan ℝ F).direction) = 0 :=
    Subtype.ext (by simpa [faceCols, b] using hh)
  have h1 : b.repr (lam 0 • b 0 + lam 1 • b 1) = (0 : Fin 2 →₀ ℝ) := by rw [hw, map_zero]
  have h2 : b.repr (lam 0 • b 0 + lam 1 • b 1)
      = (lam 0 : ℝ) • Finsupp.single 0 1 + (lam 1 : ℝ) • Finsupp.single 1 1 := by
    rw [LinearEquiv.map_add, LinearEquiv.map_smul, LinearEquiv.map_smul,
      Module.Basis.repr_self (b := b), Module.Basis.repr_self (b := b)]
  rw [h2] at h1
  intro k
  have hk : k = 0 ∨ k = 1 := by
    have hlt := k.isLt
    have : k.val = 0 ∨ k.val = 1 := by omega
    rcases this with hz | ho
    · left; exact Fin.ext hz
    · right; exact Fin.ext ho
  have h3 := DFunLike.congr_fun h1 k
  simp only [Finsupp.zero_apply] at h3
  rcases hk with rfl | rfl
  · have e0 : ((lam 0 : ℝ) • Finsupp.single (0 : Fin 2) (1 : ℝ)
        + (lam 1 : ℝ) • Finsupp.single (1 : Fin 2) (1 : ℝ)) (0 : Fin 2)
        = lam 0 := by
      simp [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]
    rw [e0] at h3
    exact h3
  · have e1 : ((lam 0 : ℝ) • Finsupp.single (0 : Fin 2) (1 : ℝ)
        + (lam 1 : ℝ) • Finsupp.single (1 : Fin 2) (1 : ℝ)) (1 : Fin 2)
        = lam 1 := by
      simp [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)]
    rw [e1] at h3
    exact h3

/-! ### Case B helpers: transverse 2×2 determinant -/

/-- Determinant of the 2×2 real matrix `[Re c₀, Re c₁; Im c₀, Im c₁]`
where `cᵢ(s) = evalAtComplex s Vᵢ`. Nonvanishing at `s*` is exactly the
transversality `P_sc ∩ dir = ⊥` (textbook `[V,−W]` full-rank, Case B). -/
noncomputable def detOf {n : ℕ} (V0 V1 : CoeffVec n) (s : ℂ) : ℝ :=
  (evalAtComplex (n := n) s V0).re * (evalAtComplex (n := n) s V1).im -
    (evalAtComplex (n := n) s V1).re * (evalAtComplex (n := n) s V0).im

/-- Continuity of `detOf` in `s` (each entry is `Re/Im` of a polynomial in `s`). -/
lemma continuous_detOf {n : ℕ} (V0 V1 : CoeffVec n) :
    Continuous (fun s : ℂ => detOf (n := n) V0 V1 s) := by
  unfold detOf
  apply Continuous.sub
  · apply Continuous.mul
    · exact Complex.continuous_re.comp (continuous_evalAtComplex V0)
    · exact Complex.continuous_im.comp (continuous_evalAtComplex V1)
  · apply Continuous.mul
    · exact Complex.continuous_re.comp (continuous_evalAtComplex V1)
    · exact Complex.continuous_im.comp (continuous_evalAtComplex V0)

/-- Sequential form: `detOf` along a convergent sequence. -/
lemma tendsto_detOf {n : ℕ} (V0 V1 : CoeffVec n) {s_seq : ℕ → ℂ} {s_star : ℂ}
    (hs : Tendsto s_seq atTop (𝓝 s_star)) :
    Tendsto (fun k => detOf (n := n) V0 V1 (s_seq k)) atTop
      (𝓝 (detOf (n := n) V0 V1 s_star)) :=
  ((continuous_detOf (n := n) V0 V1).tendsto s_star).comp hs

/-- `ℝ`-smul on `ℂ` acts coordinate-wise on `Re/Im`. -/
private lemma real_smul_re (x : ℝ) (c : ℂ) : (x • c).re = x * c.re := by
  rw [Algebra.smul_def]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-- `ℝ`-smul on `ℂ` acts coordinate-wise on `Re/Im`. -/
private lemma real_smul_im (x : ℝ) (c : ℂ) : (x • c).im = x * c.im := by
  rw [Algebra.smul_def]
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

/-- Transversality implies the 2×2 determinant is nonzero.
If `det = 0`, an explicit nonzero kernel vector `(x,y)` gives
`x•V₀ + y•V₁ ∈ P_sc ⊓ dir = ⊥`, contradicting `faceCols` independence. -/
private lemma detOf_ne_zero_of_transverse {n : ℕ} (F : Set (CoeffVec n))
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2) (s_star : ℂ)
    (hinf : P_sc n s_star ⊓ (affineSpan ℝ F).direction = ⊥) :
    detOf (n := n) (faceCols F hF_dim_2 0) (faceCols F hF_dim_2 1) s_star ≠ 0 := by
  classical
  set V0 := faceCols F hF_dim_2 0 with hV0
  set V1 := faceCols F hF_dim_2 1 with hV1
  set c0 := evalAtComplex (n := n) s_star V0 with hc0
  set c1 := evalAtComplex (n := n) s_star V1 with hc1
  intro hdet
  have hdet_eq : c0.re * c1.im - c1.re * c0.im = 0 := hdet
  -- Build an explicit nonzero kernel vector for `M = [[Re c₀, Re c₁],[Im c₀, Im c₁]]`.
  obtain ⟨x, y, hne, hrow1, hrow2⟩ :
      ∃ x y : ℝ, ¬ (x = 0 ∧ y = 0) ∧
        (c0.re * x + c1.re * y = 0) ∧ (c0.im * x + c1.im * y = 0) := by
    by_cases hdc : c1.im = 0 ∧ c0.im = 0
    · obtain ⟨hd0, hc0im⟩ := hdc
      by_cases hab : c0.re = 0 ∧ c1.re = 0
      · obtain ⟨ha0, hb0⟩ := hab
        refine ⟨1, 0, by simp, ?_, ?_⟩
        · simp [ha0, hb0]
        · simp [hd0, hc0im]
      · -- second row is zero; kill the first row with `(-b, a)`
        refine ⟨-c1.re, c0.re, ?_, ?_, ?_⟩
        · intro hcon
          rcases hcon with ⟨h1, h2⟩
          apply hab
          constructor
          · linarith
          · linarith
        · ring
        · simp [hd0, hc0im]
    · -- `(d, -c) ≠ 0` kills both rows via `det = 0`
      refine ⟨c1.im, -c0.im, ?_, ?_, ?_⟩
      · intro hcon
        rcases hcon with ⟨h1, h2⟩
        apply hdc
        constructor
        · linarith
        · linarith
      · linarith [hdet_eq]
      · ring
  -- The corresponding direction vector lies in `P_sc ⊓ dir`.
  have heval : evalAtComplex (n := n) s_star (x • V0 + y • V1) = 0 := by
    have hRe : (evalAtComplex (n := n) s_star (x • V0 + y • V1)).re = 0 := by
      have hmap : (evalAtComplex (n := n) s_star (x • V0 + y • V1)).re =
          x * (evalAtComplex (n := n) s_star V0).re +
            y * (evalAtComplex (n := n) s_star V1).re := by
        rw [map_add, map_smul, map_smul, Complex.add_re, real_smul_re,
          real_smul_re]
      rw [hmap]
      have hc0r : (evalAtComplex (n := n) s_star V0).re = c0.re := rfl
      have hc1r : (evalAtComplex (n := n) s_star V1).re = c1.re := rfl
      rw [hc0r, hc1r]
      linarith [hrow1]
    have hIm : (evalAtComplex (n := n) s_star (x • V0 + y • V1)).im = 0 := by
      have hmap : (evalAtComplex (n := n) s_star (x • V0 + y • V1)).im =
          x * (evalAtComplex (n := n) s_star V0).im +
            y * (evalAtComplex (n := n) s_star V1).im := by
        rw [map_add, map_smul, map_smul, Complex.add_im, real_smul_im,
          real_smul_im]
      rw [hmap]
      have hc0i : (evalAtComplex (n := n) s_star V0).im = c0.im := rfl
      have hc1i : (evalAtComplex (n := n) s_star V1).im = c1.im := rfl
      rw [hc0i, hc1i]
      linarith [hrow2]
    exact Complex.ext hRe hIm
  have hmemU : x • V0 + y • V1 ∈ P_sc n s_star := by
    unfold P_sc
    rw [LinearMap.mem_ker]
    exact heval
  have hmemL : x • V0 + y • V1 ∈ (affineSpan ℝ F).direction := by
    apply _root_.Submodule.add_mem
    · apply _root_.Submodule.smul_mem
      exact faceCols_mem_dir F hF_dim_2 0
    · apply _root_.Submodule.smul_mem
      exact faceCols_mem_dir F hF_dim_2 1
  have hmemInf : x • V0 + y • V1 ∈ P_sc n s_star ⊓ (affineSpan ℝ F).direction :=
    ⟨hmemU, hmemL⟩
  rw [hinf] at hmemInf
  have hzero : x • V0 + y • V1 = 0 := by
    simpa using hmemInf
  have hlam : ∀ k : Fin 2, (fun i => if i = 0 then x else y) k = 0 := by
    have h' : ((fun i => if i = 0 then x else y) 0 • V0 +
        (fun i => if i = 0 then x else y) 1 • V1) = 0 := by
      simpa using hzero
    exact eq_zero_of_faceCols_combo F hF_dim_2 _ h'
  have hx0 : x = 0 := hlam 0
  have hy0 : y = 0 := by
    have := hlam 1
    simpa using this
  exact hne ⟨hx0, hy0⟩

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
      simp only [PscSet, P_sc] at h
      exact h
    have hroot : ((polyOfVec δ_hat).map (algebraMap ℝ ℂ)).IsRoot s_star := by
      rw [Polynomial.IsRoot]
      have h_eval : ((polyOfVec δ_hat).map (algebraMap ℝ ℂ)).eval s_star
          = evalAtComplex (n := n) s_star δ_hat := rfl
      rw [h_eval, hk]
    exact rootspace_mem_of_isRoot s_star δ_hat hroot (relativeBoundary F)
      ⟨hδ_hat_F, hδ_hat_notrelint⟩
  · -- Case B: transverse (`dim = 0`), textbook `[V,−W]` full-rank.
    -- Then `aff(F) ∩ P_sc = {δ*}`, and the approximating `sₙ → s*`
    -- give `δₙ ∈ aff(F) ∖ F` with `δₙ → δ*`, so `δ* ∈ ∂F`.
    have hdim0 : dim (P_sc n s_star ⊓ (affineSpan ℝ F).direction) = 0 := by
      omega
    have hinf : P_sc n s_star ⊓ (affineSpan ℝ F).direction = ⊥ :=
      (Submodule.finrank_eq_zero (R := ℝ) (M := CoeffVec n)).mp hdim0
    have hc : s_star ∈ closure (RootSpaceSet F)ᶜ := by
      rw [frontier_eq_closure_inter_closure] at hs_star_front
      exact hs_star_front.2
    obtain ⟨s_seq, hs_out, _hs_ne, hs_tendsto⟩ :=
      exists_seq_notin_RootSpaceSet_tendsto
        (rootspace_mem_of_isRoot s_star δ_star hδ_star_root F hδ_star_in_F) hc
    -- Face basis and determinant setup.
    set V0 := faceCols F hF_dim_2 0 with hV0def
    set V1 := faceCols F hF_dim_2 1 with hV1def
    have hV0dir : V0 ∈ (affineSpan ℝ F).direction := faceCols_mem_dir F hF_dim_2 0
    have hV1dir : V1 ∈ (affineSpan ℝ F).direction := faceCols_mem_dir F hF_dim_2 1
    have hdet_ne : detOf (n := n) V0 V1 s_star ≠ 0 :=
      detOf_ne_zero_of_transverse F hF_dim_2 s_star hinf
    have hdet_tendsto :
        Tendsto (fun k => detOf (n := n) V0 V1 (s_seq k)) atTop
          (𝓝 (detOf (n := n) V0 V1 s_star)) :=
      tendsto_detOf V0 V1 hs_tendsto
    have hev_det : ∀ᶠ k in atTop, detOf (n := n) V0 V1 (s_seq k) ≠ 0 :=
      hdet_tendsto.eventually_ne hdet_ne
    -- Evaluation data and its limits.
    have heval_star : evalAtComplex (n := n) s_star δ_star = 0 := by
      have h := hδ_star_Psc
      simp only [PscSet, P_sc] at h
      exact h
    have hrhs_tendsto :
        Tendsto (fun k => evalAtComplex (n := n) (s_seq k) δ_star) atTop (𝓝 0) := by
      have h := tendsto_evalAtComplex (n := n) hs_tendsto δ_star
      rwa [heval_star] at h
    have hc0_tendsto :
        Tendsto (fun k => evalAtComplex (n := n) (s_seq k) V0) atTop
          (𝓝 (evalAtComplex (n := n) s_star V0)) :=
      tendsto_evalAtComplex hs_tendsto V0
    have hc1_tendsto :
        Tendsto (fun k => evalAtComplex (n := n) (s_seq k) V1) atTop
          (𝓝 (evalAtComplex (n := n) s_star V1)) :=
      tendsto_evalAtComplex hs_tendsto V1
    have ha_tendsto : Tendsto (fun k => (evalAtComplex (n := n) (s_seq k) V0).re)
        atTop (𝓝 (evalAtComplex (n := n) s_star V0).re) :=
      (Complex.continuous_re.tendsto _).comp hc0_tendsto
    have hb_tendsto : Tendsto (fun k => (evalAtComplex (n := n) (s_seq k) V1).re)
        atTop (𝓝 (evalAtComplex (n := n) s_star V1).re) :=
      (Complex.continuous_re.tendsto _).comp hc1_tendsto
    have hc_tendsto : Tendsto (fun k => (evalAtComplex (n := n) (s_seq k) V0).im)
        atTop (𝓝 (evalAtComplex (n := n) s_star V0).im) :=
      (Complex.continuous_im.tendsto _).comp hc0_tendsto
    have hd_tendsto : Tendsto (fun k => (evalAtComplex (n := n) (s_seq k) V1).im)
        atTop (𝓝 (evalAtComplex (n := n) s_star V1).im) :=
      (Complex.continuous_im.tendsto _).comp hc1_tendsto
    have hb0_tendsto : Tendsto (fun k => -(evalAtComplex (n := n) (s_seq k) δ_star).re)
        atTop (𝓝 0) := by
      have h : Tendsto (fun k => (evalAtComplex (n := n) (s_seq k) δ_star).re)
          atTop (𝓝 (0 : ℝ)) := by
        have h0 : (evalAtComplex (n := n) s_star δ_star).re = 0 := by
          rw [heval_star]; rfl
        have h1 : Tendsto (fun k => (evalAtComplex (n := n) (s_seq k) δ_star).re)
            atTop (𝓝 (evalAtComplex (n := n) s_star δ_star).re) :=
          (Complex.continuous_re.tendsto _).comp
            (tendsto_evalAtComplex hs_tendsto δ_star)
        rwa [h0] at h1
      simpa using h.neg
    have hb1_tendsto : Tendsto (fun k => -(evalAtComplex (n := n) (s_seq k) δ_star).im)
        atTop (𝓝 0) := by
      have h : Tendsto (fun k => (evalAtComplex (n := n) (s_seq k) δ_star).im)
          atTop (𝓝 (0 : ℝ)) := by
        have h0 : (evalAtComplex (n := n) s_star δ_star).im = 0 := by
          rw [heval_star]; rfl
        have h1 : Tendsto (fun k => (evalAtComplex (n := n) (s_seq k) δ_star).im)
            atTop (𝓝 (evalAtComplex (n := n) s_star δ_star).im) :=
          (Complex.continuous_im.tendsto _).comp
            (tendsto_evalAtComplex hs_tendsto δ_star)
        rwa [h0] at h1
      simpa using h.neg
    -- Cramer's rule solution `λₖ` and points `δₖ ∈ aff(F)`.
    set detk : ℕ → ℝ := fun k => detOf (n := n) V0 V1 (s_seq k) with hdetk
    set ak : ℕ → ℝ := fun k => (evalAtComplex (n := n) (s_seq k) V0).re with hak
    set bk : ℕ → ℝ := fun k => (evalAtComplex (n := n) (s_seq k) V1).re with hbk
    set ck : ℕ → ℝ := fun k => (evalAtComplex (n := n) (s_seq k) V0).im with hck
    set dk : ℕ → ℝ := fun k => (evalAtComplex (n := n) (s_seq k) V1).im with hdk
    set b0k : ℕ → ℝ := fun k => -(evalAtComplex (n := n) (s_seq k) δ_star).re with hb0k
    set b1k : ℕ → ℝ := fun k => -(evalAtComplex (n := n) (s_seq k) δ_star).im with hb1k
    set lam0 : ℕ → ℝ := fun k => (b0k k * dk k - bk k * b1k k) / detk k with hlam0
    set lam1 : ℕ → ℝ := fun k => (ak k * b1k k - b0k k * ck k) / detk k with hlam1
    set deltak : ℕ → CoeffVec n :=
      fun k => δ_star + (lam0 k • V0 + lam1 k • V1) with hdeltak
    have hdet_star : detk = fun k => detOf (n := n) V0 V1 (s_seq k) := rfl
    have hlam0_tendsto : Tendsto lam0 atTop (𝓝 0) := by
      have hnum : Tendsto (fun k => b0k k * dk k - bk k * b1k k) atTop (𝓝 0) := by
        have h1 : Tendsto (fun k => b0k k * dk k) atTop (𝓝 (0 * (evalAtComplex (n := n) s_star V1).im)) :=
          hb0_tendsto.mul hd_tendsto
        have h2 : Tendsto (fun k => bk k * b1k k) atTop (𝓝 ((evalAtComplex (n := n) s_star V1).re * 0)) :=
          hb_tendsto.mul hb1_tendsto
        simpa using h1.sub h2
      have hden : Tendsto detk atTop (𝓝 (detOf (n := n) V0 V1 s_star)) := hdet_tendsto
      have := hnum.div hden hdet_ne
      simpa using this
    have hlam1_tendsto : Tendsto lam1 atTop (𝓝 0) := by
      have hnum : Tendsto (fun k => ak k * b1k k - b0k k * ck k) atTop (𝓝 0) := by
        have h1 : Tendsto (fun k => ak k * b1k k) atTop (𝓝 ((evalAtComplex (n := n) s_star V0).re * 0)) :=
          ha_tendsto.mul hb1_tendsto
        have h2 : Tendsto (fun k => b0k k * ck k) atTop (𝓝 (0 * (evalAtComplex (n := n) s_star V0).im)) :=
          hb0_tendsto.mul hc_tendsto
        simpa using h1.sub h2
      have hden : Tendsto detk atTop (𝓝 (detOf (n := n) V0 V1 s_star)) := hdet_tendsto
      have := hnum.div hden hdet_ne
      simpa using this
    have hδ_aff : δ_star ∈ affineSpan ℝ F := subset_affineSpan ℝ F hδ_star_in_F
    have hdeltak_aff : ∀ᶠ k in atTop, deltak k ∈ affineSpan ℝ F := by
      apply Eventually.of_forall
      intro k
      have hcombo : lam0 k • V0 + lam1 k • V1 ∈ (affineSpan ℝ F).direction := by
        apply _root_.Submodule.add_mem
        · apply _root_.Submodule.smul_mem _ _ hV0dir
        · apply _root_.Submodule.smul_mem _ _ hV1dir
      have hmem := AffineSubspace.vadd_mem_of_mem_direction hcombo hδ_aff
      have h_eq : ((lam0 k • V0 + lam1 k • V1) +ᵥ δ_star : CoeffVec n) =
          deltak k := by
        simp only [hdeltak, vadd_eq_add]
        rw [add_comm]
      rwa [h_eq] at hmem
    -- `δₖ` carries root `sₖ` whenever `detₖ ≠ 0` (Cramer solves `Mₖλ = b`).
    have hev_root : ∀ᶠ k in atTop,
        evalAtComplex (n := n) (s_seq k) (deltak k) = 0 := by
      filter_upwards [hev_det] with k hk
      have hkdet : detk k ≠ 0 := by simpa [hdetk] using hk
      have hdet_eq : detk k = ak k * dk k - bk k * ck k := by
        simp [hdetk, hak, hbk, hck, hdk, detOf]
      have hM0 : ak k * lam0 k + bk k * lam1 k = b0k k := by
        simp only [hlam0, hlam1]
        field_simp
        rw [hdet_eq]
        ring
      have hM1 : ck k * lam0 k + dk k * lam1 k = b1k k := by
        simp only [hlam0, hlam1]
        field_simp
        rw [hdet_eq]
        ring
      have heval_eq : evalAtComplex (n := n) (s_seq k) (deltak k) =
          evalAtComplex (n := n) (s_seq k) δ_star +
            (lam0 k • evalAtComplex (n := n) (s_seq k) V0 +
              lam1 k • evalAtComplex (n := n) (s_seq k) V1) := by
        simp [hdeltak, map_add, map_smul]
      have hRe : (evalAtComplex (n := n) (s_seq k) (deltak k)).re = 0 := by
        rw [heval_eq, Complex.add_re, Complex.add_re, real_smul_re, real_smul_re]
        have hrhs : (evalAtComplex (n := n) (s_seq k) δ_star).re = -b0k k := by
          simp [hb0k]
        have ha0 : (evalAtComplex (n := n) (s_seq k) V0).re = ak k := rfl
        have hb0 : (evalAtComplex (n := n) (s_seq k) V1).re = bk k := rfl
        rw [hrhs, ha0, hb0]
        linarith [hM0]
      have hIm : (evalAtComplex (n := n) (s_seq k) (deltak k)).im = 0 := by
        rw [heval_eq, Complex.add_im, Complex.add_im, real_smul_im, real_smul_im]
        have hrhs : (evalAtComplex (n := n) (s_seq k) δ_star).im = -b1k k := by
          simp [hb1k]
        have hc0 : (evalAtComplex (n := n) (s_seq k) V0).im = ck k := rfl
        have hd0 : (evalAtComplex (n := n) (s_seq k) V1).im = dk k := rfl
        rw [hrhs, hc0, hd0]
        linarith [hM1]
      exact Complex.ext hRe hIm
    have hev_notF : ∀ᶠ k in atTop, deltak k ∉ F := by
      filter_upwards [hev_root, hdeltak_aff] with k hk haff
      intro hmem
      have hroot : ((polyOfVec (deltak k)).map (algebraMap ℝ ℂ)).IsRoot (s_seq k) := by
        rw [Polynomial.IsRoot]
        have h_eval : ((polyOfVec (deltak k)).map (algebraMap ℝ ℂ)).eval (s_seq k)
            = evalAtComplex (n := n) (s_seq k) (deltak k) := rfl
        rw [h_eval, hk]
      exact hs_out k (rootspace_mem_of_isRoot _ _ hroot F hmem)
    have hdeltak_tendsto : Tendsto deltak atTop (𝓝 δ_star) := by
      have hzero_tendsto : Tendsto (fun k => lam0 k • V0 + lam1 k • V1) atTop (𝓝 0) := by
        have h1 : Tendsto (fun k => lam0 k • V0) atTop (𝓝 ((0 : ℝ) • V0)) :=
          hlam0_tendsto.smul tendsto_const_nhds
        have h2 : Tendsto (fun k => lam1 k • V1) atTop (𝓝 ((0 : ℝ) • V1)) :=
          hlam1_tendsto.smul tendsto_const_nhds
        simpa using h1.add h2
      have hadd : Tendsto (fun k => δ_star + (lam0 k • V0 + lam1 k • V1)) atTop
          (𝓝 (δ_star + 0)) :=
        tendsto_const_nhds.add hzero_tendsto
      simpa [hdeltak] using hadd
    -- Hence `δ* ∉ ri(F)`; otherwise `δₖ ∈ F` eventually, contradiction.
    have hdeltak_aff_all : ∀ k, deltak k ∈ affineSpan ℝ F := by
      intro k
      have hcombo : lam0 k • V0 + lam1 k • V1 ∈ (affineSpan ℝ F).direction := by
        apply _root_.Submodule.add_mem
        · apply _root_.Submodule.smul_mem _ _ hV0dir
        · apply _root_.Submodule.smul_mem _ _ hV1dir
      have hmem := AffineSubspace.vadd_mem_of_mem_direction hcombo hδ_aff
      have h_eq : ((lam0 k • V0 + lam1 k • V1) +ᵥ δ_star : CoeffVec n) =
          deltak k := by
        simp only [hdeltak, vadd_eq_add]
        rw [add_comm]
      rwa [h_eq] at hmem
    have hnot_ri : δ_star ∉ intrinsicInterior ℝ F := by
      intro hri
      have hpre : (⟨δ_star, hδ_aff⟩ : affineSpan ℝ F) ∈
          interior ((Subtype.val : affineSpan ℝ F → CoeffVec n) ⁻¹' F) := by
        have h_eq : intrinsicInterior ℝ F =
            (Subtype.val : affineSpan ℝ F → CoeffVec n) ''
              interior ((Subtype.val : affineSpan ℝ F → CoeffVec n) ⁻¹' F) := rfl
        rw [h_eq] at hri
        rcases hri with ⟨y, hy, hy_val⟩
        have hy_eq : y = ⟨δ_star, hδ_aff⟩ := Subtype.ext hy_val
        rwa [hy_eq] at hy
      have hopen : IsOpen (interior ((Subtype.val : affineSpan ℝ F → CoeffVec n) ⁻¹' F)) :=
        isOpen_interior
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen _ hpre
      have hsub_tendsto : Tendsto
          (fun k : ℕ => (⟨deltak k, hdeltak_aff_all k⟩ : affineSpan ℝ F))
          atTop (𝓝 ⟨δ_star, hδ_aff⟩) := by
        rw [Metric.tendsto_atTop]
        intro ε' hε'
        obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdeltak_tendsto ε' hε'
        exact ⟨N, fun k hk => hN k hk⟩
      obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hsub_tendsto ε hε
      have hev_inF : ∀ᶠ k in atTop, deltak k ∈ F := by
        rw [eventually_atTop]
        refine ⟨N0, fun k hk => ?_⟩
        have hk_dist := hN0 k hk
        have hk_ball : (⟨deltak k, hdeltak_aff_all k⟩ : affineSpan ℝ F) ∈
            Metric.ball (⟨δ_star, hδ_aff⟩ : affineSpan ℝ F) ε :=
          Metric.mem_ball.mpr hk_dist
        have hk_in : (⟨deltak k, hdeltak_aff_all k⟩ : affineSpan ℝ F) ∈
            interior ((Subtype.val : affineSpan ℝ F → CoeffVec n) ⁻¹' F) :=
          hball hk_ball
        have hmem_pre : (⟨deltak k, hdeltak_aff_all k⟩ : affineSpan ℝ F) ∈
            (Subtype.val : affineSpan ℝ F → CoeffVec n) ⁻¹' F :=
          interior_subset hk_in
        exact hmem_pre
      obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev_inF
      obtain ⟨N2, hN2⟩ := eventually_atTop.mp hev_notF
      have h1N : deltak (max N1 N2) ∈ F := hN1 _ (le_max_left _ _)
      have h2N : deltak (max N1 N2) ∉ F := hN2 _ (le_max_right _ _)
      exact h2N h1N
    have hrel : δ_star ∈ relativeBoundary F := ⟨hδ_star_in_F, hnot_ri⟩
    exact rootspace_mem_of_isRoot s_star δ_star hδ_star_root (relativeBoundary F) hrel

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
