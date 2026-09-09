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

/-! ### Affine parametrization of the face -/

/-- A basis of the direction of `affineSpan ℝ F` indexed by `Fin 2`, from
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

/-- Complex case of Lemma 6.2:
    If `s*` is a non-real point on the frontier of `RootSpaceSet F` (where `F` is an
    exposed face of dimension 2), then `s*` is a root of a coefficient vector
    on the relative boundary of `F`. -/
theorem lemma62_complex_case {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2)
    (s_star : ℂ) (hs_star_front : s_star ∈ frontier (RootSpaceSet F)) (hcomplex : s_star.im ≠ 0) :
    s_star ∈ RootSpaceSet (relativeBoundary F) := by
  have h_polytope : IsPolytopeSet F := isExposedFace_isPolytopeSet P hF_exp
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
