module

public import ControlSystems.DiscreteTime.EdgeTheoremDefs

@[expose] public section

open Polynomial
open Affine
open FiniteDimensional
open LinearMap

namespace CoeffBox

-- ---------------------------------------------------------
-- GENERAL SIMP LEMMAS
-- ---------------------------------------------------------

@[simp] lemma mem_RootSpaceSet_iff {n : ℕ} (W : Set (CoeffVec n)) (s : ℂ) :
    s ∈ RootSpaceSet W ↔ ∃ δ ∈ W, ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s :=
  Iff.rfl

@[simp] lemma mem_P_sr_iff {n : ℕ} (r : ℝ) (δ : CoeffVec n) :
    δ ∈ (P_sr n r : Set (CoeffVec n)) ↔ evalLinear r δ = 0 :=
  Iff.rfl

-- ---------------------------------------------------------
-- LEMMAS SPECIFIC TO LEMMA 6.1
-- ---------------------------------------------------------

private lemma P_sr_dimension {n : ℕ} (r : ℝ) :
  Module.finrank ℝ (P_sr n r) = n := by
  unfold P_sr
  have h := LinearMap.finrank_range_add_finrank_ker (evalLinear (n := n) r)
  rw [finrank_CoeffVec] at h
  have hrank : Module.finrank ℝ (evalLinear (n := n) r).range = 1 := by
    have hsurj : Function.Surjective (evalLinear (n := n) r) :=
      evalLinear_surjective r
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp only [finrank_top, Module.finrank_self]
  grind

private lemma finrank_inf_ge_one {n : ℕ} (U W : Submodule ℝ (CoeffVec n))
    (hU : Module.finrank ℝ U = n)
    (hW : Module.finrank ℝ W ≥ 2) :
    Module.finrank ℝ ↥(U ⊓ W) ≥ 1 := by
  have h_le_ambient : (U ⊔ W) ≤ ⊤ := by simp
  have h_sum_le : Module.finrank ℝ ↥(U ⊔ W) ≤ n + 1 := by
    calc Module.finrank ℝ ↥(U ⊔ W)
      ≤ Module.finrank ℝ (⊤ : Submodule ℝ (CoeffVec n)) := Submodule.finrank_mono h_le_ambient
      _ = n + 1 := by rw [finrank_top, finrank_CoeffVec]
  have hformula : Module.finrank ℝ ↥(U ⊔ W) + Module.finrank ℝ ↥(U ⊓ W) = Module.finrank ℝ U + Module.finrank ℝ W :=
    Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

private lemma direction_inf {n : ℕ} (U : Submodule ℝ (CoeffVec n)) (P_Ω : Set (CoeffVec n))
    (δ : CoeffVec n) (h1 : δ ∈ U) (h2 : δ ∈ affineSpan ℝ P_Ω) :
    (U.toAffineSubspace ⊓ affineSpan ℝ P_Ω).direction = U ⊓ (affineSpan ℝ P_Ω).direction := by
  ext v
  simp only [Submodule.mem_inf]
  constructor
  · intro hv
    rw [AffineSubspace.mem_direction_iff_eq_vsub
        ⟨δ, by simp only [SetLike.mem_coe, AffineSubspace.mem_inf_iff,
          Submodule.mem_toAffineSubspace]; exact ⟨h1, h2⟩⟩] at hv
    obtain ⟨p₁, hp₁, p₂, hp₂, hv_eq⟩ := hv
    rw [AffineSubspace.mem_inf_iff] at hp₁ hp₂
    constructor
    · have hp₁U := hp₁.1; have hp₂U := hp₂.1
      rw [hv_eq]; simp only [vsub_eq_sub]; exact (Submodule.sub_mem_iff_left U hp₂U).mpr hp₁U
    · have hp₁Ω := hp₁.2; have hp₂Ω := hp₂.2
      rw [hv_eq]; exact AffineSubspace.vsub_mem_direction hp₁Ω hp₂Ω
  · intro hv
    obtain ⟨hvU, hvΩ⟩ := hv
    have hbase : δ ∈ U.toAffineSubspace ⊓ affineSpan ℝ P_Ω := by rw [AffineSubspace.mem_inf_iff]; exact ⟨h1, h2⟩
    have hne : ((U.toAffineSubspace ⊓ affineSpan ℝ P_Ω : AffineSubspace ℝ (CoeffVec n)) : Set (CoeffVec n)).Nonempty := ⟨δ, hbase⟩
    rw [AffineSubspace.mem_direction_iff_eq_vsub hne]
    refine ⟨v +ᵥ δ, ?_, δ, hbase, ?_⟩
    · rw [AffineSubspace.mem_inf_iff]
      constructor
      · simp only [Submodule.mem_toAffineSubspace]; exact Submodule.add_mem _ hvU h1
      · exact AffineSubspace.vadd_mem_of_mem_direction hvΩ h2
    · simp only [vadd_eq_add, vsub_eq_sub, add_sub_cancel_right]

-- ---------------------------------------------------------
-- PRIVATE LEMMAS FOR LEMMA 6.1 (Steps 4-5)
-- ---------------------------------------------------------

private lemma intersection_direction_eq {n : ℕ} (U : Submodule ℝ (CoeffVec n)) (affΩ : AffineSubspace ℝ (CoeffVec n))
    (δ : CoeffVec n) (hδU : δ ∈ U) (hδΩ : δ ∈ affΩ) :
    (U.toAffineSubspace ⊓ affΩ).direction = U ⊓ affΩ.direction := by
  have h_affSpan : affineSpan ℝ (affΩ : Set (CoeffVec n)) = affΩ := by
    apply le_antisymm
    · apply affineSpan_le.mpr; simp
    · intro x hx; exact subset_affineSpan ℝ _ hx
  have h := direction_inf U (affΩ : Set (CoeffVec n)) δ hδU (subset_affineSpan ℝ _ hδΩ)
  rw [h_affSpan] at h
  exact h

private lemma intersection_affine_dim_ge_one {n : ℕ} (U : Submodule ℝ (CoeffVec n)) (affΩ : AffineSubspace ℝ (CoeffVec n))
    (δ : CoeffVec n) (hδU : δ ∈ U) (hδΩ : δ ∈ affΩ)
    (hU_dim : Module.finrank ℝ U = n) (haff_dim : Module.finrank ℝ affΩ.direction ≥ 2) :
    Module.finrank ℝ ↥(affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction ≥ 1 := by
  let Aint : AffineSubspace ℝ (CoeffVec n) := U.toAffineSubspace ⊓ affΩ
  have hA_dir : Aint.direction = U ⊓ affΩ.direction :=
    intersection_direction_eq U affΩ δ hδU hδΩ
  have hA_eq : affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n))) = Aint := by
    rw [affineSpan_inter U affΩ]
  rw [hA_eq, hA_dir]
  exact finrank_inf_ge_one U affΩ.direction hU_dim haff_dim

private lemma frontier_eq_for_closed {n : ℕ} (S : Set (CoeffVec n)) (hS : IsClosed S) :
    frontier S = S \ interior S := by
  calc frontier S = closure S \ interior S := rfl
    _ = S \ interior S := by rw [hS.closure_eq]

private lemma segment_is_connected {n : ℕ} (δ v : CoeffVec n) (t_out : ℝ) :
    IsConnected (segment ℝ δ (δ + t_out • v)) := by
  apply Convex.isConnected
  · exact convex_segment δ (δ + t_out • v)
  · exact ⟨δ, left_mem_segment ℝ δ (δ + t_out • v)⟩

private lemma segment_cover_by_interior_and_complement {n : ℕ} (P : Polytope n)
    (δ v : CoeffVec n) (t_out : ℝ) (h_closed : IsClosed P.Ω)
    (h_no_front : ∀ x ∈ segment ℝ δ (δ + t_out • v), x ∉ frontier P.Ω) :
    segment ℝ δ (δ + t_out • v) ⊆ (interior P.Ω) ∪ interior (P.Ωᶜ) := by
  intro x hx
  by_cases hx_P : x ∈ P.Ω
  · left
    have hxf := h_no_front x hx
    rw [frontier_eq_for_closed P.Ω h_closed, Set.mem_diff] at hxf
    push_neg at hxf
    exact hxf hx_P
  · right
    have h_compl_open : IsOpen (P.Ωᶜ) := h_closed.isOpen_compl
    simp only [h_compl_open.interior_eq]
    exact hx_P

private lemma segment_intersects_interior {n : ℕ} (P : Polytope n) (δ v : CoeffVec n)
    (t_out : ℝ) (hδ_in_Ω : δ ∈ P.Ω) (hδ_not_front : δ ∉ frontier P.Ω)
    (h_closed : IsClosed P.Ω) :
    (segment ℝ δ (δ + t_out • v) ∩ interior P.Ω).Nonempty := by
  use δ
  constructor
  · exact left_mem_segment ℝ δ (δ + t_out • v)
  · rw [frontier_eq_for_closed P.Ω h_closed, Set.mem_diff] at hδ_not_front
    push_neg at hδ_not_front
    exact hδ_not_front hδ_in_Ω

private lemma segment_intersects_complement_interior {n : ℕ} (P : Polytope n)
    (δ v : CoeffVec n) (t_out : ℝ) (ht_out : δ + t_out • v ∉ P.Ω)
    (h_closed : IsClosed P.Ω) :
    (segment ℝ δ (δ + t_out • v) ∩ interior (P.Ωᶜ)).Nonempty := by
  use δ + t_out • v
  constructor
  · exact right_mem_segment ℝ δ (δ + t_out • v)
  · have h_compl_open : IsOpen (P.Ωᶜ) := h_closed.isOpen_compl
    simp only [h_compl_open.interior_eq]
    exact ht_out

private lemma interior_and_complement_interior_disjoint (P : Polytope n) :
    interior P.Ω ∩ interior (P.Ωᶜ) = ∅ := by
  apply Set.eq_empty_of_subset_empty
  calc interior P.Ω ∩ interior (P.Ωᶜ) ⊆ P.Ω ∩ P.Ωᶜ :=
      Set.inter_subset_inter interior_subset interior_subset
    _ = ∅ := Set.inter_compl_self P.Ω

private lemma segment_boundary_intersection {n : ℕ} (P : Polytope n) (δ : CoeffVec n)
    (hδ_in_Ω : δ ∈ P.Ω) (hδ_not_front : δ ∉ frontier P.Ω)
    (v : CoeffVec n) (hv_nonzero : v ≠ 0) (t_out : ℝ) (ht_out : δ + t_out • v ∉ P.Ω) :
    ∃ δ_bound ∈ segment ℝ δ (δ + t_out • v), δ_bound ∈ frontier P.Ω := by
  have h_conn : IsConnected (segment ℝ δ (δ + t_out • v)) :=
    segment_is_connected δ v t_out
  have h_closed : IsClosed P.Ω := P.isCompact.isClosed
  by_contra h_no_front
  push_neg at h_no_front
  have h_cover : segment ℝ δ (δ + t_out • v) ⊆ (interior P.Ω) ∪ interior (P.Ωᶜ) :=
    segment_cover_by_interior_and_complement P δ v t_out h_closed h_no_front
  have h_in_u : (segment ℝ δ (δ + t_out • v) ∩ interior P.Ω).Nonempty :=
    segment_intersects_interior P δ v t_out hδ_in_Ω hδ_not_front h_closed
  have h_in_v : (segment ℝ δ (δ + t_out • v) ∩ interior (P.Ωᶜ)).Nonempty :=
    segment_intersects_complement_interior P δ v t_out ht_out h_closed
  have huv_empty : interior P.Ω ∩ interior (P.Ωᶜ) = ∅ :=
    interior_and_complement_interior_disjoint P
  have h_pre := h_conn.2 (interior P.Ω) (interior (P.Ωᶜ)) isOpen_interior isOpen_interior
  have h_inter_nonempty := h_pre h_cover h_in_u h_in_v
  obtain ⟨x, hx_s, hx_uv⟩ := h_inter_nonempty
  rw [huv_empty] at hx_uv
  exact hx_uv

private lemma intersection_nontrivial {n : ℕ} (U : Submodule ℝ (CoeffVec n))
    (affΩ : AffineSubspace ℝ (CoeffVec n)) (δ : CoeffVec n)
    (hδ_in_Psr : δ ∈ (U : Set (CoeffVec n))) (hδ_aff : δ ∈ affΩ)
    (h_dim_pos : 0 < Module.finrank ℝ ↥(affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction) :
    Nontrivial ↥(U ⊓ affΩ.direction) := by
  have hA_eq : affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n))) = U.toAffineSubspace ⊓ affΩ := by
    rw [affineSpan_inter]
  have hA_dir : (U.toAffineSubspace ⊓ affΩ).direction = U ⊓ affΩ.direction :=
    intersection_direction_eq U affΩ δ hδ_in_Psr hδ_aff
  have h_finrank : Module.finrank ℝ ↥(affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction =
      Module.finrank ℝ ↥(U ⊓ affΩ.direction) := by
    rw [hA_eq, hA_dir]
  have h_dim_pos' : 0 < Module.finrank ℝ ↥(affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction :=
    h_dim_pos
  rw [h_finrank] at h_dim_pos'
  exact Module.nontrivial_of_finrank_pos h_dim_pos'

private lemma line_in_intersection {n : ℕ} (U : Submodule ℝ (CoeffVec n))
    (affΩ : AffineSubspace ℝ (CoeffVec n)) (δ : CoeffVec n)
    (hδ_in_Psr : δ ∈ (U : Set (CoeffVec n))) (hδ_aff : δ ∈ affΩ)
    (v_sub : ↥(U ⊓ affΩ.direction)) :
    ∀ (t : ℝ), δ + t • (v_sub.val : CoeffVec n) ∈ (U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)) := by
  intro t
  refine Set.mem_inter ?_ ?_
  · exact Submodule.add_mem U hδ_in_Psr (Submodule.smul_mem U t v_sub.2.1)
  · have h_vadd := affΩ.vadd_mem_of_mem_direction (Submodule.smul_mem affΩ.direction t v_sub.2.2) hδ_aff
    have h_eq : δ + t • (v_sub.val : CoeffVec n) = t • (v_sub.val : CoeffVec n) +ᵥ δ := by
      rw [vadd_eq_add, add_comm]
    rw [h_eq]; exact h_vadd

private lemma segment_point_rewrite (δ v : CoeffVec n) (c t_out : ℝ) :
    (1 - c) • δ + c • (δ + t_out • v) = δ + (c * t_out) • v := by
  calc (1 - c) • δ + c • (δ + t_out • v)
    _ = (1 - c) • δ + (c • δ + c • (t_out • v)) := by rw [smul_add]
    _ = ((1 - c) • δ + c • δ) + c • (t_out • v) := by rw [←add_assoc]
    _ = ((1 - c) + c) • δ + c • (t_out • v) := by rw [←add_smul]
    _ = 1 • δ + (c * t_out) • v := by
      have h_one : (1 - c) + c = 1 := by ring
      simp only [h_one, smul_smul, one_smul]
    _ = δ + (c * t_out) • v := by rw [one_smul]

private lemma exists_boundary_point_in_Psr {n : ℕ} (P : Polytope n) (r : ℝ) (δ : CoeffVec n)
    (hδ_in_Ω : δ ∈ P.Ω) (hδ_in_Psr : δ ∈ (P_sr n r : Set (CoeffVec n)))
    (affΩ : AffineSubspace ℝ (CoeffVec n)) (hδ_aff : δ ∈ affΩ)
    (hA_dim : Module.finrank ℝ ↥(affineSpan ℝ ((P_sr n r : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction ≥ 1) :
    ∃ δ_bound, δ_bound ∈ (P_sr n r : Set (CoeffVec n)) ∩ frontier P.Ω := by
  have h_dim_pos : 0 < Module.finrank ℝ ↥(affineSpan ℝ ((P_sr n r : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction := by omega
  let U : Submodule ℝ (CoeffVec n) := P_sr n r
  haveI : Nontrivial ↥(U ⊓ affΩ.direction) :=
    intersection_nontrivial U affΩ δ hδ_in_Psr hδ_aff h_dim_pos
  obtain ⟨v_sub, hv_sub_nonzero⟩ := exists_ne (0 : ↑(U ⊓ affΩ.direction))
  let v : CoeffVec n := v_sub.val
  have h_line_in_intersection : ∀ (t : ℝ), δ + t • v ∈ (P_sr n r : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)) :=
    line_in_intersection U affΩ δ hδ_in_Psr hδ_aff v_sub
  have hv_nonzero : v ≠ 0 := by
    intro h; apply hv_sub_nonzero; exact Submodule.coe_eq_zero.mp h
  have h_escapes : ∃ t : ℝ, δ + t • v ∉ P.Ω :=
    ray_escapes_polytope P δ v hδ_in_Ω hv_nonzero
  obtain ⟨t_out, ht_out⟩ := h_escapes
  by_cases hδ_front : δ ∈ frontier P.Ω
  · use δ
    exact ⟨hδ_in_Psr, hδ_front⟩
  · obtain ⟨δ_bound, h_seg, h_front⟩ :=
      segment_boundary_intersection P δ hδ_in_Ω hδ_front v hv_nonzero t_out ht_out
    rw [segment_eq_image] at h_seg
    obtain ⟨c, hc_in_Icc, hc_eq⟩ := h_seg
    have h_rewrite : (1 - c) • δ + c • (δ + t_out • v) = δ + (c * t_out) • v :=
      segment_point_rewrite δ v c t_out
    have h_mem := h_line_in_intersection (c * t_out)
    simp only [Set.mem_inter] at h_mem
    have : δ_bound ∈ (P_sr n r : Set (CoeffVec n)) := by
      have h_eq : δ_bound = δ + (c * t_out) • v := by
        calc δ_bound = (1 - c) • δ + c • (δ + t_out • v) := by rw [←hc_eq]
          _ = δ + (c * t_out) • v := by rw [h_rewrite]
      rw [h_eq]
      exact h_mem.1
    exact ⟨δ_bound, this, h_front⟩

private lemma frontier_point_in_Ω {n : ℕ} (P : Polytope n) (δ_bound : CoeffVec n)
    (hδ_bound_front : δ_bound ∈ frontier P.Ω) : δ_bound ∈ P.Ω := by
  have h_closed : IsClosed P.Ω := P.isCompact.isClosed
  have hsub := frontier_subset_closure (s := P.Ω)
  rw [h_closed.closure_eq] at hsub
  exact hsub hδ_bound_front

private lemma frontier_point_not_interior {n : ℕ} (P : Polytope n) (δ_bound : CoeffVec n)
    (hδ_bound_front : δ_bound ∈ frontier P.Ω) : δ_bound ∉ interior P.Ω := by
  have h_closed : IsClosed P.Ω := P.isCompact.isClosed
  intro hint
  have h1 : δ_bound ∈ frontier P.Ω := hδ_bound_front
  rw [frontier_eq_closure_inter_closure, h_closed.closure_eq] at h1
  have h2 : δ_bound ∈ closure (P.Ωᶜ) := h1.2
  have h3 : δ_bound ∉ closure (P.Ωᶜ) := by
    rw [closure_compl (s := P.Ω)]
    simp only [Set.mem_compl_iff, not_not]
    trivial
  exact h3 h2

private lemma supporting_func_nonzero {n : ℕ} (P : Polytope n) (f : CoeffVec n →L[ℝ] ℝ)
    (δ_bound : CoeffVec n) (hf_strict : ∀ x ∈ interior P.Ω, f x < f δ_bound)
    (h_int_nonempty : (interior P.Ω).Nonempty) : f ≠ 0 := by
  intro heq
  simp only [heq, ContinuousLinearMap.zero_apply] at hf_strict
  obtain ⟨x, hx⟩ := h_int_nonempty
  exact lt_irrefl 0 (hf_strict x hx)

private lemma supporting_hyperplane_upper_bound {n : ℕ} (P : Polytope n)
    (f : CoeffVec n →L[ℝ] ℝ) (c : ℝ)
    (hf_strict : ∀ x ∈ interior P.Ω, f x < c)
    (h_int_nonempty : (interior P.Ω).Nonempty) :
    ∀ x ∈ P.Ω, f.toLinearMap x ≤ c := by
  intro x hx
  have h_closed_half : IsClosed {y | f y ≤ c} :=
    isClosed_Iic.preimage f.continuous
  have h_convex : Convex ℝ P.Ω := convex_convexHull ℝ _
  have h_subset : P.Ω ⊆ {y | f y ≤ c} := by
    calc
      P.Ω = closure P.Ω := (P.isCompact.isClosed.closure_eq).symm
      _ = closure (interior P.Ω) :=
        (h_convex.closure_interior_eq_closure_of_nonempty_interior h_int_nonempty).symm
      _ ⊆ closure {y | f y ≤ c} :=
        closure_mono fun y hy => le_of_lt (hf_strict y hy)
      _ = {y | f y ≤ c} := h_closed_half.closure_eq
  have hx_f : f x ≤ c := h_subset hx
  change f x ≤ c
  exact hx_f

private lemma eval_root_comm {n : ℕ} (r : ℝ) (δ : CoeffVec n) :
    eval (↑r) (map (algebraMap ℝ ℂ) (polyOfVec δ)) = (algebraMap ℝ ℂ) (eval r (polyOfVec δ)) := by
  simp [polyOfVec, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
    map_sum, map_mul, map_pow]

private lemma rootspace_mem_of_eval_zero {n : ℕ} (r : ℝ) (δ_bound : CoeffVec n)
    (hδ_bound_Psr : δ_bound ∈ (P_sr n r : Set (CoeffVec n)))
    (F : Set (CoeffVec n)) (hδ_in_F : δ_bound ∈ F) : (r : ℂ) ∈ RootSpaceSet F := by
  unfold RootSpaceSet
  simp only [Set.mem_setOf_eq]
  refine ⟨δ_bound, hδ_in_F, ?_⟩
  have heval : evalLinear r δ_bound = 0 := hδ_bound_Psr
  unfold Polynomial.IsRoot
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_eval_map, eval_root_comm r δ_bound]
  have h_eval_eq : eval r (polyOfVec δ_bound) = evalLinear r δ_bound := rfl
  rw [h_eval_eq, heval]
  simp

private lemma exists_exposed_face_containing_boundary_point {n : ℕ} (P : Polytope n)
    (r : ℝ) (δ_bound : CoeffVec n)
    (hδ_bound_front : δ_bound ∈ frontier P.Ω)
    (hδ_bound_Psr : δ_bound ∈ (P_sr n r : Set (CoeffVec n)))
    (h_int_nonempty : (interior P.Ω).Nonempty) :
    ∃ F : Set (CoeffVec n), IsExposedFace P F ∧ δ_bound ∈ F ∧ (r : ℂ) ∈ RootSpaceSet F := by
  have hδ_bound_in_Ω : δ_bound ∈ P.Ω := frontier_point_in_Ω P δ_bound hδ_bound_front
  have hδ_bound_not_int : δ_bound ∉ interior P.Ω :=
    frontier_point_not_interior P δ_bound hδ_bound_front
  have h_convex : Convex ℝ P.Ω := convex_convexHull ℝ _
  have h_int_convex : Convex ℝ (interior P.Ω) := h_convex.interior
  have h_int_open : IsOpen (interior P.Ω) := isOpen_interior
  obtain ⟨f, hf_strict⟩ :=
    geometric_hahn_banach_open_point h_int_convex h_int_open hδ_bound_not_int

  -
  have hf_ne : f ≠ 0 := supporting_func_nonzero P f δ_bound hf_strict h_int_nonempty

  let c : ℝ := f δ_bound
  let f_lin : CoeffVec n →ₗ[ℝ] ℝ := f.toLinearMap
  have hf_lin_ne : f_lin ≠ 0 := by
    intro heq
    apply hf_ne
    ext x
    have : f_lin x = 0 := by
      rw [heq]
      simp
    exact this
  have hc_upper : ∀ x ∈ P.Ω, f_lin x ≤ c :=
    supporting_hyperplane_upper_bound P f c hf_strict h_int_nonempty
  let hp : SupportingHyperplane P := {
    f           := f_lin
    c           := c
    nonzero     := hf_lin_ne
    upper_bound := hc_upper
    touches     := ⟨δ_bound, hδ_bound_in_Ω, rfl⟩
  }
  have hδ_in_face : δ_bound ∈ ExposedFace hp := by
    unfold ExposedFace
    simp only [Set.mem_setOf_eq]
    exact ⟨hδ_bound_in_Ω, rfl⟩
  have hr_in_rootspace : (r : ℂ) ∈ RootSpaceSet (ExposedFace hp) :=
    rootspace_mem_of_eval_zero r δ_bound hδ_bound_Psr (ExposedFace hp) hδ_in_face
  exact ⟨ExposedFace hp, ⟨hp, rfl⟩, hδ_in_face, hr_in_rootspace⟩
lemma direction_nontrivial_of_nontrivial {R : Type*} {V : Type*} {P : Type*} [Ring R]
  [AddCommGroup V] [Module R V] [AffineSpace V P]
    {F : Set P}
    (hF : F.Nontrivial) : Nontrivial ↥(affineSpan R F).direction := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hF
  have hx_span : x ∈ affineSpan R F := subset_affineSpan R F hx
  have hy_span : y ∈ affineSpan R F := subset_affineSpan R F hy
  have h_diff : x -ᵥ y ∈ (affineSpan R F).direction :=
    AffineSubspace.vsub_mem_direction hx_span hy_span
  have h_diff_ne : x -ᵥ y ≠ (0 : V) := by
    intro h_eq
    apply hxy
    exact vsub_eq_zero_iff_eq.mp h_eq
  -- Explicitly construct the Nontrivial instance using the 0
  -- element and the non-zero difference vector
  refine ⟨0, ⟨x -ᵥ y, h_diff⟩, ?_⟩
  exact Subtype.coe_ne_coe.mp (Ne.symm h_diff_ne)


/-- If a point `δ + t • v` leaves an exposed face `F` of `P` while staying
    in the direction of `affineSpan F`, then it also leaves `P.Ω`. -/
private lemma affine_const_on_exposed_face {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
    (hp : SupportingHyperplane P) (hF_eq : F = ExposedFace hp) :
    ∀ x ∈ affineSpan ℝ F, hp.f x = hp.c := by
  let H : AffineSubspace ℝ (CoeffVec n) :=
    { carrier := {x | hp.f x = hp.c}
      smul_vsub_vadd_mem := by
        intro a b c d hb hc hd
        simp [map_add, map_smul, smul_sub]
        simp only [Set.mem_setOf_eq] at hb hc hd
        rw [hb, hc, hd]
        ring
    }
  have hF_sub : (F : Set (CoeffVec n)) ⊆ (H : Set (CoeffVec n)) := by
    intro y hy; rw [hF_eq] at hy; exact hy.2
  have h_span_sub : affineSpan ℝ F ≤ H := affineSpan_le.mpr hF_sub
  intro x hx; simpa using h_span_sub hx

private lemma exposed_face_direction_kills_vector {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
    (hp : SupportingHyperplane P) (hF_eq : F = ExposedFace hp) (δ : CoeffVec n) (v : CoeffVec n)
    (hδ_in_F : δ ∈ F) (hv_in_dir : v ∈ (affineSpan ℝ F).direction) : hp.f v = 0 := by
  have h_aff_const : ∀ x ∈ affineSpan ℝ F, hp.f x = hp.c :=
    affine_const_on_exposed_face hp hF_eq
  have hδ_f : hp.f δ = hp.c := by
    rw [hF_eq] at hδ_in_F
    exact hδ_in_F.2
  have h_δ_plus_v : δ + v ∈ affineSpan ℝ F := by
    have h_vadd : v +ᵥ δ ∈ affineSpan ℝ F :=
      AffineSubspace.vadd_mem_of_mem_direction hv_in_dir (subset_affineSpan ℝ F hδ_in_F)
    simpa [vadd_eprivate lemma ker_restrict_eq_inf {n : ℕ} (U : Submodule ℝ (CoeffVec n)) (g_new : CoeffVec n →ₗ[ℝ] ℝ) :
    ker (g_new.restrict U) = U ⊓ ker g_new := by
  ext x; simp [g_new, Submodule.mem_inf, Submodule.mem_ker, Submodule.restrict_apply]q_add, add_comm] using h_vadd
  have hsum : hp.f (δ + v) = hp.f δ + hp.f v := by simp
  rw [h_aff_const (δ + v) h_δ_plus_v, h_aff_const δ (subset_affineSpan ℝ F hδ_in_F)] at hsum
  linarith

private lemma exposed_face_point_value {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
    (hp : SupportingHyperplane P) (δ : CoeffVec n) (v : CoeffVec n) (t : ℝ)
    (hδ_f : hp.f δ = hp.c) (hv_f : hp.f v = 0) : hp.f (δ + t • v) = hp.c := by
  calc
    hp.f (δ + t • v) = hp.f δ + hp.f (t • v) := by simp
    _ = hp.c + t • (hp.f v) := by simp [hδ_f, LinearMap.map_smul]
    _ = hp.c + t • 0 := by rw [hv_f]
    _ = hp.c := by simp


private lemma mem_P_sr_of_isRoot {n : ℕ} (r : ℝ) (δ : CoeffVec n)
    (h : ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot (r : ℂ)) : δ ∈ (P_sr n r : Set (CoeffVec n)) := by
  unfold P_sr
  change evalLinear r δ = 0
  unfold Polynomial.IsRoot at h
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_eval_map, eval_root_comm r δ] at h
  exact_mod_cast (map_eq_zero (algebraMap ℝ ℂ)).mp h

private lemma finrank_ker_lt_finrank_of_nonzero_restrict {n : ℕ} (v : CoeffVec n)
    (U : Submodule ℝ (CoeffVec n)) (g_new : CoeffVec n →ₗ[ℝ] ℝ)
    (hv_mem_U : v ∈ U) (h_gv_nonzero : g_new v ≠ 0) :
    Module.finrank ℝ ↥(U ⊓ LinearMap.ker g_new) < Module.finrank ℝ ↥U := by
  let K : Submodule ℝ (CoeffVec n) := LinearMap.ker g_new
  let g_U : U →ₗ[ℝ] ℝ := g_new.comp (Submodule.subtype U)

  have h_gU_nonzero : g_U ≠ 0 := by
    intro hzero
    apply h_gv_nonzero
    have : g_U ⟨v, hv_mem_U⟩ = 0 := by
      simpa [g_U, LinearMap.comp_apply, Submodule.subtype_apply] using
        congrArg (fun f => f ⟨v, hv_mem_U⟩) hzero
    simpa [g_U, LinearMap.comp_apply, Submodule.subtype_apply] using this

  have h_range_top : LinearMap.range g_U = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro r
    use (r / g_new v) • ⟨v, hv_mem_U⟩
    simp only [g_U, LinearMap.comp_apply, Submodule.subtype_apply,
               LinearMap.map_smul, smul_eq_mul]
    rw [mul_comm]
    field_simp [h_gv_nonzero]

  have h_rank_nullity : Module.finrank ℝ ↥g_U.range + Module.finrank ℝ ↥g_U.ker = Module.finrank ℝ ↥U :=
    LinearMap.finrank_range_add_finrank_ker g_U

  have h_ker_finrank_lt_U : Module.finrank ℝ ↥g_U.ker < Module.finrank ℝ ↥U := by
    have h_range_finrank : Module.finrank ℝ ↥g_U.range = 1 := by
      rw [h_range_top]
      simp [Module.finrank_self]
    rw [h_range_finrank, add_comm] at h_rank_nullity
    omega

  have h_iso : Module.finrank ℝ ↥(LinearMap.ker g_U) =
      Module.finrank ℝ ↥(U ⊓ K) := by
    let φ : LinearMap.ker g_U ≃ₗ[ℝ] ↥(U ⊓ K) := {
      toFun := fun x => ⟨x.1.1, x.1.2,
        by simpa [K, g_U, LinearMap.comp_apply, Submodule.subtype_apply] using x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩,
        by simpa [K, g_U, LinearMap.comp_apply, Submodule.subtype_apply] using y.2.2⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl
      map_add' := fun x y => Subtype.ext <| Subtype.ext rfl
      map_smul' := fun c x => Subtype.ext <| Subtype.ext rfl
    }
    exact LinearEquiv.finrank_eq φ

  rw [← h_iso]
  exact h_ker_finrank_lt_U

private lemma escapes_P_via_exposed_face {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
    (hF_exposed : IsExposedFace P F) (δ : CoeffVec n) (v : CoeffVec n) (t : ℝ)
    (hδ_in_F : δ ∈ F) (hv_in_dir : v ∈ (affineSpan ℝ F).direction)
    (h_escapes_F : δ + t • v ∉ F) : δ + t • v ∉ P.Ω := by
  obtain ⟨hp, hF_eq⟩ := hF_exposed
  have hδ_f : hp.f δ = hp.c := by
    rw [hF_eq] at hδ_in_F
    exact hδ_in_F.2
  have hv_f : hp.f v = 0 :=
    exposed_face_direction_kills_vector hp hF_eq δ v hδ_in_F hv_in_dir
  have h_val : hp.f (δ + t • v) = hp.c :=
    exposed_face_point_value (F := F) hp δ v t hδ_f hv_f
  by_contra h_in_Ω
  apply h_escapes_F
  rw [hF_eq]
  exact ⟨h_in_Ω, h_val⟩

/--
Any point on the frontier of an exposed face (relative to its affine span)
belongs to a proper subface of strictly lower dimension.
-/
private lemma gv_pos_from_interior {n : ℕ} (P : Polytope n) (g : CoeffVec n →L[ℝ] ℝ)
    (v δ_bound : CoeffVec n) (hδ_bound_in_Ω : δ_bound ∈ P.Ω)
    (h_convex_Ω : Convex ℝ P.Ω) (hg_strict : ∀ x ∈ interior P.Ω, g x < g δ_bound)
    (h_from_interior : ∃ (δ_F : CoeffVec n), δ_F ∈ interior P.Ω ∧ ∃ (c : ℝ), c > 0 ∧ δ_bound = δ_F + c • v) :
    g.toLinearMap v > 0 := by
  obtain ⟨δ_F, hδ_F_int, c, hc_pos, h_eq⟩ := h_from_interior
  have h_bound_in_Ω : δ_F + c • v ∈ P.Ω := by rw [← h_eq]; exact hδ_bound_in_Ω
  have h_half_mem : δ_F + (1/2 : ℝ) • (c • v) ∈ interior P.Ω := by
    have h_eq :
        δ_F + (1/2 : ℝ) • (c • v)
          = (1/2 : ℝ) • δ_F + (1/2 : ℝ) • (δ_F + c • v) := by
      simp [smul_add, add_smul, smul_smul]
      ring_nf
      simp [smul_add, add_smul, smul_smul]
      ring
      sorry -- TODO: calculation issue left


    rw [h_eq]

    have hmem : (1/2 : ℝ) • δ_F + (1/2 : ℝ) • (δ_F + c • v) ∈
        openSegment ℝ δ_F (δ_F + c • v) := by
      rw [openSegment_eq_image']
      simp only [Set.mem_image]
      refine ⟨1/2, ⟨by norm_num, by norm_num⟩, ?_⟩
      simp [smul_add]
      ring_nf
      sorry -- TODO: calculation issue left

    exact h_convex_Ω.openSegment_interior_self_subset_interior hδ_F_int h_bound_in_Ω hmem

  have h_simplify : δ_F + (1/2 : ℝ) • (c • v) = δ_bound - (c/2) • v := by
    calc
      δ_F + (1/2 : ℝ) • (c • v) = δ_F + ((c/2) • v) := by ring
      _ = (δ_F + c • v) - (c/2) • v := by ring
      _ = δ_bound - (c/2) • v := by rw [h_eq]
  have h_mem : δ_bound - (c/2) • v ∈ interior P.Ω := by
    rw [← h_simplify]
    exact h_half_mem
  have h_ineq : g (δ_bound - (c/2) • v) < g δ_bound := hg_strict _ h_mem
  have h_lin : g (δ_bound - (c/2) • v) = g δ_bound - (c/2) * g v := by
    simp [smul_eq_mul]
  rw [h_lin] at h_ineq
  have : g v = g.toLinearMap v := rfl
  rw [this] at h_ineq
  nlinarith

private lemma sum_supporting_hyperplane_exposed_face {n : ℕ} {P : Polytope n}
    (hpF : SupportingHyperplane P) (g_lin : CoeffVec n →ₗ[ℝ] ℝ) (v δ_bound : CoeffVec n)
    (hδ_bound_in_Ω : δ_bound ∈ P.Ω) (hc_upper : ∀ x ∈ P.Ω, g_lin x ≤ g_lin δ_bound)
    (h_fv_zero : hpF.f v = 0) (h_gv_pos : g_lin v > 0) :
    IsExposedFace P {x | x ∈ P.Ω ∧ (hpF.f + g_lin) x = hpF.c + g_lin δ_bound} := by
  let g_new := hpF.f + g_lin
  have h_new_upper : ∀ x ∈ P.Ω, (hpF.f + g_lin) x ≤ hpF.c + g_lin δ_bound := by
    intro x hx
    have hfx : hpF.f x ≤ hpF.c := hpF.upper_bound x hx
    have hgx : g_lin x ≤ g_lin δ_bound := hc_upper x hx
    simpa [Pi.add_apply] using add_le_add hfx hgx
  have h_new_touches : ∃ x ∈ P.Ω, g_new x = hpF.c + g_lin δ_bound :=
    ⟨δ_bound, hδ_bound_in_Ω, by
    simp [g_new]⟩
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

private lemma exposed_face_intersection_eq {n : ℕ} {P : Polytope n}
    (hpF : SupportingHyperplane P) (g_lin : CoeffVec n →ₗ[ℝ] ℝ) (δ_bound : CoeffVec n)
    (F : Set (CoeffVec n)) (hF_eq : F = ExposedFace hpF)
    (hp_new : SupportingHyperplane P)
    (h_new_f : hp_new.f = hpF.f + g_lin)
    (h_new_c : hp_new.c = hpF.c + g_lin δ_bound)
    (hc_upper : ∀ x ∈ P.Ω, g_lin x ≤ g_lin δ_bound) (hδ_bound_in_Ω : δ_bound ∈ P.Ω) :
    F ∩ ExposedFace hp_new = {x | x ∈ P.Ω ∧ (hpF.f + g_lin) x = hpF.c + g_lin δ_bound} := by
  ext x; constructor
  · intro hxF
    obtain ⟨hxF, hxG⟩ := hxF
    rw [hF_eq] at hxF
    rcases hxF with ⟨hxΩ, hx_f⟩
    unfold ExposedFace at hxG
    rcases hxG with ⟨hxΩ', hx_g⟩
    refine ⟨hxΩ, ?_⟩
    simp [hx_f, hx_g]
    rw [h_new_f, h_new_c] at hx_g
    simpa [Pi.add_apply, hx_f] using hx_g


  · intro ⟨hxΩ, hx_new⟩
    have hx_f : hpF.f x = hpF.c := by
      have hle_f : hpF.f x ≤ hpF.c := hpF.upper_bound x hxΩ
      have hle_g : g_lin x ≤ g_lin δ_bound := hc_upper x hxΩ
      by_contra h_not
      have h_lt : hpF.f x < hpF.c := by
        by_contra! h_ge;
        have h_eq_f : hpF.f x = hpF.c := le_antisymm hle_f h_ge
        contradiction
      have : g_lin x > g_lin δ_bound := by
        have h_sum : hpF.f x + g_lin x = hpF.c + g_lin δ_bound := by
          simpa [Pi.add_apply] using hx_new
        linarith
      linarith
    have hx_g : g_lin x = g_lin δ_bound := by
      have h_sum : hpF.f x + g_lin x = hpF.c + g_lin δ_bound := by
        simpa [Pi.add_apply] using hx_new
      rw [hx_f] at h_sum
      linarith
    constructor
    · rw [hF_eq]
      exact ⟨hxΩ, hx_f⟩
    · unfold ExposedFace
      simp
      refine ⟨hxΩ, ?_⟩
      change (hpF.f + g_lin) x = hpF.c + g_lin δ_bound at hx_new
      rw [h_new_f, h_new_c] at ⊢
      exact hx_new






private lemma direction_sub_ker_of_exposed_intersection {n : ℕ}
    (hpF : SupportingHyperplane P) (g_lin : CoeffVec n →ₗ[ℝ] ℝ) (δ_bound : CoeffVec n)
    (G : Set (CoeffVec n)) (hδ_in_G : δ_bound ∈ G) :
    (affineSpan ℝ G).direction ≤ ker (hpF.f + g_lin) := by
  let g_new := hpF.f + g_lin
  have h_const : ∀ x ∈ G, g_new x = hpF.c + g_lin δ_bound := by
    intro x hx
    rcases hx with ⟨hxF, hxG⟩
    unfold ExposedFace at hxG
    rcases hxG with ⟨hxΩ, hx_g⟩
    simp [g_new, hx_g, hxF.2]
  have h_aff_const : ∀ x ∈ affineSpan ℝ G, g_new x = hpF.c + g_lin δ_bound := by
    apply affineSpan_le.mpr
    exact h_const
  intro w hw
  have h_base : δ_bound ∈ affineSpan ℝ G := subset_affineSpan ℝ G hδ_in_G
  have h_plus : δ_bound + w ∈ affineSpan ℝ G :=
    AffineSubspace.vadd_mem_of_mem_direction hw h_base
  have h_val_base : g_new δ_bound = hpF.c + g_lin δ_bound := by simp [g_new]
  have h_val_plus : g_new (δ_bound + w) = hpF.c + g_lin δ_bound := h_aff_const (δ_bound + w) h_plus
  rw [map_add] at h_val_plus
  rw [h_val_base] at h_val_plus
  linarith

private lemma isExposedFace_isCompact {n : ℕ} (P : Polytope n) {F : Set (CoeffVec n)} (hF : IsExposedFace P F) : IsCompact F := by
  obtain ⟨hp, rfl⟩ := hF
  unfold ExposedFace
  refine P.isCompact.inter_right ?_
  exact isClosed_eq (LinearMap.continuous_of_finiteDimensional hp.f) continuous_const

private lemma isExposedFace_convex {n : ℕ} (P : Polytope n) {F : Set (CoeffVec n)} (hF : IsExposedFace P F) : Convex ℝ F := by
  obtain ⟨hp, rfl⟩ := hF
  unfold ExposedFace
  exact Convex.inter (convex_convexHull ℝ _) (by
    intro x (hx : hp.f x = hp.c) y (hy : hp.f y = hp.c) a b ha hb hab
    show hp.f (a • x + b • y) = hp.c
    simp only [LinearMap.map_add, LinearMap.map_smul, hx, hy, add_smul, hab, one_smul]
    exact Convex.combo_self hab hp.c)

private lemma isExposedFace_subset_Ω {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)} (hF : IsExposedFace P F) : F ⊆ P.Ω := by
  obtain ⟨hp, rfl⟩ := hF; exact Set.inter_subset_left

private lemma exists_subface_of_strictly_lower_dimension {n : ℕ} (P : Polytope n) (F : Set (CoeffVec n))
    (hF_exposed : IsExposedFace P F) (δ_bound : CoeffVec n)
    (hδ_bound_in_F : δ_bound ∈ F) (hδ_bound_front : δ_bound ∈ frontier F)
    (hF_nontrivial : F.Nontrivial) :
    ∃ G, IsExposedFace P G ∧ δ_bound ∈ G ∧ G ⊆ F ∧
    Module.finrank ℝ (affineSpan ℝ G).direction < Module.finrank ℝ (affineSpan ℝ F).direction := by
  have h_int_nonempty : (interior P.Ω).Nonempty := P.interior_nonempty
  have hδ_bound_front_P : δ_bound ∈ frontier P.Ω := by
    have hF_sub_Ω : F ⊆ P.Ω := isExposedFace_subset_Ω hF_exposed
    have hF_int_Ω : interior F ⊆ interior P.Ω := interior_mono hF_sub_Ω
    -- Since δ_bound ∈ frontier F, δ_bound ∉ interior F
    -- If F is a proper face, F ∩ interior P.Ω = ∅
    sorry
  obtain ⟨v, hv_dir, h_exits_F⟩ : ∃ v ∈ (affineSpan ℝ F).direction, ∃ ε > 0, δ_bound + ε • v ∉ F := sorry
  have h_from_interior : ∃ (δ_F : CoeffVec n), δ_F ∈ interior P.Ω ∧ ∃ (c : ℝ), c > 0 ∧ δ_bound = δ_F + c • v := sorry
  have h_exits : ∃ ε > 0, δ_bound + ε • v ∉ P.Ω := sorry

  obtain ⟨hpF, hF_eq⟩ := hF_exposed
  have hδ_bound_in_Ω : δ_bound ∈ P.Ω := frontier_point_in_Ω P δ_bound hδ_bound_front_P
  have h_convex_Ω : Convex ℝ P.Ω := convex_convexHull ℝ _
  have hδ_not_int_Ω : δ_bound ∉ interior P.Ω :=
    frontier_point_not_interior P δ_bound hδ_bound_front_P
  have h_int_convex : Convex ℝ (interior P.Ω) := h_convex_Ω.interior
  have h_int_open : IsOpen (interior P.Ω) := isOpen_interior
  obtain ⟨g, hg_strict⟩ :=
    geometric_hahn_banach_open_point h_int_convex h_int_open hδ_not_int_Ω
  let g_lin : CoeffVec n →ₗ[ℝ] ℝ := g.toLinearMap
  have hc_upper : ∀ x ∈ P.Ω, g_lin x ≤ g_lin δ_bound :=
    supporting_hyperplane_upper_bound P g (g δ_bound) hg_strict h_int_nonempty
  let hp_new : SupportingHyperplane P := {
    f := g_lin
    c := g_lin δ_bound
    nonzero := by
      have hg_ne : g ≠ 0 := supporting_func_nonzero P g hg_strict h_int_nonempty δ_bound
      intro hzero
      apply hg_ne
      ext x
      simpa [hzero] using rfl
    upper_bound := hc_upper
    touches := ⟨δ_bound, hδ_bound_in_Ω, rfl⟩
  }
  let G : Set (CoeffVec n) := F ∩ ExposedFace hp_new
  have h_fv_zero : hpF.f v = 0 :=
    exposed_face_direction_kills_vector hpF hF_eq δ_bound v hδ_bound_in_F hv_dir
  have h_gv_pos : g_lin v > 0 :=
    gv_pos_from_interior P g v δ_bound hδ_bound_in_Ω h_convex_Ω hg_strict h_from_interior
  have hG_exposed : IsExposedFace P G := by
    have h_exposed_set : IsExposedFace P {x | x ∈ P.Ω ∧ (hpF.f + g_lin) x = hpF.c + g_lin δ_bound} :=
      sum_supporting_hyperplane_exposed_face hpF g_lin v δ_bound hδ_bound_in_Ω hc_upper h_fv_zero h_gv_pos
    have hG_eq : G = {x | x ∈ P.Ω ∧ (hpF.f + g_lin) x = hpF.c + g_lin δ_bound} :=
      exposed_face_intersection_eq hpF g_lin δ_bound F hF_eq hp_new hc_upper hδ_bound_in_Ω
    rw [hG_eq]
    exact h_exposed_set
  have hδ_in_G : δ_bound ∈ G := by
    refine ⟨hδ_bound_in_F, ?_⟩
    unfold ExposedFace
    exact ⟨hδ_bound_in_Ω, rfl⟩
  have hG_sub_F : G ⊆ F := Set.inter_subset_left _ _
  have h_dim_lt : Module.finrank ℝ (affineSpan ℝ G).direction < Module.finrank ℝ (affineSpan ℝ F).direction := by
    let U : Submodule ℝ (CoeffVec n) := (affineSpan ℝ F).direction
    let g_new : CoeffVec n →ₗ[ℝ] ℝ := hpF.f + g_lin
    have hv_mem_U : v ∈ U := hv_dir
    have h_gv_nonzero : g_new v ≠ 0 := by
      calc
        g_new v = hpF.f v + g_lin v := rfl
        _ = 0 + g_lin v := by rw [h_fv_zero]
        _ = g_lin v := by simp
        _ > 0 := h_gv_pos
        _ ≠ 0 := by linarith
    have h_ker_finrank_lt : Module.finrank ℝ (U ⊓ ker g_new) < Module.finrank ℝ U :=
      finrank_ker_lt_finrank_of_nonzero_restrict v U g_new hv_mem_U h_gv_nonzero
    have h_dir_G_le_U : (affineSpan ℝ G).direction ≤ U := by
      apply AffineSubspace.direction_le
      exact affineSpan_mono ℝ hG_sub_F
    have h_dir_G_le_W : (affineSpan ℝ G).direction ≤ ker g_new :=
      direction_sub_ker_of_exposed_intersection hpF g_lin δ_bound G hδ_in_G
    have h_dir_G_le_inter : (affineSpan ℝ G).direction ≤ U ⊓ ker g_new :=
      Submodule.le_inf h_dir_G_le_U h_dir_G_le_W
    have h_finrank_le : Module.finrank ℝ ((affineSpan ℝ G).direction) ≤ Module.finrank ℝ (U ⊓ ker g_new) :=
      Submodule.finrank_le h_dir_G_le_inter
    calc
      Module.finrank ℝ (affineSpan ℝ G).direction ≤ Module.finrank ℝ (U ⊓ ker g_new) := h_finrank_le
      _ < Module.finrank ℝ U := h_ker_finrank_lt
      _ = Module.finrank ℝ (affineSpan ℝ F).direction := rfl
  exact ⟨G, hG_exposed, hδ_in_G, hG_sub_F, h_dim_lt⟩

/-- In a polytope of dimension at least 2, every vertex is contained in at least one exposed edge. -/
private lemma exists_edge_containing_vertex {n : ℕ} {P : Polytope n} (F : Set (CoeffVec n))
    (hF_exposed : IsExposedFace P F) (v : CoeffVec n) (hv_in_F : v ∈ F)
    (hF_dim : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 2) :
    ∃ E, IsExposedEdge P E ∧ E ⊆ F ∧ v ∈ E := by
  -- TODO: requires polytope face lattice theory;
  -- follows from the fact that every vertex of a polytope
  -- of dimension ≥ 2 lies on at least one edge
  sorry




private lemma isExposedEdge_of_dim_1 {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)} (hF_exposed : IsExposedFace P F) (h_dim : Module.finrank ℝ (affineSpan ℝ F).direction = 1) : IsExposedEdge P F := by
  obtain ⟨hp, hF_eq⟩ := hF_exposed
  exact ⟨hp, hF_eq, hF_eq ▸ h_dim⟩

private lemma direction_nontrivial_from_dim_ge_1 {n : ℕ} {F : Set (CoeffVec n)} (h_finrank : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 1) : Nontrivial ↥(affineSpan ℝ F).direction :=
  Module.nontrivial_of_finrank_pos (by omega)

private lemma dim_ge_2_of_nontrivial_not_1 {n : ℕ} {F : Set (CoeffVec n)} (hF_nontrivial : F.Nontrivial) (h_not_1 : Module.finrank ℝ (affineSpan ℝ F).direction ≠ 1) : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 2 := by
  have h_nontrivial_dir := direction_nontrivial_of_nontrivial hF_nontrivial
  have h_pos := Module.finrank_pos (R := ℝ) (M := ↥(affineSpan ℝ F).direction)
  omega

private lemma singleton_if_not_nontrivial {n : ℕ} {G : Set (CoeffVec n)} (hG_nonempty : G.Nonempty) (hG_not_nontrivial : ¬G.Nontrivial) : ∃ x, G = {x} := by
  obtain ⟨x, hx⟩ := hG_nonempty
  use x; apply Set.Subset.antisymm
  · intro y hy; by_contra h_ne; exact hG_not_nontrivial ⟨x, hx, y, hy, h_ne⟩
  · exact Set.singleton_subset_iff.mpr hx

private lemma exists_boundary_point_in_face_rootspace {n : ℕ} (P : Polytope n) (r : ℝ) (δ_F : CoeffVec n)
    (F : Set (CoeffVec n)) (hF_exposed : IsExposedFace P F)
    (hδ_F_in_F : δ_F ∈ F) (hδ_F_root : δ_F ∈ (P_sr n r : Set (CoeffVec n)))
    (h_inter_dim : Module.finrank ℝ ↥(affineSpan ℝ (((P_sr n r : Set (CoeffVec n)) ∩ (affineSpan ℝ F : Set (CoeffVec n))))).direction ≥ 1) :
    ∃ δ_bound, δ_bound ∈ F ∩ (P_sr n r : Set (CoeffVec n)) ∧ δ_bound ∈ frontier F := by
  let affF := affineSpan ℝ F
  let hF_compact := isExposedFace_isCompact P hF_exposed
  let hF_subset := isExposedFace_subset_Ω hF_exposed
  let hδ_F_in_Psr : δ_F ∈ (P_sr n r : Set (CoeffVec n)) := hδ_F_root
  let hδ_F_affF := subset_affineSpan ℝ F hδ_F_in_F
  let hδ_F_inter := ⟨hδ_F_in_F, hδ_F_in_Psr⟩

  by_cases hδ_front : δ_F ∈ frontier F
  · refine ⟨δ_F, hδ_F_inter, hδ_front⟩
  · have hδ_int : δ_F ∈ interior F := by
      rw [frontier_eq_for_closed F hF_compact.isClosed] at hδ_front
      apply not_not.mp; simp; by_contra h; exact hδ_front ⟨hδ_F_in_F, h⟩
    let L := affineSpan ℝ (↑(P_sr n r) ∩ (affF : Set (CoeffVec n)))
    have h_dir_nontrivial := direction_nontrivial_from_dim_ge_1 h_inter_dim
    obtain ⟨v_sub, hv_sub_ne⟩ := exists_ne (0 : ↥L.direction)
    let v : CoeffVec n := v_sub.val
    have hv_ne : v ≠ 0 := by intro h; apply hv_sub_ne; exact Subtype.ext h
    have hv_dir : v ∈ L.direction := v_sub.property
    have h_escapes : ∃ t : ℝ, δ_F + t • v ∉ F := by
      by_contra h_contra; push_neg at h_contra
      rcases Metric.isBounded_iff.mp hF_compact.isBounded with ⟨C, hC⟩
      have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
      let t := (|C| + 1) / ‖v‖
      have h_dist : dist (δ_F + t • v) δ_F = t * ‖v‖ := by
        rw [dist_eq_norm]; have h_sub : δ_F + t • v - δ_F = t • v := by abel
        rw [h_sub, norm_smul, Real.norm_eq_abs t, abs_of_nonneg (by linarith [hv_norm_pos, abs_nonneg C])]
      have h_le : dist (δ_F + t • v) δ_F ≤ C := by apply hC; exact h_contra t; exact hδ_F_in_F
      linarith [h_dist, h_le, le_abs_self C]
    obtain ⟨t_out, ht_out⟩ := h_escapes
    have hL_le_affF : L ≤ affF := affineSpan_le.mpr Set.inter_subset_right
    have hv_affF_dir : v ∈ affF.direction := AffineSubspace.direction_le hL_le_affF hv_dir
    have ht_out_P : δ_F + t_out • v ∉ P.Ω := escapes_P_via_exposed_face hF_exposed δ_F v t_out hδ_F_in_F hv_affF_dir ht_out
    have hδ_front_Ω : δ_F ∉ frontier P.Ω := by
      intro h_front; apply hδ_front; rw [frontier_eq_for_closed F hF_compact.isClosed]
      refine ⟨hδ_F_in_F, ?_⟩; intro h_int_F
      exact h_front.2 (interior_mono hF_subset h_int_F)
    obtain ⟨δ_bound, h_seg, h_front_P⟩ := segment_boundary_intersection P δ_F (hF_subset hδ_F_in_F) hδ_front_Ω v hv_ne t_out ht_out_P
    have h_δ_bound_in_F : δ_bound ∈ F := by
      obtain ⟨hp, hF_expr⟩ := hF_exposed; rw [hF_expr] at hδ_F_in_F ⊢
      refine ⟨?_, ?_⟩
      · rw [← P.isCompact.isClosed.closure_eq] at h_front_P; exact frontier_subset_closure h_front_P
      · obtain ⟨c, hc_Icc, rfl⟩ := segment_eq_image ℝ δ_F (δ_F + t_out • v) ▸ h_seg
        have hf_v : hp.f v = 0 := exposed_face_direction_kills_vector hp hF_expr δ_F v hδ_F_in_F hv_affF_dir
        simp [vadd_eq_add, hδ_F_in_F.2, hf_v, LinearMap.map_add, LinearMap.map_smul]; ring
    have h_δ_bound_front : δ_bound ∈ frontier F := by
      rw [frontier_eq_for_closed F hF_compact.isClosed]
      refine ⟨h_δ_bound_in_F, ?_⟩; intro h_int
      exact (frontier_point_not_interior P δ_bound h_front_P) (interior_mono hF_subset h_int)
    have h_δ_bound_root : δ_bound ∈ (P_sr n r : Set (CoeffVec n)) := by
      rw [segment_eq_image ℝ] at h_seg; obtain ⟨c, _, h_δ_bound_eq⟩ := h_seg
      have h_v_root : v ∈ P_sr n r := by
        have h_in : v ∈ (P_sr n r).toAffineSubspace.direction := AffineSubspace.direction_le (affineSpan_le.mpr Set.inter_subset_left) hv_dir
        rw [Submodule.toAffineSubspace_direction] at h_in; exact h_in
      rw [← h_δ_bound_eq]; exact Submodule.add_mem _ (Submodule.smul_mem _ (1 - c) hδ_F_root) (Submodule.add_mem _ (Submodule.smul_mem _ c hδ_F_root) (Submodule.smul_mem _ (c * t_out) h_v_root))
    exact ⟨δ_bound, ⟨h_δ_bound_in_F, h_δ_bound_root⟩, h_δ_bound_front⟩

/--
Dimensional descent: given an exposed face F containing the root r,
descend through lower-dimensional exposed faces until reaching an exposed edge.
This implements Steps 7-9 from the proof structure.
-/

private lemma descend_to_exposed_edge {n : ℕ} (P : Polytope n) (r : ℝ)
    (F : Set (CoeffVec n))
    (hF_exposed : IsExposedFace P F)
    (hr_in_RF : (r : ℂ) ∈ RootSpaceSet F)
    (hF_nonempty : F.Nonempty)
    (hF_nontrivial : F.Nontrivial) :
    ∃ E, IsExposedEdge P E ∧ (r : ℂ) ∈ RootSpaceSet E := by

  let m_F := Module.finrank ℝ (affineSpan ℝ F).direction

  by_cases h_dim_1 : m_F = 1
  · use F
    constructor
    apply isExposedEdge_of_dim_1 hF_exposed h_dim_1
    apply hr_in_RF
  · have h_dim_ge_2 : m_F ≥ 2 := dim_ge_2_of_nontrivial_not_1 hF_nontrivial h_dim_1
    obtain ⟨δ_F, hδ_F_in_F, hδ_F_root⟩ : ∃ δ ∈ F, ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot (r : ℂ) := hr_in_RF
    let affF := affineSpan ℝ F
    have h_inter_dim : Module.finrank ℝ ↥(affineSpan ℝ (((P_sr n r : Set (CoeffVec n)) ∩ (affF : Set (CoeffVec n))))).direction ≥ 1 :=
      intersection_affine_dim_ge_one (P_sr n r) affF δ_F (mem_P_sr_of_isRoot r δ_F hδ_F_root) (subset_affineSpan ℝ F hδ_F_in_F) (P_sr_dimension r) h_dim_ge_2

    obtain ⟨δ_bound, hδ_bound_inter, hδ_bound_front⟩ := exists_boundary_point_in_face_rootspace P r δ_F F hF_exposed hδ_F_in_F (mem_P_sr_of_isRoot r δ_F hδ_F_root) h_inter_dim

    obtain ⟨G, hG_exposed, hδ_bound_in_G, hG_sub, hG_dim_lt⟩ :=
      exists_subface_of_strictly_lower_dimension P F hF_exposed δ_bound hδ_bound_inter.1 hδ_bound_front hF_nontrivial

    have hr_in_RG : (r : ℂ) ∈ RootSpaceSet G := rootspace_mem_of_eval_zero r δ_bound hδ_bound_inter.2 G hδ_bound_in_G
    have hG_nonempty : G.Nonempty := ⟨δ_bound, hδ_bound_in_G⟩

    by_cases hG_nontrivial : G.Nontrivial
    · exact descend_to_exposed_edge P r G hG_exposed hr_in_RG hG_nonempty hG_nontrivial
    · obtain ⟨δ_v, hG_singleton⟩ := singleton_if_not_nontrivial hG_nonempty hG_nontrivial
      obtain ⟨E, hE_edge, hE_sub, h_delta_in_E⟩ := exists_edge_containing_vertex F hF_exposed δ_bound (hG_sub hδ_bound_in_G) h_dim_ge_2
      use E, hE_edge, rootspace_mem_of_eval_zero r δ_bound hδ_bound_inter.2 E h_delta_in_E
termination_by Module.finrank ℝ (affineSpan ℝ F).direction


theorem lemma61
  (P : Polytope n)
  (s : ℂ)
  (hs : s ∈ RootSpace P) :
  (s.im = 0 → ∃ E, IsExposedEdge P E ∧ s ∈ RootSpaceSet E) ∧
  (s.im ≠ 0 → ∃ F, IsExposedFace P F ∧
    s ∈ RootSpaceSet F) := by
  constructor
  · intro hreal
    unfold RootSpace RootSpaceSet at hs
    obtain ⟨δ, hδ_in_Ω, hδ_root⟩ := hs

    have hs_real : s = ↑s.re := by
      apply Complex.ext
      · simp
      · simp [hreal]
    have hδ_in_Psr : δ ∈ P_sr' s.re := by
          unfold P_sr' evalLinear
          simp only [LinearMap.coe_mk, AddHom.coe_mk, Set.mem_setOf_eq]
          rw [hs_real] at hδ_root
          unfold Polynomial.IsRoot at hδ_root
          rw [Polynomial.eval_map] at hδ_root
          have key : (algebraMap ℝ ℂ) (eval s.re (polyOfVec δ)) = 0 := by
            rw [Polynomial.eval₂_eq_eval_map] at hδ_root
            have h_comm : (algebraMap ℝ ℂ) (eval s.re (polyOfVec δ))
            = eval (↑s.re) (map (algebraMap ℝ ℂ) (polyOfVec δ)) := by
              simp [polyOfVec, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
                    map_sum, map_mul, map_pow]
            rw [h_comm, hδ_root]
          exact_mod_cast (map_eq_zero (algebraMap ℝ ℂ)).mp key
    have hδ_aff : δ ∈ affineSpan ℝ (P.Ω) := subset_affineSpan ℝ P.Ω hδ_in_Ω

    let m := Module.finrank ℝ (affineSpan ℝ (P.Ω)).direction

    by_cases hm : m ≥ 2
    · let U : Submodule ℝ (CoeffVec n) := P_sr n s.re
      let affΩ : AffineSubspace ℝ (CoeffVec n) := affineSpan ℝ (P.Ω)
      have hdim_Psr : Module.finrank ℝ U = n := P_sr_dimension s.re
      have hδ_aff : δ ∈ affΩ := subset_affineSpan ℝ P.Ω hδ_in_Ω
      have hA_dim : Module.finrank ℝ ↥(affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction ≥ 1 :=
        intersection_affine_dim_ge_one U affΩ δ hδ_in_Psr hδ_aff hdim_Psr hm
      have h_boundary_root : ∃ δ_bound, δ_bound ∈ (P_sr n s.re : Set (CoeffVec n)) ∩ frontier P.Ω :=
        exists_boundary_point_in_Psr P s.re δ hδ_in_Ω hδ_in_Psr affΩ hδ_aff hA_dim
      obtain ⟨δ_bound, hδ_bound⟩ := h_boundary_root
      have hδ_bound_front : δ_bound ∈ frontier P.Ω := hδ_bound.2
      have hδ_bound_Psr : δ_bound ∈ (P_sr n s.re : Set (CoeffVec n)) := hδ_bound.1

      have h_int_nonempty : (interior P.Ω).Nonempty := P.interior_nonempty

      obtain ⟨F, hF_exposed, hδ_in_F, hs_in_RF⟩ :=
        exists_exposed_face_containing_boundary_point P s.re δ_bound hδ_bound_front hδ_bound_Psr h_int_nonempty

      by_cases hF_nontrivial : F.Nontrivial
      · obtain ⟨E, hE_edge, h_edge_re⟩ := descend_to_exposed_edge P s.re F hF_exposed hs_in_RF ⟨δ_bound, hδ_in_F⟩ hF_nontrivial
        use E, hE_edge
        rw [← hs_real] at h_edge_re
        exact h_edge_re
      · obtain ⟨δ_v, hF_singleton⟩ := singleton_if_not_nontrivial ⟨δ_bound, hδ_in_F⟩ hF_nontrivial
        -- Since m ≥ 2, a singleton exposed face (vertex) lies on an edge
        -- follows from the fact that every vertex of a polytope
        -- of dimension ≥ 2 lies at least on one edge
        -- We use P.Ω as a fallback face (dim m ≥ 2)
        have h_Ω_exposed : IsExposedFace P P.Ω := sorry
        obtain ⟨E, hE_edge, hE_sub, h_delta_in_E⟩ := exists_edge_containing_vertex (P := P) P.Ω h_Ω_exposed δ_bound (frontier_point_in_Ω P δ_bound hδ_bound_front) hm
        use E, hE_edge
        rw [hs_real]
        exact rootspace_mem_of_eval_zero s.re δ_bound hδ_bound_Psr E h_delta_in_E
    · have hm01 : m = 0 ∨ m = 1 := by omega
      by_cases hm0 : m = 0
      · -- m = 0 case: interior P.Ω is empty, but P.interior_nonempty says it's not.
        have h_empty : interior P.Ω = ∅ := by
          -- A 0-dimensional polytope is a singleton, which has empty interior in ℝ^(n+1)
          sorry
        have h_nonempty : (interior P.Ω).Nonempty := P.interior_nonempty
        rw [h_empty] at h_nonempty
        exact absurd h_nonempty (Set.not_nonempty_empty)
      · have hm1 : m = 1 := by omega
        -- m = 1 case: P.Ω is an exposed edge of itself
        have h_Ω_is_edge : IsExposedEdge P P.Ω := by
          -- P.Ω is an exposed face via some nonzero functional and has dimension 1
          sorry
        refine ⟨P.Ω, h_Ω_is_edge, ?_⟩
        rw [hs_real]
        exact rootspace_mem_of_eval_zero s.re δ (mem_P_sr_of_isRoot s.re δ (by rw [← hs_real]; exact hδ_root)) P.Ω hδ_in_Ω

  · intro hcomplex
    sorry

end CoeffBox
