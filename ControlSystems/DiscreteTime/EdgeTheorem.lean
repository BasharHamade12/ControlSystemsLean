module

public import ControlSystems.DiscreteTime.EdgeTheoremDefs
public import Mathlib.Analysis.Convex.Intrinsic
set_option maxHeartbeats 0

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
  have hformula : Module.finrank ℝ ↥(U ⊔ W) + Module.finrank ℝ ↥(U ⊓ W) =
    Module.finrank ℝ U + Module.finrank ℝ W :=
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
    have hbase : δ ∈ U.toAffineSubspace ⊓ affineSpan ℝ P_Ω := by
      rw [AffineSubspace.mem_inf_iff]
      exact ⟨h1, h2⟩
    have hne : Set.Nonempty
      ((U.toAffineSubspace ⊓ affineSpan ℝ P_Ω : AffineSubspace ℝ (CoeffVec n)) :
        Set (CoeffVec n)) :=
      ⟨δ, hbase⟩
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

private lemma intersection_direction_eq {n : ℕ} (U : Submodule ℝ (CoeffVec n))
    (affΩ : AffineSubspace ℝ (CoeffVec n))
    (δ : CoeffVec n) (hδU : δ ∈ U) (hδΩ : δ ∈ affΩ) :
    (U.toAffineSubspace ⊓ affΩ).direction = U ⊓ affΩ.direction := by
  have h_affSpan : affineSpan ℝ (affΩ : Set (CoeffVec n)) = affΩ := by
    apply le_antisymm
    · apply affineSpan_le.mpr; simp
    · intro x hx; exact subset_affineSpan ℝ _ hx
  have h := direction_inf U (affΩ : Set (CoeffVec n)) δ hδU (subset_affineSpan ℝ _ hδΩ)
  rw [h_affSpan] at h
  exact h

private lemma intersection_affine_dim_ge_one {n : ℕ} (U : Submodule ℝ (CoeffVec n))
    (affΩ : AffineSubspace ℝ (CoeffVec n))
    (δ : CoeffVec n) (hδU : δ ∈ U) (hδΩ : δ ∈ affΩ)
    (hU_dim : Module.finrank ℝ U = n) (haff_dim : Module.finrank ℝ affΩ.direction ≥ 2) :
    Module.finrank ℝ ↥(affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction
      ≥ 1 := by
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
    (v : CoeffVec n) (_hv_nonzero : v ≠ 0) (t_out : ℝ) (ht_out : δ + t_out • v ∉ P.Ω) :
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
    (h_dim_pos : 0 < Module.finrank ℝ (↥(affineSpan ℝ
      ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction)) :
    Nontrivial ↥(U ⊓ affΩ.direction) := by
  have hA_eq : affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n))) =
    U.toAffineSubspace ⊓ affΩ := by
    rw [affineSpan_inter]
  have hA_dir : (U.toAffineSubspace ⊓ affΩ).direction = U ⊓ affΩ.direction :=
    intersection_direction_eq U affΩ δ hδ_in_Psr hδ_aff
  let dir := (affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction
  have h_finrank : Module.finrank ℝ (↥dir) = Module.finrank ℝ ↥(U ⊓ affΩ.direction) := by
    dsimp [dir]
    rw [hA_eq, hA_dir]
  have h_dim_pos' : 0 < Module.finrank ℝ (↥dir) :=
    h_dim_pos
  rw [h_finrank] at h_dim_pos'
  exact Module.nontrivial_of_finrank_pos h_dim_pos'

private lemma line_in_intersection {n : ℕ} (U : Submodule ℝ (CoeffVec n))
    (affΩ : AffineSubspace ℝ (CoeffVec n)) (δ : CoeffVec n)
    (hδ_in_Psr : δ ∈ (U : Set (CoeffVec n))) (hδ_aff : δ ∈ affΩ)
    (v_sub : ↥(U ⊓ affΩ.direction)) :
    ∀ (t : ℝ), δ + t • (v_sub.val : CoeffVec n) ∈ (U : Set (CoeffVec n)) ∩
      (affΩ : Set (CoeffVec n)) := by
  intro t
  refine Set.mem_inter ?_ ?_
  · exact Submodule.add_mem U hδ_in_Psr (Submodule.smul_mem U t v_sub.2.1)
  · have h_vadd :=
      affΩ.vadd_mem_of_mem_direction (Submodule.smul_mem affΩ.direction t v_sub.2.2) hδ_aff
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
    (hA_dim : Module.finrank ℝ ↥(affineSpan ℝ ((P_sr n r : Set (CoeffVec n)) ∩
      (affΩ : Set (CoeffVec n)))).direction ≥ 1) :
    ∃ δ_bound, δ_bound ∈ (P_sr n r : Set (CoeffVec n)) ∩ frontier P.Ω := by
  have h_dim_pos : 0 <
      Module.finrank ℝ ↥(affineSpan ℝ ((P_sr n r : Set (CoeffVec n)) ∩
      (affΩ : Set (CoeffVec n)))).direction := by
    omega
  let U : Submodule ℝ (CoeffVec n) := P_sr n r
  haveI : Nontrivial ↥(U ⊓ affΩ.direction) :=
    intersection_nontrivial U affΩ δ hδ_in_Psr hδ_aff h_dim_pos
  obtain ⟨v_sub, hv_sub_nonzero⟩ := exists_ne (0 : ↑(U ⊓ affΩ.direction))
  let v : CoeffVec n := v_sub.val
  have h_line_in_intersection : ∀ (t : ℝ), δ + t • v ∈ (P_sr n r : Set (CoeffVec n)) ∩
      (affΩ : Set (CoeffVec n)) :=
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
    rcases h_mem with ⟨hmem_Psr, hmem_aff⟩
    have : δ_bound ∈ (P_sr n r : Set (CoeffVec n)) := by
      have h_eq : δ_bound = δ + (c * t_out) • v := by
        calc δ_bound = (1 - c) • δ + c • (δ + t_out • v) := by rw [←hc_eq]
          _ = δ + (c * t_out) • v := by rw [h_rewrite]
      rw [h_eq]
      exact hmem_Psr
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

/-- If a point `δ + t • v` leaves an exposed face `F` of `P` while staying
    in the direction of `affineSpan F`, then it also leaves `P.Ω`. -/
private lemma affine_const_on_exposed_face {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
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
    simpa [vadd_eq_add, add_comm] using h_vadd
  have hsum : hp.f (δ + v) = hp.f δ + hp.f v := by simp
  rw [h_aff_const (δ + v) h_δ_plus_v, h_aff_const δ (subset_affineSpan ℝ F hδ_in_F)] at hsum
  linarith

private lemma exposed_face_point_value {n : ℕ} {P : Polytope n}
    (hp : SupportingHyperplane P) (δ : CoeffVec n) (v : CoeffVec n) (t : ℝ)
    (hδ_f : hp.f δ = hp.c) (hv_f : hp.f v = 0) : hp.f (δ + t • v) = hp.c := by
  calc
    hp.f (δ + t • v) = hp.f δ + hp.f (t • v) := by simp
    _ = hp.c + t • (hp.f v) := by simp [hδ_f]
    _ = hp.c + t • 0 := by rw [hv_f]
    _ = hp.c := by simp


private lemma mem_P_sr_of_isRoot {n : ℕ} (r : ℝ) (δ : CoeffVec n)
    (h : ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot (r : ℂ)) :
    δ ∈ (P_sr n r : Set (CoeffVec n)) := by
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
  have h_rank_nullity :
    Module.finrank ℝ ↥g_U.range + Module.finrank ℝ ↥g_U.ker = Module.finrank ℝ ↥U :=
    LinearMap.finrank_range_add_finrank_ker g_U
  have h_ker_finrank_lt_U : Module.finrank ℝ ↥g_U.ker < Module.finrank ℝ ↥U := by
    have h_range_finrank : Module.finrank ℝ ↥g_U.range = 1 := by
      rw [h_range_top]
      simp [Module.finrank_self]
    rw [h_range_finrank, add_comm] at h_rank_nullity
    omega
  have h_iso : Module.finrank ℝ ↥(LinearMap.ker g_U) = Module.finrank ℝ ↥(U ⊓ K) := by
    let φ : LinearMap.ker g_U ≃ₗ[ℝ] ↥(U ⊓ K) := {
      toFun := fun x => by
        refine ⟨x.1.1, ?_⟩
        constructor
        · exact x.1.2
        · change g_new x.1.1 = 0
          exact x.2
      invFun := fun y => by
        refine ⟨⟨y.1, y.2.1⟩, ?_⟩
        change g_new y.1 = 0
        exact y.2.2
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl
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
    exposed_face_point_value hp δ v t hδ_f hv_f
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
    (h_from_interior : ∃ (δ_F : CoeffVec n), δ_F ∈ interior P.Ω ∧
      ∃ (c : ℝ), c > 0 ∧ δ_bound = δ_F + c • v) :
    g.toLinearMap v > 0 := by
  obtain ⟨δ_F, hδ_F_int, c, hc_pos, h_eq⟩ := h_from_interior
  have h_bound_in_Ω : δ_F + c • v ∈ P.Ω := by rw [← h_eq]; exact hδ_bound_in_Ω
  have h_half_mem : δ_F + (1/2 : ℝ) • (c • v) ∈ interior P.Ω := by
    have h_eq' : δ_F + (1/2 : ℝ) • (c • v) = (1/2 : ℝ) • δ_F + (1/2 : ℝ) • (δ_F + c • v) := by
      ext i; simp [smul_add, smul_smul]; ring
    rw [h_eq']
    have hmem : (1/2 : ℝ) • δ_F + (1/2 : ℝ) • (δ_F + c • v) ∈
        openSegment ℝ δ_F (δ_F + c • v) := by
      rw [openSegment_eq_image']
      simp only [Set.mem_image]
      refine ⟨1/2, ⟨by norm_num, by norm_num⟩, ?_⟩
      calc
        δ_F + (1/2 : ℝ) • ((δ_F + c • v) - δ_F) = δ_F + (1/2 : ℝ) • (c • v) := by simp
        _ = (1/2 : ℝ) • δ_F + (1/2 : ℝ) • (δ_F + c • v) := h_eq'
    exact h_convex_Ω.openSegment_interior_self_subset_interior hδ_F_int h_bound_in_Ω hmem
  have h_simplify : δ_F + (1/2 : ℝ) • (c • v) = δ_bound - (c/2) • v := by
    calc
      δ_F + (1/2 : ℝ) • (c • v) = δ_F + ((1/2 : ℝ) * c) • v := by simp [smul_smul]
      _ = δ_F + ((c/2 : ℝ) • v) := by
        have h : ((1/2 : ℝ) * c) = (c/2 : ℝ) := by ring
        rw [h]
      _ = (δ_F + c • v) - (c/2 : ℝ) • v := by
        ext i; simp; ring
      _ = δ_bound - (c/2 : ℝ) • v := by rw [h_eq]
  have h_mem : δ_bound - (c/2) • v ∈ interior P.Ω := by
    rw [← h_simplify]
    exact h_half_mem
  have h_ineq : g (δ_bound - (c/2) • v) < g δ_bound := hg_strict _ h_mem
  have h_lin : g (δ_bound - (c/2) • v) = g δ_bound - (c/2) * g v := by
    simp [map_sub, map_smul, smul_eq_mul]
  rw [h_lin] at h_ineq
  have : g v = g.toLinearMap v := rfl
  rw [this] at h_ineq
  nlinarith

private lemma sum_supporting_hyperplane_exposed_face {n : ℕ} {P : Polytope n}
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
    ⟨δ_bound, hδ_bound_in_Ω, by
    simp [g_new, h_fδ_bound]⟩
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
    (hp_g : SupportingHyperplane P)
    (h_g_f : hp_g.f = g_lin)
    (h_g_c : hp_g.c = g_lin δ_bound)
    (hc_upper : ∀ x ∈ P.Ω, g_lin x ≤ g_lin δ_bound) (_hδ_bound_in_Ω : δ_bound ∈ P.Ω) :
    F ∩ ExposedFace hp_g = {x | x ∈ P.Ω ∧ (hpF.f + g_lin) x = hpF.c + g_lin δ_bound} := by
  ext x; constructor
  · intro hxF
    obtain ⟨hxF, hxG⟩ := hxF
    rw [hF_eq] at hxF
    rcases hxF with ⟨hxΩ, hx_f⟩
    unfold ExposedFace at hxG
    rcases hxG with ⟨_, hx_g⟩
    refine ⟨hxΩ, ?_⟩
    calc
      (hpF.f + g_lin) x = hpF.f x + g_lin x := rfl
      _ = hpF.c + g_lin x := by rw [hx_f]
      _ = hpF.c + hp_g.f x := by rw [h_g_f]
      _ = hpF.c + hp_g.c := by rw [hx_g]
      _ = hpF.c + g_lin δ_bound := by rw [h_g_c]
  · intro ⟨hxΩ, hx_new⟩
    have hx_f : hpF.f x = hpF.c := by
      have hle_f : hpF.f x ≤ hpF.c := hpF.upper_bound x hxΩ
      have hle_g : g_lin x ≤ g_lin δ_bound := hc_upper x hxΩ
      by_contra h_not
      have h_lt : hpF.f x < hpF.c := lt_of_le_of_ne hle_f h_not
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
    · rw [hF_eq]; exact ⟨hxΩ, hx_f⟩
    · unfold ExposedFace
      refine ⟨hxΩ, ?_⟩
      rw [h_g_f, h_g_c]
      exact hx_g






private lemma direction_sub_ker_of_exposed_intersection {n : ℕ} {P : Polytope n}
    (hpF : SupportingHyperplane P)
    (g_lin : CoeffVec n →ₗ[ℝ] ℝ)
    (δ_bound : CoeffVec n)
    (G : Set (CoeffVec n))
    (hδ_in_G : δ_bound ∈ G)
    (h_const : ∀ x ∈ G, (hpF.f + g_lin) x = hpF.c + g_lin δ_bound) :
    (affineSpan ℝ G).direction ≤
      LinearMap.ker (hpF.f + g_lin : CoeffVec n →ₗ[ℝ] ℝ) := by
  let g_new : CoeffVec n →ₗ[ℝ] ℝ := hpF.f + g_lin
  have h_base : δ_bound ∈ affineSpan ℝ G :=
    subset_affineSpan ℝ G hδ_in_G
  intro v hv
  have h_plus : δ_bound + v ∈ affineSpan ℝ G := by
    have h_vadd :
        v +ᵥ δ_bound ∈ affineSpan ℝ G :=
      AffineSubspace.vadd_mem_of_mem_direction hv h_base
    simpa [vadd_eq_add, add_comm] using h_vadd
  -- Step 3:
  have h_aff_const :
      ∀ x ∈ affineSpan ℝ G,
        g_new x = hpF.c + g_lin δ_bound := by
    intro x hx
    refine affineSpan_induction hx ?_ ?_
    · simp only [g_new]
      exact h_const
    · intros c u v w h1 h2 h3
      rw [vsub_eq_sub, vadd_eq_add]
      simp only [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_sub]
      rw [h1, h2, h3]
      ring_nf
      simp only [smul_eq_mul, mul_zero, add_zero]
  have h_val_base :
      g_new δ_bound = hpF.c + g_lin δ_bound :=
    h_aff_const δ_bound h_base
  have h_val_plus :
      g_new (δ_bound + v) = hpF.c + g_lin δ_bound :=
    h_aff_const (δ_bound + v) h_plus
  have h_linear :
      g_new (δ_bound + v) = g_new δ_bound + g_new v := by
    simp [g_new, map_add]
  rw [h_linear, h_val_base] at h_val_plus
  have hv_zero : g_new v = 0 := by
    linarith
  exact hv_zero



private lemma isExposedFace_isCompact {n : ℕ} (P : Polytope n) {F : Set (CoeffVec n)}
    (hF : IsExposedFace P F) : IsCompact F := by
  obtain ⟨hp, rfl⟩ := hF
  unfold ExposedFace
  refine P.isCompact.inter_right ?_
  exact isClosed_eq (LinearMap.continuous_of_finiteDimensional hp.f) continuous_const

private lemma isExposedFace_convex {n : ℕ} (P : Polytope n) {F : Set (CoeffVec n)}
    (hF : IsExposedFace P F) : Convex ℝ F := by
  obtain ⟨hp, rfl⟩ := hF
  unfold ExposedFace
  refine Convex.inter (convex_convexHull ℝ _) ?_
  intro x hx y hy a b ha hb hab
  have hx' : hp.f x = hp.c := hx
  have hy' : hp.f y = hp.c := hy
  calc
    hp.f (a • x + b • y) = hp.f (a • x) + hp.f (b • y) := by simp
    _ = a • hp.f x + b • hp.f y := by simp
    _ = a • hp.c + b • hp.c := by simp [hx', hy']
    _ = (a + b) • hp.c := by rw [← add_smul]
    _ = 1 • hp.c := by simp [hab]
    _ = hp.c := by simp

private lemma isExposedFace_subset_Ω {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
    (hF : IsExposedFace P F) : F ⊆ P.Ω := by
  obtain ⟨hp, rfl⟩ := hF; exact Set.inter_subset_left

/-- If a point lies on the frontier of an exposed face of a polytope,
    it also lies on the frontier of the polytope itself. -/
private lemma frontier_of_exposed_face_implies_frontier_of_polytope {n : ℕ} (P : Polytope n)
    (F : Set (CoeffVec n)) (hpF : SupportingHyperplane P) (hF_expr : F = ExposedFace hpF)
    (δ_bound : CoeffVec n) (hδ_bound_in_F : δ_bound ∈ F) (_hδ_bound_front : δ_bound ∈ frontier F) :
    δ_bound ∈ frontier P.Ω := by
  have h_not_interior : δ_bound ∉ interior P.Ω := by
    intro h_int
    have hx_support : hpF.f δ_bound = hpF.c := by
      have : δ_bound ∈ ExposedFace hpF := hF_expr ▸ hδ_bound_in_F
      exact this.2
    have h_exists_pos_dir : ∃ w : CoeffVec n, hpF.f w > 0 := by
      by_cases h : ∃ w, hpF.f w > 0
      · exact h
      · push_neg at h
        have hzero : hpF.f = 0 := by
          ext v
          apply le_antisymm
          · simp only [coe_comp, coe_single, Function.comp_apply, LinearMap.zero_comp, zero_apply]
            apply h
          · have hneg : hpF.f (-Pi.single v 1) ≤ 0 := h (-Pi.single v 1)
            rw [map_neg] at hneg
            exact neg_nonpos.mp hneg
        exact absurd hzero hpF.nonzero
    obtain ⟨w, hw⟩ := h_exists_pos_dir
    have h_open : IsOpen (interior P.Ω) := isOpen_interior
    have h_ball_surround : ∃ r > 0, Metric.ball δ_bound r ⊆ interior P.Ω :=
      (Metric.isOpen_iff.mp h_open) δ_bound h_int
    rcases h_ball_surround with ⟨r, hr_pos, h_ball⟩
    have h_norm_w_pos : 0 < ‖w‖ := by
      have hw_nonzero : w ≠ 0 := by
        intro hzero
        have : hpF.f w = 0 := by rw [hzero, LinearMap.map_zero]
        linarith
      exact norm_pos_iff.mpr hw_nonzero
    set ε := r / (2 * ‖w‖) with hε_def
    have hε_pos : 0 < ε := div_pos (by linarith) (by nlinarith)
    have h_mem_ball : δ_bound + ε • w ∈ Metric.ball δ_bound r := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h_sub : (δ_bound + ε • w) - δ_bound = ε • w := by abel
      rw [h_sub, norm_smul]
      have h_ε_mul : ε * ‖w‖ = r / 2 := by
        dsimp [ε]; field_simp [h_norm_w_pos.ne.symm]
      have h_norm_ε : ‖ε‖ = ε := abs_of_pos hε_pos
      rw [h_norm_ε, h_ε_mul]
      nlinarith
    have h_mem_int : δ_bound + ε • w ∈ interior P.Ω := h_ball h_mem_ball
    have h_mem_P : δ_bound + ε • w ∈ P.Ω := interior_subset h_mem_int
    have h_val : hpF.f (δ_bound + ε • w) = hpF.c + ε * hpF.f w := by
      simp [hx_support, map_add, map_smul, smul_eq_mul]
    have h_upper := hpF.upper_bound (δ_bound + ε • w) h_mem_P
    nlinarith
  have h_Ω : δ_bound ∈ P.Ω := by
    have : δ_bound ∈ ExposedFace hpF := hF_expr ▸ hδ_bound_in_F
    exact this.1
  exact ⟨subset_closure h_Ω, h_not_interior⟩

/--
An exposed face of a polytope P.Ω that contains a point of the interior of P.Ω
must be the whole polytope. (Any supporting hyperplane achieving its max on P.Ω
at an interior point must be constant on P.Ω.)
-/
private lemma exposed_face_eq_Ω_of_mem_interior {n : ℕ} (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hδ_F : CoeffVec n) (hδ_F_in_F : hδ_F ∈ F) (hδ_F_int : hδ_F ∈ interior P.Ω) :
    F = P.Ω := by
  obtain ⟨hp, hF_expr⟩ := hF_exp
  rw [hF_expr, ExposedFace]
  ext x
  constructor
  · intro hx; exact hx.1
  · intro hxΩ
    have hp_f_hδ : hp.f hδ_F = hp.c := (hF_expr ▸ hδ_F_in_F).2
    have hpx_le : hp.f x ≤ hp.c := hp.upper_bound x hxΩ
    by_cases hx_eq : hp.f x = hp.c
    · exact ⟨hxΩ, hx_eq⟩
    · have hx_strict : hp.f x < hp.c := lt_of_le_of_ne hpx_le hx_eq
      -- Pick ε > 0 such that B(hδ_F, ε) ⊆ interior P.Ω
      obtain ⟨ε, hε_pos, h_ball⟩ := Metric.isOpen_iff.mp isOpen_interior hδ_F hδ_F_int
      have h_ball_sub : Metric.ball hδ_F ε ⊆ P.Ω := h_ball.trans interior_subset
      let u := x - hδ_F
      have hu_nonzero : u ≠ 0 := by
        intro hzero
        have : x = hδ_F := by
          apply sub_eq_zero.mp ?_
          exact hzero
        have : hp.f x = hp.c := by simpa [this] using hp_f_hδ
        linarith
      have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_nonzero
      let u_normed := (1 / ‖u‖) • u
      have hnorm_u_normed : ‖u_normed‖ = 1 := by
        calc
          ‖u_normed‖ = ‖(1 / ‖u‖) • u‖ := rfl
          _ = |1 / ‖u‖| * ‖u‖ := norm_smul _ _
          _ = (1 / ‖u‖) * ‖u‖ := by rw [abs_of_pos (by positivity : 0 < 1 / ‖u‖)]
          _ = 1 := by field_simp [hnorm_pos.ne']
      -- Both hδ_F ± (ε/2)·u_normed are in B(hδ_F, ε) ⊆ P.Ω
      have h_mem_pos : hδ_F + ((ε / 2) : ℝ) • u_normed ∈ Metric.ball hδ_F ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        have h_sub : (hδ_F + ((ε / 2) : ℝ) • u_normed) - hδ_F = ((ε / 2) : ℝ) • u_normed := by
          abel
        rw [h_sub, norm_smul]
        rw [hnorm_u_normed, mul_comm, Real.norm_of_nonneg (by positivity : 0 ≤ ε / 2)]
        nlinarith
      have h_mem_neg : hδ_F - ((ε / 2) : ℝ) • u_normed ∈ Metric.ball hδ_F ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        have h_sub : (hδ_F - ((ε / 2) : ℝ) • u_normed) - hδ_F = -(((ε / 2) : ℝ) • u_normed) := by
          abel
        rw [h_sub, norm_neg, norm_smul]
        rw [hnorm_u_normed, mul_comm, Real.norm_of_nonneg (by positivity : 0 ≤ ε / 2)]
        nlinarith
      have hp_pos : hp.f (hδ_F + ((ε / 2) : ℝ) • u_normed) ≤ hp.c :=
        hp.upper_bound _ (h_ball_sub h_mem_pos)
      have hp_neg : hp.f (hδ_F - ((ε / 2) : ℝ) • u_normed) ≤ hp.c :=
        hp.upper_bound _ (h_ball_sub h_mem_neg)
      -- Expand using linearity
      have hp_pos_expand : hp.f hδ_F + ((ε / 2) : ℝ) * hp.f u_normed ≤ hp.c := by
        simpa [map_add, map_smul, hp_f_hδ] using hp_pos
      have hp_neg_expand : hp.f hδ_F - ((ε / 2) : ℝ) * hp.f u_normed ≤ hp.c := by
        simpa [map_sub, map_smul, hp_f_hδ] using hp_neg
      -- From hp_pos_expand: (ε/2) * hp.f u_normed ≤ 0
      -- From hp_neg_expand: -(ε/2) * hp.f u_normed ≤ 0
      -- Since ε/2 > 0, we get hp.f u_normed = 0
      have h1 : hp.f u_normed ≤ 0 := by nlinarith
      have h2 : hp.f u_normed ≥ 0 := by nlinarith
      have hp_f_u_normed_zero : hp.f u_normed = 0 := by linarith
      -- Therefore hp.f u = 0
      have hp_f_u_zero : hp.f u = 0 := by
        have h_eq : u = ‖u‖ • u_normed := by
          dsimp [u_normed]
          have h_scalar : (1 : ℝ) = (‖u‖ : ℝ) * (1 / ‖u‖) := by
            field_simp [hnorm_pos.ne']
          calc
            u = (1 : ℝ) • u := by simp
            _ = ((‖u‖ : ℝ) * (1 / ‖u‖)) • u := by
              rw [h_scalar]
              simp
              grind
            _ = ‖u‖ • ((1 / ‖u‖) • u) := by simp [smul_smul]
        rw [h_eq, hp.f.map_smul, hp_f_u_normed_zero, smul_zero]
      -- Hence hp.f x = hp.c, contradiction
      have : hp.f x = hp.c := by
        calc
          hp.f x = hp.f (hδ_F + (x - hδ_F)) := by simp
          _ = hp.f (hδ_F + u) := rfl
          _ = hp.f hδ_F + hp.f u := by simp
          _ = hp.c := by simp [hp_f_hδ, hp_f_u_zero]
      linarith

/--
The intrinsic interior of a polytope P.Ω with nonempty interior equals the
topological interior (since affine span of P.Ω is the full ambient).
-/
private lemma intrinsicInterior_polytope_eq_interior {n : ℕ} (P : Polytope n) :
    intrinsicInterior ℝ P.Ω = interior P.Ω := by
  have h_convex : Convex ℝ P.Ω := convex_convexHull ℝ _
  have h_span_top : affineSpan ℝ P.Ω = ⊤ :=
    (h_convex.interior_nonempty_iff_affineSpan_eq_top).mp P.interior_nonempty
  let A := affineSpan ℝ P.Ω
  have hA_set_eq_univ : (A : Set (CoeffVec n)) = Set.univ := by
    simpa [A] using congrArg (fun (s : AffineSubspace ℝ (CoeffVec n)) => (s : Set (CoeffVec n))) h_span_top
  have h_mem : ∀ x : CoeffVec n, x ∈ (A : Set (CoeffVec n)) := by
    simpa [hA_set_eq_univ]
  let h_homeo : Homeomorph A (CoeffVec n) := {
    toFun := Subtype.val
    invFun := λ x => ⟨x, h_mem x⟩
    left_inv := λ _ => rfl
    right_inv := λ _ => rfl
    continuous_toFun := by continuity
    continuous_invFun := by continuity
  }
  calc
    intrinsicInterior ℝ P.Ω = (Subtype.val : A → CoeffVec n) ''
      interior ((Subtype.val : A → CoeffVec n)⁻¹' P.Ω) := rfl
    _ = interior ((Subtype.val : A → CoeffVec n) '' ((Subtype.val : A → CoeffVec n)⁻¹' P.Ω)) := by
      have h_image := h_homeo.image_interior ((Subtype.val : A → CoeffVec n)⁻¹' P.Ω)
      simpa using h_image
    _ = interior (P.Ω ∩ (A : Set (CoeffVec n))) := by
      simp [Set.image_preimage_eq_inter_range, Subtype.range_coe]
    _ = interior (P.Ω ∩ Set.univ) := by rw [hA_set_eq_univ]
    _ = interior P.Ω := by simp

/--
Given a polytope P, an exposed face F of P, and a boundary point δ_bound of F,
construct a proper exposed subface G ⊊ F containing δ_bound with dim(G) < dim(F).
-/
private lemma exists_proper_subface_of_boundary_point {n : ℕ} (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F) (δ_bound : CoeffVec n)
    (hδ_bound_in_F : δ_bound ∈ F) (hδ_bound_front : δ_bound ∈ frontier F)
    (hδ_bound_not_relint : δ_bound ∉ intrinsicInterior ℝ F)
    (hF_dim : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 2) :
    ∃ (G : Set (CoeffVec n)), IsExposedFace P G ∧ δ_bound ∈ G ∧
    Module.finrank ℝ (affineSpan ℝ G).direction < Module.finrank ℝ (affineSpan ℝ F).direction ∧
    Module.finrank ℝ (affineSpan ℝ G).direction ≥ 1 := by
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
    -- ----------------------------------------------------------------
    -- hG_dim_ge_1: In case A, g_Ω is non-constant on F and the level set
    -- {x ∈ F | g_Ω x = g_c} has dimension dim(F) - 1 ≥ 1. The proof uses
    -- rank-nullity and the fact that g_Ω v_dir > 0.
    -- ----------------------------------------------------------------
    have hG_dim_ge_1 : Module.finrank ℝ (affineSpan ℝ G).direction ≥ 1 := by
      have h_dim_lt : Module.finrank ℝ (affineSpan ℝ G).direction <
          Module.finrank ℝ (affineSpan ℝ F).direction := hG_dim_lt
      have h_dim_F_ge_2 : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 2 := hF_dim
      have h_gv_pos : g_Ω v_dir > 0 := hgv_pos

      sorry
    -- ----------------------------------------------------------------
    -- CONCLUSION: Return G as the proper subface
    -- ----------------------------------------------------------------
    exact ⟨G, hG_exposed, hδ_in_G, hG_dim_lt, hG_dim_ge_1⟩
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
    -- The construction of a proper subface in Case B requires a supporting functional
    -- of P.Ω at δ_bound that varies on F. This is obtained by:
    -- (1) Separating δ_bound from intrinsicInterior ℝ F within affF using
    --     geometric_hahn_banach_open_point, giving w_F on affF.direction.
    -- (2) Extending w_F to the whole space (by zero on a complement) to get w_ext.
    -- (3) Adding hp.f to ensure support of P.Ω: g_new := hp.f + w_ext.
    -- Then G = {x ∈ P.Ω | g_new x = g_new δ_bound} is a proper subface with dim = dim(F)-1 ≥ 1.
    -- The detailed proof is non-trivial (requires supporting hyperplane theorem).
    sorry

private lemma isExposedEdge_of_dim_1 {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
    (hF_exposed : IsExposedFace P F)
    (h_dim : Module.finrank ℝ (affineSpan ℝ F).direction = 1) : IsExposedEdge P F := by
  obtain ⟨hp, hF_eq⟩ := hF_exposed
  exact ⟨hp, hF_eq, hF_eq ▸ h_dim⟩

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
      have h_not_relint : δ_bound ∉ intrinsicInterior ℝ F := by
        intro h_relint
        rcases h_relint with ⟨x, hx_int, hx_eq⟩
        have h_open_int : IsOpen (interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF)) :=
          isOpen_interior
        haveI : Nonempty affF := ⟨⟨δ_F, hδ_F_affF⟩⟩
        let v_dir : (affineSpan ℝ F).direction := ⟨v, hv_affF_dir⟩
        have h_cont_ambient : Continuous (fun (t : ℝ) => (t • v : CoeffVec n) + (x : CoeffVec n)) := by
          continuity
        have h_mem_affF : ∀ (t : ℝ), (t • v : CoeffVec n) + (x : CoeffVec n) ∈ affF := by
          intro t
          simpa using
            AffineSubspace.vadd_mem_of_mem_direction (s := affF) (hv := affF.direction.smul_mem t hv_affF_dir)
              (hp := x.property)
        have h_cont : Continuous (fun (t : ℝ) => (t • v_dir) +ᵥ (x : affF)) := by
          have : (fun (t : ℝ) => ((t • v_dir) +ᵥ (x : affF) : CoeffVec n)) = (fun (t : ℝ) => (t • v : CoeffVec n) + (x : CoeffVec n)) := by
            ext t
            simp [v_dir, vadd_eq_add]
          have h_cont_ambient' : Continuous (fun (t : ℝ) => ((t • v_dir) +ᵥ (x : affF) : CoeffVec n)) := by
            simpa [this] using h_cont_ambient
          exact h_cont_ambient'.subtype_mk (fun t => h_mem_affF t)
        have h_preimage_open : IsOpen ((fun (t : ℝ) => (t • v_dir) +ᵥ (x : affF))⁻¹'
            (interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF))) :=
          h_open_int.preimage h_cont
        have h_zero_mem : (0 : ℝ) ∈ (fun (t : ℝ) => (t • v_dir) +ᵥ (x : affF))⁻¹'
            (interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF)) := by
          simpa using hx_int
        obtain ⟨ε, hε_pos, h_ball⟩ :=
          Metric.isOpen_iff.mp h_preimage_open 0 h_zero_mem
        have h_eps_div2_pos : 0 < ε / 2 := by linarith
        have h_in_ball : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
          rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          nlinarith
        have h_interior : ((ε / 2) • v_dir) +ᵥ (x : affF) ∈
            interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF) :=
          h_ball h_in_ball
        have h_in_intrinsic : δ_bound + (ε / 2) • v ∈ intrinsicInterior ℝ F := by
          refine ⟨((ε / 2) • v_dir) +ᵥ (x : affF), h_interior, ?_⟩
          calc
            (Subtype.val : affF → CoeffVec n) (((ε / 2) • v_dir) +ᵥ (x : affF))
                = ((ε / 2) • v_dir).val + (x : CoeffVec n) := by
              simp [vadd_eq_add]
            _ = (ε / 2) • v + δ_bound := by
              simp [v_dir, hx_eq]
            _ = δ_bound + (ε / 2) • v := by abel
        have h_in_F : δ_bound + (ε / 2) • v ∈ F :=
          intrinsicInterior_subset h_in_intrinsic
        have h_t1_plus_eps_div2 : t1 + ε / 2 ∈ S := by
          refine ⟨by positivity, ?_⟩
          have h_eq : δ_F + (t1 + ε / 2) • v = δ_bound + (ε / 2) • v := by
            calc
              δ_F + (t1 + ε / 2) • v = (δ_F + t1 • v) + (ε / 2) • v := by
                rw [add_smul, add_assoc]
              _ = δ_bound + (ε / 2) • v := rfl
          rw [h_eq]
          exact h_in_F
        have h_t1_lt : t1 < t1 + ε / 2 := by nlinarith
        have h_sup_ge : t1 + ε / 2 ≤ sSup S :=
          le_csSup h_bdd_above h_t1_plus_eps_div2
        have h_t1_eq_sup : t1 = sSup S := rfl
        rw [h_t1_eq_sup] at h_sup_ge
        nlinarith
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


private lemma descend_to_exposed_edge {n : ℕ} (P : Polytope n) (r : ℝ)
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
    obtain ⟨G, hG_exp, hδ_bound_in_G, hG_dim_lt, hG_dim_ge_1⟩ :=
      exists_proper_subface_of_boundary_point P F hF_exp δ_bound
        hδ_bound_in_F hδ_bound_front hδ_bound_not_relint hm_F_ge_2
    have hs_G : (r : ℂ) ∈ RootSpaceSet G :=
      rootspace_mem_of_eval_zero r δ_bound hδ_bound_Psr G hδ_bound_in_G
    by_cases hG_dim_ge_2 : Module.finrank ℝ (affineSpan ℝ G).direction ≥ 2
    · exact descend_to_exposed_edge P r G hG_exp hs_G hG_dim_ge_2
    · -- dim(G) = 1 (exists_proper_subface_of_boundary_point guarantees dim(G) ≥ 1)
      have hm_G_ge_1 : Module.finrank ℝ (affineSpan ℝ G).direction ≥ 1 := hG_dim_ge_1
      have hm_G_1 : Module.finrank ℝ (affineSpan ℝ G).direction = 1 :=
        le_antisymm (by omega) hm_G_ge_1
      refine ⟨G, isExposedEdge_of_dim_1 hG_exp hm_G_1, hs_G⟩
  termination_by Module.finrank ℝ (affineSpan ℝ F).direction
  decreasing_by exact hG_dim_lt



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
      · -- F has dim 0 (vertex case): δ_bound is a vertex of P.Ω and we need an exposed
        -- edge containing it. This is the existence of an edge through a vertex of a
        -- polytope with dim ≥ 2, which requires polyhedral combinatorics (e.g., a
        -- supporting functional of P.Ω at δ_bound exposing a 1-dim face).
        have hm_F_0 : m_F = 0 := by omega
        have hδ_bound_in_Ω : δ_bound ∈ P.Ω :=
          frontier_point_in_Ω P δ_bound hδ_bound_front
        -- Find a linear functional exposing an edge through δ_bound.
        -- Strategy: extend the existing F-exposing functional to one whose exposed
        -- face has dim ≥ 1 containing δ_bound.

        sorry
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
        (mem_P_sr_of_isRoot s.re δ (by rw [← hs_real]; exact hδ_root)) P.Ω hδ_in_Ω

theorem lemma61_complex (hn : n ≥ 1) (P : Polytope n) (s : ℂ) (hs : s ∈ RootSpace P) :
    s.im ≠ 0 → ∃ F, IsExposedFace P F ∧ s ∈ RootSpaceSet F := by
  intro hcomplex
  sorry

theorem lemma61 (hn : n ≥ 1) (P : Polytope n) (s : ℂ) (hs : s ∈ RootSpace P) :
    (s.im = 0 → ∃ E, IsExposedEdge P E ∧ s ∈ RootSpaceSet E) ∧
    (s.im ≠ 0 → ∃ F, IsExposedFace P F ∧ s ∈ RootSpaceSet F) :=
  ⟨lemma61_real hn P s hs, lemma61_complex hn P s hs⟩

end CoeffBox
