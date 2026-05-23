module

public import ControlSystems.DiscreteTime.EdgeTheoremDefs

@[expose] public section

open Polynomial
open Affine
open FiniteDimensional

namespace CoeffBox

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

private lemma segment_boundary_intersection {n : ℕ} (P : Polytope n) (δ : CoeffVec n)
    (hδ_in_Ω : δ ∈ P.Ω) (hδ_not_front : δ ∉ frontier P.Ω)
    (v : CoeffVec n) (hv_nonzero : v ≠ 0) (t_out : ℝ) (ht_out : δ + t_out • v ∉ P.Ω) :
    ∃ δ_bound ∈ segment ℝ δ (δ + t_out • v), δ_bound ∈ frontier P.Ω := by
  have h_conn : IsConnected (segment ℝ δ (δ + t_out • v)) := by
    apply Convex.isConnected
    · exact convex_segment δ (δ + t_out • v)
    · exact ⟨δ, left_mem_segment ℝ δ (δ + t_out • v)⟩
  have h_closed : IsClosed P.Ω := P.isCompact.isClosed
  have h_frontier_eq : frontier P.Ω = P.Ω \ interior P.Ω := frontier_eq_for_closed P.Ω h_closed
  by_contra h_no_front
  push_neg at h_no_front
  let U_open := interior P.Ω
  let V_open := interior (P.Ωᶜ)
  have h_pre := h_conn.2 U_open V_open isOpen_interior isOpen_interior
  have h_cover : segment ℝ δ (δ + t_out • v) ⊆ U_open ∪ V_open := by
    intro x hx
    by_cases hx_P : x ∈ P.Ω
    · left
      have hxf := h_no_front x hx
      rw [h_frontier_eq, Set.mem_diff] at hxf
      push_neg at hxf
      exact hxf hx_P
    · right
      have h_compl_open : IsOpen (P.Ωᶜ) := h_closed.isOpen_compl
      simp only [V_open, h_compl_open.interior_eq]
      exact hx_P
  have h_in_u : (segment ℝ δ (δ + t_out • v) ∩ U_open).Nonempty := by
    use δ
    constructor
    · exact left_mem_segment ℝ δ (δ + t_out • v)
    · rw [h_frontier_eq, Set.mem_diff] at hδ_not_front
      push_neg at hδ_not_front
      exact hδ_not_front hδ_in_Ω
  have h_in_v : (segment ℝ δ (δ + t_out • v) ∩ V_open).Nonempty := by
    use δ + t_out • v
    constructor
    · exact right_mem_segment ℝ δ (δ + t_out • v)
    · have h_compl_open : IsOpen (P.Ωᶜ) := h_closed.isOpen_compl
      simp only [V_open]
      rw [h_compl_open.interior_eq]
      exact ht_out
  have huv_empty : U_open ∩ V_open = ∅ := by
    apply Set.eq_empty_of_subset_empty
    calc U_open ∩ V_open ⊆ P.Ω ∩ P.Ωᶜ := Set.inter_subset_inter interior_subset interior_subset
      _ = ∅ := Set.inter_compl_self P.Ω
  have h_inter_nonempty := h_pre h_cover h_in_u h_in_v
  obtain ⟨x, hx_s, hx_uv⟩ := h_inter_nonempty
  rw [huv_empty] at hx_uv
  exact hx_uv

private lemma exists_boundary_point_in_Psr {n : ℕ} (P : Polytope n) (r : ℝ) (δ : CoeffVec n)
    (hδ_in_Ω : δ ∈ P.Ω) (hδ_in_Psr : δ ∈ (P_sr n r : Set (CoeffVec n)))
    (affΩ : AffineSubspace ℝ (CoeffVec n)) (hδ_aff : δ ∈ affΩ)
    (hA_dim : Module.finrank ℝ ↥(affineSpan ℝ ((P_sr n r : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction ≥ 1) :
    ∃ δ_bound, δ_bound ∈ (P_sr n r : Set (CoeffVec n)) ∩ frontier P.Ω := by
  have h_dim_pos : 0 < Module.finrank ℝ ↥(affineSpan ℝ ((P_sr n r : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction := by omega
  let U : Submodule ℝ (CoeffVec n) := P_sr n r
  haveI : Nontrivial ↥(U ⊓ affΩ.direction) := by
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
  obtain ⟨v_sub, hv_sub_nonzero⟩ := exists_ne (0 : ↑(U ⊓ affΩ.direction))
  let v : CoeffVec n := v_sub.val
  have h_line_in_intersection : ∀ (t : ℝ), δ + t • v ∈ (P_sr n r : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)) := by
    intro t
    refine Set.mem_inter ?_ ?_
    · exact Submodule.add_mem U hδ_in_Psr (Submodule.smul_mem U t v_sub.2.1)
    · have h_vadd := affΩ.vadd_mem_of_mem_direction (Submodule.smul_mem affΩ.direction t v_sub.2.2) hδ_aff
      have h_eq : δ + t • v = t • v +ᵥ δ := by rw [vadd_eq_add, add_comm]
      rw [h_eq]; exact h_vadd
  have hv_nonzero : v ≠ 0 := by intro h; apply hv_sub_nonzero; exact Submodule.coe_eq_zero.mp h
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
    have h_rewrite : (1 - c) • δ + c • (δ + t_out • v) = δ + (c * t_out) • v := by
      calc (1 - c) • δ + c • (δ + t_out • v)
        _ = (1 - c) • δ + (c • δ + c • (t_out • v)) := by rw [smul_add]
        _ = ((1 - c) • δ + c • δ) + c • (t_out • v) := by rw [←add_assoc]
        _ = ((1 - c) + c) • δ + c • (t_out • v) := by rw [←add_smul]
        _ = 1 • δ + (c * t_out) • v := by
            have h_one : (1 - c) + c = 1 := by ring
            simp only [h_one, smul_smul, one_smul]
        _ = δ + (c * t_out) • v := by rw [one_smul]
    have h_mem := h_line_in_intersection (c * t_out)
    simp only [Set.mem_inter] at h_mem
    have : δ_bound ∈ (P_sr n r : Set (CoeffVec n)) := by
      have h_eq : δ_bound = δ + (c * t_out) • v := by
        calc δ_bound = (1 - c) • δ + c • (δ + t_out • v) := by rw [←hc_eq]
          _ = δ + (c * t_out) • v := by rw [h_rewrite]
      rw [h_eq]
      exact h_mem.1
    exact ⟨δ_bound, this, h_front⟩

private lemma exists_exposed_face_containing_boundary_point {n : ℕ} (P : Polytope n)
    (r : ℝ) (δ_bound : CoeffVec n)
    (hδ_bound_front : δ_bound ∈ frontier P.Ω)
    (hδ_bound_Psr : δ_bound ∈ (P_sr n r : Set (CoeffVec n)))
    (h_int_nonempty : (interior P.Ω).Nonempty) :
    ∃ F : Set (CoeffVec n), IsExposedFace P F ∧ δ_bound ∈ F ∧ (r : ℂ) ∈ RootSpaceSet F := by

  have h_closed : IsClosed P.Ω := P.isCompact.isClosed
  have hδ_bound_in_Ω : δ_bound ∈ P.Ω := by
    have hsub := frontier_subset_closure (s := P.Ω)
    rw [h_closed.closure_eq] at hsub
    exact hsub hδ_bound_front

  have hδ_bound_not_int : δ_bound ∉ interior P.Ω := by
    intro hint
    have h1 : δ_bound ∈ frontier P.Ω := hδ_bound_front
    rw [frontier_eq_closure_inter_closure, h_closed.closure_eq] at h1
    have h2 : δ_bound ∈ closure (P.Ωᶜ) := h1.2
    have h3 : δ_bound ∉ closure (P.Ωᶜ) := by
      rw [closure_compl (s := P.Ω)]
      simp only [Set.mem_compl_iff, not_not]
      trivial
    exact h3 h2

  have h_convex : Convex ℝ P.Ω := convex_convexHull ℝ _

  have h_int_convex : Convex ℝ (interior P.Ω) := h_convex.interior
  have h_int_open : IsOpen (interior P.Ω) := isOpen_interior

  obtain ⟨f, hf_strict⟩ :=
      geometric_hahn_banach_open_point h_int_convex h_int_open hδ_bound_not_int

  have hf_ne : f ≠ 0 := by
    intro heq
    simp only [heq, ContinuousLinearMap.zero_apply] at hf_strict
    obtain ⟨x, hx⟩ := h_int_nonempty
    exact lt_irrefl 0 (hf_strict x hx)

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

  have hc_upper : ∀ x ∈ P.Ω, f_lin x ≤ c := by
    intro x hx
    have h_closed_half : IsClosed {y | f y ≤ c} :=
      isClosed_Iic.preimage f.continuous
    have h_subset : P.Ω ⊆ {y | f y ≤ c} := by
      calc
        P.Ω = closure P.Ω := (P.isCompact.isClosed.closure_eq).symm
        _ = closure (interior P.Ω) :=
          (h_convex.closure_interior_eq_closure_of_nonempty_interior h_int_nonempty).symm
        _ ⊆ closure {y | f y ≤ c} :=
          closure_mono fun y hy => le_of_lt (hf_strict y hy)
        _ = {y | f y ≤ c} := h_closed_half.closure_eq
    have hx_f : f x ≤ c := h_subset hx
    simpa [f_lin] using hx_f

  have hc_touches : ∃ x ∈ P.Ω, f_lin x = c :=
    ⟨δ_bound, hδ_bound_in_Ω, rfl⟩

  let hp : SupportingHyperplane P := {
    f           := f_lin
    c           := c
    nonzero     := hf_lin_ne
    upper_bound := hc_upper
    touches     := hc_touches
  }

  have hδ_in_face : δ_bound ∈ ExposedFace hp := by
    unfold ExposedFace
    simp only [Set.mem_setOf_eq]
    exact ⟨hδ_bound_in_Ω, rfl⟩

  have hr_in_rootspace : (r : ℂ) ∈ RootSpaceSet (ExposedFace hp) := by
    unfold RootSpaceSet
    simp only [Set.mem_setOf_eq]
    refine ⟨δ_bound, hδ_in_face, ?_⟩
    have heval : evalLinear r δ_bound = 0 := hδ_bound_Psr
    unfold Polynomial.IsRoot
    rw [Polynomial.eval_map]
    rw [Polynomial.eval₂_eq_eval_map]
    have h_comm : eval (↑r) (map (algebraMap ℝ ℂ) (polyOfVec δ_bound))
        = (algebraMap ℝ ℂ) (eval r (polyOfVec δ_bound)) := by
      simp [polyOfVec, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
            map_sum, map_mul, map_pow]
    rw [h_comm]
    have h_eval_eq : eval r (polyOfVec δ_bound) = evalLinear r δ_bound := rfl
    rw [h_eval_eq, heval]
    simp

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
private lemma escapes_P_via_exposed_face {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
    (hF_exposed : IsExposedFace P F) (δ : CoeffVec n) (v : CoeffVec n) (t : ℝ)
    (hδ_in_F : δ ∈ F) (hv_in_dir : v ∈ (affineSpan ℝ F).direction)
    (h_escapes_F : δ + t • v ∉ F) : δ + t • v ∉ P.Ω := by
  obtain ⟨hp, hF_eq⟩ := hF_exposed
  have hδ_f : hp.f δ = hp.c := by
    rw [hF_eq] at hδ_in_F
    exact hδ_in_F.2
  have h_aff_const : ∀ x ∈ affineSpan ℝ F, hp.f x = hp.c := by
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
  have h_δ_plus_v : δ + v ∈ affineSpan ℝ F := by
    have h_vadd : v +ᵥ δ ∈ affineSpan ℝ F :=
      AffineSubspace.vadd_mem_of_mem_direction hv_in_dir (subset_affineSpan ℝ F hδ_in_F)
    simpa [vadd_eq_add, add_comm] using h_vadd
  have hv_f : hp.f v = 0 := by
    have hsum : hp.f (δ + v) = hp.f δ + hp.f v := by simp
    rw [h_aff_const (δ + v) h_δ_plus_v, h_aff_const δ (subset_affineSpan ℝ F hδ_in_F)] at hsum
    linarith
  have h_val : hp.f (δ + t • v) = hp.c := by
    calc
      hp.f (δ + t • v) = hp.f δ + hp.f (t • v) := by simp
      _ = hp.c + t • (hp.f v) := by simp [hδ_f, LinearMap.map_smul]
      _ = hp.c + t • 0 := by rw [hv_f]
      _ = hp.c := by simp
  by_contra h_in_Ω
  apply h_escapes_F
  rw [hF_eq]
  exact ⟨h_in_Ω, h_val⟩

/--
Any point on the frontier of an exposed face (relative to its affine span)
belongs to a proper subface of strictly lower dimension.
-/
private lemma exists_subface_of_strictly_lower_dimension {n : ℕ} (P : Polytope n) (F : Set (CoeffVec n))
    (hF_exposed : IsExposedFace P F) (δ_bound : CoeffVec n)
    (hδ_bound_in_F : δ_bound ∈ F) (hδ_bound_front : δ_bound ∈ frontier F)
    (hF_nontrivial : F.Nontrivial)
    (hδ_bound_front_P : δ_bound ∈ frontier P.Ω)
    (h_int_nonempty : (interior P.Ω).Nonempty)
    (v : CoeffVec n) (hv_dir : v ∈ (affineSpan ℝ F).direction)
    (h_exits : ∃ ε > 0, δ_bound + ε • v ∉ P.Ω)
    (h_from_interior : ∃ (δ_F : CoeffVec n), δ_F ∈ interior P.Ω ∧ ∃ (c : ℝ), c > 0 ∧ δ_bound = δ_F + c • v) :
    ∃ G, IsExposedFace P G ∧ δ_bound ∈ G ∧ G ⊆ F ∧
    Module.finrank ℝ (affineSpan ℝ G).direction < Module.finrank ℝ (affineSpan ℝ F).direction := by
  obtain ⟨hpF, hF_eq⟩ := hF_exposed
  have hF_compact : IsCompact F := by
    rw [hF_eq]
    refine P.isCompact.inter_right ?_
    exact isClosed_eq (LinearMap.continuous_of_finiteDimensional hpF.f) continuous_const
  have hF_convex : Convex ℝ F := by
    rw [hF_eq]
    apply Convex.inter (convex_convexHull ℝ _)
    rintro x hx y hy a b ha hb hab
    change hpF.f (a • x + b • y) = hpF.c
    rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul, hx, hy, ←add_smul, hab, one_smul]

  have hδ_bound_in_Ω : δ_bound ∈ P.Ω := by
    have hsub := frontier_subset_closure (s := P.Ω)
    rw [P.isCompact.isClosed.closure_eq] at hsub
    exact hsub hδ_bound_front_P
  have h_convex_Ω : Convex ℝ P.Ω := convex_convexHull ℝ _
  have hδ_not_int_Ω : δ_bound ∉ interior P.Ω := by
    rw [frontier_eq_for_closed P.Ω (P.isCompact.isClosed)] at hδ_bound_front_P
    exact hδ_bound_front_P.2
  have h_int_convex : Convex ℝ (interior P.Ω) := h_convex_Ω.interior
  have h_int_open : IsOpen (interior P.Ω) := isOpen_interior

  obtain ⟨g, hg_strict⟩ :=
    geometric_hahn_banach_open_point h_int_convex h_int_open hδ_not_int_Ω

  have hg_ne : g ≠ 0 := by
    intro heq
    simp only [heq, ContinuousLinearMap.zero_apply] at hg_strict
    obtain ⟨x, hx⟩ := h_int_nonempty
    exact lt_irrefl 0 (hg_strict x hx)

  let g_lin : CoeffVec n →ₗ[ℝ] ℝ := g.toLinearMap

  have hc_upper : ∀ x ∈ P.Ω, g_lin x ≤ g_lin δ_bound := by
    intro x hx
    have h_closed_half : IsClosed {y | g y ≤ g δ_bound} :=
      isClosed_Iic.preimage g.continuous
    have h_subset : P.Ω ⊆ {y | g y ≤ g δ_bound} := by
      calc
        P.Ω = closure P.Ω := (P.isCompact.isClosed.closure_eq).symm
        _ = closure (interior P.Ω) :=
          (h_convex_Ω.closure_interior_eq_closure_of_nonempty_interior h_int_nonempty).symm
        _ ⊆ closure {y | g y ≤ g δ_bound} :=
          closure_mono fun y hy => le_of_lt (hg_strict y hy)
        _ = {y | g y ≤ g δ_bound} := h_closed_half.closure_eq
    have hx_g : g x ≤ g δ_bound := h_subset hx
    simpa [g_lin] using hx_g

  have hc_touches : ∃ x ∈ P.Ω, g_lin x = g_lin δ_bound :=
    ⟨δ_bound, hδ_bound_in_Ω, rfl⟩

  let hp_new : SupportingHyperplane P := {
    f := g_lin
    c := g_lin δ_bound
    nonzero := by
      intro hzero
      apply hg_ne
      ext x
      simpa [hzero] using rfl
    upper_bound := hc_upper
    touches := hc_touches
  }

  let G_new : Set (CoeffVec n) := ExposedFace hp_new
  let G : Set (CoeffVec n) := F ∩ G_new

  have h_fv_zero : hpF.f v = 0 := by
    have h_dir_le_ker : (affineSpan ℝ F).direction ≤ ker hpF.f := by
      intro w hw
      have h_const : ∀ x : affineSpan ℝ F, hpF.f x = hpF.c := by
        intro x
        apply affineSpan_le.mpr (fun y hy => ?_) (SetLike.coe_mem x)
        rw [hF_eq] at hy
        exact hy.2
      sorry
    sorry

  have h_gv_pos : g_lin v > 0 := by
    obtain ⟨δ_F, hδ_F_int, c, hc_pos, h_eq⟩ := h_from_interior
    have h_bound_in_Ω : δ_F + c • v ∈ P.Ω := by rw [← h_eq]; exact hδ_bound_in_Ω
    have h_half_mem : δ_F + (1/2 : ℝ) • (c • v) ∈ interior P.Ω :=
      h_convex_Ω.add_smul_mem_interior hδ_F_int h_bound_in_Ω ⟨by norm_num, by norm_num⟩
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
    have : g v = g_lin v := rfl
    rw [this] at h_ineq
    nlinarith

  have hG_exposed : IsExposedFace P G := by
    let g_new : CoeffVec n →ₗ[ℝ] ℝ := hpF.f + g_lin
    have h_new_upper : ∀ x ∈ P.Ω, g_new x ≤ hpF.c + g_lin δ_bound := by
      intro x hx
      have hfx : hpF.f x ≤ hpF.c := hpF.upper_bound x hx
      have hgx : g_lin x ≤ g_lin δ_bound := hc_upper x hx
      nlinarith
    have h_new_touches : ∃ x ∈ P.Ω, g_new x = hpF.c + g_lin δ_bound :=
      ⟨δ_bound, hδ_bound_in_Ω, by simp [g_new]⟩
    have h_new_nonzero : g_new ≠ 0 := by
      intro hzero
      have : g_lin v = 0 := by
        calc
          g_lin v = g_new v := by
            simp [g_new, h_fv_zero]
          _ = (0 : CoeffVec n →ₗ[ℝ] ℝ) v := by rw [hzero]
          _ = 0 := by simp
      linarith
    have hG_eq : G = {x | x ∈ P.Ω ∧ g_new x = hpF.c + g_lin δ_bound} := by
      ext x; constructor
      · intro ⟨hxF, hxG⟩
        rcases hxG with ⟨hxΩ, hx_g⟩
        refine ⟨hxΩ, ?_⟩
        simp [g_new, hx_g.2, hx_g.1]
      · intro ⟨hxΩ, hx_new⟩
        have hx_f : hpF.f x = hpF.c := by
          have h_sum : g_new x = hpF.c + g_lin δ_bound := hx_new
          have hle_f : hpF.f x ≤ hpF.c := hpF.upper_bound x hxΩ
          have hle_g : g_lin x ≤ g_lin δ_bound := hc_upper x hxΩ
          by_contra h_not
          have h_lt : hpF.f x < hpF.c := by
            by_contra! h_ge; linarith
          have : g_lin x > g_lin δ_bound := by
            nlinarith
          linarith
        have hx_g : g_lin x = g_lin δ_bound := by
          have h_sum : g_new x = hpF.c + g_lin δ_bound := hx_new
          rw [g_new, hx_f] at h_sum
          linarith
        refine ⟨⟨hxΩ, hx_f⟩, hxΩ, hx_g⟩
    have : IsExposedFace P {x | x ∈ P.Ω ∧ g_new x = hpF.c + g_lin δ_bound} :=
      ⟨{
        f := g_new
        c := hpF.c + g_lin δ_bound
        nonzero := h_new_nonzero
        upper_bound := h_new_upper
        touches := h_new_touches
      }, rfl⟩
    rw [hG_eq]
    exact this

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
    
    have h_ker_finrank_lt : Module.finrank ℝ (U ⊓ ker g_new) < Module.finrank ℝ U := by
      have h_restrict_nonzero : g_new.restrict U ≠ 0 := by
        intro hzero
        apply h_gv_nonzero
        have : (g_new.restrict U) ⟨v, hv_mem_U⟩ = 0 := by
          simpa using congrArg (fun f : U →ₗ[ℝ] ℝ => f ⟨v, hv_mem_U⟩) hzero
        simpa using this
      have h_range_finrank_pos : 0 < Module.finrank ℝ (LinearMap.range (g_new.restrict U)) := by
        have h_range_top : LinearMap.range (g_new.restrict U) = ⊤ := by
          apply LinearMap.range_eq_top.mpr
          intro r
          refine ⟨(r / g_new v) • (⟨v, hv_mem_U⟩ : U), ?_⟩
          simp [g_new, h_fv_zero, smul_smul, mul_comm, mul_div_cancel (g_new v) (by
            have hpos : g_new v > 0 := by
              calc
                g_new v = g_lin v := by simp [g_new, h_fv_zero]
                _ > 0 := h_gv_pos
            linarith)]
        rw [h_range_top, finrank_top, finrank_self]
        exact Nat.one_pos
      have h_rank_nullity : Module.finrank ℝ (ker (g_new.restrict U)) + Module.finrank ℝ (LinearMap.range (g_new.restrict U)) =
          Module.finrank ℝ U :=
        LinearMap.finrank_range_add_finrank_ker (g_new.restrict U)
      have h_ker_finrank_lt_U : Module.finrank ℝ (ker (g_new.restrict U)) < Module.finrank ℝ U := by
        omega
      have h_ker_eq_inf : ker (g_new.restrict U) = U ⊓ ker g_new := by
        ext x; simp [g_new, Submodule.mem_inf, Submodule.mem_ker, Submodule.restrict_apply]
      rw [h_ker_eq_inf] at h_ker_finrank_lt_U
      exact h_ker_finrank_lt_U
    
    have h_dir_G_le_U : (affineSpan ℝ G).direction ≤ U := by
      apply AffineSubspace.direction_le
      exact affineSpan_mono ℝ hG_sub_F
    
    have h_dir_G_le_W : (affineSpan ℝ G).direction ≤ ker g_new := by
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
      have h_base : δ_bound ∈ affineSpan ℝ G := subset_affineSpan ℝ G ⟨hδ_bound_in_F, ⟨hδ_bound_in_Ω, rfl⟩⟩
      have h_plus : δ_bound + w ∈ affineSpan ℝ G :=
        AffineSubspace.vadd_mem_of_mem_direction hw h_base
      have h_val_base : g_new δ_bound = hpF.c + g_lin δ_bound := by simp [g_new]
      have h_val_plus : g_new (δ_bound + w) = hpF.c + g_lin δ_bound := h_aff_const (δ_bound + w) h_plus
      rw [map_add] at h_val_plus
      rw [h_val_base] at h_val_plus
      linarith
    
    have h_dir_G_le_inter : (affineSpan ℝ G).direction ≤ U ⊓ ker g_new :=
      Submodule.le_inf h_dir_G_le_U h_dir_G_le_W
    
    have h_finrank_le : Module.finrank ℝ ((affineSpan ℝ G).direction) ≤ Module.finrank ℝ (U ⊓ ker g_new) :=
      Submodule.finrank_le h_dir_G_le_inter
    
    calc
      Module.finrank ℝ (affineSpan ℝ G).direction ≤ Module.finrank ℝ (U ⊓ ker g_new) := h_finrank_le
      _ < Module.finrank ℝ U := h_ker_finrank_lt
      _ = Module.finrank ℝ (affineSpan ℝ F).direction := rfl

  exact ⟨G, hG_exposed, hδ_in_G, hG_sub_F, h_dim_lt⟩
    sorry

  have hδ_in_G : δ_bound ∈ G := by
    refine ⟨hδ_bound_in_F, ?_⟩
    unfold ExposedFace
    exact ⟨hδ_bound_in_Ω, rfl⟩

  have hG_sub_F : G ⊆ F := Set.inter_subset_left _ _

  have h_gv_pos : g_lin v > 0 := by
    obtain ⟨δ_F, hδ_F_int, c, hc_pos, h_eq⟩ := h_from_interior
    have h_ε_pos : 0 < c / 2 := by linarith
    have h_mem : δ_bound - (c / 2) • v ∈ interior P.Ω := by
      calc
        δ_bound - (c / 2) • v = δ_F + (c - (c / 2)) • v := by
          rw [h_eq, add_comm, add_sub_assoc, sub_smul, one_smul]
          ring
        _ = δ_F + (c / 2) • v := by ring
      -- Use Convex.add_smul_mem_interior: δ_F ∈ interior P.Ω, δ_F + c·v = δ_bound ∈ P.Ω
      -- For t = 1/2: δ_F + (1/2)·(c·v) = δ_F + (c/2)·v ∈ interior P.Ω
      have h_convex_Ω : Convex ℝ P.Ω := convex_convexHull ℝ _
      have h_bound_in_Ω : δ_F + c • v ∈ P.Ω := by
        rw [← h_eq]
        exact hδ_bound_in_Ω
      have h_half : (c / 2) / c = 1/2 := by
        field_simp [ne_of_gt hc_pos]
      -- Use the lemma with t = 1/2
      have h_half_pos : 0 < (1/2 : ℝ) := by norm_num
      have h_half_le_one : (1/2 : ℝ) ≤ 1 := by norm_num
      have h_mem_interior : δ_F + ((1/2 : ℝ) • (c • v)) ∈ interior P.Ω :=
        h_convex_Ω.add_smul_mem_interior hδ_F_int h_bound_in_Ω ⟨h_half_pos, h_half_le_one⟩
      simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using h_mem_interior
    have h_ineq : g (δ_bound - (c / 2) • v) < g δ_bound :=
      hg_strict _ h_mem
    have h_lin : g_lin (δ_bound - (c / 2) • v) = g_lin δ_bound - (c / 2) • g_lin v := by
      simp [g_lin, map_sub, map_smul]
    have h_g_ineq : g_lin δ_bound - (c / 2) • g_lin v < g_lin δ_bound := by
      -- Convert from g to g_lin
      calc
        g_lin (δ_bound - (c / 2) • v) = g (δ_bound - (c / 2) • v) := rfl
        _ < g δ_bound := h_ineq
        _ = g_lin δ_bound := rfl
      -- But we need to use the linearity relation
      sorry
    sorry

  sorry

/-- In a polytope of dimension at least 2, every vertex is contained in at least one exposed edge. -/
private lemma exists_edge_containing_vertex {n : ℕ} {P : Polytope n} (F : Set (CoeffVec n))
    (hF_exposed : IsExposedFace P F) (v : CoeffVec n) (hv_in_F : v ∈ F)
    (hF_dim : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 2) :
    ∃ E, IsExposedEdge P E ∧ E ⊆ F ∧ v ∈ E := by
  -- For a polytope, every face is the convex hull of its vertices.
  -- A vertex of a face of dimension d >= 2 is always incident to at least d edges.
  sorry

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
    · obtain ⟨hp, hF_eq⟩ := hF_exposed
      exact ⟨hp, hF_eq, hF_eq ▸ h_dim_1⟩
    · exact hr_in_RF
  · have h_dim_ge_2 : m_F ≥ 2 := by
      contrapose! h_dim_1
      have h_le_1 : m_F ≤ 1 := by omega
      have h_nontrivial_dir : Nontrivial ↥(affineSpan ℝ F).direction :=
        direction_nontrivial_of_nontrivial hF_nontrivial
      have h_pos : 1 ≤ m_F := Module.finrank_pos (R := ℝ) (M := ↥(affineSpan ℝ F).direction)
      grind

    obtain ⟨δ_F, hδ_F_in_F, hδ_F_root⟩ := hr_in_RF

    have hδ_F_in_Psr : δ_F ∈ (P_sr n r : Set (CoeffVec n)) := by
      unfold P_sr
      change evalLinear r δ_F = 0
      change eval r (polyOfVec δ_F) = 0
      unfold Polynomial.IsRoot at hδ_F_root
      rw [Polynomial.eval_map] at hδ_F_root
      rw [Polynomial.eval₂_eq_eval_map] at hδ_F_root
      have h_comm :
          eval (↑r) (map (algebraMap ℝ ℂ) (polyOfVec δ_F))
            =
          (algebraMap ℝ ℂ) (eval r (polyOfVec δ_F)) := by
        simp [polyOfVec,
              Polynomial.eval_finset_sum,
              Polynomial.eval_monomial,
              map_sum, map_mul, map_pow]
      rw [h_comm] at hδ_F_root
      exact Complex.ofReal_eq_zero.mp hδ_F_root

    have hδ_F_inter : δ_F ∈ F ∩ (P_sr n r : Set (CoeffVec n)) :=
      ⟨hδ_F_in_F, hδ_F_in_Psr⟩

    let affF : AffineSubspace ℝ (CoeffVec n) := affineSpan ℝ F

    have hδ_F_affF : δ_F ∈ affF := by
      exact subset_affineSpan ℝ F hδ_F_in_F

    have h_affF_dim :
        Module.finrank ℝ affF.direction = m_F := by
      rfl

    have h_inter_dim :
        Module.finrank ℝ
          ↥(affineSpan ℝ
            (((P_sr n r : Set (CoeffVec n)) ∩ (affF : Set (CoeffVec n))))).direction ≥ 1 := by
      exact
        intersection_affine_dim_ge_one
          (P_sr n r)
          affF
          δ_F
          hδ_F_in_Psr
          hδ_F_affF
          (P_sr_dimension r)
          (by
            rw [h_affF_dim]
            exact h_dim_ge_2)

    have hF_compact : IsCompact F := by
      obtain ⟨hp, rfl⟩ := hF_exposed
      unfold ExposedFace
      refine P.isCompact.inter_right ?_
      exact isClosed_eq (LinearMap.continuous_of_finiteDimensional hp.f) continuous_const

    have hF_convex : Convex ℝ F := by
      obtain ⟨hp, rfl⟩ := hF_exposed
      unfold ExposedFace
      exact Convex.inter (convex_convexHull ℝ _) (by
        intro x (hx : hp.f x = hp.c) y (hy : hp.f y = hp.c) a b ha hb hab
        show hp.f (a • x + b • y) = hp.c
        simp only [LinearMap.map_add, LinearMap.map_smul, hx, hy, add_smul, hab, one_smul]
        exact Convex.combo_self hab hp.c)

    have h_inter_nontrivial :
        ((F ∩ (P_sr n r : Set (CoeffVec n))) : Set (CoeffVec n)).Nontrivial := by
      have h_dim_pos :
          0 <
            Module.finrank ℝ
              ↥(affineSpan ℝ
                (((P_sr n r : Set (CoeffVec n)) ∩ (affF : Set (CoeffVec n))))).direction := by
        grind
      let L :=
        affineSpan ℝ
          (((P_sr n r : Set (CoeffVec n)) ∩ (affF : Set (CoeffVec n))))
      have hL_dim_ge_one :
          Module.finrank ℝ ↥L.direction ≥ 1 := by
        simpa [L] using h_inter_dim
      have hL_nonempty : (L : Set (CoeffVec n)).Nonempty := by
        refine ⟨δ_F, ?_⟩
        apply subset_affineSpan
        exact ⟨hδ_F_in_Psr, hδ_F_affF⟩
      have hL_dir_nontrivial : Nontrivial ↥L.direction := by
        exact Module.nontrivial_of_finrank_pos (by
          have : 0 < Module.finrank ℝ ↥L.direction := by omega
          exact this)
      obtain ⟨v_sub, hv_sub_ne⟩ :=
        exists_ne (0 : ↥L.direction)
      let v : CoeffVec n := v_sub.val
      have hv_mem : v ∈ L.direction := v_sub.property
      have hv_ne : v ≠ 0 := by
        intro hv0
        apply hv_sub_ne
        exact Submodule.coe_eq_zero.mp hv0
      let ℓ : Set (CoeffVec n) := { x | ∃ t : ℝ, x = δ_F + t • v }
      have h_ℓ_subset_L : ℓ ⊆ L := by
        intro x hx
        obtain ⟨t, ht⟩ := hx
        subst ht
        have h_v_dir : v ∈ L.direction := v_sub.property
        have h_smul : t • v ∈ L.direction := Submodule.smul_mem _ t h_v_dir
        have h_vadd := AffineSubspace.vadd_mem_of_mem_direction h_smul
          (subset_affineSpan ℝ _ ⟨hδ_F_in_Psr, hδ_F_affF⟩)
        rw [vadd_eq_add] at h_vadd
        refine (AffineSubspace.mem_coe ℝ (CoeffVec n) (δ_F + t • v) L).mpr ?_
        simpa [add_comm] using h_vadd
      have hF_bounded : Bornology.IsBounded F :=
        hF_compact.isBounded

    have h_exists_boundary :
        ∃ δ_bound,
          δ_bound ∈ F ∩ (P_sr n r : Set (CoeffVec n)) ∧
          δ_bound ∈ frontier F := by
      by_cases hδ_front : δ_F ∈ frontier F
      · refine ⟨δ_F, hδ_F_inter, hδ_front⟩
      · have hδ_int : δ_F ∈ interior F := by
          unfold frontier at hδ_front
          rw [hF_compact.isClosed.closure_eq] at hδ_front
          apply not_not.mp
          simp
          by_contra h
          exact hδ_front ⟨hδ_F_in_F, h⟩
        let L :=
          affineSpan ℝ (↑(P_sr n r) ∩ (affF : Set (CoeffVec n)))

        have hL_pos :
            0 < Module.finrank ℝ ↥L.direction := by
          have : Module.finrank ℝ ↥L.direction ≥ 1 := by
            simpa [L] using h_inter_dim
          omega

        have h_dir_nontrivial : Nontrivial ↥L.direction :=
          Module.nontrivial_of_finrank_pos hL_pos
        obtain ⟨v_sub, hv_sub_ne⟩ := exists_ne (0 : ↥L.direction)
        let v : CoeffVec n := v_sub.val
        have hv_ne : v ≠ 0 := by
          intro h; apply hv_sub_ne; exact Subtype.ext h
        have hv_dir : v ∈ L.direction := v_sub.property
        have h_escapes : ∃ t : ℝ, δ_F + t • v ∉ F := by
          by_contra h_contra
          push_neg at h_contra
          have h_bounded : Bornology.IsBounded F := hF_compact.isBounded
          rcases Metric.isBounded_iff.mp h_bounded with ⟨C, hC⟩
          have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
          let t := (|C| + 1) / ‖v‖
          have ht_pos : 0 < t := div_pos (by have : 0 ≤ |C| := abs_nonneg C; linarith) hv_norm_pos
          have h_in := h_contra t
          have h_dist : dist (δ_F + t • v) δ_F = t * ‖v‖ := by
            rw [dist_eq_norm]
            have h_sub : δ_F + t • v - δ_F = t • v := by abel
            have ht_nonneg : 0 ≤ t := ht_pos.le
            rw [h_sub, norm_smul, Real.norm_eq_abs t, abs_of_nonneg ht_nonneg]
          have h_le : dist (δ_F + t • v) δ_F ≤ C := by apply hC; exact h_in; exact hδ_F_in_F
          have h_C_lt : C < |C| + 1 := by have : C ≤ |C| := le_abs_self C; linarith
          rw [h_dist] at h_le
          have h_t_mul : t * ‖v‖ = |C| + 1 := div_mul_cancel₀ (|C| + 1) (ne_of_gt hv_norm_pos)
          rw [h_t_mul] at h_le
          linarith

        obtain ⟨t_out, ht_out⟩ := h_escapes
        have hF_subset : F ⊆ P.Ω := by
          obtain ⟨hp, rfl⟩ := hF_exposed
          exact Set.inter_subset_left

        have hL_le_affF : L ≤ affF :=
          affineSpan_le.mpr Set.inter_subset_right
        have hv_affF_dir : v ∈ affF.direction :=
          AffineSubspace.direction_le hL_le_affF hv_dir
        have ht_out_P : δ_F + t_out • v ∉ P.Ω :=
          escapes_P_via_exposed_face hF_exposed δ_F v t_out hδ_F_in_F hv_affF_dir ht_out

        have hF_subset : F ⊆ P.Ω := by
          obtain ⟨hp, rfl⟩ := hF_exposed
          exact Set.inter_subset_left

        have hδ_F_in_Ω : δ_F ∈ P.Ω := hF_subset hδ_F_in_F


        have hδ_front_Ω : δ_F ∉ frontier P.Ω := by
          intro h_front
          apply hδ_front
          rw [frontier_eq_for_closed F hF_compact.isClosed] at hδ_front ⊢
          unfold frontier at *
          simp
          constructor
          . trivial
          . intro h_int_F

            have h_not_int_Ω : δ_F ∉ interior P.Ω := h_front.2
            have h_int_Ω : δ_F ∈ interior P.Ω := by
              simp only [Set.mem_diff] at h_front
              have h : interior F ⊆ interior P.Ω := interior_mono hF_subset
              exact h h_int_F

            exact h_not_int_Ω h_int_Ω

        obtain ⟨δ_bound, h_seg, h_front_P⟩ :=
          segment_boundary_intersection P δ_F hδ_F_in_Ω hδ_front_Ω v hv_ne t_out ht_out_P

        have h_δ_bound_in_F : δ_bound ∈ F := by
          obtain ⟨hp, hF_expr⟩ := hF_exposed
          rw [hF_expr] at hδ_F_in_F ⊢
          refine ⟨?_, ?_⟩
          · -- δ_bound is in P.Ω because it is in the segment and in P.Ω (from h_front_P)
            have hsub := frontier_subset_closure (s := P.Ω)
            rw [P.isCompact.isClosed.closure_eq] at hsub
            exact Set.mem_of_subset_of_mem hsub h_front_P
          ·
            obtain ⟨c, hc_Icc, rfl⟩ := segment_eq_image ℝ δ_F (δ_F + t_out • v) ▸ h_seg
            simp only [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_sub]
            have hf_δ : hp.f δ_F = hp.c := hδ_F_in_F.2
            have hf_v : hp.f v = 0 := by
              -- v is in L direction, and L is in Psr inter affF
              have h_aff_const : ∀ x ∈ affF, hp.f x = hp.c := by
                intro x hx
                let H : AffineSubspace ℝ (CoeffVec n) :=
                  { carrier := { y | hp.f y = hp.c }
                    smul_vsub_vadd_mem := by
                      intro a y1 y2 y3 hy1 hy2 hy3
                      simp only [Set.mem_setOf_eq] at hy1 hy2 hy3 ⊢
                      simp [hy1, hy2, hy3]
                      }
                have h_le : affF ≤ H := by
                  apply affineSpan_le.mpr
                  intro y hy
                  rw [hF_expr] at hy
                  exact hy.2
                exact h_le hx
              have hL_le_affF : L ≤ affF := affineSpan_le.mpr Set.inter_subset_right
              have hv_affF : v ∈ affF.direction := AffineSubspace.direction_le hL_le_affF hv_dir
              have h_vadd : v +ᵥ δ_F ∈ affF :=
                AffineSubspace.vadd_mem_of_mem_direction hv_affF (subset_affineSpan ℝ F hδ_F_inter.1)
              have h2 := h_aff_const (v +ᵥ δ_F) h_vadd
              have h1 := h_aff_const δ_F (subset_affineSpan ℝ F hδ_F_inter.1)
              simp [vadd_eq_add, h1] at h2
              exact h2
            simp [vadd_eq_add, hf_δ, hf_v]
            ring

        have h_δ_bound_front : δ_bound ∈ frontier F := by
          rw [frontier_eq_for_closed F hF_compact.isClosed]
          refine ⟨h_δ_bound_in_F, ?_⟩
          intro h_int
          have h_int_sub : interior F ⊆ interior P.Ω := interior_mono hF_subset
          have h_int_P : δ_bound ∈ interior P.Ω := h_int_sub h_int
          rw [frontier_eq_for_closed P.Ω (P.isCompact.isClosed)] at h_front_P
          rcases h_front_P with ⟨_, h_not_int_P⟩
          exact h_not_int_P h_int_P

        have h_δ_bound_root : δ_bound ∈ (P_sr n r : Set (CoeffVec n)) := by
          -- δ_bound is on the segment which is in Psr
          rw [segment_eq_image ℝ] at h_seg
          obtain ⟨c, _, h_δ_bound_eq⟩ := h_seg
          rw [← h_δ_bound_eq]
          have h_F_root : δ_F ∈ P_sr n r := hδ_F_in_Psr
          have h_v_root : v ∈ P_sr n r := by
            have hsub : L ≤ (P_sr n r).toAffineSubspace :=
              affineSpan_le.mpr (Set.inter_subset_left)
            have h_in : v ∈ (P_sr n r).toAffineSubspace.direction :=
              AffineSubspace.direction_le hsub hv_dir
            rw [Submodule.toAffineSubspace_direction] at h_in
            exact h_in
          have h_term2 : δ_F + t_out • v ∈ P_sr n r :=
            Submodule.add_mem _ h_F_root (Submodule.smul_mem _ t_out h_v_root)
          exact Submodule.add_mem _ (Submodule.smul_mem _ (1 - c) h_F_root) (Submodule.smul_mem _ c h_term2)

        exact ⟨δ_bound, ⟨h_δ_bound_in_F, h_δ_bound_root⟩, h_δ_bound_front⟩

    obtain ⟨δ_bound, hδ_bound_inter, hδ_bound_front⟩ := h_exists_boundary

    obtain ⟨G, hG_exposed, hδ_bound_in_G, hG_sub, hG_dim_lt⟩ :=
      exists_subface_of_strictly_lower_dimension P F hF_exposed δ_bound hδ_bound_inter.1 hδ_bound_front hF_nontrivial

    have hr_in_RG : (r : ℂ) ∈ RootSpaceSet G := by
      unfold RootSpaceSet
      use δ_bound
      constructor
      · exact hδ_bound_in_G
      · -- Show δ_bound (which is in P_sr) is a root
        have h_eval : evalLinear r δ_bound = 0 := hδ_bound_inter.2
        unfold Polynomial.IsRoot
        rw [Polynomial.eval_map, Polynomial.eval₂_eq_eval_map]
        have h_comm : eval (↑r) (map (algebraMap ℝ ℂ) (polyOfVec δ_bound))
            = (algebraMap ℝ ℂ) (eval r (polyOfVec δ_bound)) := by
          simp [polyOfVec, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
                map_sum, map_mul, map_pow]
        rw [h_comm]
        have h_eval_eq : eval r (polyOfVec δ_bound) = evalLinear r δ_bound := rfl
        rw [h_eval_eq, h_eval]
        simp

    have hG_nonempty : G.Nonempty := ⟨δ_bound, hδ_bound_in_G⟩

    by_cases hG_nontrivial : G.Nontrivial
    · -- Recursive descent
      exact descend_to_exposed_edge P r G hG_exposed hr_in_RG hG_nonempty hG_nontrivial
    · -- G is a vertex (trivial).
      -- If we hit a vertex, we can show it's on an edge of F (and thus P).
      -- Since G is a non-empty convex set and not nontrivial, it's a singleton.
      have hG_singleton : G = {δ_bound} := by
        apply Set.Subset.antisymm
        · intro y hy
          by_contra h_ne
          have : δ_bound ≠ y := by
            intro h_eq; subst h_eq; exact h_ne (Set.mem_singleton _)
          exact hG_nontrivial ⟨δ_bound, hδ_bound_in_G, y, hy, this⟩
        · exact Set.singleton_subset_iff.mpr hδ_bound_in_G

      obtain ⟨E, hE_edge, hE_sub, h_delta_in_E⟩ :=
        exists_edge_containing_vertex F hF_exposed δ_bound (hG_sub hδ_bound_in_G) h_dim_ge_2

      use E
      constructor
      · exact hE_edge
      · -- r is a root at delta_bound, and delta_bound is in E
        unfold RootSpaceSet
        refine ⟨δ_bound, h_delta_in_E, ?_⟩
        -- Show delta_bound is a root
        have h_eval : evalLinear r δ_bound = 0 := hδ_bound_inter.2
        unfold Polynomial.IsRoot
        rw [Polynomial.eval_map, Polynomial.eval₂_eq_eval_map]
        have h_comm : eval (↑r) (map (algebraMap ℝ ℂ) (polyOfVec δ_bound))
            = (algebraMap ℝ ℂ) (eval r (polyOfVec δ_bound)) := by
          simp [polyOfVec, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
                map_sum, map_mul, map_pow]
        rw [h_comm]
        have h_eval_eq : eval r (polyOfVec δ_bound) = evalLinear r δ_bound := rfl
        rw [h_eval_eq, h_eval]
        simp
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

      have h_int_nonempty : (interior P.Ω).Nonempty := by
        sorry

      obtain ⟨F, hF_exposed, hδ_in_F, hs_in_RF⟩ :=
        exists_exposed_face_containing_boundary_point P s.re δ_bound hδ_bound_front hδ_bound_Psr h_int_nonempty

      have h_edge : ∃ (E : Set (CoeffVec n)), IsExposedEdge P E ∧ s ∈ RootSpaceSet E := by
        sorry

      exact h_edge
    · have hm01 : m = 0 ∨ m = 1 := by grind
      by_cases hm0 : m = 0
      · sorry
      · have hm1 : m = 1 := by
          have h_not_0 : m ≠ 0 := hm0
          rcases hm01 with (h0 | h1)
          · exact (h_not_0 h0).elim
          · exact h1
        have h_Ω_is_edge : IsExposedEdge P P.Ω := by
          sorry
        refine ⟨P.Ω, h_Ω_is_edge, ?_⟩
        have : ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s := hδ_root
        exact Set.mem_setOf.mpr ⟨δ, hδ_in_Ω, this⟩

  · intro hcomplex
    sorry

end CoeffBox
