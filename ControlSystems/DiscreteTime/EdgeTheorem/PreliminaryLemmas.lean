module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeTheoremDefs
public import ControlSystems.DiscreteTime.EdgeTheorem.BasicLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.SubfaceConstruction


@[expose] public section

open Polynomial
open Affine
open FiniteDimensional
open LinearMap

namespace CoeffBox

/-- The submodule `P_sr n r` has dimension `n` in the space of coefficient vectors. -/
lemma P_sr_dimension {n : ℕ} (r : ℝ) :
  dim (P_sr n r) = n := by
  unfold P_sr
  have h := LinearMap.finrank_range_add_finrank_ker (evalLinear (n := n) r)
  rw [finrank_CoeffVec] at h
  have hrank : dim (evalLinear (n := n) r).range = 1 := by
    have hsurj : Function.Surjective (evalLinear (n := n) r) :=
      evalLinear_surjective r
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp only [finrank_top, Module.finrank_self]
  grind

/-- The complex evaluation map `evalAtComplex n s : CoeffVec n →ₗ[ℝ] ℂ` is surjective
when `s` is non-real and `n ≥ 1`.  Proof: the constant polynomial `a` and the linear
polynomial `b·s` already span ℂ over ℝ because `1` and `s` are ℝ-linearly independent. -/
lemma evalAtComplex_surjective {n : ℕ} (hn : n ≥ 1) (s : ℂ) (hs : s.im ≠ 0) :
    Function.Surjective (evalAtComplex (n := n) s) := by
  intro z
  let b := z.im / s.im
  let a := z.re - b * s.re
  let δ : CoeffVec n := fun j =>
    if h0 : j.val = 0 then a
    else if h1 : j.val = 1 then b
    else 0
  use δ
  have h0pos : 0 < n + 1 := by omega
  have h1pos : 1 < n + 1 := by omega
  have h_unique_0 : (Finset.univ.filter fun (j : Fin (n+1)) => j.val = 0) = {⟨0, h0pos⟩} := by
    ext j; constructor
    · intro hj
      have hj' : j.val = 0 := by simpa [Finset.mem_filter, Finset.mem_univ] using hj
      exact Finset.mem_singleton.mpr (Fin.ext hj')
    · intro hj
      have hj_eq : j = ⟨0, h0pos⟩ := Finset.mem_singleton.mp hj
      simp [hj_eq, Finset.mem_filter, Finset.mem_univ]
  have h_unique_1 : (Finset.univ.filter fun (j : Fin (n+1)) => j.val = 1) = {⟨1, h1pos⟩} := by
    ext j; constructor
    · intro hj
      have hj' : j.val = 1 := by simpa [Finset.mem_filter, Finset.mem_univ] using hj
      exact Finset.mem_singleton.mpr (Fin.ext hj')
    · intro hj
      have hj_eq : j = ⟨1, h1pos⟩ := Finset.mem_singleton.mp hj
      simp [hj_eq, Finset.mem_filter, Finset.mem_univ]
  have h_sum0 : ∑ (j : Fin (n+1)), (if j.val = 0 then Polynomial.monomial j.val a else 0) = Polynomial.monomial 0 a := by
    rw [← Finset.sum_filter, h_unique_0]; simp
  have h_sum1 : ∑ (j : Fin (n+1)), (if j.val = 1 then Polynomial.monomial j.val b else 0) = Polynomial.monomial 1 b := by
    rw [← Finset.sum_filter, h_unique_1]; simp
  have h_δ_split : δ = (fun (j : Fin (n+1)) => if j.val = 0 then a else 0) +
    (fun (j : Fin (n+1)) => if j.val = 1 then b else 0) := by
    ext j
    dsimp [δ]
    by_cases h0 : j.val = 0
    · simp [h0]
    · by_cases h1 : j.val = 1
      · simp [h0, h1]
      · simp [h0, h1]
  have h_poly : polyOfVec δ = Polynomial.C a + Polynomial.C b * Polynomial.X := by
    calc
      polyOfVec δ = ∑ j : Fin (n+1), Polynomial.monomial j.val (δ j) := rfl
      _ = ∑ j : Fin (n+1), Polynomial.monomial j.val (((fun (j : Fin (n+1)) => if j.val = 0 then a else 0) +
        (fun (j : Fin (n+1)) => if j.val = 1 then b else 0)) j) := by
        rw [h_δ_split]
      _ = ∑ j : Fin (n+1), Polynomial.monomial j.val ((if j.val = 0 then a else 0) + (if j.val = 1 then b else 0)) := rfl
      _ = ∑ j : Fin (n+1), (Polynomial.monomial j.val (if j.val = 0 then a else 0) +
        Polynomial.monomial j.val (if j.val = 1 then b else 0)) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        simp
      _ = (∑ (j : Fin (n+1)), Polynomial.monomial j.val (if j.val = 0 then a else 0)) +
          (∑ (j : Fin (n+1)), Polynomial.monomial j.val (if j.val = 1 then b else 0)) := by
        simp [Finset.sum_add_distrib]
      _ = (∑ (j : Fin (n+1)), (if j.val = 0 then Polynomial.monomial j.val a else 0)) +
          (∑ (j : Fin (n+1)), (if j.val = 1 then Polynomial.monomial j.val b else 0)) := by
        refine congrArg₂ (· + ·) ?_ ?_
        · refine Finset.sum_congr rfl fun j hj => ?_
          by_cases h0 : j.val = 0
          · simp [h0]
          · simp [h0]
        · refine Finset.sum_congr rfl fun j hj => ?_
          by_cases h1 : j.val = 1
          · simp [h1]
          · simp [h1]
      _ = Polynomial.monomial 0 a + Polynomial.monomial 1 b := by rw [h_sum0, h_sum1]
      _ = Polynomial.C a + Polynomial.C b * Polynomial.X := by
        simp [Polynomial.C_mul_X_eq_monomial]
  calc
    ((polyOfVec δ).map (algebraMap ℝ ℂ)).eval s
        = ((Polynomial.C a + Polynomial.C b * Polynomial.X).map (algebraMap ℝ ℂ)).eval s := by
          rw [h_poly]
    _ = ((Polynomial.C (a : ℂ) + Polynomial.C (b : ℂ) * Polynomial.X).eval s) := by simp
    _ = (a : ℂ) + (b : ℂ) * s := by simp
    _ = ((z.re : ℂ) - ((z.im / s.im : ℝ) : ℂ) * (s.re : ℂ)) + ((z.im / s.im : ℝ) : ℂ) * s := by
      dsimp [a, b]; push_cast; ring
    _ = (z.re : ℂ) + ((z.im / s.im : ℝ) : ℂ) * (s - (s.re : ℂ)) := by ring
    _ = (z.re : ℂ) + ((z.im / s.im : ℝ) : ℂ) * ((s.im : ℂ) * Complex.I) := by
      have h_eq : s - (s.re : ℂ) = (s.im : ℂ) * Complex.I := by
        calc
          s - (s.re : ℂ) = ((s.re : ℂ) + (s.im : ℂ) * Complex.I) - (s.re : ℂ) := by
            rw [Complex.re_add_im s]
          _ = (s.im : ℂ) * Complex.I := by ring
      rw [h_eq]
    _ = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
      have h_mul : ((z.im / s.im : ℝ) : ℂ) * (s.im : ℂ) = (z.im : ℂ) := by
        push_cast
        field_simp [hs]
      calc
        (z.re : ℂ) + ((z.im / s.im : ℝ) : ℂ) * ((s.im : ℂ) * Complex.I)
            = (z.re : ℂ) + (((z.im / s.im : ℝ) : ℂ) * (s.im : ℂ)) * Complex.I := by ring
        _ = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by rw [h_mul]
    _ = z := by simp

/-- The submodule `P_sc n s` has ℝ-dimension `n-1` when `s` is non-real and `n ≥ 1`. -/
lemma P_sc_dimension {n : ℕ} (hn : n ≥ 1) (s : ℂ) (hs : s.im ≠ 0) :
    dim (P_sc n s) = n - 1 := by
  unfold P_sc
  have h := LinearMap.finrank_range_add_finrank_ker (evalAtComplex (n := n) s)
  rw [finrank_CoeffVec] at h
  have hrank : dim (evalAtComplex (n := n) s).range = 2 := by
    have hsurj : Function.Surjective (evalAtComplex (n := n) s) :=
      evalAtComplex_surjective hn s hs
    rw [LinearMap.range_eq_top.mpr hsurj]
    simpa using Complex.finrank_real_complex
  have h' : dim (evalAtComplex (n := n) s).range +
      dim (evalAtComplex (n := n) s).ker = n + 1 := h
  omega

/-- If `U` has dimension `n` and `W` has dimension at least 2, then `U ⊓ W` has dimension at least 1. -/
lemma finrank_inf_ge_one {n : ℕ} (U W : Submodule ℝ (CoeffVec n))
    (hU : dim U = n)
    (hW : dim W ≥ 2) :
    dim (U ⊓ W) ≥ 1 := by
  have h_le_ambient : (U ⊔ W) ≤ ⊤ := by simp
  have h_sum_le : dim (U ⊔ W) ≤ n + 1 := by
    calc dim (U ⊔ W)
      ≤ dim (⊤ : Submodule ℝ (CoeffVec n)) := Submodule.finrank_mono h_le_ambient
      _ = n + 1 := by
        show Module.finrank ℝ (⊤ : Submodule ℝ (CoeffVec n)) = n + 1
        rw [finrank_top, finrank_CoeffVec]
  have hformula : dim (U ⊔ W) + dim (U ⊓ W) =
    dim U + dim W :=
    Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

/-- The direction of the intersection of `U` (as an affine subspace) with the affine span of `P_Ω` equals the intersection of the submodule `U` with the direction of `affineSpan ℝ P_Ω`. -/
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

/-- The direction of `U.toAffineSubspace ⊓ affΩ` equals `U ⊓ affΩ.direction` when `δ` lies in both. -/
lemma intersection_direction_eq {n : ℕ} (U : Submodule ℝ (CoeffVec n))
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

/-- If `U` has full dimension `n` and `affΩ` has direction dimension at least 2, then the affine span of their intersection has direction dimension at least 1. -/
lemma intersection_affine_dim_ge_one {n : ℕ} (U : Submodule ℝ (CoeffVec n))
    (affΩ : AffineSubspace ℝ (CoeffVec n))
    (δ : CoeffVec n) (hδU : δ ∈ U) (hδΩ : δ ∈ affΩ)
    (hU_dim : dim U = n) (haff_dim : dim affΩ.direction ≥ 2) :
    dim (meetDir n U affΩ) ≥ 1 := by
  unfold meetDir
  let Aint : AffineSubspace ℝ (CoeffVec n) := U.toAffineSubspace ⊓ affΩ
  have hA_dir : Aint.direction = U ⊓ affΩ.direction :=
    intersection_direction_eq U affΩ δ hδU hδΩ
  have hA_eq : affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n))) = Aint := by
    rw [affineSpan_inter U affΩ]
  rw [hA_eq, hA_dir]
  exact finrank_inf_ge_one U affΩ.direction hU_dim haff_dim

/-- If no point of the segment from `δ` to `δ + t_out • v` lies on the frontier of `P.Ω`, then the segment is covered by the interior of `P.Ω` and the interior of its complement. -/
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

/-- If `δ ∈ P.Ω` but not on its frontier, then the segment from `δ` to `δ + t_out • v` intersects the interior of `P.Ω`. -/
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

/-- If `δ + t_out • v ∉ P.Ω`, then the segment from `δ` to that point intersects the interior of the complement of `P.Ω`. -/
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

/-- The interior of a polytope and the interior of its complement are disjoint. -/
private lemma interior_and_complement_interior_disjoint (P : Polytope n) :
    interior P.Ω ∩ interior (P.Ωᶜ) = ∅ := by
  apply Set.eq_empty_of_subset_empty
  calc interior P.Ω ∩ interior (P.Ωᶜ) ⊆ P.Ω ∩ P.Ωᶜ :=
      Set.inter_subset_inter interior_subset interior_subset
    _ = ∅ := Set.inter_compl_self P.Ω

/-- Given a point `δ` in `P.Ω` not on its frontier and a direction `v ≠ 0` with `δ + t_out • v ∉ P.Ω`, the segment between them contains a point of the frontier of `P.Ω`. -/
lemma segment_boundary_intersection {n : ℕ} (P : Polytope n) (δ : CoeffVec n)
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

/-- If the affine span of `U ∩ affΩ` has positive dimension, then `U ⊓ affΩ.direction` is nontrivial. -/
private lemma intersection_nontrivial {n : ℕ} (U : Submodule ℝ (CoeffVec n))
    (affΩ : AffineSubspace ℝ (CoeffVec n)) (δ : CoeffVec n)
    (hδ_in_Psr : δ ∈ (U : Set (CoeffVec n))) (hδ_aff : δ ∈ affΩ)
    (h_dim_pos : 0 < dim (affineSpan ℝ
      ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction) :
    Nontrivial ↥(U ⊓ affΩ.direction) := by
  have hA_eq : affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n))) =
    U.toAffineSubspace ⊓ affΩ := by
    rw [affineSpan_inter]
  have hA_dir : (U.toAffineSubspace ⊓ affΩ).direction = U ⊓ affΩ.direction :=
    intersection_direction_eq U affΩ δ hδ_in_Psr hδ_aff
  let dir := (affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction
  have h_finrank : dim dir = dim (U ⊓ affΩ.direction) := by
    dsimp [dir]
    rw [hA_eq, hA_dir]
  have h_dim_pos' : 0 < dim dir :=
    h_dim_pos
  rw [h_finrank] at h_dim_pos'
  exact Module.nontrivial_of_finrank_pos h_dim_pos'

/-- If `v_sub` lies in `U ⊓ affΩ.direction`, then the entire line through `δ` in direction `v_sub` stays inside `U ∩ affΩ`. -/
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

/-- Rewrite a convex combination of `δ` and `δ + t_out • v` as `δ + (c * t_out) • v`. -/
private lemma segment_point_rewrite2 (δ v : CoeffVec n) (c t_out : ℝ) :
    (1 - c) • δ + c • (δ + t_out • v) = δ + (c * t_out) • v := by
  calc (1 - c) • δ + c • (δ + t_out • v)
    _ = (1 - c) • δ + (c • δ + c • (t_out • v)) := by rw [smul_add]
    _ = ((1 - c) • δ + c • δ) + c • (t_out • v) := by rw [←add_assoc]
    _ = ((1 - c) + c) • δ + c • (t_out • v) := by rw [←add_smul]
    _ = 1 • δ + (c * t_out) • v := by
      have h_one : (1 - c) + c = 1 := by ring
      simp only [h_one, smul_smul, one_smul]
    _ = δ + (c * t_out) • v := by rw [one_smul]

/-- Given a point `δ` in `P.Ω ∩ P_sr n r` and an affine subspace `affΩ` containing `δ` whose intersection with `P_sr` has direction dimension at least 1, there exists a boundary point of `P.Ω` also in `P_sr n r`. -/
lemma exists_boundary_point_in_Psr {n : ℕ} (P : Polytope n) (r : ℝ) (δ : CoeffVec n)
    (hδ_in_Ω : δ ∈ P.Ω) (hδ_in_Psr : δ ∈ PsrSet n r)
    (affΩ : AffineSubspace ℝ (CoeffVec n)) (hδ_aff : δ ∈ affΩ)
    (hA_dim : dim (meetDir n (P_sr n r) affΩ) ≥ 1) :
    ∃ δ_bound, δ_bound ∈ PsrSet n r ∩ frontier P.Ω := by
  have h_dim_pos : 0 < dim (meetDir n (P_sr n r) affΩ) := by
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
  have h_escapes : ∃ (t : ℝ), 0 < t ∧ δ + t • v ∉ P.Ω :=
    ray_escapes_polytope P δ v hδ_in_Ω hv_nonzero
  obtain ⟨t_out, ht_out_pos, ht_out⟩ := h_escapes
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

/-- Given a point `δ` in `P.Ω ∩ P_sc n s` and an affine subspace `affΩ` containing `δ` whose intersection with `P_sc` has direction dimension at least 1, there exists a boundary point of `P.Ω` also in `P_sc n s`. -/
lemma exists_boundary_point_in_Psc {n : ℕ} (P : Polytope n) (s : ℂ) (δ : CoeffVec n)
    (hδ_in_Ω : δ ∈ P.Ω) (hδ_in_Psc : δ ∈ PscSet n s)
    (affΩ : AffineSubspace ℝ (CoeffVec n)) (hδ_aff : δ ∈ affΩ)
    (hA_dim : dim (meetDir n (P_sc n s) affΩ) ≥ 1) :
    ∃ δ_bound, δ_bound ∈ PscSet n s ∩ frontier P.Ω := by
  have h_dim_pos : 0 < dim (meetDir n (P_sc n s) affΩ) := by
    omega
  let U : Submodule ℝ (CoeffVec n) := P_sc n s
  haveI : Nontrivial ↥(U ⊓ affΩ.direction) :=
    intersection_nontrivial U affΩ δ hδ_in_Psc hδ_aff h_dim_pos
  obtain ⟨v_sub, hv_sub_nonzero⟩ := exists_ne (0 : ↑(U ⊓ affΩ.direction))
  let v : CoeffVec n := v_sub.val
  have h_line_in_intersection : ∀ (t : ℝ), δ + t • v ∈ (P_sc n s : Set (CoeffVec n)) ∩
      (affΩ : Set (CoeffVec n)) :=
    line_in_intersection U affΩ δ hδ_in_Psc hδ_aff v_sub
  have hv_nonzero : v ≠ 0 := by
    intro h; apply hv_sub_nonzero; exact Submodule.coe_eq_zero.mp h
  have h_escapes : ∃ (t : ℝ), 0 < t ∧ δ + t • v ∉ P.Ω :=
    ray_escapes_polytope P δ v hδ_in_Ω hv_nonzero
  obtain ⟨t_out, ht_out_pos, ht_out⟩ := h_escapes
  by_cases hδ_front : δ ∈ frontier P.Ω
  · use δ
    exact ⟨hδ_in_Psc, hδ_front⟩
  · obtain ⟨δ_bound, h_seg, h_front⟩ :=
      segment_boundary_intersection P δ hδ_in_Ω hδ_front v hv_nonzero t_out ht_out
    rw [segment_eq_image] at h_seg
    obtain ⟨c, hc_in_Icc, hc_eq⟩ := h_seg
    have h_rewrite : (1 - c) • δ + c • (δ + t_out • v) = δ + (c * t_out) • v :=
      segment_point_rewrite δ v c t_out
    have h_mem := h_line_in_intersection (c * t_out)
    rcases h_mem with ⟨hmem_Psc, hmem_aff⟩
    have : δ_bound ∈ (P_sc n s : Set (CoeffVec n)) := by
      have h_eq : δ_bound = δ + (c * t_out) • v := by
        calc δ_bound = (1 - c) • δ + c • (δ + t_out • v) := by rw [←hc_eq]
          _ = δ + (c * t_out) • v := by rw [h_rewrite]
      rw [h_eq]
      exact hmem_Psc
    exact ⟨δ_bound, this, h_front⟩

/-- If `U` has dimension `n-1` and `W` has dimension at least 3, then `U ⊓ W` has dimension at least 1. -/
private lemma finrank_inf_ge_one' {n : ℕ} (U W : Submodule ℝ (CoeffVec n))
    (hU : dim U = n - 1) (hW : dim W ≥ 3) :
    dim (U ⊓ W) ≥ 1 := by
  have h_le_ambient : (U ⊔ W) ≤ ⊤ := by simp
  have h_sum_le : dim (U ⊔ W) ≤ n + 1 := by
    calc dim (U ⊔ W)
      ≤ dim (⊤ : Submodule ℝ (CoeffVec n)) := Submodule.finrank_mono h_le_ambient
      _ = n + 1 := by
        show Module.finrank ℝ (⊤ : Submodule ℝ (CoeffVec n)) = n + 1
        rw [finrank_top, finrank_CoeffVec]
  have hformula : dim (U ⊔ W) + dim (U ⊓ W) =
    dim U + dim W :=
    Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

/-- Variant of `intersection_affine_dim_ge_one` for the complex root subspace:
  `dim(U) = n-1` and `dim(affΩ.direction) ≥ 3` ensure intersection dimension ≥ 1. -/
lemma intersection_affine_dim_ge_one_complex {n : ℕ} (U : Submodule ℝ (CoeffVec n))
    (affΩ : AffineSubspace ℝ (CoeffVec n))
    (δ : CoeffVec n) (hδU : δ ∈ U) (hδΩ : δ ∈ affΩ)
    (hU_dim : dim U = n - 1) (haff_dim : dim affΩ.direction ≥ 3) :
    dim (affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction
      ≥ 1 := by
  let Aint : AffineSubspace ℝ (CoeffVec n) := U.toAffineSubspace ⊓ affΩ
  have hA_dir : Aint.direction = U ⊓ affΩ.direction :=
    intersection_direction_eq U affΩ δ hδU hδΩ
  have hA_eq : affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n))) = Aint := by
    rw [affineSpan_inter U affΩ]
  rw [hA_eq, hA_dir]
  exact finrank_inf_ge_one' U affΩ.direction hU_dim haff_dim

/-- The relative boundary of a set `F` (with respect to its affine hull).
For a convex set, this is `F \ intrinsicInterior ℝ F`.  This is the single
definition; `Lemma62.lean` and `EdgeDescent.lean` use it from here. -/
def relativeBoundary (F : Set (CoeffVec n)) : Set (CoeffVec n) :=
  F \ intrinsicInterior ℝ F

/-- If `F` is a compact convex set in `CoeffVec n` whose affine span has
dimension at least 2 and which contains a point `x`, then `F` has a point
on its relative boundary, i.e. `(relativeBoundary F).Nonempty`.

Proof: pick a nonzero direction `v` in the affine span of `F`, follow the
ray `x + t • v` until it exits the bounded set `F`, then take the *supremum*
of `t`-values that stay inside `F`.  The endpoint `x + t₁ • v` lies in `F`
but is not in the relative interior of `F`, so it belongs to
`relativeBoundary F`. -/
lemma nonempty_relativeBoundary_of_dim_ge_2 {n : ℕ} (F : Set (CoeffVec n))
    (hF_compact : IsCompact F) (hF_convex : Convex ℝ F)
    (x : CoeffVec n) (hx : x ∈ F)
    (hF_dim_ge_2 : dim (affineSpan ℝ F).direction ≥ 2) :
    (relativeBoundary F).Nonempty := by
  -- The affine span direction is nontrivial (dimension ≥ 2 ≥ 1)
  have h_dir_pos : 0 < dim (affineSpan ℝ F).direction := by
    have h1 : (0 : ℕ) < 1 := by decide
    have h12 : (1 : ℕ) ≤ dim (affineSpan ℝ F).direction :=
      le_trans (by decide) hF_dim_ge_2
    exact h1.trans_le h12
  haveI : Nontrivial ↥(affineSpan ℝ F).direction :=
    Module.nontrivial_of_finrank_pos h_dir_pos
  -- Pick a nonzero direction in the affine span
  obtain ⟨v_sub, hv_sub_ne⟩ := exists_ne (0 : ↥(affineSpan ℝ F).direction)
  let v : CoeffVec n := v_sub.val
  have hv_ne : v ≠ 0 := by
    intro h; apply hv_sub_ne; exact Submodule.coe_eq_zero.mp h
  have hv_affF_dir : v ∈ (affineSpan ℝ F).direction := v_sub.property
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  -- Construct an escape time `t_out` from the diameter bound of F.
  rcases Metric.isBounded_iff.mp hF_compact.isBounded with ⟨C, hC⟩
  let t_out : ℝ := (|C| + 1) / ‖v‖
  have ht_out_pos : 0 < t_out := div_pos (by positivity) hv_norm_pos
  -- Show that t_out is an escape time for the ray from x: if x + t_out • v ∈ F,
  -- then dist(x, x + t_out • v) ≤ C but also = t_out * ‖v‖ = |C| + 1 > C.
  have ht_out : x + t_out • v ∉ F := by
    intro h_in_F
    have h_dist : dist (x + t_out • v) x = t_out * ‖v‖ := by
      rw [dist_eq_norm]
      have h_sub : x + t_out • v - x = t_out • v := by abel
      have ht_nonneg : 0 ≤ t_out := ht_out_pos.le
      rw [h_sub, norm_smul, Real.norm_eq_abs t_out, abs_of_nonneg ht_nonneg]
    have h_le : dist (x + t_out • v) x ≤ C := hC h_in_F hx
    have h_C_lt : C < |C| + 1 := by
      have hC_abs : C ≤ |C| := le_abs_self C
      linarith
    have h_t_mul : t_out * ‖v‖ = |C| + 1 := by
      dsimp [t_out]
      field_simp [hv_norm_pos]
    rw [h_dist, h_t_mul] at h_le
    linarith
  -- Define the set of t ≥ 0 for which the ray stays in F
  let S : Set ℝ := {t | 0 ≤ t ∧ x + t • v ∈ F}
  have hS_nonempty : S.Nonempty := ⟨0, by simp [S, hx]⟩
  have hS_closed : IsClosed S := by
    have h_cont : Continuous (fun (t : ℝ) => x + t • v) := by continuity
    have h_preimage_closed : IsClosed {t | x + t • v ∈ F} :=
      hF_compact.isClosed.preimage h_cont
    have h_nonneg_closed : IsClosed {t : ℝ | 0 ≤ t} := isClosed_Ici
    have hS_eq : S = {t | x + t • v ∈ F} ∩ {t : ℝ | 0 ≤ t} := by
      ext t; constructor
      · rintro ⟨ht_nonneg, ht_mem⟩; exact ⟨ht_mem, ht_nonneg⟩
      · rintro ⟨ht_mem, ht_nonneg⟩; exact ⟨ht_nonneg, ht_mem⟩
    rw [hS_eq]
    exact h_preimage_closed.inter h_nonneg_closed
  -- S is bounded above by t_out
  have h_bdd_above : BddAbove S := by
    refine ⟨t_out, ?_⟩
    rintro t ⟨ht_nonneg, ht_mem⟩
    by_contra! h_gt
    have ha_nonneg : 0 ≤ t_out / t := div_nonneg (by linarith) (by linarith)
    have hdiv : t_out / t ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have hb_nonneg : 0 ≤ 1 - t_out / t := by linarith
    have hsum : (t_out / t : ℝ) + (1 - t_out / t) = 1 := by ring
    have hstar : StarConvex ℝ (x + t • v) F := hF_convex ht_mem
    have h_conv : ((t_out / t : ℝ) • (x + t • v) + (1 - t_out / t) • x) = x + t_out • v := by
      calc
        ((t_out / t : ℝ) • (x + t • v) + (1 - t_out / t) • x)
            = (t_out / t) • x + (t_out / t) • (t • v) + (1 - t_out / t) • x := by rw [smul_add]
        _ = ((t_out / t) • x + (1 - t_out / t) • x) + (t_out / t) • (t • v) := by abel
        _ = ((t_out / t + (1 - t_out / t)) • x) + ((t_out / t) * t) • v := by
          simp [smul_smul]
        _ = (1 • x) + (t_out • v) := by
          have h_t_ne_zero : t ≠ 0 := by linarith
          have h_sum : t_out / t + (1 - t_out / t) = 1 := by ring
          have h_mul : (t_out / t) * t = t_out := by field_simp [h_t_ne_zero]
          simp [h_sum, h_mul]
        _ = x + t_out • v := by simp
    have h_mem_conv : (t_out / t : ℝ) • (x + t • v) + (1 - t_out / t) • x ∈ F :=
      hstar hx ha_nonneg hb_nonneg hsum
    have h_mem : x + t_out • v ∈ F := by
      rw [← h_conv]
      exact h_mem_conv
    exact ht_out h_mem
  -- Take the supremum
  let t1 := sSup S
  have h_max : t1 ∈ S := hS_closed.csSup_mem hS_nonempty h_bdd_above
  rcases h_max with ⟨h_t1_nonneg, h_t1_mem⟩
  let δ_bound : CoeffVec n := x + t1 • v
  have hδ_bound_in_F : δ_bound ∈ F := h_t1_mem
  -- δ_bound is not in the relative interior
  have h_not_relint : δ_bound ∉ intrinsicInterior ℝ F :=
    not_mem_intrinsicInterior_of_escapes_along_direction
      F hF_convex x hx v hv_ne hv_affF_dir
      S rfl hS_nonempty h_bdd_above
      t1 rfl h_t1_nonneg h_t1_mem
      t_out ht_out_pos ht_out
  -- Therefore δ_bound ∈ relativeBoundary F
  exact ⟨δ_bound, ⟨hδ_bound_in_F, h_not_relint⟩⟩

end CoeffBox
