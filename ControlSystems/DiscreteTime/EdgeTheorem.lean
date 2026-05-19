module


public import ControlSystems.Init
public import Mathlib

@[expose] public section


-- public import Mathlib.Algebra.Polynomial.Degree.Defs

open Polynomial
/--
A box `B_n` in the space of coefficients for polynomials of degree `n`.
It is defined by lower bounds `l` and upper bounds `u` for each coefficient index `j ∈ {0, ..., n}`.
-/
structure CoeffBox (n : ℕ) where
  l : Fin (n + 1) → ℝ  -- Lower bounds l_j
  u : Fin (n + 1) → ℝ  -- Upper bounds u_j
  interval : ∀ j : Fin (n + 1), l j ≤ u j





namespace CoeffBox

/--
Predicate stating that the polynomial `f` has natural degree `n`
and its coefficients lie within the box `B`.
Note: We explicitly require `f.natDegree = n` to ensure the leading coefficient
is non-zero and corresponds to index `n`.
-/
def InBox (B : CoeffBox n) (f : Polynomial ℝ) : Prop :=
  f.natDegree = n ∧  ∀ j : Fin (n + 1), B.l j ≤ coeff f j.val ∧ coeff f j.val ≤ B.u j

def FOIP (B : CoeffBox n) : Set (Polynomial ℝ) :=
  { f | InBox B f }
/--
The set of extreme coefficient vectors `E_k` for a fixed index `k`.
A coefficient vector `α` (represented here as a function `Fin (n+1) → ℝ`)
is in `E_k B` if:
1. The k-th coefficient `α k` is within its interval `[l k, u k]`.
2. For all other indices `j ≠ k`, the coefficient `α j` is exactly either `l j` or `u j`.
-/
def ExtremeCoeffs (B : CoeffBox n) (k : Fin (n + 1)) : Set (Fin (n + 1) → ℝ) :=
  { α |
    (B.l k ≤ α k ∧ α k ≤ B.u k) ∧
    ∀ j : Fin (n + 1), j ≠ k → (α j = B.l j ∨ α j = B.u j)
  }

/--
The collection of all extreme coefficient vectors `E`.
This is the union of `ExtremeCoeffs B k` for all `k` from `0` to `n`.
Geometrically, this represents the "edges" of the hyperrectangle `B_n`
parallel to the axes.
-/
def ExtremeSet (B : CoeffBox n) : Set (Fin (n + 1) → ℝ) :=
  ⋃ k : Fin (n + 1), ExtremeCoeffs B k

/--
The Family of Extreme Polynomials.
This maps the extreme coefficient vectors back to polynomials.
Note: Not every vector in `ExtremeSet` necessarily forms a polynomial of degree `n`
(i.e., the leading coefficient might be 0 if `l n = 0` and `α n` is chosen as `l n`).
We filter for `natDegree = n` to match the definition of `FOIP`.
-/
def ExtremePolys (B : CoeffBox n) : Set (Polynomial ℝ) :=
  { f | ∃ α ∈ ExtremeSet B,
      (∀ j : Fin (n + 1), coeff f j.val = α j) ∧
      f.natDegree = n
  }

def Schur_Stable (f : Polynomial ℝ) : Prop :=
  ∀ a : ℝ , f.IsRoot a → abs a < 1

theorem Product_of_Schur_Stable (f : Polynomial ℝ) (g : Polynomial ℝ) :
  (Schur_Stable f) → (Schur_Stable g) → (Schur_Stable (f * g)) := by
  intros hf hg
  unfold Schur_Stable
  intro a hfg
  have heval : f.eval a * g.eval a = 0 := by
    rw [← eval_mul]
    exact hfg
  rcases mul_eq_zero.mp heval with hfa | hga
  -- Case 1: a is a root of f → apply Schur stability of f
  · exact hf a hfa
  -- Case 2: a is a root of g → apply Schur stability of g
  · exact hg a hga


abbrev CoeffVec (n : ℕ) := Fin (n + 1) → ℝ

/--
A polytope Ω in coefficient space ℝ^{n+1}.
It is defined as the convex hull of a finite set of vertices V.
This matches the PDF: "the convex hull of a finite number of points".
-/
structure Polytope (n : ℕ) where
  vertices : Finset (CoeffVec n)     -- finite set of vertex polynomials
  nonempty  : vertices.Nonempty       -- at least one vertex

/-- The actual set Ω ⊆ ℝ^{n+1} as a convex hull -/
def Polytope.Ω (P : Polytope n) : Set (CoeffVec n) :=
  convexHull ℝ (P.vertices : Set (CoeffVec n))

open Polynomial

/-- Convert a coefficient vector α : Fin(n+1) → ℝ to a polynomial
    δ(s) = α(0) + α(1)·s + ... + α(n)·sⁿ
-/
noncomputable def polyOfVec {n : ℕ} (α : CoeffVec n) : Polynomial ℝ :=
  ∑ j : Fin (n + 1), Polynomial.monomial j.val (α j)


def RootSpaceSet {n : ℕ}
  (W : Set (CoeffVec n)) : Set ℂ :=
  { s | ∃ δ ∈ W,
      ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s }

def RootSpace (P : Polytope n) : Set ℂ :=
  RootSpaceSet P.Ω

/--
def HyperPlaneAffineSet (f : Polynomial ℝ) (c : ℝ) : Set ℝ :=
  { x | f.eval x = c }


structure SupportingHyperplane (f : Polynomial ℝ) (c : ℕ ) (P : Polytope n) where
   H : HyperPlaneAffineSet f c
   inclusion : ∀ x ∈ P.Ω , f.eval x ≤ c
   intersection : Ω_1 ∩ H ≠ ∅
-/
def Hyperplane {n : ℕ}
    (f : CoeffVec n →ₗ[ℝ] ℝ)
    (c : ℝ) : Set (CoeffVec n) :=
  { x | f x = c }

structure SupportingHyperplane (P : Polytope n) where
  f : CoeffVec n →ₗ[ℝ] ℝ
  c : ℝ
  nonzero : f ≠ 0
  upper_bound : ∀ x ∈ P.Ω, f x ≤ c
  touches : ∃ x ∈ P.Ω, f x = c
  H : Set (CoeffVec n) := Hyperplane f c

def ExposedFace_ (P : Polytope n) (hp : SupportingHyperplane P) :=
  P.Ω ∩ hp.H

def ExposedFace {n : ℕ} {P : Polytope n} (hp : SupportingHyperplane P) :
    Set (CoeffVec n) :=
  { x | x ∈ P.Ω ∧ hp.f x = hp.c }
  -- equivalently: P.Ω ∩ hp.H

open Affine

/-- `E` is an exposed edge of `P` if it is an exposed face of affine dimension 1. -/
def IsExposedEdge {n : ℕ} (P : Polytope n) (E : Set (CoeffVec n)) : Prop :=
  ∃ hp : SupportingHyperplane P,
    E = ExposedFace hp ∧
    Module.finrank ℝ (affineSpan ℝ (ExposedFace hp)).direction = 1
open FiniteDimensional

def ExposedEdge {n : ℕ} {P : Polytope n} (hp : SupportingHyperplane P) : Prop :=
  Module.finrank ℝ (affineSpan ℝ (ExposedFace hp)).direction = 1

noncomputable def evalLinear {n : ℕ} (r : ℝ) :
  CoeffVec n →ₗ[ℝ] ℝ :=
{
  toFun := fun δ => Polynomial.eval r (polyOfVec δ),
  map_add' := by
    intros δ₁ δ₂
    simp [polyOfVec, Polynomial.eval_add, Finset.sum_add_distrib],
  map_smul' := by
    intros a δ
    unfold polyOfVec
    simp only [Pi.smul_apply, smul_eq_mul, Real.ringHom_apply]
    rw [Polynomial.eval_finset_sum]
    rw [Polynomial.eval_finset_sum]
    rw [Finset.mul_sum]
    congr 1
    ext j
    rw [Polynomial.eval_monomial]
    rw [Polynomial.eval_monomial]
    ring
}


def P_sr' {n : ℕ} (r : ℝ) : Set (CoeffVec n) :=
  { δ | evalLinear r δ = 0 }

noncomputable def P_sr (n : ℕ) (r : ℝ) : Submodule ℝ (CoeffVec n) :=
  (evalLinear r).ker

lemma finrank_CoeffVec {n : ℕ} :
  Module.finrank ℝ (CoeffVec n) = n + 1 := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp


lemma evalLinear_surjective {n : ℕ} (r : ℝ) :
    Function.Surjective (evalLinear (n := n) r) := by
  intro y
  -- The constant polynomial with value y works: δ j = y if j = 0, else 0
  use fun j => if j.val = 0 then y else 0
  simp [evalLinear, polyOfVec]
  simp [Polynomial.eval_finset_sum, Polynomial.eval_monomial]


lemma P_sr_dimension {n : ℕ} (r : ℝ) :
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

/-- E is an exposed face of P if it is an exposed face of affine dimension 2 -/
def IsExposedFace {n : ℕ} (P : Polytope n) (F : Set (CoeffVec n)) : Prop :=
  ∃ hp : SupportingHyperplane P, F = ExposedFace hp


-- ---------------------------------------------------------
-- HELPER LEMMAS
-- ---------------------------------------------------------

lemma Polytope.isCompact {n : ℕ} (P : Polytope n) : IsCompact P.Ω := by
  have h_fin : (P.vertices : Set (CoeffVec n)).Finite := Finset.finite_toSet P.vertices
  exact Set.Finite.isCompact_convexHull h_fin

lemma Polytope.isBounded {n : ℕ} (P : Polytope n) : Bornology.IsBounded P.Ω :=
  P.isCompact.isBounded

lemma ray_escapes_polytope {n : ℕ} (P : Polytope n) (δ v : CoeffVec n)
    (hp_in_Ω : δ ∈ P.Ω) (hv_nonzero : v ≠ 0) : ∃ t : ℝ, δ + t • v ∉ P.Ω := by
  by_contra h_contra
  push_neg at h_contra
  rcases Metric.isBounded_iff.mp P.isBounded with ⟨C, hC⟩
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_nonzero
  let t := (|C| + 1) / ‖v‖
  have ht_pos : 0 < t := div_pos (by have : 0 ≤ |C| := abs_nonneg C; linarith) hv_norm_pos
  have h_in := h_contra t
  have h_dist : dist (δ + t • v) δ = t * ‖v‖ := by
    rw [dist_eq_norm]
    have h_sub : δ + t • v - δ = t • v := by abel
    have ht_nonneg : 0 ≤ t := ht_pos.le
    rw [h_sub, norm_smul, Real.norm_eq_abs t, abs_of_nonneg ht_nonneg]
  have h_le : dist (δ + t • v) δ ≤ C := by apply hC; exact h_in; exact hp_in_Ω
  have h_C_lt : C < |C| + 1 := by have : C ≤ |C| := le_abs_self C; linarith
  rw [h_dist] at h_le
  have h_t_mul : t * ‖v‖ = |C| + 1 := div_mul_cancel₀ (|C| + 1) (ne_of_gt hv_norm_pos)
  rw [h_t_mul] at h_le
  linarith

lemma finrank_inf_ge_one {n : ℕ} (U W : Submodule ℝ (CoeffVec n))
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
lemma direction_inf {n : ℕ} (U : Submodule ℝ (CoeffVec n)) (P_Ω : Set (CoeffVec n))
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

lemma affineSpan_inter {n : ℕ} (U : Submodule ℝ (CoeffVec n)) (affΩ : AffineSubspace ℝ (CoeffVec n)) :
    affineSpan ℝ (↑U ∩ ↑affΩ) = U.toAffineSubspace ⊓ affΩ := by
  ext x
  simp only [AffineSubspace.mem_inf_iff]
  constructor
  · intro hx
    constructor
    · exact affineSpan_le.mpr (Set.inter_subset_left) hx
    · apply affineSpan_le.mpr (Set.inter_subset_left); rw [Set.inter_comm]; exact hx
  · intro ⟨h1, h2⟩
    apply subset_affineSpan; simp only [Set.mem_inter_iff, SetLike.mem_coe]; exact ⟨h1, h2⟩

-- ---------------------------------------------------------
-- PRIVATE LEMMAS FOR LEMMA 6.1 (Step 4-5)
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

  -- f is nonzero
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
    -- δ_bound ∈ P_sr n r means evalLinear r δ_bound = 0
    have heval : evalLinear r δ_bound = 0 := hδ_bound_Psr
    unfold Polynomial.IsRoot
    rw [Polynomial.eval_map]
    rw [Polynomial.eval₂_eq_eval_map]
    have h_comm : eval (↑r) (map (algebraMap ℝ ℂ) (polyOfVec δ_bound))
        = (algebraMap ℝ ℂ) (eval r (polyOfVec δ_bound)) := by
      simp [polyOfVec, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
            map_sum, map_mul, map_pow]
    rw [h_comm]
    -- evalLinear r δ_bound = eval r (polyOfVec δ_bound) = 0
    have h_eval_eq : eval r (polyOfVec δ_bound) = evalLinear r δ_bound := rfl
    rw [h_eval_eq, heval]
    simp

  -- -------------------------------------------------------
  -- Conclusion: assemble the witnesses
  -- -------------------------------------------------------
  exact ⟨ExposedFace hp, ⟨hp, rfl⟩, hδ_in_face, hr_in_rootspace⟩
#check Module.finrank_pos
#check Module.nontrivial_of_finrank_pos
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

  -- Measure the dimension of F
  let m_F := Module.finrank ℝ (affineSpan ℝ F).direction

  -- Case split: is F already 1-dimensional?
  by_cases h_dim_1 : m_F = 1
  · -- Step 9: Base case - F is already an exposed edge
    use F
    constructor
    · obtain ⟨hp, hF_eq⟩ := hF_exposed
      exact ⟨hp, hF_eq, hF_eq ▸ h_dim_1⟩
    · exact hr_in_RF
  · -- Inductive case: dim(F) ≥ 2
    have h_dim_ge_2 : m_F ≥ 2 := by
      contrapose! h_dim_1
      have h_le_1 : m_F ≤ 1 := by omega
      have h_nontrivial_dir : Nontrivial ↥(affineSpan ℝ F).direction := by
        obtain ⟨x, hx, y, hy, hxy⟩ := hF_nontrivial
        have hx_span : x ∈ affineSpan ℝ F := subset_affineSpan ℝ F hx
        have hy_span : y ∈ affineSpan ℝ F := subset_affineSpan ℝ F hy
        have h_diff : x - y ∈ (affineSpan ℝ F).direction := by
          apply AffineSubspace.vsub_mem_direction
          · exact hx_span
          · exact hy_span
        have h_diff_ne : x - y ≠ 0 := by
          intro h_eq
          apply hxy
          exact sub_eq_zero.mp h_eq
        use 0, ⟨x - y, h_diff⟩
        exact Subtype.coe_ne_coe.mp (id (Ne.symm h_diff_ne))
      have h_pos : 1 ≤ m_F := Module.finrank_pos (R := ℝ) (M := ↥(affineSpan ℝ F).direction)
      grind

    obtain ⟨δ_F, hδ_F_in_F, hδ_F_root⟩ := hr_in_RF

    -- δ_F lies in P_sr n r
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

    -- δ_F is in the intersection F ∩ P_sr n r
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
      -- Boundedness of F
      have hF_bounded : Bornology.IsBounded F :=
        hF_compact.isBounded
      -- Therefore the intersection F ∩ ℓ is a bounded subset of the line ℓ

    -- Now outside h_inter_nontrivial, back at the `Inductive case` level
    have h_exists_boundary :
        ∃ δ_bound,
          δ_bound ∈ F ∩ (P_sr n r : Set (CoeffVec n)) ∧
          δ_bound ∈ frontier F := by
      by_cases hδ_front : δ_F ∈ frontier F
      · -- δ_F is already on the frontier
        refine ⟨δ_F, hδ_F_inter, hδ_front⟩
      · -- δ_F is in the interior of F
        have hδ_int : δ_F ∈ interior F := by
          unfold frontier at hδ_front
          rw [hF_compact.isClosed.closure_eq] at hδ_front
          apply not_not.mp
          simp
          by_contra h
          exact hδ_front ⟨hδ_F_in_F, h⟩
        -- The intersection L has dimension ≥ 1, so its direction is nontrivial
        let L :=
          affineSpan ℝ (↑(P_sr n r) ∩ (affF : Set (CoeffVec n)))

        have hL_pos :
            0 < Module.finrank ℝ ↥L.direction := by
          have : Module.finrank ℝ ↥L.direction ≥ 1 := by
            simpa [L] using h_inter_dim
          omega

        have h_dir_nontrivial : Nontrivial ↥L.direction :=
          Module.nontrivial_of_finrank_pos hL_pos
        -- Pick a nonzero vector v in the direction of L
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

        -- Since the line escapes F, it also escapes P.Ω
        have ht_out_P : δ_F + t_out • v ∉ P.Ω := sorry

        -- Generalize the properties from F to P.Ω
        have hF_subset : F ⊆ P.Ω := by
          obtain ⟨hp, rfl⟩ := hF_exposed
          exact Set.inter_subset_left

        have hδ_F_in_Ω : δ_F ∈ P.Ω := hF_subset hδ_F_in_F
        have ht_out_Ω : δ_F + t_out • v ∉ P.Ω := sorry

        -- Because F is closed and F ⊆ P.Ω, their frontiers coincide on F
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



        -- Apply `segment_boundary_intersection` to the ambient polytope P
        obtain ⟨δ_bound, h_seg, h_front_P⟩ :=
          segment_boundary_intersection P δ_F hδ_F_in_Ω hδ_front_Ω v hv_ne t_out ht_out_Ω

        sorry






















theorem lemma61
  (P : Polytope n)
  (s : ℂ)
  (hs : s ∈ RootSpace P) :
  (s.im = 0 → ∃ E, IsExposedEdge P E ∧ s ∈ RootSpaceSet E) ∧
  (s.im ≠ 0 → ∃ F, IsExposedFace P F ∧
    s ∈ RootSpaceSet F) := by
  constructor
  · intro hreal
    -- Step 1: extract δ ∈ Ω with δ(s_r) = 0
    unfold RootSpace RootSpaceSet at hs
    obtain ⟨δ, hδ_in_Ω, hδ_root⟩ := hs

    -- Step 2: show δ ∈ P_sr' s.re
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
          -- hδ_root : eval₂ (algebraMap ℝ ℂ) ↑s.re (polyOfVec δ) = 0
          have key : (algebraMap ℝ ℂ) (eval s.re (polyOfVec δ)) = 0 := by
            rw [Polynomial.eval₂_eq_eval_map] at hδ_root
            have h_comm : (algebraMap ℝ ℂ) (eval s.re (polyOfVec δ))
            = eval (↑s.re) (map (algebraMap ℝ ℂ) (polyOfVec δ)) := by
              simp [polyOfVec, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
                    map_sum, map_mul, map_pow]
            rw [h_comm, hδ_root]
          exact_mod_cast (map_eq_zero (algebraMap ℝ ℂ)).mp key
    -- Step 3: δ lies in both P_sr and aff(Ω)
    have hδ_aff : δ ∈ affineSpan ℝ (P.Ω) := subset_affineSpan ℝ P.Ω hδ_in_Ω

    let m := Module.finrank ℝ (affineSpan ℝ (P.Ω)).direction


    by_cases hm : m ≥ 2
    · -- Step 4: intersection has dimension ≥ 1
      let U : Submodule ℝ (CoeffVec n) := P_sr n s.re
      let affΩ : AffineSubspace ℝ (CoeffVec n) := affineSpan ℝ (P.Ω)
      have hdim_Psr : Module.finrank ℝ U = n := P_sr_dimension s.re
      have hδ_aff : δ ∈ affΩ := subset_affineSpan ℝ P.Ω hδ_in_Ω
      have hA_dim : Module.finrank ℝ ↥(affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction ≥ 1 :=
        intersection_affine_dim_ge_one U affΩ δ hδ_in_Psr hδ_aff hdim_Psr hm
      -- Step 5: existence of boundary point in P_sr
      have h_boundary_root : ∃ δ_bound, δ_bound ∈ (P_sr n s.re : Set (CoeffVec n)) ∩ frontier P.Ω :=
        exists_boundary_point_in_Psr P s.re δ hδ_in_Ω hδ_in_Psr affΩ hδ_aff hA_dim
      -- Steps 6-9: descend through exposed faces to an exposed edge
      obtain ⟨δ_bound, hδ_bound⟩ := h_boundary_root
      have hδ_bound_front : δ_bound ∈ frontier P.Ω := hδ_bound.2
      have hδ_bound_Psr : δ_bound ∈ (P_sr n s.re : Set (CoeffVec n)) := hδ_bound.1

      -- The polytope P.Ω has nonempty interior when m ≥ 2 because it has dimension ≥ 2.
      -- (If the ambient dimension n+1 > m, this uses the relative interior; for now we assume
      --  the polytope is full-dimensional or that a suitable relative-interior lemma exists.)
      have h_int_nonempty : (interior P.Ω).Nonempty := by
        sorry

      -- Step 6: There exists an exposed face F of P containing δ_bound with s ∈ RootSpaceSet F
      obtain ⟨F, hF_exposed, hδ_in_F, hs_in_RF⟩ :=
        exists_exposed_face_containing_boundary_point P s.re δ_bound hδ_bound_front hδ_bound_Psr h_int_nonempty

      -- Step 7-8: Iteratively descend through exposed faces of decreasing dimension
      -- until we reach one of dimension 1 (an exposed edge).
      have h_edge : ∃ (E : Set (CoeffVec n)), IsExposedEdge P E ∧ s ∈ RootSpaceSet E := by
        sorry

      exact h_edge
    · -- Step 10: trivial cases m = 0 or m = 1
      have hm01 : m = 0 ∨ m = 1 := by grind
      by_cases hm0 : m = 0
      · -- m = 0: Ω is a single point. This degenerate case needs to produce an exposed edge
        -- with s ∈ RootSpaceSet E. Since P has at least one vertex (by Polytope.nonempty),
        -- an exposed edge can be constructed, but the root condition must also hold.
        sorry
      · -- m = 1: Ω is 1-dimensional, so it is itself an exposed edge
        have hm1 : m = 1 := by
          have h_not_0 : m ≠ 0 := hm0
          rcases hm01 with (h0 | h1)
          · exact (h_not_0 h0).elim
          · exact h1
        -- Show P.Ω is an exposed edge: its affine hull has dimension 1, so P.Ω is a segment,
        -- and there exists a supporting hyperplane that exposes the whole polytope.
        have h_Ω_is_edge : IsExposedEdge P P.Ω := by
          sorry
        refine ⟨P.Ω, h_Ω_is_edge, ?_⟩
        -- Show s ∈ RootSpaceSet P.Ω using the δ extracted at step 1
        have : ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s := hδ_root
        exact Set.mem_setOf.mpr ⟨δ, hδ_in_Ω, this⟩


  · intro hcomplex
    sorry


/-
lemma lemma61a
  [Fintype ℕ]
  (P : Polytope n)
  {s : ℂ}
  (hs : s ∈ RootSpace P) :
  ∃ hp : SupportingHyperplane P,
    s ∈ RootSpaceSet (ExposedFace hp) := by
  by_cases hreal : s.im = 0
  · -- Case 1: s is real, i.e. s = ↑s.re
    have hs_real : s = ↑s.re := by
      apply Complex.ext
      · simp
      · simp [hreal]
    unfold RootSpace RootSpaceSet at hs
    obtain ⟨δ, hδ_in_Ω, hδ_root⟩ := hs
    -- δ is in P_{s_r}: evalLinear s.re δ = 0
    have hδ_in_Psr : δ ∈ P_sr' s.re := by
          unfold P_sr' evalLinear
          simp only [LinearMap.coe_mk, AddHom.coe_mk, Set.mem_setOf_eq]
          rw [hs_real] at hδ_root
          unfold Polynomial.IsRoot at hδ_root
          rw [Polynomial.eval_map] at hδ_root
          -- hδ_root : eval₂ (algebraMap ℝ ℂ) ↑s.re (polyOfVec δ) = 0
          have key : (algebraMap ℝ ℂ) (eval s.re (polyOfVec δ)) = 0 := by
            rw [Polynomial.eval₂_eq_eval_map] at hδ_root
            have h_comm : (algebraMap ℝ ℂ) (eval s.re (polyOfVec δ))
            = eval (↑s.re) (map (algebraMap ℝ ℂ) (polyOfVec δ)) := by
              simp [polyOfVec, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
                    map_sum, map_mul, map_pow]
            rw [h_comm, hδ_root]
          exact_mod_cast (map_eq_zero (algebraMap ℝ ℂ)).mp key



    sorry
  ·

    sorry
-/
end CoeffBox
