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
    ∃ p q : CoeffVec n, p ≠ q ∧ E = segment ℝ p q
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
    -- Step 3: P_sr' s.re ∩ aff(Ω) is nonempty (because δ is in both)
    have hinter_nonempty : δ ∈ P_sr' s.re ∩ (affineSpan ℝ (P.Ω) : Set (CoeffVec n)) := by
      constructor
      · exact hδ_in_Psr
      · exact subset_affineSpan ℝ _ hδ_in_Ω
    have hδ_in_Psr_submodule : δ ∈ (P_sr n s.re : Set (CoeffVec n)) := by
      exact hδ_in_Psr

    let m := Module.finrank ℝ (affineSpan ℝ (P.Ω)).direction

    by_cases hm : m ≥ 2
    ·
      have hdim_Psr : Module.finrank ℝ (P_sr n s.re) = n := P_sr_dimension s.re

      -- The ambient space has dimension n+1
      have hdim_ambient : Module.finrank ℝ (CoeffVec n) = n + 1 := finrank_CoeffVec
      have hA_nonempty : ((P_sr n s.re : Set (CoeffVec n)) ∩ (affineSpan ℝ (P.Ω)
      : Set (CoeffVec n))).Nonempty := by
        use δ
        constructor
        · exact hδ_in_Psr_submodule
        · exact subset_affineSpan ℝ (P.Ω) hδ_in_Ω
      let A_set := (P_sr n s.re : Set (CoeffVec n)) ∩ (affineSpan ℝ (P.Ω) : Set (CoeffVec n))
      let A := affineSpan ℝ A_set
      let U : Submodule ℝ (CoeffVec n) := P_sr n s.re
      let affΩ : AffineSubspace ℝ (CoeffVec n) := affineSpan ℝ (P.Ω)
      let Aint : AffineSubspace ℝ (CoeffVec n) := U.toAffineSubspace ⊓ affΩ

      have hA_dir : Aint.direction = U ⊓ affΩ.direction := by
        simp only [Aint, U, affΩ]
        ext v
        simp only [Submodule.mem_inf]
        constructor
        · intro hv
          -- v ∈ (U.toAffineSubspace ⊓ affΩ).direction
          -- means ∃ p ∈ (U.toAffineSubspace ⊓ affΩ), p + v ∈ (U.toAffineSubspace ⊓ affΩ)
          rw [AffineSubspace.mem_direction_iff_eq_vsub
              ⟨δ, by simp only [SetLike.mem_coe, AffineSubspace.mem_inf_iff,
                Submodule.mem_toAffineSubspace]; exact ⟨hδ_in_Psr_submodule,
                subset_affineSpan ℝ _ hδ_in_Ω⟩⟩] at hv
          obtain ⟨p₁, hp₁, p₂, hp₂, hv_eq⟩ := hv
          rw [AffineSubspace.mem_inf_iff] at hp₁ hp₂
          constructor
          · -- v ∈ U
            have hp₁U := hp₁.1
            have hp₂U := hp₂.1
            rw [hv_eq]
            simp only [vsub_eq_sub]
            exact (Submodule.sub_mem_iff_left (P_sr n s.re) hp₂U).mpr hp₁U
          · -- v ∈ affΩ.direction
            have hp₁Ω := hp₁.2
            have hp₂Ω := hp₂.2
            rw [hv_eq]
            exact AffineSubspace.vsub_mem_direction hp₁Ω hp₂Ω
        · intro hv
          obtain ⟨hvU, hvΩ⟩ := hv
          have hbase : δ ∈ (P_sr n s.re).toAffineSubspace ⊓ affineSpan ℝ P.Ω := by
            rw [AffineSubspace.mem_inf_iff]
            exact ⟨hδ_in_Psr_submodule, subset_affineSpan ℝ _ hδ_in_Ω⟩
          have hne : ((P_sr n s.re).toAffineSubspace ⊓ affineSpan ℝ P.Ω :
           Set (CoeffVec n)).Nonempty :=
            ⟨δ, hbase⟩
          rw [AffineSubspace.mem_direction_iff_eq_vsub hne]
          refine ⟨v +ᵥ δ, ?_, δ, hbase, ?_⟩
          · -- show v +ᵥ δ ∈ (P_sr n s.re).toAffineSubspace ⊓ affineSpan ℝ P.Ω
            rw [AffineSubspace.mem_inf_iff]
            constructor
            · simp only [Submodule.mem_toAffineSubspace]
              exact Submodule.add_mem _ hvU hδ_in_Psr_submodule
            · exact AffineSubspace.vadd_mem_of_mem_direction hvΩ
                    (subset_affineSpan ℝ _ hδ_in_Ω)
          · simp only [vadd_eq_add, vsub_eq_sub, add_sub_cancel_right]



      have hA_dim : Module.finrank ℝ A.direction ≥ 1 := by

        have h_sum_le : Module.finrank ℝ (U + affΩ.direction) ≤ n + 1 := by
          have h_le_ambient : (U + affΩ.direction) ≤ ⊤ := by simp
          calc Module.finrank ℝ (U + affΩ.direction)
            ≤ Module.finrank ℝ (⊤ : Submodule ℝ (CoeffVec n)) := by
                apply Submodule.finrank_mono h_le_ambient
          _ = n + 1 := by
                rw [finrank_top]
                exact hdim_ambient
        have hformula : Module.finrank ℝ ↥(U ⊔ affΩ.direction) +
            Module.finrank ℝ ↥(U ⊓ affΩ.direction) =
            Module.finrank ℝ U + Module.finrank ℝ affΩ.direction :=
          Submodule.finrank_sup_add_finrank_inf_eq U affΩ.direction

        have hsup_eq_add : U ⊔ affΩ.direction = U + affΩ.direction := rfl


        rw [hsup_eq_add] at hformula

        -- Now hformula says: finrank(U + W) + finrank(U ⊓ W) = finrank(U) + finrank(W)
        -- We want: finrank(U ⊓ W) ≥ 1

        have hW_dim : Module.finrank ℝ affΩ.direction = m := rfl
        have hU_dim : Module.finrank ℝ U = n := hdim_Psr

        rw [hW_dim, hU_dim] at hformula
        -- hformula: finrank(U + W) + finrank(U ⊓ W) = n + m


        have h_inf_ge_1 : Module.finrank ℝ ↥(U ⊓ affΩ.direction) ≥ 1 := by
          omega

        -- Now connect A.direction to U ⊓ affΩ.direction
        have hA_eq : A.direction = U ⊓ affΩ.direction := by
          have hA_unfold : A = affineSpan ℝ A_set := rfl

          -- Step 2: Unfold A_set
          have hA_set_unfold : A_set = (U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)) := rfl

          -- Step 3: Substitute A_set
          rw [hA_unfold, hA_set_unfold]

                    -- Step 4: Show this equals Aint
          have hA_eq_Aint : affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ
          : Set (CoeffVec n))) = Aint := by
            simp only [Aint]
            ext x
            simp only [AffineSubspace.mem_inf_iff]
            constructor
            · intro hx
              constructor
              ·
                exact affineSpan_le.mpr (Set.inter_subset_left) hx

              ·
                apply affineSpan_le.mpr (Set.inter_subset_left)
                rw [Set.inter_comm]
                exact hx


            · intro ⟨h1, h2⟩
              apply subset_affineSpan
              simp only [Set.mem_inter_iff, SetLike.mem_coe]
              exact ⟨h1, h2⟩

          -- Step 5: Rewrite using this equality
          rw [hA_eq_Aint]

          -- Step 6: Aint is defined as U.toAffineSubspace ⊓ affΩ
          have hAint_unfold : Aint = U.toAffineSubspace ⊓ affΩ := rfl

          -- Step 7: Use hA_dir
          exact hA_dir



        rw [hA_eq]
        exact h_inf_ge_1
      have h_boundary_root : ∃ δ_bound, δ_bound ∈
      (P_sr n s.re : Set (CoeffVec n)) ∩ frontier P.Ω := by
        obtain ⟨p, hp_in_L⟩ := hA_nonempty

        -- Since dim(A.direction) ≥ 1, the dimension is strictly positive
        have h_dim_pos : 0 < Module.finrank ℝ A.direction := by grind


        -- A vector space with positive dimension is Nontrivial (it contains more than just the zero vector)
        haveI : Nontrivial A.direction := Module.nontrivial_of_finrank_pos h_dim_pos

        -- Extract a non-zero direction vector 'v' for our line
        obtain ⟨v_sub, hv_sub_nonzero⟩ := exists_ne (0 : A.direction)
        -- Define the direction vector in the ambient space
        let v : CoeffVec n := v_sub.val

        -- Establish that the line {p + t•v | t : ℝ} is contained in the intersection
        have h_line_in_L : ∀ (t : ℝ), p + t • v ∈ A_set := by
          intro t
          refine Set.mem_inter ?_ ?_
          · have hv_U : v ∈ U := by
              -- A.direction is a subset of U because A is contained in the affine subspace version of U
              have h_le : A.direction ≤ U := by
                have h_subset : A_set ⊆ U.toAffineSubspace := Set.inter_subset_left
                have h_aff_le : A ≤ U.toAffineSubspace := affineSpan_le.mpr h_subset
                -- Use the fact that direction of a submodule is the submodule itself
                have h_dir_le := AffineSubspace.direction_le h_aff_le
                rw [Submodule.toAffineSubspace_direction] at h_dir_le
                exact h_dir_le
              exact h_le v_sub.2

            exact Submodule.add_mem U hp_in_L.1 (Submodule.smul_mem U t hv_U)

          · have hv_affΩ : v ∈ affΩ.direction := by
                have h_le : A.direction ≤ affΩ.direction := by
                  have h_subset : A_set ⊆ affΩ := Set.inter_subset_right
                  have h_aff_le : A ≤ affΩ := affineSpan_le.mpr h_subset
                  exact AffineSubspace.direction_le h_aff_le
                exact h_le v_sub.2


            have h_vadd := affΩ.vadd_mem_of_mem_direction (Submodule.smul_mem affΩ.direction t hv_affΩ) hp_in_L.2
            refine SetLike.mem_coe.mpr ?_
            have h_eq : p + t • v = t • v +ᵥ p := by
              rw [vadd_eq_add, add_comm]
            rw [h_eq]
            exact h_vadd
        have hp_in_L : δ  ∈ A_set := ⟨hδ_in_Psr_submodule, subset_affineSpan ℝ P.Ω hδ_in_Ω⟩
        have hp_in_Ω : δ ∈ P.Ω := hδ_in_Ω
        have h_Ω_compact : IsCompact P.Ω := by
          have h_fin : (P.vertices : Set (CoeffVec n)).Finite := Finset.finite_toSet P.vertices
          exact Set.Finite.isCompact_convexHull h_fin
        have h_Ω_bounded : Bornology.IsBounded P.Ω := h_Ω_compact.isBounded
        have hv_nonzero : v ≠ 0 := by
          intro h
          apply hv_sub_nonzero
          -- have h_eq : v_sub.val = v := rfl
          exact Submodule.coe_eq_zero.mp h

        have h_escapes : ∃ t : ℝ, δ + t • v ∉ P.Ω := by
          by_contra h_contra
          push_neg at h_contra
          -- Because P.Ω is bounded, it sits in a metric ball of some diameter C
          rcases Metric.isBounded_iff.mp h_Ω_bounded with ⟨C, hC⟩
          have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_nonzero
          let t := (|C| + 1) / ‖v‖
          have ht_pos : 0 < t := by
            apply div_pos
            · have : 0 ≤ |C| := abs_nonneg C
              linarith
            · exact hv_norm_pos

          have h_in := h_contra t
          -- have h_le := hC (δ + t • v) h_in δ hp_in_Ω
          have h_dist : dist (δ + t • v) δ = t * ‖v‖ := by
            rw [dist_eq_norm]
            have h_sub : δ + t • v - δ = t • v := by abel
            have ht_nonneg : 0 ≤ t := ht_pos.le
            rw [h_sub, norm_smul, Real.norm_eq_abs t, abs_of_nonneg ht_nonneg]
          have h_le : dist (δ + t • v) δ ≤ C := by
            apply hC
            · exact h_in
            · exact hp_in_Ω
          have h_C_lt : C < |C| + 1 := by
            have : C ≤ |C| := le_abs_self C
            linarith
          rw [h_dist] at h_le
          have h_t_mul : t * ‖v‖ = |C| + 1 := div_mul_cancel₀ (|C| + 1) (ne_of_gt hv_norm_pos)
          rw [h_t_mul] at h_le
          linarith

        sorry


      sorry
    ·
      have hm01 : m = 0 ∨ m = 1 := by grind
      by_cases hm01 : m = 0
      ·
        sorry
      ·
        sorry


  · intro hcomplex
    sorry


/--
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
