module

public import ControlSystems.Init
public import Mathlib

@[expose] public section

open Polynomial

/--
A box `B_n` in the space of coefficients for polynomials of degree `n`.
It is defined by lower bounds `l` and upper bounds `u` for each coefficient index `j ∈ {0, ..., n}`.
-/
structure CoeffBox (n : ℕ) where
  l : Fin (n + 1) → ℝ
  u : Fin (n + 1) → ℝ
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
  · exact hf a hfa
  · exact hg a hga

abbrev CoeffVec (n : ℕ) := Fin (n + 1) → ℝ

/--
A polytope Ω in coefficient space ℝ^{n+1}.
It is defined as the convex hull of a finite set of vertices V.
This matches the PDF: "the convex hull of a finite number of points".
-/
structure Polytope (n : ℕ) where
  vertices : Finset (CoeffVec n)
  nonempty  : vertices.Nonempty

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

/-- E is an exposed face of P if it is an exposed face of affine dimension 2 -/
def IsExposedFace {n : ℕ} (P : Polytope n) (F : Set (CoeffVec n)) : Prop :=
  ∃ hp : SupportingHyperplane P, F = ExposedFace hp

lemma finrank_CoeffVec {n : ℕ} :
  Module.finrank ℝ (CoeffVec n) = n + 1 := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp

lemma evalLinear_surjective {n : ℕ} (r : ℝ) :
    Function.Surjective (evalLinear (n := n) r) := by
  intro y
  use fun j => if j.val = 0 then y else 0
  simp [evalLinear, polyOfVec]
  simp [Polynomial.eval_finset_sum, Polynomial.eval_monomial]

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
  have h_le : dist (δ + t • v) δ ≤ C := by
    apply hC
    · exact h_in
    · exact hp_in_Ω
  have h_C_lt : C < |C| + 1 := by have : C ≤ |C| := le_abs_self C; linarith
  rw [h_dist] at h_le
  have h_t_mul : t * ‖v‖ = |C| + 1 := div_mul_cancel₀ (|C| + 1) (ne_of_gt hv_norm_pos)
  rw [h_t_mul] at h_le
  linarith

lemma affineSpan_inter {n : ℕ} (U : Submodule ℝ (CoeffVec n))
    (affΩ : AffineSubspace ℝ (CoeffVec n)) :
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

end CoeffBox
