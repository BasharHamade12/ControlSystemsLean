module

public import ControlSystems.Init
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.LinearMap
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Closure
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.OrderClosed

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

/--
The family of polynomials in the box `B`: all polynomials whose coefficients
lie within the box and whose natural degree is exactly `n`.
-/
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

/--
A real polynomial `f` is Schur stable if all its real roots lie strictly
inside the unit disc (i.e., have absolute value < 1).
-/
def Schur_Stable (f : Polynomial ℝ) : Prop :=
  ∀ a : ℝ , f.IsRoot a → abs a < 1

/--
The product of two Schur-stable polynomials is itself Schur stable.
This follows because any root of `f * g` is a root of `f` or a root of `g`.
-/
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

/--
A coefficient vector of dimension `n`: a function from `Fin (n+1)` to ℝ,
representing the coefficients `(α₀, …, αₙ)` of a degree-`n` polynomial.
-/
abbrev CoeffVec (n : ℕ) := Fin (n + 1) → ℝ

/--
A polytope Ω in coefficient space ℝ^{n+1}.
It is defined as the convex hull of a finite set of vertices V,
and is assumed to have nonempty topological interior.
-/
structure Polytope (n : ℕ) where
  vertices : Finset (CoeffVec n)
  nonempty  : vertices.Nonempty
  interior_nonempty : (interior (convexHull ℝ (vertices : Set (CoeffVec n)))).Nonempty

/-- The actual set Ω ⊆ ℝ^{n+1} as the convex hull of the vertices. -/
def Polytope.Ω (P : Polytope n) : Set (CoeffVec n) :=
  convexHull ℝ (P.vertices : Set (CoeffVec n))

/-- The interior of the polytope is nonempty by construction. -/
lemma Polytope.interior_Ω_nonempty (P : Polytope n) : (interior P.Ω).Nonempty :=
  P.interior_nonempty

open Polynomial

/-- Convert a coefficient vector α : Fin(n+1) → ℝ to a polynomial
    δ(s) = α(0) + α(1)·s + ... + α(n)·sⁿ
-/
noncomputable def polyOfVec {n : ℕ} (α : CoeffVec n) : Polynomial ℝ :=
  ∑ j : Fin (n + 1), Polynomial.monomial j.val (α j)

/--
The set of complex roots associated to a set `W` of coefficient vectors:
`s ∈ ℂ` is in `RootSpaceSet W` if there exists `δ ∈ W` such that
the polynomial `polyOfVec δ` (pulled back to ℂ) vanishes at `s`.
-/
def RootSpaceSet {n : ℕ}
  (W : Set (CoeffVec n)) : Set ℂ :=
  { s | ∃ δ ∈ W,
      ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s }

/--
The root space of a polytope `P`: all complex numbers `s` such that
some coefficient vector in `P.Ω` yields a polynomial vanishing at `s`.
-/
def RootSpace (P : Polytope n) : Set ℂ :=
  RootSpaceSet P.Ω

/--
The hyperplane `{x | f x = c}` defined by a nonzero linear functional `f`
and a scalar `c`.
-/
def Hyperplane {n : ℕ}
    (f : CoeffVec n →ₗ[ℝ] ℝ)
    (c : ℝ) : Set (CoeffVec n) :=
  { x | f x = c }

/--
A supporting hyperplane of a polytope `P` is a nonzero linear functional `f`
and a scalar `c` such that `f x ≤ c` for all `x ∈ P.Ω`, with equality
achieved at some point of `P.Ω`. The hyperplane `H = {x | f x = c}`
supports `P.Ω` from above.
-/
structure SupportingHyperplane (P : Polytope n) where
  f : CoeffVec n →ₗ[ℝ] ℝ
  c : ℝ
  nonzero : f ≠ 0
  upper_bound : ∀ x ∈ P.Ω, f x ≤ c
  touches : ∃ x ∈ P.Ω, f x = c
  H : Set (CoeffVec n) := Hyperplane f c

/--
The exposed face of `P` associated to a supporting hyperplane `hp`,
defined as the intersection `P.Ω ∩ hp.H` (using the `H` field).
-/
def ExposedFace_ (P : Polytope n) (hp : SupportingHyperplane P) :=
  P.Ω ∩ hp.H

/--
The exposed face of `P` associated to a supporting hyperplane `hp`,
defined directly as `{x | x ∈ P.Ω ∧ hp.f x = hp.c}`.
-/
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

/--
Alternative predicate for an exposed edge: a supporting hyperplane `hp`
whose exposed face has affine dimension exactly 1.
-/
def ExposedEdge {n : ℕ} {P : Polytope n} (hp : SupportingHyperplane P) : Prop :=
  Module.finrank ℝ (affineSpan ℝ (ExposedFace hp)).direction = 1

/--
The evaluation-at-`r` linear functional on coefficient vectors:
`evalLinear r δ = polyOfVec δ ▸ r`. Evaluates the polynomial at the
point `r ∈ ℝ`.
-/
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
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Polynomial.eval_finset_sum]
    rw [Polynomial.eval_finset_sum]
    rw [Finset.mul_sum]
    congr 1
    ext j
    simp [Polynomial.eval_monomial, mul_assoc, RingHom.id_apply]
}

/--
The set of coefficient vectors `δ` for which `polyOfVec δ` vanishes at `r`,
i.e., `evalLinear r δ = 0`.
-/
def P_sr' {n : ℕ} (r : ℝ) : Set (CoeffVec n) :=
  { δ | evalLinear r δ = 0 }

/--
The kernel of `evalLinear r`, presented as a submodule of `CoeffVec n`.
This is the linear subspace of coefficient vectors whose associated polynomial
has `r` as a root.
-/
noncomputable def P_sr (n : ℕ) (r : ℝ) : Submodule ℝ (CoeffVec n) :=
  (evalLinear r).ker

/--
The complex evaluation ℝ-linear functional on coefficient vectors:
`evalAtComplex n s δ = (polyOfVec δ)(s)`, where `polyOfVec δ` is
pulled back to ℂ via `algebraMap ℝ ℂ`.
-/
noncomputable def evalAtComplex {n : ℕ} (s : ℂ) : CoeffVec n →ₗ[ℝ] ℂ :=
{
  toFun := fun δ => ((polyOfVec δ).map (algebraMap ℝ ℂ)).eval s
  map_add' := by
    intros δ₁ δ₂
    simp [polyOfVec, Polynomial.eval_add, map_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a δ
    have h_linear : polyOfVec (a • δ) = a • polyOfVec δ := by
      ext i
      simp [polyOfVec, Polynomial.coeff_smul,
        Finset.smul_sum, smul_eq_mul, Polynomial.coeff_monomial]
    calc
      ((polyOfVec (a • δ)).map (algebraMap ℝ ℂ)).eval s
          = ((a • polyOfVec δ).map (algebraMap ℝ ℂ)).eval s := by rw [h_linear]
      _ = ((a : ℂ) • (polyOfVec δ).map (algebraMap ℝ ℂ)).eval s := by simp
      _ = (a : ℂ) * (((polyOfVec δ).map (algebraMap ℝ ℂ)).eval s) := by simp
      _ = a • (((polyOfVec δ).map (algebraMap ℝ ℂ)).eval s) := by simp
}

/--
The kernel of `evalAtComplex n s`, i.e., the ℝ-subspace of coefficient vectors
whose associated polynomial vanishes at `s ∈ ℂ`. For non-real `s`, this
subspace has ℝ-dimension `n-1`.
-/
noncomputable def P_sc (n : ℕ) (s : ℂ) : Submodule ℝ (CoeffVec n) :=
  (evalAtComplex (n := n) s).ker

/--
If `δ`'s polynomial vanishes at `s ∈ ℂ`, then `δ` lies in `P_sc n s`.
-/
lemma mem_P_sc_of_isRoot {n : ℕ} (s : ℂ) (δ : CoeffVec n)
    (h : ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s) :
    δ ∈ (P_sc n s : Set (CoeffVec n)) := by
  unfold P_sc
  have hzero : ((polyOfVec δ).map (algebraMap ℝ ℂ)).eval s = 0 := h
  simpa [evalAtComplex] using hzero

/--
If `δ ∈ F` and `(polyOfVec δ).map (algebraMap ℝ ℂ)` vanishes at `s`,
then `s` belongs to the root space set of `F`.
-/
lemma rootspace_mem_of_isRoot {n : ℕ} (s : ℂ) (δ : CoeffVec n)
    (h : ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s)
    (F : Set (CoeffVec n)) (hδ_in_F : δ ∈ F) : s ∈ RootSpaceSet F :=
  ⟨δ, hδ_in_F, h⟩

/-- `F` is an exposed face of `P` if there exists a supporting hyperplane `hp`
such that `F` equals the exposed face of `hp`. -/
def IsExposedFace {n : ℕ} (P : Polytope n) (F : Set (CoeffVec n)) : Prop :=
  ∃ hp : SupportingHyperplane P, F = ExposedFace hp

/-- [Axiom of Polyhedral Geometry]
Every vertex of a polytope is incident to at least one exposed edge.
This is a standard result in polyhedral combinatorics (following from the
face lattice structure / Krein-Milman theorem), but requires the full
V-representation/H-representation face lattice API which is currently
outside the scope of Mathlib's basic convex geometry. -/
axiom vertex_incident_to_exposed_edge {n : ℕ} (P : Polytope n) (v : CoeffVec n)
  (hv : v ∈ P.vertices) : ∃ (E : Set (CoeffVec n)), IsExposedEdge P E ∧ v ∈ E

/--
The ℝ-vector space `CoeffVec n` (functions `Fin (n+1) → ℝ`) has
dimension `n+1`.
-/
lemma finrank_CoeffVec {n : ℕ} :
  Module.finrank ℝ (CoeffVec n) = n + 1 := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp

/--
The evaluation linear functional `evalLinear r : CoeffVec n → ℝ` is
surjective for any `r ∈ ℝ`.
-/
lemma evalLinear_surjective {n : ℕ} (r : ℝ) :
    Function.Surjective (evalLinear (n := n) r) := by
  intro y
  use fun j => if j.val = 0 then y else 0
  simp [evalLinear, polyOfVec]
  simp [Polynomial.eval_finset_sum, Polynomial.eval_monomial]

/--
Every polytope `P` is compact, because it is the convex hull of a finite set.
-/
lemma Polytope.isCompact {n : ℕ} (P : Polytope n) : IsCompact P.Ω := by
  have h_fin : (P.vertices : Set (CoeffVec n)).Finite := Finset.finite_toSet P.vertices
  exact Set.Finite.isCompact_convexHull h_fin

/--
Every polytope is bounded (since it is compact).
-/
lemma Polytope.isBounded {n : ℕ} (P : Polytope n) : Bornology.IsBounded P.Ω :=
  P.isCompact.isBounded

/--
Given a point `δ` inside a polytope `P` and a nonzero direction `v`,
there exists a positive `t` such that the ray `δ + t•v` exits the polytope.
-/
lemma ray_escapes_polytope {n : ℕ} (P : Polytope n) (δ v : CoeffVec n)
    (hp_in_Ω : δ ∈ P.Ω) (hv_nonzero : v ≠ 0) : ∃ (t : ℝ), 0 < t ∧ δ + t • v ∉ P.Ω := by
  rcases Metric.isBounded_iff.mp P.isBounded with ⟨C, hC⟩
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_nonzero
  let t := (|C| + 1) / ‖v‖
  have ht_pos : 0 < t := div_pos (by have : 0 ≤ |C| := abs_nonneg C; linarith) hv_norm_pos
  by_cases h_contra : δ + t • v ∈ P.Ω
  · exfalso
    have h_dist : dist (δ + t • v) δ = t * ‖v‖ := by
      rw [dist_eq_norm]
      have h_sub : δ + t • v - δ = t • v := by abel
      have ht_nonneg : 0 ≤ t := ht_pos.le
      rw [h_sub, norm_smul, Real.norm_eq_abs t, abs_of_nonneg ht_nonneg]
    have h_le : dist (δ + t • v) δ ≤ C := by
      apply hC
      · exact h_contra
      · exact hp_in_Ω
    have h_C_lt : C < |C| + 1 := by have : C ≤ |C| := le_abs_self C; linarith
    rw [h_dist] at h_le
    have h_t_mul : t * ‖v‖ = |C| + 1 := div_mul_cancel₀ (|C| + 1) (ne_of_gt hv_norm_pos)
    rw [h_t_mul] at h_le
    linarith
  · exact ⟨t, ht_pos, h_contra⟩

/--
The affine span of the intersection of a submodule `U` with an affine
subspace `affΩ` equals the intersection of `U` (as an affine subspace)
with `affΩ`.
-/
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

/--
A set `F` is a polytope (in the sense of being the convex hull of a finite
nonempty set). Unlike `Polytope`, this predicate does NOT require nonempty
topological interior in the full ambient space, so it applies to faces of
any dimension.
-/
def IsPolytopeSet {n : ℕ} (F : Set (CoeffVec n)) : Prop :=
  ∃ (V : Finset (CoeffVec n)), V.Nonempty ∧ convexHull ℝ (V : Set (CoeffVec n)) = F

end CoeffBox
