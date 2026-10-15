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

/-! # Core definitions for the Edge Theorem (Ch. 6, §6.2)

Textbook mapping (`edgetheorem.md`):
- `CoeffVec n` = coefficient space `ℝ^{n+1}`, `δ = [δₙ,…,δ₀]ᵀ` (6.1).
- `P.Ω` = polytope `Ω ⊂ ℝ^{n+1}` (convex hull of `P.vertices`).
- `RootSpaceSet W` = root space `R(W) = {s : δ(s)=0 for some δ ∈ W}`.
- `RootSpace P` = `R(Ω)`.
- `SupportingHyperplane` / `IsExposedFace` / `IsExposedEdge` = §6.2 exposed sets;
  one-dimensional exposed sets are edges, two-dimensional are faces.
- `P_sr n r` = `𝒫_{s_r}` (real-root subspace, `dim = n`);
  `P_sc n s` = `𝒫_{s_c}` (complex-root subspace, `dim = n-1`).
- `dim U` = `dim U` (finrank over ℝ); `meetDir` = `dir(aff(U ∩ affΩ))`.
- Assumption 6.1 (fixed leading-sign / degree) is taken as explicit
  hypotheses (`hleading`) at use sites, not baked into `Polytope`.

Notation: `open EdgeNotation` enables `R[W]`, `Ω[P]`
shorthands below. Existing names (`RootSpaceSet`, `P.Ω`, `frontier`, …)
remain canonical; notations are additive aliases only.
-/

namespace CoeffBox

/-- Coefficient vector `(α₀,…,αₙ) : ℝ^{n+1}` for `δ(s) = α₀+α₁s+…+αₙsⁿ`. -/
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

/-- The exposed face of `P` for `hp`: `F = Ω ∩ {x | hp.f x = hp.c}`. -/
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

/-- Shorthand for the carrier of `P_sr n r` as a set: the coefficient
vectors of real polynomials vanishing at the real point `r`.  Kept as a
reducible abbreviation so that it is interchangeable with the coercion
`(P_sr n r : Set (CoeffVec n))` in older statements. -/
abbrev PsrSet (n : ℕ) (r : ℝ) : Set (CoeffVec n) :=
  (P_sr n r : Set (CoeffVec n))

/-- Shorthand for the carrier of `P_sc n s` as a set: the coefficient
vectors of real polynomials vanishing at the (possibly non-real) point
`s`.  Reducible abbreviation, interchangeable with the coercion. -/
abbrev PscSet (n : ℕ) (s : ℂ) : Set (CoeffVec n) :=
  (P_sc n s : Set (CoeffVec n))

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

-- NOTE (fix-vertex-edge-axiom): the old axiom
-- `vertex_incident_to_exposed_edge : v ∈ P.vertices → ∃ edge ∋ v`
-- was false for redundant vertices. It has been removed; the geometric
-- replacement `exists_exposed_edge_of_singleton` lives in `VertexEdge.lean`
-- (singleton exposed face `{v}` lies on an exposed edge).

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

-- Ray escape for polytopes is `ray_escapes_of_bounded` in `BasicLemmas`
-- (single copy): `ray_escapes_of_bounded P.isBounded δ v hδ hv`.

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
Shorthand for the *direction of the affine span of the intersection* of a
submodule `U` (as a set) with an affine subspace `affΩ` — the quantity that
appears in the `h_inter_dim` hypotheses throughout the Edge Theorem files.
`U meet affΩ` as an affine subspace, so `meetDir U affΩ = (U ⊓ affΩ.direction)`
whenever `U ∩ affΩ` is nonempty (see `intersection_direction_eq`).
-/
abbrev meetDir (n : ℕ) (U : Submodule ℝ (CoeffVec n))
    (affΩ : AffineSubspace ℝ (CoeffVec n)) : Submodule ℝ (CoeffVec n) :=
  (affineSpan ℝ ((U : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction

/--
Shorthand for the *dimension* of a real subspace, the `dim` of the
mathematical exposition: `dim U = Module.finrank ℝ U`.  It composes with
`meetDir` and `.direction`, e.g. `dim (meetDir n U affΩ)` renders
`dim dir(aff(U ∩ affΩ))` and `dim (affineSpan ℝ F).direction` renders
`dim dir(aff F)`.
-/
noncomputable abbrev dim {M : Type*} [AddCommGroup M] [Module ℝ M]
    (U : Submodule ℝ M) : ℕ :=
  Module.finrank ℝ U

end CoeffBox
