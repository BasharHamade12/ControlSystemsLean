module


import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.LocallyConvex.Separation
import ControlSystems.DiscreteTime.EdgeTheoremDefs

open Affine FiniteDimensional LinearMap Set

namespace CoeffBox

/--
A continuous linear functional that strictly separates `x_int` from `δ_bound`,
i.e. `g_F x_int < g_F δ_bound`.  When `x_int ≠ δ_bound` we pick one via
`geometric_hahn_banach_point_point`; otherwise we return `0`.
-/
noncomputable def separatingFunctionalRelint {n : ℕ} {F : Set (CoeffVec n)}
    (hF_convex : Convex ℝ F) (hF_compact : IsCompact F)
    (δ_bound : CoeffVec n) (hδ_bound_front : δ_bound ∈ frontier F)
    (x_int : CoeffVec n) (hx_int_relint : x_int ∈ intrinsicInterior ℝ F) :
    CoeffVec n →L[ℝ] ℝ :=
  if h : x_int ≠ δ_bound then
    Classical.choose (geometric_hahn_banach_point_point h)
  else
    0

lemma separatingFunctionalRelint_strict {n : ℕ} {F : Set (CoeffVec n)}
    {hF_convex : Convex ℝ F} {hF_compact : IsCompact F}
    {δ_bound : CoeffVec n} {hδ_bound_front : δ_bound ∈ frontier F}
    {x_int : CoeffVec n} {hx_int_relint : x_int ∈ intrinsicInterior ℝ F}
    (hx_ne : x_int ≠ δ_bound) :
    separatingFunctionalRelint hF_convex hF_compact δ_bound hδ_bound_front x_int hx_int_relint x_int <
    separatingFunctionalRelint hF_convex hF_compact δ_bound hδ_bound_front x_int hx_int_relint δ_bound := by
  dsimp [separatingFunctionalRelint]
  rw [dif_pos hx_ne]
  have h_exists := geometric_hahn_banach_point_point hx_ne
  exact Classical.choose_spec h_exists

/--
For a nonzero linear functional `g` on a finite-dimensional real vector space `U`,
`dim(ker g) = dim(U) - 1`.  This follows from rank-nullity and the fact that
`g : U → ℝ` is surjective when nonzero.
-/
lemma finrank_ker_eq_finrank_sub_one {U : Type*} [AddCommGroup U] [Module ℝ U]
    [FiniteDimensional ℝ U] (g : U →ₗ[ℝ] ℝ) (hg_nonzero : g ≠ 0) :
    Module.finrank ℝ (LinearMap.ker g) = Module.finrank ℝ U - 1 := by
  -- Show that g is surjective, so its range is ⊤, hence finrank(range) = 1
  have h_range_top : LinearMap.range g = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro y
    -- Since g ≠ 0, there exists some x with g x ≠ 0
    have ⟨x, hx⟩ : ∃ x, g x ≠ 0 := by
      by_contra h_allzero
      apply hg_nonzero
      apply LinearMap.ext
      intro x
      by_contra hgx_ne
      apply h_allzero
      exact ⟨x, hgx_ne⟩
    refine ⟨(y / g x) • x, ?_⟩
    simp [hx, mul_comm]
    grind
  have h_finrank_range : Module.finrank ℝ (LinearMap.range g) = 1 := by
    rw [h_range_top]
    simp
  have h_total : Module.finrank ℝ (LinearMap.range g) + Module.finrank ℝ (LinearMap.ker g) = Module.finrank ℝ U :=
    LinearMap.finrank_range_add_finrank_ker g
  rw [h_finrank_range] at h_total
  omega

lemma exists_strict_less_in_F {n : ℕ} (P : Polytope n) (F : Set (CoeffVec n))
    (hF_convex : Convex ℝ F) (hF_compact : IsCompact F)
    (δ_bound : CoeffVec n) (hδ_bound_front : δ_bound ∈ frontier F)
    (x_int : CoeffVec n) (hx_int_relint : x_int ∈ intrinsicInterior ℝ F)
    (hp : SupportingHyperplane P) (hF_eq : F = ExposedFace hp)
    (hx_ne : x_int ≠ δ_bound) :
    ∃ x₀ ∈ ExposedFace hp,
      (separatingFunctionalRelint hF_convex hF_compact δ_bound hδ_bound_front x_int hx_int_relint).toLinearMap x₀ <
      (separatingFunctionalRelint hF_convex hF_compact δ_bound hδ_bound_front x_int hx_int_relint).toLinearMap δ_bound := by
  let g_F := separatingFunctionalRelint hF_convex hF_compact δ_bound hδ_bound_front x_int hx_int_relint
  use x_int
  constructor
  · rw [← hF_eq]; exact intrinsicInterior_subset hx_int_relint
  · have h_strict := separatingFunctionalRelint_strict (F := F) (hF_convex := hF_convex) (hF_compact := hF_compact)
      (δ_bound := δ_bound) (hδ_bound_front := hδ_bound_front) (x_int := x_int) (hx_int_relint := hx_int_relint) hx_ne
    simpa [g_F]




end CoeffBox
