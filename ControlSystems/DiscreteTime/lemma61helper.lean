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
