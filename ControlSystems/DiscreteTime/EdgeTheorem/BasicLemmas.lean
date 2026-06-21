module

public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeTheoremDefs
public import Mathlib.Analysis.Convex.Intrinsic


@[expose] public section

open Polynomial Affine FiniteDimensional LinearMap Set

namespace CoeffBox

/-- A scalar `s` is in the root space set of `W` iff there exists `δ ∈ W` whose polynomial has `s` as a root over ℂ. -/
@[simp] lemma mem_RootSpaceSet_iff {n : ℕ} (W : Set (CoeffVec n)) (s : ℂ) :
    s ∈ RootSpaceSet W ↔ ∃ δ ∈ W, ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s :=
  Iff.rfl

/-- A coefficient vector `δ` belongs to the set `P_sr n r` iff its `evalLinear r` is zero. -/
@[simp] lemma mem_P_sr_iff {n : ℕ} (r : ℝ) (δ : CoeffVec n) :
    δ ∈ (P_sr n r : Set (CoeffVec n)) ↔ evalLinear r δ = 0 :=
  Iff.rfl

  -- ---------------------------------------------------------
-- HELPER SIMP LEMMAS TO AVOID COMMON ERRORS
-- ---------------------------------------------------------

-- 1. Linear map addition and scalar multiplication
/-- Pointwise addition of linear maps: `(f + g) x = f x + g x`. -/
@[simp] lemma LinearMap.add_apply {α β : Type*} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  (f g : α →ₗ[ℝ] β) (x : α) : (f + g) x = f x + g x := rfl

/-- Scalar multiplication of linear maps: `(c • f) x = c • f x`. -/
@[simp] lemma LinearMap.smul_apply {α β : Type*} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  (c : ℝ) (f : α →ₗ[ℝ] β) (x : α) : (c • f) x = c • f x := rfl

-- 2. Pi.add_apply for function spaces (critical for `hp.f + g_Ω`)
/-- Pointwise addition of dependent functions: `(f + g) i = f i + g i`. -/
@[simp] lemma Pi.add_apply {α : Type*} {β : α → Type*} [∀ i, AddCommGroup (β i)]
  (f g : ∀ i, β i) (i : α) : (f + g) i = f i + g i := rfl

-- 4. Submodule inclusion and intersection basics
/-- An element lies in the infimum (intersection) of two submodules iff it lies in each. -/
@[simp] lemma Submodule.mem_inf {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
  (U W : Submodule R M) (x : M) : x ∈ U ⊓ W ↔ x ∈ U ∧ x ∈ W := Iff.rfl

-- 9. Norm and positivity helpers (to help `linarith` succeed)
/-- The norm of a real number is non-negative. -/
@[simp] lemma norm_nonneg_real (x : ℝ) : 0 ≤ ‖x‖ := norm_nonneg _

/-- A real number has positive norm iff it is non-zero. -/
@[simp] lemma norm_pos_iff_real (x : ℝ) : ‖x‖ > 0 ↔ x ≠ 0 := norm_pos_iff

-- 11. Subtype coercion simplifications (critical for `Subtype.val`, `Subtype.coe`)
/-- Coercing a `Subtype` term back to the ambient type yields the original element. -/
@[simp] lemma Subtype.coe_eq_zero {α : Type*} (p : α) (s : Set α) (h : p ∈ s) :
  ((⟨p, h⟩ : s) : α) = p := rfl

/-- For a closed set, the frontier is the set minus its interior. -/
lemma frontier_eq_for_closed {n : ℕ} (S : Set (CoeffVec n)) (hS : IsClosed S) :
    frontier S = S \ interior S := by
  calc frontier S = closure S \ interior S := rfl
    _ = S \ interior S := by rw [hS.closure_eq]

/-- The line segment between `δ` and `δ + t_out • v` is connected. -/
lemma segment_is_connected {n : ℕ} (δ v : CoeffVec n) (t_out : ℝ) :
    IsConnected (segment ℝ δ (δ + t_out • v)) := by
  apply Convex.isConnected
  · exact convex_segment δ (δ + t_out • v)
  · exact ⟨δ, left_mem_segment ℝ δ (δ + t_out • v)⟩

/-- Rewrite a convex combination of `δ` and `δ + t_out • v` as `δ + (c * t_out) • v`. -/
lemma segment_point_rewrite (δ v : CoeffVec n) (c t_out : ℝ) :
    (1 - c) • δ + c • (δ + t_out • v) = δ + (c * t_out) • v := by
  calc (1 - c) • δ + c • (δ + t_out • v)
    _ = (1 - c) • δ + (c • δ + c • (t_out • v)) := by rw [smul_add]
    _ = ((1 - c) • δ + c • δ) + c • (t_out • v) := by rw [←add_assoc]
    _ = ((1 - c) + c) • δ + c • (t_out • v) := by rw [←add_smul]
    _ = 1 • δ + (c * t_out) • v := by
      have h_one : (1 - c) + c = 1 := by ring
      simp only [h_one, smul_smul, one_smul]
    _ = δ + (c * t_out) • v := by rw [one_smul]

/-- Evaluation at `(r : ℂ)` of the complexified polynomial commutes with the algebraic embedding of the real evaluation. -/
private lemma eval_root_comm {n : ℕ} (r : ℝ) (δ : CoeffVec n) :
    eval (↑r) (map (algebraMap ℝ ℂ) (polyOfVec δ)) = (algebraMap ℝ ℂ) (eval r (polyOfVec δ)) := by
  simp [polyOfVec, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
    map_sum, map_mul, map_pow]

/--
A continuous linear functional that strictly separates `x_int` from `δ_bound`,
i.e. `g_F x_int < g_F δ_bound`.  When `x_int ≠ δ_bound` we pick one via
`geometric_hahn_banach_point_point`; otherwise we return `0`.
-/
private noncomputable def separatingFunctionalRelint {n : ℕ} {F : Set (CoeffVec n)}
    (hF_convex : Convex ℝ F) (hF_compact : IsCompact F)
    (δ_bound : CoeffVec n) (hδ_bound_front : δ_bound ∈ frontier F)
    (x_int : CoeffVec n) (hx_int_relint : x_int ∈ intrinsicInterior ℝ F) :
    CoeffVec n →L[ℝ] ℝ :=
  if h : x_int ≠ δ_bound then
    Classical.choose (geometric_hahn_banach_point_point h)
  else
    0

/--
The separating functional constructed above strictly separates `x_int` from
`δ_bound`: `g_F x_int < g_F δ_bound`.
-/
private lemma separatingFunctionalRelint_strict {n : ℕ} {F : Set (CoeffVec n)}
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
private lemma finrank_ker_eq_finrank_sub_one {U : Type*} [AddCommGroup U] [Module ℝ U]
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

/--
Given a compact convex set `F` equal to an exposed face of `P`,
and a boundary point `δ_bound` of `F` together with a point `x_int` in the
intrinsic interior of `F`, there exists a point `x₀` in the exposed face
(not necessarily `x_int`) such that the separating functional evaluated at
`x₀` is strictly less than its value at `δ_bound`.
-/
private lemma exists_strict_less_in_F {n : ℕ} (P : Polytope n) (F : Set (CoeffVec n))
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
