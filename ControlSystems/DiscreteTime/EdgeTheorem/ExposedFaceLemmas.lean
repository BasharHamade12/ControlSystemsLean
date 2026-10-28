module

public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeTheoremDefs
public import Mathlib.Analysis.Convex.Intrinsic
public import ControlSystems.DiscreteTime.EdgeTheorem.RelativeInterior
public import ControlSystems.DiscreteTime.EdgeTheorem.BasicLemmas


@[expose] public section

open Polynomial
open Affine
open FiniteDimensional
open LinearMap
open Set
open scoped BigOperators

namespace CoeffBox

/-- A point on the frontier of a polytope is in the polytope. -/
lemma frontier_point_in_Ω {n : ℕ} (P : Polytope n) (δ_bound : CoeffVec n)
    (hδ_bound_front : δ_bound ∈ frontier P.Ω) : δ_bound ∈ P.Ω := by
  have h_closed : IsClosed P.Ω := P.isCompact.isClosed
  have hsub := frontier_subset_closure (s := P.Ω)
  rw [h_closed.closure_eq] at hsub
  exact hsub hδ_bound_front

/-- A point on the frontier of a polytope is not in its interior. -/
lemma frontier_point_not_interior {n : ℕ} (P : Polytope n) (δ_bound : CoeffVec n)
    (hδ_bound_front : δ_bound ∈ frontier P.Ω) : δ_bound ∉ interior P.Ω := by
  have h_closed : IsClosed P.Ω := P.isCompact.isClosed
  intro hint
  have h1 : δ_bound ∈ frontier P.Ω := hδ_bound_front
  rw [frontier_eq_closure_inter_closure, h_closed.closure_eq] at h1
  have h2 : δ_bound ∈ closure (P.Ωᶜ) := h1.2
  have h3 : δ_bound ∉ closure (P.Ωᶜ) := by
    rw [closure_compl (s := P.Ω)]
    simp only [Set.mem_compl_iff, not_not]
    trivial
  exact h3 h2

/-- If a continuous linear functional `f` is strictly larger at `δ_bound` than on the nonempty interior of `P.Ω`, then `f` is nonzero. -/
private lemma supporting_func_nonzero {n : ℕ} (P : Polytope n) (f : CoeffVec n →L[ℝ] ℝ)
    (δ_bound : CoeffVec n) (hf_strict : ∀ x ∈ interior P.Ω, f x < f δ_bound)
    (h_int_nonempty : (interior P.Ω).Nonempty) : f ≠ 0 := by
  intro heq
  simp only [heq, ContinuousLinearMap.zero_apply] at hf_strict
  obtain ⟨x, hx⟩ := h_int_nonempty
  exact lt_irrefl 0 (hf_strict x hx)

/-- If a functional `f` is strictly less than `c` on the interior of `P.Ω`, then it is `≤ c` on all of `P.Ω`. -/
private lemma supporting_hyperplane_upper_bound {n : ℕ} (P : Polytope n)
    (f : CoeffVec n →L[ℝ] ℝ) (c : ℝ)
    (hf_strict : ∀ x ∈ interior P.Ω, f x < c)
    (h_int_nonempty : (interior P.Ω).Nonempty) :
    ∀ x ∈ P.Ω, f.toLinearMap x ≤ c := by
  intro x hx
  have h_closed_half : IsClosed {y | f y ≤ c} :=
    isClosed_Iic.preimage f.continuous
  have h_convex : Convex ℝ P.Ω := convex_convexHull ℝ _
  have h_subset : P.Ω ⊆ {y | f y ≤ c} := by
    calc
      P.Ω = closure P.Ω := (P.isCompact.isClosed.closure_eq).symm
      _ = closure (interior P.Ω) :=
        (h_convex.closure_interior_eq_closure_of_nonempty_interior h_int_nonempty).symm
      _ ⊆ closure {y | f y ≤ c} :=
        closure_mono fun y hy => le_of_lt (hf_strict y hy)
      _ = {y | f y ≤ c} := h_closed_half.closure_eq
  have hx_f : f x ≤ c := h_subset hx
  change f x ≤ c
  exact hx_f

/-- If `δ_bound ∈ P_sr n r` and `δ_bound ∈ F`, then `(r : ℂ)` is in the root space set of `F`. -/
lemma rootspace_mem_of_eval_zero {n : ℕ} (r : ℝ) (δ_bound : CoeffVec n)
    (hδ_bound_Psr : δ_bound ∈ PsrSet n r)
    (F : Set (CoeffVec n)) (hδ_in_F : δ_bound ∈ F) : (r : ℂ) ∈ RootSpaceSet F := by
  unfold RootSpaceSet
  simp only [Set.mem_setOf_eq]
  refine ⟨δ_bound, hδ_in_F, ?_⟩
  have heval : evalLinear r δ_bound = 0 := hδ_bound_Psr
  unfold Polynomial.IsRoot
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_eval_map, eval_root_comm r δ_bound]
  have h_eval_eq : eval r (polyOfVec δ_bound) = evalLinear r δ_bound := rfl
  rw [h_eval_eq, heval]
  simp

/-- If `(r : ℂ)` is a root of the complexified polynomial of `δ`, then `δ ∈ P_sr n r`. -/
lemma mem_P_sr_of_isRoot {n : ℕ} (r : ℝ) (δ : CoeffVec n)
    (h : ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot (r : ℂ)) :
    δ ∈ PsrSet n r := by
  show evalLinear r δ = 0
  unfold Polynomial.IsRoot at h
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_eval_map, eval_root_comm r δ] at h
  exact_mod_cast (map_eq_zero (algebraMap ℝ ℂ)).mp h

/-- For any boundary point `δ_bound` of `P.Ω` that also lies in `P_sr n r`, there exists an exposed face `F` of `P` containing `δ_bound` and whose root space set contains `(r : ℂ)`. -/
lemma exists_exposed_face_containing_boundary_point {n : ℕ} (P : Polytope n)
    (r : ℝ) (δ_bound : CoeffVec n)
    (hδ_bound_front : δ_bound ∈ frontier P.Ω)
    (hδ_bound_Psr : δ_bound ∈ PsrSet n r) :
    ∃ F : Set (CoeffVec n), IsExposedFace P F ∧ δ_bound ∈ F ∧ (r : ℂ) ∈ RootSpaceSet F := by
  have hδ_bound_in_Ω : δ_bound ∈ P.Ω := frontier_point_in_Ω P δ_bound hδ_bound_front
  by_cases htop : (affineSpan ℝ P.Ω).direction = ⊤
  · -- Ambient-full-dimensional case: interior nonempty, Hahn-Banach applies.
    have hspan_top : affineSpan ℝ P.Ω = ⊤ := by
      have hne : ((affineSpan ℝ P.Ω : AffineSubspace ℝ (CoeffVec n)) :
          Set (CoeffVec n)).Nonempty :=
        ⟨δ_bound, subset_affineSpan ℝ P.Ω hδ_bound_in_Ω⟩
      rw [← AffineSubspace.direction_eq_top_iff_of_nonempty hne]
      exact htop
    have h_int_nonempty : (interior P.Ω).Nonempty :=
      (Convex.interior_nonempty_iff_affineSpan_eq_top
        (convex_convexHull ℝ (P.vertices : Set (CoeffVec n)))).mpr hspan_top
    have hδ_bound_not_int : δ_bound ∉ interior P.Ω :=
      frontier_point_not_interior P δ_bound hδ_bound_front
    have h_convex : Convex ℝ P.Ω := convex_convexHull ℝ _
    have h_int_convex : Convex ℝ (interior P.Ω) := h_convex.interior
    have h_int_open : IsOpen (interior P.Ω) := isOpen_interior
    obtain ⟨f, hf_strict⟩ :=
      geometric_hahn_banach_open_point h_int_convex h_int_open hδ_bound_not_int
    have hf_ne : f ≠ 0 := supporting_func_nonzero P f δ_bound hf_strict h_int_nonempty
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
    have hc_upper : ∀ x ∈ P.Ω, f_lin x ≤ c :=
      supporting_hyperplane_upper_bound P f c hf_strict h_int_nonempty
    let hp : SupportingHyperplane P := {
      f           := f_lin
      c           := c
      nonzero     := hf_lin_ne
      upper_bound := hc_upper
      touches     := ⟨δ_bound, hδ_bound_in_Ω, rfl⟩
    }
    have hδ_in_face : δ_bound ∈ ExposedFace hp := by
      unfold ExposedFace
      simp only [Set.mem_setOf_eq]
      exact ⟨hδ_bound_in_Ω, rfl⟩
    have hr_in_rootspace : (r : ℂ) ∈ RootSpaceSet (ExposedFace hp) :=
      rootspace_mem_of_eval_zero r δ_bound hδ_bound_Psr (ExposedFace hp) hδ_in_face
    exact ⟨ExposedFace hp, ⟨hp, rfl⟩, hδ_in_face, hr_in_rootspace⟩
  · -- Degenerate family in a proper affine slice: `Ω` itself is an exposed face.
    exact ⟨P.Ω, isExposedFace_Ω_of_direction_ne_top P htop, hδ_bound_in_Ω,
      rootspace_mem_of_eval_zero r δ_bound hδ_bound_Psr P.Ω hδ_bound_in_Ω⟩

/-- If a point `δ + t • v` leaves an exposed face `F` of `P` while staying
    in the direction of `affineSpan F`, then it also leaves `P.Ω`. -/
private lemma affine_const_on_exposed_face {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
    (hp : SupportingHyperplane P) (hF_eq : F = ExposedFace hp) :
    ∀ x ∈ affineSpan ℝ F, hp.f x = hp.c := by
  let H : AffineSubspace ℝ (CoeffVec n) :=
    { carrier := {x | hp.f x = hp.c}
      smul_vsub_vadd_mem := by
        intro a b c d hb hc hd
        have hb' : hp.f b = hp.c := hb
        have hc' : hp.f c = hp.c := hc
        have hd' : hp.f d = hp.c := hd
        have : hp.f (a • (b - c) + d) = hp.c := by
          calc
            hp.f (a • (b - c) + d) = hp.f (a • (b - c)) + hp.f d := by rw [map_add]
            _ = a • hp.f (b - c) + hp.c := by rw [map_smul, hd']
            _ = a • (hp.f b - hp.f c) + hp.c := by rw [map_sub]
            _ = a • (hp.c - hp.c) + hp.c := by rw [hb', hc']
            _ = a • 0 + hp.c := by rw [sub_self]
            _ = 0 + hp.c := by rw [smul_zero]
            _ = hp.c := by rw [zero_add]
        simpa [Set.mem_setOf_eq, vsub_eq_sub, vadd_eq_add] using this
    }
  have hF_sub : (F : Set (CoeffVec n)) ⊆ (H : Set (CoeffVec n)) := by
    intro y hy; rw [hF_eq] at hy; exact hy.2
  have h_span_sub : affineSpan ℝ F ≤ H := affineSpan_le.mpr hF_sub
  intro x hx; simpa using h_span_sub hx

/-- If `F` is the exposed face defined by a supporting hyperplane `hp`, then `hp.f` vanishes on any vector `v` in the direction of `affineSpan ℝ F`. -/
lemma exposed_face_direction_kills_vector {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
    (hp : SupportingHyperplane P) (hF_eq : F = ExposedFace hp) (δ : CoeffVec n) (v : CoeffVec n)
    (hδ_in_F : δ ∈ F) (hv_in_dir : v ∈ (affineSpan ℝ F).direction) : hp.f v = 0 := by
  have h_aff_const : ∀ x ∈ affineSpan ℝ F, hp.f x = hp.c :=
    affine_const_on_exposed_face hp hF_eq
  have hδ_f : hp.f δ = hp.c := by
    rw [hF_eq] at hδ_in_F
    exact hδ_in_F.2
  have h_δ_plus_v : δ + v ∈ affineSpan ℝ F := by
    have h_vadd : v +ᵥ δ ∈ affineSpan ℝ F :=
      AffineSubspace.vadd_mem_of_mem_direction hv_in_dir (subset_affineSpan ℝ F hδ_in_F)
    simpa [vadd_eq_add, add_comm] using h_vadd
  have hsum : hp.f (δ + v) = hp.f δ + hp.f v := by simp
  rw [h_aff_const (δ + v) h_δ_plus_v, h_aff_const δ (subset_affineSpan ℝ F hδ_in_F)] at hsum
  linarith

/-- If `hp.f δ = hp.c` and `hp.f v = 0`, then `hp.f` stays constant at `hp.c` along the ray `δ + t • v`. -/
private lemma exposed_face_point_value {n : ℕ} {P : Polytope n}
    (hp : SupportingHyperplane P) (δ : CoeffVec n) (v : CoeffVec n) (t : ℝ)
    (hδ_f : hp.f δ = hp.c) (hv_f : hp.f v = 0) : hp.f (δ + t • v) = hp.c := by
  calc
    hp.f (δ + t • v) = hp.f δ + hp.f (t • v) := by simp
    _ = hp.c + t • (hp.f v) := by simp [hδ_f]
    _ = hp.c + t • 0 := by rw [hv_f]
    _ = hp.c := by simp

lemma escapes_P_via_exposed_face {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
    (hF_exposed : IsExposedFace P F) (δ : CoeffVec n) (v : CoeffVec n) (t : ℝ)
    (hδ_in_F : δ ∈ F) (hv_in_dir : v ∈ (affineSpan ℝ F).direction)
    (h_escapes_F : δ + t • v ∉ F) : δ + t • v ∉ P.Ω := by
  obtain ⟨hp, hF_eq⟩ := hF_exposed
  have hδ_f : hp.f δ = hp.c := by
    rw [hF_eq] at hδ_in_F
    exact hδ_in_F.2
  have hv_f : hp.f v = 0 :=
    exposed_face_direction_kills_vector hp hF_eq δ v hδ_in_F hv_in_dir
  have h_val : hp.f (δ + t • v) = hp.c :=
    exposed_face_point_value hp δ v t hδ_f hv_f
  by_contra h_in_Ω
  apply h_escapes_F
  rw [hF_eq]
  exact ⟨h_in_Ω, h_val⟩

/-- The sum of a supporting hyperplane functional and a functional `g_lin` (with `g_lin v > 0` and `hpF.f v = 0`) defines an exposed face of `P`. -/
lemma sum_supporting_hyperplane_exposed_face {n : ℕ} {P : Polytope n}
    (hpF : SupportingHyperplane P) (g_lin : CoeffVec n →ₗ[ℝ] ℝ) (v δ_bound : CoeffVec n)
    (hδ_bound_in_Ω : δ_bound ∈ P.Ω) (h_fδ_bound : hpF.f δ_bound = hpF.c)
    (hc_upper : ∀ x ∈ P.Ω, g_lin x ≤ g_lin δ_bound)
    (h_fv_zero : hpF.f v = 0) (h_gv_pos : g_lin v > 0) :
    IsExposedFace P {x | x ∈ P.Ω ∧ (hpF.f + g_lin) x = hpF.c + g_lin δ_bound} := by
  let g_new := hpF.f + g_lin
  have h_new_upper : ∀ x ∈ P.Ω, (hpF.f + g_lin) x ≤ hpF.c + g_lin δ_bound := by
    intro x hx
    have hfx : hpF.f x ≤ hpF.c := hpF.upper_bound x hx
    have hgx : g_lin x ≤ g_lin δ_bound := hc_upper x hx
    simpa [Pi.add_apply] using add_le_add hfx hgx
  have h_new_touches : ∃ x ∈ P.Ω, g_new x = hpF.c + g_lin δ_bound :=
    ⟨δ_bound, hδ_bound_in_Ω, by
    simp [g_new, h_fδ_bound]⟩
  have h_new_nonzero : g_new ≠ 0 := by
    intro hzero
    have : g_lin v = 0 := by
      calc
        g_lin v = g_new v := by simp [g_new, h_fv_zero]
        _ = (0 : CoeffVec n →ₗ[ℝ] ℝ) v := by rw [hzero]
        _ = 0 := by simp
    linarith
  exact ⟨{
    f := g_new
    c := hpF.c + g_lin δ_bound
    nonzero := h_new_nonzero
    upper_bound := h_new_upper
    touches := h_new_touches
  }, rfl⟩

/-- If `hpF.f + g_lin` is constant on `G` (equal to its value at `δ_bound`), then the direction of `affineSpan ℝ G` is contained in the kernel of that linear functional. -/
lemma direction_sub_ker_of_exposed_intersection {n : ℕ} {P : Polytope n}
    (hpF : SupportingHyperplane P)
    (g_lin : CoeffVec n →ₗ[ℝ] ℝ)
    (δ_bound : CoeffVec n)
    (G : Set (CoeffVec n))
    (hδ_in_G : δ_bound ∈ G)
    (h_const : ∀ x ∈ G, (hpF.f + g_lin) x = hpF.c + g_lin δ_bound) :
    (affineSpan ℝ G).direction ≤
      LinearMap.ker (hpF.f + g_lin : CoeffVec n →ₗ[ℝ] ℝ) := by
  let g_new : CoeffVec n →ₗ[ℝ] ℝ := hpF.f + g_lin
  have h_base : δ_bound ∈ affineSpan ℝ G :=
    subset_affineSpan ℝ G hδ_in_G
  intro v hv
  have h_plus : δ_bound + v ∈ affineSpan ℝ G := by
    have h_vadd :
        v +ᵥ δ_bound ∈ affineSpan ℝ G :=
      AffineSubspace.vadd_mem_of_mem_direction hv h_base
    simpa [vadd_eq_add, add_comm] using h_vadd
  -- Step 3:
  have h_aff_const :
      ∀ x ∈ affineSpan ℝ G,
        g_new x = hpF.c + g_lin δ_bound := by
    intro x hx
    refine affineSpan_induction hx ?_ ?_
    · simp only [g_new]
      exact h_const
    · intros c u v w h1 h2 h3
      rw [vsub_eq_sub, vadd_eq_add]
      simp only [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_sub]
      rw [h1, h2, h3]
      ring_nf
      simp only [smul_eq_mul, mul_zero, add_zero]
  have h_val_base :
      g_new δ_bound = hpF.c + g_lin δ_bound :=
    h_aff_const δ_bound h_base
  have h_val_plus :
      g_new (δ_bound + v) = hpF.c + g_lin δ_bound :=
    h_aff_const (δ_bound + v) h_plus
  have h_linear :
      g_new (δ_bound + v) = g_new δ_bound + g_new v := by
    simp [g_new, map_add]
  rw [h_linear, h_val_base] at h_val_plus
  have hv_zero : g_new v = 0 := by
    linarith
  exact hv_zero

/-- An exposed face of a polytope is compact. -/
lemma isExposedFace_isCompact {n : ℕ} (P : Polytope n) {F : Set (CoeffVec n)}
    (hF : IsExposedFace P F) : IsCompact F := by
  obtain ⟨hp, rfl⟩ := hF
  unfold ExposedFace
  refine P.isCompact.inter_right ?_
  exact isClosed_eq (LinearMap.continuous_of_finiteDimensional hp.f) continuous_const

/-- An exposed face of a polytope is convex. -/
lemma isExposedFace_convex {n : ℕ} (P : Polytope n) {F : Set (CoeffVec n)}
    (hF : IsExposedFace P F) : Convex ℝ F := by
  obtain ⟨hp, rfl⟩ := hF
  unfold ExposedFace
  refine Convex.inter (convex_convexHull ℝ _) ?_
  intro x hx y hy a b ha hb hab
  have hx' : hp.f x = hp.c := hx
  have hy' : hp.f y = hp.c := hy
  calc
    hp.f (a • x + b • y) = hp.f (a • x) + hp.f (b • y) := by simp
    _ = a • hp.f x + b • hp.f y := by simp
    _ = a • hp.c + b • hp.c := by simp [hx', hy']
    _ = (a + b) • hp.c := by rw [← add_smul]
    _ = 1 • hp.c := by simp [hab]
    _ = hp.c := by simp

/-- An exposed face of `P` is contained in `P.Ω`. -/
lemma isExposedFace_subset_Ω {n : ℕ} {P : Polytope n} {F : Set (CoeffVec n)}
    (hF : IsExposedFace P F) : F ⊆ P.Ω := by
  obtain ⟨hp, rfl⟩ := hF; exact Set.inter_subset_left

/-- If a point lies on the frontier of an exposed face of a polytope,
    it also lies on the frontier of the polytope itself. -/
lemma frontier_of_exposed_face_implies_frontier_of_polytope {n : ℕ} (P : Polytope n)
    (F : Set (CoeffVec n)) (hpF : SupportingHyperplane P) (hF_expr : F = ExposedFace hpF)
    (δ_bound : CoeffVec n) (hδ_bound_in_F : δ_bound ∈ F) (_hδ_bound_front : δ_bound ∈ frontier F) :
    δ_bound ∈ frontier P.Ω := by
  have h_not_interior : δ_bound ∉ interior P.Ω := by
    intro h_int
    have hx_support : hpF.f δ_bound = hpF.c := by
      have : δ_bound ∈ ExposedFace hpF := hF_expr ▸ hδ_bound_in_F
      exact this.2
    have h_exists_pos_dir : ∃ w : CoeffVec n, hpF.f w > 0 := by
      by_cases h : ∃ w, hpF.f w > 0
      · exact h
      · push_neg at h
        have hzero : hpF.f = 0 := by
          ext v
          apply le_antisymm
          · simp only [coe_comp, coe_single, Function.comp_apply, LinearMap.zero_comp, zero_apply]
            apply h
          · have hneg : hpF.f (-Pi.single v 1) ≤ 0 := h (-Pi.single v 1)
            rw [map_neg] at hneg
            exact neg_nonpos.mp hneg
        exact absurd hzero hpF.nonzero
    obtain ⟨w, hw⟩ := h_exists_pos_dir
    have h_open : IsOpen (interior P.Ω) := isOpen_interior
    have h_ball_surround : ∃ r > 0, Metric.ball δ_bound r ⊆ interior P.Ω :=
      (Metric.isOpen_iff.mp h_open) δ_bound h_int
    rcases h_ball_surround with ⟨r, hr_pos, h_ball⟩
    have h_norm_w_pos : 0 < ‖w‖ := by
      have hw_nonzero : w ≠ 0 := by
        intro hzero
        have : hpF.f w = 0 := by rw [hzero, LinearMap.map_zero]
        linarith
      exact norm_pos_iff.mpr hw_nonzero
    set ε := r / (2 * ‖w‖) with hε_def
    have hε_pos : 0 < ε := div_pos (by linarith) (by nlinarith)
    have h_mem_ball : δ_bound + ε • w ∈ Metric.ball δ_bound r := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h_sub : (δ_bound + ε • w) - δ_bound = ε • w := by abel
      rw [h_sub, norm_smul]
      have h_ε_mul : ε * ‖w‖ = r / 2 := by
        dsimp [ε]; field_simp [h_norm_w_pos.ne.symm]
      have h_norm_ε : ‖ε‖ = ε := abs_of_pos hε_pos
      rw [h_norm_ε, h_ε_mul]
      nlinarith
    have h_mem_int : δ_bound + ε • w ∈ interior P.Ω := h_ball h_mem_ball
    have h_mem_P : δ_bound + ε • w ∈ P.Ω := interior_subset h_mem_int
    have h_val : hpF.f (δ_bound + ε • w) = hpF.c + ε * hpF.f w := by
      simp [hx_support, map_add, map_smul, smul_eq_mul]
    have h_upper := hpF.upper_bound (δ_bound + ε • w) h_mem_P
    nlinarith
  have h_Ω : δ_bound ∈ P.Ω := by
    have : δ_bound ∈ ExposedFace hpF := hF_expr ▸ hδ_bound_in_F
    exact this.1
  exact ⟨subset_closure h_Ω, h_not_interior⟩

/--
An exposed face of a polytope P.Ω that contains a point of the interior of P.Ω
must be the whole polytope. (Any supporting hyperplane achieving its max on P.Ω
at an interior point must be constant on P.Ω.)
-/
private lemma exposed_face_eq_Ω_of_mem_interior {n : ℕ} (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hδ_F : CoeffVec n) (hδ_F_in_F : hδ_F ∈ F) (hδ_F_int : hδ_F ∈ interior P.Ω) :
    F = P.Ω := by
  obtain ⟨hp, hF_expr⟩ := hF_exp
  rw [hF_expr, ExposedFace]
  ext x
  constructor
  · intro hx; exact hx.1
  · intro hxΩ
    have hp_f_hδ : hp.f hδ_F = hp.c := (hF_expr ▸ hδ_F_in_F).2
    have hpx_le : hp.f x ≤ hp.c := hp.upper_bound x hxΩ
    by_cases hx_eq : hp.f x = hp.c
    · exact ⟨hxΩ, hx_eq⟩
    · have hx_strict : hp.f x < hp.c := lt_of_le_of_ne hpx_le hx_eq
      -- Pick ε > 0 such that B(hδ_F, ε) ⊆ interior P.Ω
      obtain ⟨ε, hε_pos, h_ball⟩ := Metric.isOpen_iff.mp isOpen_interior hδ_F hδ_F_int
      have h_ball_sub : Metric.ball hδ_F ε ⊆ P.Ω := h_ball.trans interior_subset
      let u := x - hδ_F
      have hu_nonzero : u ≠ 0 := by
        intro hzero
        have : x = hδ_F := by
          apply sub_eq_zero.mp ?_
          exact hzero
        have : hp.f x = hp.c := by simpa [this] using hp_f_hδ
        linarith
      have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_nonzero
      let u_normed := (1 / ‖u‖) • u
      have hnorm_u_normed : ‖u_normed‖ = 1 := by
        calc
          ‖u_normed‖ = ‖(1 / ‖u‖) • u‖ := rfl
          _ = |1 / ‖u‖| * ‖u‖ := norm_smul _ _
          _ = (1 / ‖u‖) * ‖u‖ := by rw [abs_of_pos (by positivity : 0 < 1 / ‖u‖)]
          _ = 1 := by field_simp [hnorm_pos.ne']
      -- Both hδ_F ± (ε/2)·u_normed are in B(hδ_F, ε) ⊆ P.Ω
      have h_mem_pos : hδ_F + ((ε / 2) : ℝ) • u_normed ∈ Metric.ball hδ_F ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        have h_sub : (hδ_F + ((ε / 2) : ℝ) • u_normed) - hδ_F = ((ε / 2) : ℝ) • u_normed := by
          abel
        rw [h_sub, norm_smul]
        rw [hnorm_u_normed, mul_comm, Real.norm_of_nonneg (by positivity : 0 ≤ ε / 2)]
        nlinarith
      have h_mem_neg : hδ_F - ((ε / 2) : ℝ) • u_normed ∈ Metric.ball hδ_F ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        have h_sub : (hδ_F - ((ε / 2) : ℝ) • u_normed) - hδ_F = -(((ε / 2) : ℝ) • u_normed) := by
          abel
        rw [h_sub, norm_neg, norm_smul]
        rw [hnorm_u_normed, mul_comm, Real.norm_of_nonneg (by positivity : 0 ≤ ε / 2)]
        nlinarith
      have hp_pos : hp.f (hδ_F + ((ε / 2) : ℝ) • u_normed) ≤ hp.c :=
        hp.upper_bound _ (h_ball_sub h_mem_pos)
      have hp_neg : hp.f (hδ_F - ((ε / 2) : ℝ) • u_normed) ≤ hp.c :=
        hp.upper_bound _ (h_ball_sub h_mem_neg)
      -- Expand using linearity
      have hp_pos_expand : hp.f hδ_F + ((ε / 2) : ℝ) * hp.f u_normed ≤ hp.c := by
        simpa [map_add, map_smul, hp_f_hδ] using hp_pos
      have hp_neg_expand : hp.f hδ_F - ((ε / 2) : ℝ) * hp.f u_normed ≤ hp.c := by
        simpa [map_sub, map_smul, hp_f_hδ] using hp_neg
      -- From hp_pos_expand: (ε/2) * hp.f u_normed ≤ 0
      -- From hp_neg_expand: -(ε/2) * hp.f u_normed ≤ 0
      -- Since ε/2 > 0, we get hp.f u_normed = 0
      have h1 : hp.f u_normed ≤ 0 := by nlinarith
      have h2 : hp.f u_normed ≥ 0 := by nlinarith
      have hp_f_u_normed_zero : hp.f u_normed = 0 := by linarith
      -- Therefore hp.f u = 0
      have hp_f_u_zero : hp.f u = 0 := by
        have h_eq : u = ‖u‖ • u_normed := by
          dsimp [u_normed]
          have h_scalar : (1 : ℝ) = (‖u‖ : ℝ) * (1 / ‖u‖) := by
            field_simp [hnorm_pos.ne']
          calc
            u = (1 : ℝ) • u := by simp
            _ = ((‖u‖ : ℝ) * (1 / ‖u‖)) • u := by
              rw [h_scalar]
              simp
              grind
            _ = ‖u‖ • ((1 / ‖u‖) • u) := by simp [smul_smul]
        rw [h_eq, hp.f.map_smul, hp_f_u_normed_zero, smul_zero]
      -- Hence hp.f x = hp.c, contradiction
      have : hp.f x = hp.c := by
        calc
          hp.f x = hp.f (hδ_F + (x - hδ_F)) := by simp
          _ = hp.f (hδ_F + u) := rfl
          _ = hp.f hδ_F + hp.f u := by simp
          _ = hp.c := by simp [hp_f_hδ, hp_f_u_zero]
      linarith

/--
Relint version of the full-dim bridge: if an exposed face of `P.Ω` contains a
point of the *relative* (intrinsic) interior of `P.Ω`, then it is the whole
polytope. This transports relative-boundary hypotheses from an exposed face
`F` to relative-boundary points of `P.Ω` in the non-full-dimensional setting
(where the ambient interior may be empty).
-/
lemma exposed_face_eq_Ω_of_mem_relint {n : ℕ} (P : Polytope n) (δ : CoeffVec n)
    (F : Set (CoeffVec n)) (hp : SupportingHyperplane P) (hF_eq : F = ExposedFace hp)
    (hδ_in_F : δ ∈ F) (hδ_relint : δ ∈ intrinsicInterior ℝ P.Ω) :
    F = P.Ω := by
  have hδ_in_Face : δ ∈ ExposedFace hp := hF_eq ▸ hδ_in_F
  have hδ_in_Ω : δ ∈ P.Ω := hδ_in_Face.1
  have hδ_f : hp.f δ = hp.c := hδ_in_Face.2
  -- The exposing functional is constant (`= hp.c`) on all of `P.Ω`.
  have hf_const : ∀ y ∈ P.Ω, hp.f y = hp.c := by
    intro y hy
    by_cases h_yδ : y = δ
    · simpa [h_yδ] using hδ_f
    · by_contra hne
      have hy_le : hp.f y ≤ hp.c := hp.upper_bound y hy
      have hylt : hp.f y < hp.c := lt_of_le_of_ne hy_le hne
      have hu_ne : (y - δ) ≠ (0 : CoeffVec n) := sub_ne_zero.mpr h_yδ
      have hnorm : 0 < ‖(y - δ : CoeffVec n)‖ := norm_pos_iff.mpr hu_ne
      -- A ball around `δ` intersected with `affΩ` stays in `Ω` (relint membership).
      obtain ⟨rr, hrr_pos, hball⟩ : ∃ rr : ℝ, 0 < rr ∧ ∀ z : CoeffVec n,
          dist z δ < rr → z ∈ affineSpan ℝ P.Ω → z ∈ P.Ω := by
        have hδ_int : δ ∈ (Subtype.val : affineSpan ℝ P.Ω → CoeffVec n) '' interior
            ((Subtype.val : affineSpan ℝ P.Ω → CoeffVec n)⁻¹' P.Ω) := by
          simpa [intrinsicInterior] using hδ_relint
        obtain ⟨δ₀ₐ, hδ₀ₐ_int, hδ₀ₐ_coe⟩ := hδ_int
        let affΩ : AffineSubspace ℝ (CoeffVec n) := affineSpan ℝ P.Ω
        have hδ_aff : δ ∈ affΩ := subset_affineSpan ℝ P.Ω hδ_in_Ω
        let V : Submodule ℝ (CoeffVec n) := affΩ.direction
        -- Affine homeomorphism `V ≃ₜ affΩ` with base point `δ`.
        let τ : V ≃ₜ affΩ := {
          toFun := fun v => ⟨δ +ᵥ (v : CoeffVec n), by
            have h := AffineSubspace.vadd_mem_of_mem_direction v.2 hδ_aff
            simpa [vadd_eq_add, add_comm] using h⟩
          invFun := fun p => ⟨(p : CoeffVec n) -ᵥ δ,
            AffineSubspace.vsub_mem_direction p.property hδ_aff⟩
          left_inv := by intro v; ext; simp [vadd_vsub]
          right_inv := by intro p; ext; simp [vsub_vadd]
          continuous_toFun := by
            refine Continuous.subtype_mk ?_ ?_
            exact continuous_const.add continuous_subtype_val
        }
        have hτ0_val : ((τ 0 : affΩ) : CoeffVec n) = δ := by
          simp [τ, vadd_eq_add]
        have hτ0_pt : τ 0 = δ₀ₐ := Subtype.ext (hτ0_val.trans hδ₀ₐ_coe.symm)
        have hτ0_int : τ 0 ∈ interior
            ((Subtype.val : affΩ → CoeffVec n)⁻¹' P.Ω) := hτ0_pt ▸ hδ₀ₐ_int
        -- Pull the openness back to `V` through the homeomorphism `τ`.
        have h_pull : τ ⁻¹' interior ((Subtype.val : affΩ → CoeffVec n)⁻¹' P.Ω)
            = interior (τ ⁻¹' ((Subtype.val : affΩ → CoeffVec n)⁻¹' P.Ω)) :=
          τ.preimage_interior _
        have h0_int : (0 : V)
            ∈ interior (τ ⁻¹' ((Subtype.val : affΩ → CoeffVec n)⁻¹' P.Ω)) := by
          rw [← h_pull, Set.mem_preimage, hτ0_pt]
          exact hδ₀ₐ_int
        obtain ⟨rr, hrr_pos, hballV⟩ := Metric.isOpen_iff.mp isOpen_interior (0 : V) h0_int
        refine ⟨rr, hrr_pos, fun z hz_ball hz_aff => ?_⟩
        have hu_mem : (z - δ) ∈ affΩ.direction :=
          AffineSubspace.vsub_mem_direction hz_aff hδ_aff
        let u : V := ⟨z - δ, hu_mem⟩
        have hu_ball : (u : V) ∈ Metric.ball (0 : V) rr := by
          rw [Metric.mem_ball]
          change dist ((u : V) : CoeffVec n) (0 : CoeffVec n) < rr
          simpa [dist_eq_norm, u] using hz_ball
        have h_uA : τ u ∈ ((Subtype.val : affΩ → CoeffVec n)⁻¹' P.Ω) :=
          (hballV.trans interior_subset) hu_ball
        simp only [Set.mem_preimage] at h_uA
        have hτu_val : ((τ u : affΩ) : CoeffVec n) = z := by
          simp [τ, u, vadd_eq_add]
        rw [hτu_val] at h_uA
        exact h_uA
      -- Slide `y` a little past `δ`; the point stays in `Ω` but has a larger value.
      have hu_dir2 : (δ - y) ∈ (affineSpan ℝ P.Ω).direction :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ P.Ω hδ_in_Ω)
          (subset_affineSpan ℝ P.Ω hy)
      set s : ℝ := rr / (2 * ‖(y - δ : CoeffVec n)‖) with hs_def
      have hs_pos : 0 < s := by
        rw [hs_def]
        exact div_pos hrr_pos (by nlinarith)
      have h_sub_norm : ((δ - s • (y - δ)) - δ : CoeffVec n) = s • (δ - y) := by
        simp only [sub_smul, smul_sub]
        abel
      have h_neg : (δ - y : CoeffVec n) = -((y - δ : CoeffVec n)) := by abel
      have h_norm_eq : ‖(δ - y : CoeffVec n)‖ = ‖(y - δ : CoeffVec n)‖ := by
        rw [h_neg, norm_neg]
      have hdist_lt : dist (δ - s • (y - δ)) δ < rr := by
        rw [dist_eq_norm, h_sub_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos]
        rw [h_norm_eq, hs_def]
        have h2N : (0 : ℝ) < 2 * ‖(y - δ : CoeffVec n)‖ := by nlinarith
        have hhalf : rr / (2 * ‖(y - δ : CoeffVec n)‖) * ‖(y - δ : CoeffVec n)‖ = rr / 2 := by
          field_simp
        rw [hhalf]
        linarith
      have hh : (δ - s • (y - δ) : CoeffVec n) = δ + s • (δ - y) := by
        simp only [sub_smul, smul_sub]
        abel
      have h_mem_aff : (δ - s • (y - δ)) ∈ affineSpan ℝ P.Ω := by
        have h2 : (s • (δ - y) : CoeffVec n) ∈ (affineSpan ℝ P.Ω).direction :=
          Submodule.smul_mem _ _ hu_dir2
        have h3 := AffineSubspace.vadd_mem_of_mem_direction h2
          (subset_affineSpan ℝ P.Ω hδ_in_Ω)
        have h3' : (δ + s • (δ - y) : CoeffVec n) ∈ affineSpan ℝ P.Ω := by
          simpa [vadd_eq_add, add_comm] using h3
        rw [hh]
        exact h3'
      have h_mem_P : (δ - s • (y - δ)) ∈ P.Ω := hball _ hdist_lt h_mem_aff
      have h_pos_prod : 0 < s * (hp.c - hp.f y) := mul_pos hs_pos (by linarith)
      have h_val : hp.f (δ - s • (y - δ)) = hp.c + s * (hp.c - hp.f y) := by
        rw [map_sub, map_smul, map_sub, smul_eq_mul, hδ_f]
        ring
      have h_le : hp.f (δ - s • (y - δ)) ≤ hp.c := hp.upper_bound _ h_mem_P
      rw [h_val] at h_le
      linarith
  rw [hF_eq]
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hxΩ
    exact ⟨hxΩ, hf_const x hxΩ⟩
/--
Full-dimensional bridge: if the ambient interior of `P.Ω` is nonempty (i.e. the
polytope is full-dimensional), the intrinsic interior equals the topological
interior. Not used by the relint-threaded arguments below (which never go
through ambient interiors), but kept for the full-dim corollary package.
-/
private lemma intrinsicInterior_polytope_eq_interior {n : ℕ} (P : Polytope n)
    (h_int_nonempty : (interior P.Ω).Nonempty) :
    intrinsicInterior ℝ P.Ω = interior P.Ω := by
  have h_convex : Convex ℝ P.Ω := convex_convexHull ℝ _
  have h_span_top : affineSpan ℝ P.Ω = ⊤ :=
    (h_convex.interior_nonempty_iff_affineSpan_eq_top).mp h_int_nonempty
  let A := affineSpan ℝ P.Ω
  have hA_set_eq_univ : (A : Set (CoeffVec n)) = Set.univ := by
    simpa [A] using congrArg (fun (s : AffineSubspace ℝ (CoeffVec n)) => (s : Set (CoeffVec n))) h_span_top
  have h_mem : ∀ x : CoeffVec n, x ∈ (A : Set (CoeffVec n)) := by
    simpa [hA_set_eq_univ]
  let h_homeo : Homeomorph A (CoeffVec n) := {
    toFun := Subtype.val
    invFun := λ x => ⟨x, h_mem x⟩
    left_inv := λ _ => rfl
    right_inv := λ _ => rfl
    continuous_toFun := by continuity
    continuous_invFun := by continuity
  }
  calc
    intrinsicInterior ℝ P.Ω = (Subtype.val : A → CoeffVec n) ''
      interior ((Subtype.val : A → CoeffVec n)⁻¹' P.Ω) := rfl
    _ = interior ((Subtype.val : A → CoeffVec n) '' ((Subtype.val : A → CoeffVec n)⁻¹' P.Ω)) := by
      have h_image := h_homeo.image_interior ((Subtype.val : A → CoeffVec n)⁻¹' P.Ω)
      simpa using h_image
    _ = interior (P.Ω ∩ (A : Set (CoeffVec n))) := by
      simp [Set.image_preimage_eq_inter_range, Subtype.range_coe]
    _ = interior (P.Ω ∩ Set.univ) := by rw [hA_set_eq_univ]
    _ = interior P.Ω := by simp


/--
If `g_Ω` and `hp.f` sum to a constant `hp.c + g_c` over a set `G` contained
in an exposed face of `P`, then any direction `v` in the affine span of `G`
lies in the kernel of `g_Ω`. In other words, `g_Ω` is constant along
the affine subspace generated by `G`.
-/
private lemma direction_sub_ker_gΩ {n : ℕ} {P : Polytope n}
    (hp : SupportingHyperplane P) (g_Ω : CoeffVec n →ₗ[ℝ] ℝ) (g_c : ℝ)
    (δ_bound : CoeffVec n) (G : Set (CoeffVec n))
    (hδ_in_G : δ_bound ∈ G)
    (hG_sub_ExF : G ⊆ ExposedFace hp)
    (h_const : ∀ x ∈ G, (hp.f + g_Ω) x = hp.c + g_c) :
    (affineSpan ℝ G).direction ≤ LinearMap.ker g_Ω := by
  have h_g_const_on_G : ∀ x ∈ G, g_Ω x = g_c := by
    intro x hx
    have hx_ExF : x ∈ ExposedFace hp := hG_sub_ExF hx
    have h_hp_f_x : hp.f x = hp.c := hx_ExF.2
    have h_sum : (hp.f + g_Ω) x = hp.c + g_c := h_const x hx
    simp [h_hp_f_x] at h_sum
    linarith
  have h_base : δ_bound ∈ affineSpan ℝ G := subset_affineSpan ℝ G hδ_in_G
  intro v hv
  have h_plus : δ_bound + v ∈ affineSpan ℝ G := by
    have h_vadd : v +ᵥ δ_bound ∈ affineSpan ℝ G :=
      AffineSubspace.vadd_mem_of_mem_direction hv h_base
    simpa [vadd_eq_add, add_comm] using h_vadd
  have h_aff_const : ∀ x ∈ affineSpan ℝ G, g_Ω x = g_c := by
    intro x hx
    refine affineSpan_induction hx (fun y hy => h_g_const_on_G y hy) ?_
    intro c u v w h1 h2 h3
    rw [vsub_eq_sub, vadd_eq_add]
    simp only [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_sub]
    rw [h1, h2, h3]
    simp
  have h_val_base : g_Ω δ_bound = g_c := h_aff_const δ_bound h_base
  have h_val_plus : g_Ω (δ_bound + v) = g_c := h_aff_const (δ_bound + v) h_plus
  rw [map_add] at h_val_plus
  rw [h_val_base] at h_val_plus
  have hv_zero : g_Ω v = 0 := by linarith
  exact hv_zero

/--
Strengthening of `direction_sub_ker_gΩ`: the direction of the affine span of `G`
is contained in the intersection of the direction of the affine span of `F`
(which equals the exposed face) with the kernel of `g_Ω`.
-/
private lemma direction_sub_inf_ker_gΩ {n : ℕ} {P : Polytope n}
    (hp : SupportingHyperplane P) (g_Ω : CoeffVec n →ₗ[ℝ] ℝ) (g_c : ℝ)
    (δ_bound : CoeffVec n) (F G : Set (CoeffVec n))
    (hδ_in_G : δ_bound ∈ G)
    (hG_sub_ExF : G ⊆ ExposedFace hp)
    (hF_eq : F = ExposedFace hp)
    (h_const : ∀ x ∈ G, (hp.f + g_Ω) x = hp.c + g_c) :
    (affineSpan ℝ G).direction ≤ (affineSpan ℝ F).direction ⊓ LinearMap.ker g_Ω := by
  have h_dir_le_F_dir : (affineSpan ℝ G).direction ≤ (affineSpan ℝ F).direction := by
    have hG_sub_F : G ⊆ F := by
      intro x hx; rw [hF_eq]; exact hG_sub_ExF hx
    exact AffineSubspace.direction_le (affineSpan_mono (k := ℝ) hG_sub_F)
  have h_dir_le_ker : (affineSpan ℝ G).direction ≤ LinearMap.ker g_Ω :=
    direction_sub_ker_gΩ hp g_Ω g_c δ_bound G hδ_in_G hG_sub_ExF h_const
  exact le_inf h_dir_le_F_dir h_dir_le_ker

/-- For a non-real `s ∈ ℂ` and a boundary point `δ_bound` of `P.Ω` in `P_sc n s`, there exists an exposed face `F` of `P` containing `δ_bound` and with `s ∈ RootSpaceSet F`. -/
lemma exists_exposed_face_containing_boundary_point_complex {n : ℕ} (P : Polytope n)
    (s : ℂ) (δ_bound : CoeffVec n)
    (hδ_bound_front : δ_bound ∈ frontier P.Ω)
    (hδ_bound_Psc : δ_bound ∈ PscSet n s) :
    ∃ F : Set (CoeffVec n), IsExposedFace P F ∧ δ_bound ∈ F ∧ s ∈ RootSpaceSet F := by
  have hδ_bound_in_Ω : δ_bound ∈ P.Ω := frontier_point_in_Ω P δ_bound hδ_bound_front
  by_cases htop : (affineSpan ℝ P.Ω).direction = ⊤
  · -- Ambient-full-dimensional case: interior nonempty, Hahn-Banach applies.
    have hspan_top : affineSpan ℝ P.Ω = ⊤ := by
      have hne : ((affineSpan ℝ P.Ω : AffineSubspace ℝ (CoeffVec n)) :
          Set (CoeffVec n)).Nonempty :=
        ⟨δ_bound, subset_affineSpan ℝ P.Ω hδ_bound_in_Ω⟩
      rw [← AffineSubspace.direction_eq_top_iff_of_nonempty hne]
      exact htop
    have h_int_nonempty : (interior P.Ω).Nonempty :=
      (Convex.interior_nonempty_iff_affineSpan_eq_top
        (convex_convexHull ℝ (P.vertices : Set (CoeffVec n)))).mpr hspan_top
    have hδ_bound_not_int : δ_bound ∉ interior P.Ω :=
      frontier_point_not_interior P δ_bound hδ_bound_front
    have h_convex : Convex ℝ P.Ω := convex_convexHull ℝ _
    have h_int_convex : Convex ℝ (interior P.Ω) := h_convex.interior
    have h_int_open : IsOpen (interior P.Ω) := isOpen_interior
    obtain ⟨f, hf_strict⟩ :=
      geometric_hahn_banach_open_point h_int_convex h_int_open hδ_bound_not_int
    have hf_ne : f ≠ 0 := supporting_func_nonzero P f δ_bound hf_strict h_int_nonempty
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
    have hc_upper : ∀ x ∈ P.Ω, f_lin x ≤ c :=
      supporting_hyperplane_upper_bound P f c hf_strict h_int_nonempty
    let hp : SupportingHyperplane P := {
      f           := f_lin
      c           := c
      nonzero     := hf_lin_ne
      upper_bound := hc_upper
      touches     := ⟨δ_bound, hδ_bound_in_Ω, rfl⟩
    }
    have hδ_in_face : δ_bound ∈ ExposedFace hp := by
      unfold ExposedFace
      simp only [Set.mem_setOf_eq]
      exact ⟨hδ_bound_in_Ω, rfl⟩
    have h_isRoot : ((polyOfVec δ_bound).map (algebraMap ℝ ℂ)).IsRoot s := by
      have hzero : evalAtComplex s δ_bound = 0 := hδ_bound_Psc
      simpa [evalAtComplex] using hzero
    have hs_in_rootspace : s ∈ RootSpaceSet (ExposedFace hp) :=
      rootspace_mem_of_isRoot s δ_bound h_isRoot (ExposedFace hp) hδ_in_face
    exact ⟨ExposedFace hp, ⟨hp, rfl⟩, hδ_in_face, hs_in_rootspace⟩
  · -- Degenerate family in a proper affine slice: `Ω` itself is an exposed face.
    have h_isRoot : ((polyOfVec δ_bound).map (algebraMap ℝ ℂ)).IsRoot s := by
      have hzero : evalAtComplex s δ_bound = 0 := hδ_bound_Psc
      simpa [evalAtComplex] using hzero
    exact ⟨P.Ω, isExposedFace_Ω_of_direction_ne_top P htop, hδ_bound_in_Ω,
      rootspace_mem_of_isRoot s δ_bound h_isRoot P.Ω hδ_bound_in_Ω⟩


end CoeffBox
