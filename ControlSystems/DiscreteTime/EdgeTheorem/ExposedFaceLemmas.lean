module

public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeTheoremDefs
public import Mathlib.Analysis.Convex.Intrinsic
public import ControlSystems.DiscreteTime.EdgeTheorem.BasicLemmas


@[expose] public section

open Polynomial
open Affine
open FiniteDimensional
open LinearMap
open Set

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

/-- Evaluation at `(r : ℂ)` of the complexified polynomial commutes with the algebraic embedding of the real evaluation. -/
private lemma eval_root_comm {n : ℕ} (r : ℝ) (δ : CoeffVec n) :
    eval (↑r) (map (algebraMap ℝ ℂ) (polyOfVec δ)) = (algebraMap ℝ ℂ) (eval r (polyOfVec δ)) := by
  simp [polyOfVec, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
    map_sum, map_mul, map_pow]

/-- If `δ_bound ∈ P_sr n r` and `δ_bound ∈ F`, then `(r : ℂ)` is in the root space set of `F`. -/
lemma rootspace_mem_of_eval_zero {n : ℕ} (r : ℝ) (δ_bound : CoeffVec n)
    (hδ_bound_Psr : δ_bound ∈ (P_sr n r : Set (CoeffVec n)))
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
    δ ∈ (P_sr n r : Set (CoeffVec n)) := by
  unfold P_sr
  change evalLinear r δ = 0
  unfold Polynomial.IsRoot at h
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_eval_map, eval_root_comm r δ] at h
  exact_mod_cast (map_eq_zero (algebraMap ℝ ℂ)).mp h

/-- For any boundary point `δ_bound` of `P.Ω` that also lies in `P_sr n r`, there exists an exposed face `F` of `P` containing `δ_bound` and whose root space set contains `(r : ℂ)`. -/
lemma exists_exposed_face_containing_boundary_point {n : ℕ} (P : Polytope n)
    (r : ℝ) (δ_bound : CoeffVec n)
    (hδ_bound_front : δ_bound ∈ frontier P.Ω)
    (hδ_bound_Psr : δ_bound ∈ (P_sr n r : Set (CoeffVec n)))
    (h_int_nonempty : (interior P.Ω).Nonempty) :
    ∃ F : Set (CoeffVec n), IsExposedFace P F ∧ δ_bound ∈ F ∧ (r : ℂ) ∈ RootSpaceSet F := by
  have hδ_bound_in_Ω : δ_bound ∈ P.Ω := frontier_point_in_Ω P δ_bound hδ_bound_front
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
The intrinsic interior of a polytope P.Ω with nonempty interior equals the
topological interior (since affine span of P.Ω is the full ambient).
-/
private lemma intrinsicInterior_polytope_eq_interior {n : ℕ} (P : Polytope n) :
    intrinsicInterior ℝ P.Ω = interior P.Ω := by
  have h_convex : Convex ℝ P.Ω := convex_convexHull ℝ _
  have h_span_top : affineSpan ℝ P.Ω = ⊤ :=
    (h_convex.interior_nonempty_iff_affineSpan_eq_top).mp P.interior_nonempty
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

/-- If `x ∈ F` and `y` is in the intrinsic interior of a convex set `F`, then any convex combination `(1 - t) • x + t • y` with `0 < t < 1` also lies in the intrinsic interior. -/
lemma mem_intrinsicInterior_add_smul (F : Set (CoeffVec n)) (hF_convex : Convex ℝ F)
    (hx : x ∈ F) (hy : y ∈ intrinsicInterior ℝ F) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (1 - t) • x + t • y ∈ intrinsicInterior ℝ F := by
  let affF := affineSpan ℝ F
  have hy' : y ∈ (↑) '' interior ((↑)⁻¹' F : Set affF) := by
    simpa [intrinsicInterior] using hy
  rcases hy' with ⟨y_aff, hy_aff_int, hy_eq⟩
  let V := affF.direction
  let base : affF := ⟨x, subset_affineSpan ℝ F hx⟩
  haveI : Nonempty affF := ⟨base⟩
  let A : affF ≃ₜ V := {
    toFun    := fun p => ⟨(p : CoeffVec n) - x,
      AffineSubspace.vsub_mem_direction p.2 (subset_affineSpan ℝ F hx)⟩
    invFun   := fun v => ⟨(v : CoeffVec n) +ᵥ x,
      AffineSubspace.vadd_mem_of_mem_direction v.2 (subset_affineSpan ℝ F hx)⟩
    left_inv  := by
      intro p; ext; simp [vadd_eq_add, vsub_eq_sub]
    right_inv := by
      intro v; ext; simp [vadd_eq_add, vsub_eq_sub]
    continuous_toFun  := by
      apply Continuous.subtype_mk
      apply Continuous.sub
      · exact continuous_subtype_val
      · exact continuous_const
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply Continuous.add
      · exact continuous_subtype_val
      · exact continuous_const
  }
  let f : V →ᵃ[ℝ] CoeffVec n :=
    { toFun := λ v => x + (v : CoeffVec n)
      linear := Submodule.subtype V
      map_vadd' := λ v w => by
        dsimp; abel }
  have hS_eq : A '' ((↑)⁻¹' F : Set affF) = f⁻¹' F := by
    ext v; constructor
    · rintro ⟨p, hp, rfl⟩
      have hAp : f (A p) = (p : CoeffVec n) := by
        calc
          f (A p) = x + ((A p : V) : CoeffVec n) := rfl
          _ = x + ((p -ᵥ base : V) : CoeffVec n) := by
            have : A p = (p -ᵥ base : V) := by
              dsimp [A]
              rfl
            simpa [this]
          _ = x + ((p : CoeffVec n) -ᵥ (base : CoeffVec n)) := by
            simpa using congrArg (λ t => x + (t : CoeffVec n)) (AffineSubspace.coe_vsub affF p base)
          _ = x + ((p : CoeffVec n) - (base : CoeffVec n)) := by simp
          _ = x + ((p : CoeffVec n) - x) := rfl
          _ = (p : CoeffVec n) := by simp
      have hmem : f (A p) ∈ F := by
        rw [hAp]
        exact hp
      exact hmem
    · intro hv
      have hfp : f (v : V) ∈ F := by
        simpa using hv
      have h_coe_vadd : ((v : V) +ᵥ base : CoeffVec n) = (v : CoeffVec n) +ᵥ (base : CoeffVec n) := by
        calc
          ((v : V) +ᵥ base : CoeffVec n) = ((v : V) +ᵥ base : affF).val := rfl
          _ = (v : V).val +ᵥ base.val := rfl
          _ = (v : CoeffVec n) +ᵥ (base : CoeffVec n) := rfl
      have h_vadd_eq_add : (v : CoeffVec n) +ᵥ (base : CoeffVec n) = (v : CoeffVec n) + (base : CoeffVec n) := by simp
      have h_base_coe : (base : CoeffVec n) = x := rfl
      have h_eq : ((v : V) +ᵥ base : CoeffVec n) = f (v : V) := by
        calc
          ((v : V) +ᵥ base : CoeffVec n) = (v : CoeffVec n) +ᵥ (base : CoeffVec n) := h_coe_vadd
          _ = (v : CoeffVec n) + (base : CoeffVec n) := h_vadd_eq_add
          _ = (v : CoeffVec n) + x := by simp [base]
          _ = x + (v : CoeffVec n) := by abel
          _ = f (v : V) := rfl
      have : (v : V) +ᵥ base ∈ ((↑)⁻¹' F : Set affF) := by
        simpa [h_eq] using hfp

      refine ⟨(v : V) +ᵥ base, this, ?_⟩
      ext x'
      show ((v +ᵥ base : affF) : CoeffVec n) x' - x x' = (v : CoeffVec n) x'
      have : ((v +ᵥ base : affF) : CoeffVec n) x' = (v : CoeffVec n) x' + x x' := by
        have := h_coe_vadd
        simp [vadd_eq_add] at this
        rw [this, h_base_coe]
        simp [vadd_eq_add]
      linarith

  have hS_convex : Convex ℝ (f⁻¹' F) :=
    hF_convex.affine_preimage f
  have h0 : (0 : V) ∈ f⁻¹' F := by
    simpa [f] using hx
  have h_int : (y_aff -ᵥ base : V) ∈ interior (f⁻¹' F) := by
    have hA_image : A '' interior ((↑)⁻¹' F : Set affF) = interior (f⁻¹' F) := by
      rw [A.image_interior ((↑)⁻¹' F : Set affF)]
      congr 1

    have h_mem' : A y_aff ∈ interior (f⁻¹' F) := by
      rw [← hA_image]
      exact Set.mem_image_of_mem A hy_aff_int
    have : A y_aff = (y_aff -ᵥ base : V) := by
      dsimp [A]; rfl
    rw [this] at h_mem'
    exact h_mem'
  have h_t_mem : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht0, le_of_lt ht1⟩
  have h_add_smul : t • (y_aff -ᵥ base : V) ∈ interior (f⁻¹' F) := by
    have := hS_convex.add_smul_mem_interior h0 (by simpa [zero_add] using h_int) h_t_mem
    simpa [zero_add] using this
  have h_mem_int_C : (t • (y_aff -ᵥ base : V) : V) +ᵥ base ∈ interior ((↑)⁻¹' F : Set affF) := by
    have h_eq_symm_image : A.symm '' (f⁻¹' F) = ((↑)⁻¹' F : Set affF) := by
      calc
        A.symm '' (f⁻¹' F) = A.symm '' (A '' ((↑)⁻¹' F : Set affF)) := by rw [hS_eq]
        _ = (A.symm ∘ A) '' ((↑)⁻¹' F : Set affF) := by rw [Set.image_comp]
        _ = _root_.id '' ((↑)⁻¹' F : Set affF) := by
          have : A.symm ∘ A = _root_.id := by
            ext p; simp
          rw [this]
        _ = ((↑)⁻¹' F : Set affF) := by simp
    have h_image_eq : A.symm '' interior (f⁻¹' F) =
        interior ((↑)⁻¹' F : Set affF) := by
      have h1 : A.symm '' interior (f⁻¹' F) =
                interior (A.symm '' (f⁻¹' F)) := by
        exact Homeomorph.image_interior A.symm (f⁻¹' F)
      have h2 : A.symm '' (f⁻¹' F) = A.symm '' (A '' ((↑)⁻¹' F : Set affF)) := by
        rw [hS_eq]
      have h3 : A.symm '' (A '' ((↑)⁻¹' F : Set affF)) = ((↑)⁻¹' F : Set affF) := by
        rw [← Set.image_comp]
        have : A.symm ∘ A = id := Homeomorph.symm_comp_self A
        rw [this, Set.image_id]
      rw [h1, h2, h3]
    have h_mem_image' : A.symm (t • (y_aff -ᵥ base : V)) ∈ interior ((↑)⁻¹' F : Set affF) := by
      rw [← h_image_eq]
      exact Set.mem_image_of_mem A.symm h_add_smul
    have h_A_symm : A.symm (t • (y_aff -ᵥ base : V)) = (t • (y_aff -ᵥ base : V) : V) +ᵥ base := by
      dsimp [A]; rfl
    rw [h_A_symm] at h_mem_image'
    exact h_mem_image'
  have h_proj : (((t • (y_aff -ᵥ base : V) : V) +ᵥ base : affF) : CoeffVec n) = (1 - t) • x + t • y := by
    simp [base, hy_eq, vadd_eq_add, vsub_eq_sub, smul_sub, sub_smul]; abel
  have h_final : (1 - t) • x + t • y ∈ (↑) '' interior ((↑)⁻¹' F : Set affF) :=
    ⟨(t • (y_aff -ᵥ base : V) : V) +ᵥ base, h_mem_int_C, h_proj⟩
  simpa [intrinsicInterior] using h_final

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

end CoeffBox
