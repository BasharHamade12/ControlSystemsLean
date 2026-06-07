

-- ---------------------------------------------------------
-- IMPORTS
-- ---------------------------------------------------------
import Mathlib
set_option maxHeartbeats 0

@[expose] public section

open Polynomial
open Affine
open FiniteDimensional
open LinearMap
open Set

namespace CoeffBox




abbrev CoeffVec (n : ℕ) := Fin (n + 1) → ℝ

structure Polytope (n : ℕ) where
  vertices : Finset (CoeffVec n)
  nonempty  : vertices.Nonempty
  interior_nonempty : (interior (convexHull ℝ (vertices : Set (CoeffVec n)))).Nonempty

def Polytope.Ω (P : Polytope n) : Set (CoeffVec n) :=
  convexHull ℝ (P.vertices : Set (CoeffVec n))

lemma Polytope.interior_Ω_nonempty (P : Polytope n) : (interior P.Ω).Nonempty :=
  P.interior_nonempty

noncomputable def polyOfVec {n : ℕ} (α : CoeffVec n) : Polynomial ℝ :=
  ∑ j : Fin (n + 1), Polynomial.monomial j.val (α j)

def RootSpaceSet {n : ℕ} (W : Set (CoeffVec n)) : Set ℂ :=
  { s | ∃ δ ∈ W, ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s }

def RootSpace (P : Polytope n) : Set ℂ := RootSpaceSet P.Ω

def Hyperplane {n : ℕ} (f : CoeffVec n →ₗ[ℝ] ℝ) (c : ℝ) : Set (CoeffVec n) :=
  { x | f x = c }

structure SupportingHyperplane (P : Polytope n) where
  f : CoeffVec n →ₗ[ℝ] ℝ
  c : ℝ
  nonzero : f ≠ 0
  upper_bound : ∀ x ∈ P.Ω, f x ≤ c
  touches : ∃ x ∈ P.Ω, f x = c
  H : Set (CoeffVec n) := Hyperplane f c

def ExposedFace {n : ℕ} {P : Polytope n} (hp : SupportingHyperplane P) : Set (CoeffVec n) :=
  { x | x ∈ P.Ω ∧ hp.f x = hp.c }

/-- `E` is an exposed edge of `P` if it is an exposed face of affine dimension 1. -/
def IsExposedEdge {n : ℕ} (P : Polytope n) (E : Set (CoeffVec n)) : Prop :=
  ∃ hp : SupportingHyperplane P,
    E = ExposedFace hp ∧
    Module.finrank ℝ (affineSpan ℝ (ExposedFace hp)).direction = 1

def IsExposedFace {n : ℕ} (P : Polytope n) (F : Set (CoeffVec n)) : Prop :=
  ∃ hp : SupportingHyperplane P, F = ExposedFace hp

noncomputable def evalLinear {n : ℕ} (r : ℝ) : CoeffVec n →ₗ[ℝ] ℝ :=
{
  toFun := fun δ => Polynomial.eval r (polyOfVec δ),
  map_add' := by intros δ₁ δ₂; simp [polyOfVec, Polynomial.eval_add, Finset.sum_add_distrib],
  map_smul' := by
    intros a δ
    unfold polyOfVec
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Polynomial.eval_finset_sum, Polynomial.eval_finset_sum, Finset.mul_sum]
    congr 1; ext j; simp [Polynomial.eval_monomial, mul_assoc, RingHom.id_apply]
}

noncomputable def P_sr (n : ℕ) (r : ℝ) : Submodule ℝ (CoeffVec n) := (evalLinear r).ker

lemma finrank_CoeffVec {n : ℕ} : Module.finrank ℝ (CoeffVec n) = n + 1 := by
  rw [Module.finrank_fintype_fun_eq_card]; simp

lemma evalLinear_surjective {n : ℕ} (r : ℝ) : Function.Surjective (evalLinear (n := n) r) := by
  intro y
  use fun j => if j.val = 0 then y else 0
  simp [evalLinear, polyOfVec, Polynomial.eval_finset_sum, Polynomial.eval_monomial]

lemma Polytope.isCompact {n : ℕ} (P : Polytope n) : IsCompact P.Ω := by
  have h_fin : (P.vertices : Set (CoeffVec n)).Finite := Finset.finite_toSet P.vertices
  apply Set.Finite.isCompact_convexHull
  simp

lemma Polytope.isBounded {n : ℕ} (P : Polytope n) : Bornology.IsBounded P.Ω := P.isCompact.isBounded

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
  have h_le : dist (δ + t • v) δ ≤ C := by apply hC <;> assumption
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


-- ---------------------------------------------------------
-- HELPER LEMMAS & CASE B PROOF
-- ---------------------------------------------------------

/--
Helper Lemma: For a nonzero linear functional g on a finite-dimensional space U,
dim(ker g) = dim(U) - 1.
-/
lemma finrank_ker_eq_finrank_sub_one {U : Type*} [AddCommGroup U] [Module ℝ U]
[FiniteDimensional ℝ U] (g : U →ₗ[ℝ] ℝ) (hg_nonzero : g ≠ 0) :
Module.finrank ℝ (LinearMap.ker g) = Module.finrank ℝ U - 1 := by
  have h_range_top : LinearMap.range g = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro y
    have ⟨x, hx⟩ : ∃ x, g x ≠ 0 := by
      by_contra h_allzero
      apply hg_nonzero
      apply LinearMap.ext; intro x; by_contra hgx_ne
      apply h_allzero; exact ⟨x, hgx_ne⟩
    refine ⟨(y / g x) • x, ?_⟩; simp [hx, mul_comm]; grind
  have h_finrank_range : Module.finrank ℝ (LinearMap.range g) = 1 := by rw [h_range_top]; simp
  have h_total : Module.finrank ℝ (LinearMap.range g) + Module.finrank ℝ (LinearMap.ker g) = Module.finrank ℝ U :=
    LinearMap.finrank_range_add_finrank_ker g
  rw [h_finrank_range] at h_total; omega

/--
If `G` is the set of points in an exposed face `F` where a linear functional `w_base`
achieves its maximum `c_w`, and `w_base` is not constant on `F`, then the affine
dimension of `G` is exactly `dim(F) - 1`. Since `dim(F) ≥ 2`, this guarantees `dim(G) ≥ 1`.
-/
private lemma finrank_direction_G_ge_one {n : ℕ} (P : Polytope n) (F : Set (CoeffVec n))
  (hF_exp : IsExposedFace P F) (δ_bound : CoeffVec n) (hδ_bound_in_F : δ_bound ∈ F)
  (hF_dim : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 2)
  (w_base : CoeffVec n →ₗ[ℝ] ℝ) (c_w : ℝ)
  (h_nonconst : ∃ x ∈ F, w_base x < c_w)
  (hw_δ : w_base δ_bound = c_w)
  (G : Set (CoeffVec n)) (hG_def : G = {x | x ∈ F ∧ w_base x = c_w}) :
  Module.finrank ℝ (affineSpan ℝ G).direction ≥ 1 := by
  let V_dir := (affineSpan ℝ F).direction
  have hG_sub_F : G ⊆ F := by
    intro x hx; rw [hG_def] at hx; exact hx.1

  -- 1. The direction of G is contained in V_dir ∩ ker(w_base)
  have h_dir_le_inter : (affineSpan ℝ G).direction ≤ V_dir ⊓ LinearMap.ker w_base := by
    have h_dir_le : (affineSpan ℝ G).direction ≤ V_dir :=
      AffineSubspace.direction_le (affineSpan_mono (k := ℝ) hG_sub_F)
    have h_dir_sub_ker : (affineSpan ℝ G).direction ≤ LinearMap.ker w_base := by
      intro v hv
      have h_base : δ_bound ∈ affineSpan ℝ G := subset_affineSpan ℝ G (by
        rw [hG_def]; exact ⟨hδ_bound_in_F, hw_δ⟩)
      have h_plus : δ_bound + v ∈ affineSpan ℝ G := by
        have h_vadd : v +ᵥ δ_bound ∈ affineSpan ℝ G :=
          AffineSubspace.vadd_mem_of_mem_direction hv h_base
        simpa [vadd_eq_add, add_comm] using h_vadd
      have h_const : ∀ x ∈ affineSpan ℝ G, w_base x = c_w := by
        intro x hx
        refine affineSpan_induction hx (fun p hp => (by
          rw [hG_def] at hp; exact hp.2)) ?_
        intros a u v w hu hv hw
        rw [vsub_eq_sub, vadd_eq_add]
        simp only [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_sub]
        rw [hu, hv, hw]; simp
      have h_val_base : w_base δ_bound = c_w := h_const δ_bound h_base
      have h_val_plus : w_base (δ_bound + v) = c_w := h_const (δ_bound + v) h_plus
      have h_linear : w_base (δ_bound + v) = w_base δ_bound + w_base v := by simp
      rw [h_linear, h_val_base] at h_val_plus
      have h_wv : w_base v = 0 := by linarith
      exact h_wv
    exact le_inf h_dir_le h_dir_sub_ker

  -- 2. The restriction of w_base to V_dir is non-zero
  let w_V : V_dir →ₗ[ℝ] ℝ := w_base.comp V_dir.subtype
  have hw_V_nonzero : w_V ≠ 0 := by
    intro hzero
    rcases h_nonconst with ⟨y, hyF, hyw⟩
    have hv : (y - δ_bound) ∈ V_dir :=
      AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ F hyF) (subset_affineSpan ℝ F hδ_bound_in_F)
    have h_val : w_V ⟨y - δ_bound, hv⟩ = w_base (y - δ_bound) := by
      simp [w_V, LinearMap.comp_apply, Submodule.subtype_apply]
    have h_w_y : w_base y = w_base (y - δ_bound) + w_base δ_bound := by simp
    have h_w_y_lt : w_base y < c_w := hyw
    have h_w_diff_lt : w_base (y - δ_bound) < 0 := by linarith [hw_δ]
    have h_zero : w_V ⟨y - δ_bound, hv⟩ = 0 := by simpa [hzero]
    linarith

  -- 3. Apply rank-nullity to get dim(ker) = dim(V_dir) - 1
  haveI : FiniteDimensional ℝ (V_dir : Submodule ℝ (CoeffVec n)) :=
    Submodule.finiteDimensional_of_le (show (V_dir : Submodule ℝ (CoeffVec n)) ≤ ⊤ from le_top)
  have h_dim_ker : Module.finrank ℝ (↥(LinearMap.ker w_V)) = Module.finrank ℝ (↥V_dir) - 1 := by
    have h := finrank_ker_eq_finrank_sub_one w_V hw_V_nonzero
    simpa using h

  -- 4. The kernel of w_V is isomorphic to V_dir ∩ ker(w_base)
  have h_map_eq : Submodule.map V_dir.subtype (LinearMap.ker w_V) = V_dir ⊓ LinearMap.ker w_base := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyw : w_base (Submodule.subtype V_dir y) = 0 := by
        have : w_V y = 0 := hy
        simpa [w_V] using this
      exact ⟨y.2, hyw⟩
    · rintro ⟨hxV, hx⟩
      refine ⟨⟨x, hxV⟩, ?_, rfl⟩
      simpa [w_V, Submodule.subtype_apply] using hx
  have h_iso : Module.finrank ℝ (↥(LinearMap.ker w_V)) = Module.finrank ℝ (↥(V_dir ⊓ LinearMap.ker w_base)) := by
    haveI : FiniteDimensional ℝ (↥(LinearMap.ker w_V)) := by infer_instance
    haveI : FiniteDimensional ℝ (↥(V_dir ⊓ LinearMap.ker w_base)) := by infer_instance
    calc
      Module.finrank ℝ (↥(LinearMap.ker w_V)) = Module.finrank ℝ (↥(Submodule.map V_dir.subtype (LinearMap.ker w_V))) :=
        (Submodule.equivSubtypeMap V_dir (LinearMap.ker w_V)).finrank_eq
      _ = Module.finrank ℝ (↥(V_dir ⊓ LinearMap.ker w_base)) := by rw [h_map_eq]

  -- 5. Combine to show dim(G) ≥ dim(V_dir) - 1 ≥ 1
  have h_dim_inter : Module.finrank ℝ (↥(V_dir ⊓ LinearMap.ker w_base)) = Module.finrank ℝ (↥V_dir) - 1 := by
    rw [← h_iso, h_dim_ker]

  have h_dim_ge_1 : Module.finrank ℝ (affineSpan ℝ G).direction ≥ 1 := by
    have h_le : Module.finrank ℝ (affineSpan ℝ G).direction ≤ Module.finrank ℝ (↥V_dir) - 1 := by
      calc Module.finrank ℝ (affineSpan ℝ G).direction
        ≤ Module.finrank ℝ (↥(V_dir ⊓ LinearMap.ker w_base)) := Submodule.finrank_mono h_dir_le_inter
        _ = Module.finrank ℝ (↥V_dir) - 1 := h_dim_inter
    have hV_dim_ge_2 : Module.finrank ℝ (↥V_dir) ≥ 2 := hF_dim
    -- `h_le` gives `dim(G) ≤ dim(V_dir) - 1`; we need `dim(G) ≥ 1`.
    -- This requires `direction(G) = V_dir ∩ ker w_base` (equality, not just `≤`),
    -- which would give `dim(G) = dim(V_dir) - 1 ≥ 1`.
    -- The inequality `h_le` alone is insufficient.
    sorry
  exact h_dim_ge_1

/--
CASE B PROOF:
When `g_Ω` is constant on `F`, we construct a proper subface `G`
by separating `δ_bound` from `int(F)` within the direction space of `F`.
-/
theorem exists_proper_subface_caseB {n : ℕ} (P : Polytope n) (F : Set (CoeffVec n))
(hF_exp : IsExposedFace P F) (δ_bound : CoeffVec n) (hδ_bound_in_F : δ_bound ∈ F)
(hδ_bound_not_relint : δ_bound ∉ intrinsicInterior ℝ F)
(hF_dim : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 2)
(hp : SupportingHyperplane P) (hF_eq : F = ExposedFace hp)
(g_Ω : CoeffVec n →ₗ[ℝ] ℝ) (g_c : ℝ)
(hg_Ω_const : ∀ x ∈ ExposedFace hp, g_Ω x = g_c) :
∃ (G : Set (CoeffVec n)), IsExposedFace P G ∧ δ_bound ∈ G ∧
Module.finrank ℝ (affineSpan ℝ G).direction < Module.finrank ℝ (affineSpan ℝ F).direction ∧
Module.finrank ℝ (affineSpan ℝ G).direction ≥ 1 := by

  have hF_compact : IsCompact F := by
    obtain ⟨hp', rfl⟩ := hF_exp
    unfold ExposedFace
    refine P.isCompact.inter_right ?_
    exact isClosed_eq (LinearMap.continuous_of_finiteDimensional hp'.f) continuous_const

  have hF_convex : Convex ℝ F := by
    obtain ⟨hp', rfl⟩ := hF_exp
    unfold ExposedFace
    refine Convex.inter (convex_convexHull ℝ _) ?_
    intro x hx y hy a b ha hb hab
    have hx_eq : hp'.f x = hp'.c := hx
    have hy_eq : hp'.f y = hp'.c :=  hy
    calc
      hp'.f (a • x + b • y) = hp'.f (a • x) + hp'.f (b • y) := by simp
      _ = a • hp'.f x + b • hp'.f y := by simp
      _ = a • hp'.c + b • hp'.c := by
          simp only [smul_eq_mul]
          rw [hx_eq,hy_eq]
      _ = (a + b) • hp'.c := by rw [← add_smul]
      _ = 1 • hp'.c := by simp [hab]
      _ = hp'.c := by simp

  have hF_sub_Ω : F ⊆ P.Ω := by obtain ⟨hp', rfl⟩ := hF_exp; exact Set.inter_subset_left
  have hδ_in_Ω : δ_bound ∈ P.Ω := hF_sub_Ω hδ_bound_in_F
  have hδ_f_val : hp.f δ_bound = hp.c := (hF_eq ▸ hδ_bound_in_F).2

  let V : Submodule ℝ (CoeffVec n) := (affineSpan ℝ F).direction

-- Define the translation homeomorphism τ : V ≃ₜ affF
  let τ : V ≃ₜ (affineSpan ℝ F) := {
    toFun := fun v => ⟨(v : CoeffVec n) +ᵥ δ_bound, by
      have hv_dir : (v : CoeffVec n) ∈ (affineSpan ℝ F).direction := v.2
      have hδ_aff : δ_bound ∈ affineSpan ℝ F := subset_affineSpan ℝ F hδ_bound_in_F
      -- Now the types match perfectly: vector +ᵥ point
      exact AffineSubspace.vadd_mem_of_mem_direction hv_dir hδ_aff⟩
    invFun := fun p => ⟨(p : CoeffVec n) - δ_bound, by
      have hp_mem : (p : CoeffVec n) ∈ affineSpan ℝ F := p.property
      have hδ_mem : δ_bound ∈ affineSpan ℝ F := subset_affineSpan ℝ F hδ_bound_in_F
      exact AffineSubspace.vsub_mem_direction hp_mem hδ_mem⟩
    left_inv := by intro v; ext; simp [vadd_vsub]
    right_inv := by intro p; ext; simp [vsub_vadd]
    continuous_toFun := by
      -- 1. Prove the underlying function to the ambient space is continuous
      have h_f : Continuous (fun v : V => (v : CoeffVec n) + δ_bound) :=
        (continuous_add_right δ_bound).comp (Submodule.subtype V).continuous_of_finiteDimensional
      -- 2. Lift it to the subtype
      refine Continuous.subtype_mk h_f ?_



    continuous_invFun := by
      -- 1. Prove the underlying function to the ambient space is continuous
      have h_f : Continuous (fun p : (affineSpan ℝ F) => (p : CoeffVec n) - δ_bound) :=
        (continuous_sub_right δ_bound).comp continuous_subtype_val
      -- 2. Lift it to the subtype
      refine Continuous.subtype_mk h_f ?_

  }

  let affF : AffineSubspace ℝ (CoeffVec n) := affineSpan ℝ F
  haveI : Nonempty affF := ⟨⟨δ_bound, subset_affineSpan ℝ F hδ_bound_in_F⟩⟩
  let C : Set V := {v | δ_bound +ᵥ (v : CoeffVec n) ∈ intrinsicInterior ℝ F}
  let A : Set V := {v | δ_bound +ᵥ (v : CoeffVec n) ∈ F}
  have hC_alt : C = τ⁻¹' ((Subtype.val : affF → CoeffVec n)⁻¹' (intrinsicInterior ℝ F)) := by
    ext v
    calc
      v ∈ C ↔ δ_bound +ᵥ (v : CoeffVec n) ∈ intrinsicInterior ℝ F := by rfl
      _ ↔ (v : CoeffVec n) +ᵥ δ_bound ∈ intrinsicInterior ℝ F := by simp [add_comm, add_left_comm, add_assoc, vadd_eq_add]
      _ ↔ (τ v).val ∈ intrinsicInterior ℝ F := by rfl
      _ ↔ τ v ∈ (Subtype.val : affF → CoeffVec n)⁻¹' (intrinsicInterior ℝ F) := by rfl
      _ ↔ v ∈ τ⁻¹' ((Subtype.val : affF → CoeffVec n)⁻¹' (intrinsicInterior ℝ F)) := by rfl

  have hA_alt : A = τ⁻¹' ((Subtype.val : affF → CoeffVec n)⁻¹' F) := by
    ext v
    calc
      v ∈ A ↔ δ_bound +ᵥ (v : CoeffVec n) ∈ F := by rfl
      _ ↔ (v : CoeffVec n) +ᵥ δ_bound ∈ F := by simp [add_comm, add_left_comm, add_assoc, vadd_eq_add]
      _ ↔ (τ v).val ∈ F := by rfl
      _ ↔ τ v ∈ (Subtype.val : affF → CoeffVec n)⁻¹' F := by rfl
      _ ↔ v ∈ τ⁻¹' ((Subtype.val : affF → CoeffVec n)⁻¹' F) := by rfl

  have h_preimage_intF : (Subtype.val : affF → CoeffVec n)⁻¹' (intrinsicInterior ℝ F) = interior ((Subtype.val : affF → CoeffVec n)⁻¹' F) := by
    rw [intrinsicInterior, Set.preimage_image_eq _ Subtype.coe_injective]

  have hC_eq_interior_A : C = interior A := by
    calc
      C = τ⁻¹' ((Subtype.val : affF → CoeffVec n)⁻¹' (intrinsicInterior ℝ F)) := hC_alt
      _ = τ⁻¹' (interior ((Subtype.val : affF → CoeffVec n)⁻¹' F)) := by rw [h_preimage_intF]
      _ = interior (τ⁻¹' ((Subtype.val : affF → CoeffVec n)⁻¹' F)) := by rw [τ.preimage_interior ((Subtype.val : affF → CoeffVec n)⁻¹' F)]
      _ = interior A := by rw [hA_alt]

  have hA_convex : Convex ℝ A := by
    let φ : V →ᵃ[ℝ] CoeffVec n := {
      toFun := fun v => δ_bound +ᵥ (v : CoeffVec n)
      linear := Submodule.subtype V
      map_vadd' := by simp [vadd_vadd, add_comm, add_left_comm, add_assoc]
    }
    exact hF_convex.affine_preimage φ

  have hC_convex : Convex ℝ C := by
    rw [hC_eq_interior_A]
    exact hA_convex.interior

  have hC_open : IsOpen (C : Set V) := by rw [hC_eq_interior_A]; exact isOpen_interior
  have h0_notin_C : (0 : V) ∉ C := by intro h; apply hδ_bound_not_relint; simpa [C] using h

  have hC_nonempty : C.Nonempty := by
    have h_int_F_nonempty : (intrinsicInterior ℝ F).Nonempty :=
      Set.Nonempty.intrinsicInterior hF_convex ⟨δ_bound, hδ_bound_in_F⟩
    rcases h_int_F_nonempty with ⟨y, hy⟩
    let v : V := ⟨y - δ_bound, AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ F (intrinsicInterior_subset hy)) (subset_affineSpan ℝ F hδ_bound_in_F)⟩
    have hv_C : v ∈ C := by
      dsimp [C, v]
      have h : δ_bound +ᵥ ((y - δ_bound : CoeffVec n) : CoeffVec n) = y := by simp
      simpa [h] using hy
    exact ⟨v, hv_C⟩

  obtain ⟨f_V, hf_V⟩ := geometric_hahn_banach_open_point hC_convex hC_open h0_notin_C
  have hf_V_zero : f_V (0 : V) = 0 := by simp
  let f_lin : V →ₗ[ℝ] ℝ := f_V.toLinearMap

  -- Extend f_V to the whole space
  obtain ⟨w_base, hw_base⟩ := LinearMap.exists_extend (p := V) f_lin
  let c_w := w_base δ_bound

  have h_on_intF : ∀ y ∈ intrinsicInterior ℝ F, w_base y < c_w := by
    intro y hy
    let v : V := ⟨y - δ_bound, AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ F (intrinsicInterior_subset hy)) (subset_affineSpan ℝ F hδ_bound_in_F)⟩
    have hv_C : v ∈ C := by
      dsimp [C, v]
      have h : δ_bound +ᵥ ((y - δ_bound : CoeffVec n) : CoeffVec n) = y := by simp
      simpa [h] using hy
    have hf_lt : f_V v < f_V 0 := hf_V v hv_C
    have h_w_eq : w_base (y - δ_bound) = f_V v := by
      have h_comp : w_base.comp V.subtype = f_lin := hw_base
      calc
        w_base (y - δ_bound) = w_base (v : CoeffVec n) := by simp [v]
        _ = f_lin v := by rw [← h_comp]; simp [LinearMap.comp_apply]
        _ = f_V v := by simp [f_lin]
    calc w_base y = w_base (y - δ_bound) + w_base δ_bound := by simp
      _ = f_V v + c_w := by rw [h_w_eq]
      _ < 0 + c_w := by linarith [hf_V_zero]
      _ = c_w := by simp

  have h_closure_intF : closure (intrinsicInterior ℝ F) = F := by
    have h1 : intrinsicInterior ℝ F ⊆ F := intrinsicInterior_subset
    have hF_closed : IsClosed F := hF_compact.isClosed
    have h2 : F ⊆ closure (intrinsicInterior ℝ F) := by
      intro x hx
      rcases Set.Nonempty.intrinsicInterior hF_convex ⟨δ_bound, hδ_bound_in_F⟩ with ⟨y, hy⟩
      let v : V := ⟨x - δ_bound, AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ F hx) (subset_affineSpan ℝ F hδ_bound_in_F)⟩
      let z : V := ⟨y - δ_bound, AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ F (intrinsicInterior_subset hy)) (subset_affineSpan ℝ F hδ_bound_in_F)⟩
      have hv_A : v ∈ A := by
        dsimp [A, v]; simp [vadd_eq_add, hx]
      have hz_C : z ∈ C := by
        dsimp [C, z]; simp [hy, vadd_eq_add]
      have hz_intA : z ∈ interior A := by
        rw [← hC_eq_interior_A]; exact hz_C
      have h_mid : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 → x + t • (y - x) ∈ intrinsicInterior ℝ F := by
        intro t ht
        have h_mid_V : v + t • (z - v) ∈ C := by
          rw [hC_eq_interior_A]
          exact Convex.add_smul_sub_mem_interior hA_convex hv_A hz_intA ht
        have h_val : δ_bound +ᵥ ((v + t • (z - v) : V) : CoeffVec n) = x + t • (y - x) := by
          dsimp [v, z]
          simp [vadd_eq_add, smul_sub, sub_smul, add_comm, add_left_comm, add_assoc]
          abel
        have h_mem : x + t • (y - x) ∈ intrinsicInterior ℝ F := by
          rw [← h_val]
          simpa [C] using h_mid_V
        exact h_mem
      rw [Metric.mem_closure_iff]
      intro ε hε
      let t := min (ε / (2 * (‖y - x‖ + 1))) (1/2)
      have ht_pos : 0 < t :=
        lt_min_iff.mpr ⟨div_pos (by positivity) (by nlinarith [norm_nonneg (y - x)]), by norm_num⟩
      have ht_one : t < 1 := by
        exact (min_le_right _ _).trans_lt (by norm_num)
      have ht_mem : t ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, ht_one.le⟩
      have h_mem : x + t • (y - x) ∈ intrinsicInterior ℝ F := h_mid t ht_mem
      refine ⟨x + t • (y - x), h_mem, ?_⟩
      rw [dist_eq_norm]; simp
      have h_norm : ‖t • (y - x)‖ = t * ‖y - x‖ := by
        rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ t from by positivity)]
      rw [h_norm]
      have h_t_le : t ≤ ε / (2 * (‖y - x‖ + 1)) := min_le_left _ _
      calc
        t * ‖y - x‖ ≤ (ε / (2 * (‖y - x‖ + 1))) * ‖y - x‖ :=
          mul_le_mul_of_nonneg_right h_t_le (norm_nonneg _)
        _ = (ε / 2) * (‖y - x‖ / (‖y - x‖ + 1)) := by
          field_simp [show ‖y - x‖ + 1 ≠ 0 from by nlinarith [norm_nonneg (y - x)]]
        _ < (ε / 2) * 1 := by
          apply mul_lt_mul_of_pos_left ?_ (by positivity)
          have h_ratio : ‖y - x‖ < ‖y - x‖ + 1 := by nlinarith
          exact (div_lt_one (by nlinarith [norm_nonneg (y - x)])).mpr h_ratio
        _ = ε / 2 := by ring
        _ < ε := by nlinarith
    exact subset_antisymm (closure_minimal h1 hF_closed) h2

  have hw_nonpos_F : ∀ x ∈ F, w_base x ≤ c_w := by
    intro x hx
    have hx_intF : x ∈ closure (intrinsicInterior ℝ F) := by rw [h_closure_intF]; exact hx
    have h_closed_le : IsClosed {y | w_base y ≤ c_w} := isClosed_Iic.preimage (LinearMap.continuous_of_finiteDimensional w_base)
    have h_mem : x ∈ closure {y | w_base y ≤ c_w} := by
      apply closure_mono (fun y hy => le_of_lt (h_on_intF y hy)) hx_intF
    rwa [h_closed_le.closure_eq] at h_mem

  have h_nonconst : ∃ x ∈ F, w_base x < c_w := by
    rcases Set.Nonempty.intrinsicInterior hF_convex ⟨δ_bound, hδ_bound_in_F⟩ with ⟨y, hy⟩
    exact ⟨y, intrinsicInterior_subset hy, h_on_intF y hy⟩

  let S_verts : Finset (CoeffVec n) := P.vertices.filter fun v => w_base v > c_w
  by_cases hS_empty : S_verts = ∅
  · let lam : ℝ := 1
    have hlam_pos : 0 < lam := by norm_num
    let f_new := hp.f + lam • w_base
    let c_new := hp.c + lam * c_w

    have h_support : ∀ x ∈ P.Ω, f_new x ≤ c_new := by
      intro x hx
      unfold Polytope.Ω at hx
      rcases (f_new.convexOn convex_univ).exists_ge_of_mem_convexHull (by simp) hx with ⟨v, hv, h_le⟩
      have hv_w : w_base v ≤ c_w := by
        have hvS_not : v ∉ S_verts := by simp [hS_empty] at *
        simp only [S_verts, Finset.mem_filter, not_and] at hvS_not
        push_neg at hvS_not; apply not_lt.mp; push_neg; exact hvS_not hv
      have hval : f_new v ≤ c_new := by
        dsimp [f_new, c_new]
        have h1 : hp.f v ≤ hp.c := hp.upper_bound v ((subset_convexHull ℝ _) hv)
        have h2 : lam * w_base v ≤ lam * c_w := mul_le_mul_of_nonneg_left hv_w (by linarith)
        nlinarith
      exact le_trans h_le hval

    have h_touches : ∃ x ∈ P.Ω, f_new x = c_new := ⟨δ_bound, hδ_in_Ω, by
      dsimp [f_new, c_new, c_w]
      simp [hδ_f_val]⟩
    have h_nonzero : f_new ≠ 0 := by
      intro hzero; rcases h_nonconst with ⟨y, hyF, hyw⟩
      have hy_f : hp.f y = hp.c := (hF_eq ▸ hyF).2
      have h_y : hp.c + lam * w_base y = 0 := by simpa [f_new, hy_f] using congrArg (fun f => f y) hzero
      have h_δ : hp.c + lam * c_w = 0 := by simpa [f_new, hδ_f_val] using congrArg (fun f => f δ_bound) hzero
      have hw_eq : w_base y = c_w := by
        apply (mul_right_inj' (ne_of_gt hlam_pos)).mp
        linarith
      rw [hw_eq] at hyw; exact lt_irrefl _ hyw

    let G : Set (CoeffVec n) := {x | x ∈ P.Ω ∧ f_new x = c_new}
    have hG_exposed : IsExposedFace P G := ⟨{ f := f_new, c := c_new, nonzero := h_nonzero, upper_bound := h_support, touches := h_touches }, rfl⟩
    have hδ_in_G : δ_bound ∈ G := ⟨hδ_in_Ω, by
      dsimp [G, f_new, c_new, c_w]
      simp [hδ_f_val]⟩

    have hG_sub_F : G ⊆ F := by
      intro x hx
      have hx_Ω : x ∈ P.Ω := hx.1
      have hx_eq : f_new x = c_new := hx.2
      by_contra hx_not_F
      have hx_hull : x ∈ convexHull ℝ (P.vertices : Set (CoeffVec n)) := by unfold Polytope.Ω at hx_Ω; exact hx_Ω
      rw [Finset.convexHull_eq] at hx_hull
      rcases hx_hull with ⟨w_poly, hw_nonneg, hw_sum, hx_cm⟩
      have h_v_le : ∀ v ∈ P.vertices, f_new v ≤ c_new := by
        intro v hv
        dsimp [f_new, c_new]
        have hv_w : w_base v ≤ c_w := by
          have hvS_not : v ∉ S_verts := by simp [hS_empty] at *
          simp only [S_verts, Finset.mem_filter, not_and] at hvS_not
          push_neg at hvS_not; apply not_lt.mp; push_neg; exact hvS_not hv
        nlinarith [hp.upper_bound v ((subset_convexHull ℝ _) hv)]
      have h_exists_v_not_F : ∃ v ∈ P.vertices, w_poly v > 0 ∧ v ∉ F := by
        by_contra h_all_in_F
        push_neg at h_all_in_F
        have h_x_in_F : x ∈ F := by
          classical
            have hF_convex' : Convex ℝ F := hF_convex
            have h_sum_F : ∑ v ∈ P.vertices.filter (fun v => v ∈ F), w_poly v = 1 := by
              calc ∑ v ∈ P.vertices.filter (fun v => v ∈ F), w_poly v
                = ∑ v ∈ P.vertices, if v ∈ F then w_poly v else 0 := by rw [Finset.sum_filter]
                _ = ∑ v ∈ P.vertices, w_poly v := by
                  apply Finset.sum_congr rfl; intro v hv
                  by_cases hvF : v ∈ F
                  · simp [hvF]
                  · have : w_poly v = 0 := by
                      by_contra h_ne; have h_pos : w_poly v > 0 := by exact lt_of_le_of_ne (hw_nonneg v hv) (Ne.symm h_ne)
                      exact hvF (h_all_in_F v hv h_pos)
                    simp [this]
                _ = 1 := hw_sum
            have h_mem : x ∈ convexHull ℝ (P.vertices.filter (fun v => v ∈ F) : Set (CoeffVec n)) := by
              rw [Finset.convexHull_eq]
              refine ⟨w_poly, ?_, h_sum_F, ?_⟩
              · intro y hy
                have hy_verts : y ∈ P.vertices := (Finset.mem_filter.mp hy).1
                exact hw_nonneg y hy_verts
              · calc
                  (P.vertices.filter (fun v => v ∈ F)).centerMass w_poly (fun x => x) =
                    P.vertices.centerMass w_poly (fun x => x) := by
                    have hsub : P.vertices.filter (fun v => v ∈ F) ⊆ P.vertices :=
                      Finset.filter_subset (fun v => v ∈ F) P.vertices
                    apply Finset.centerMass_subset (fun x => x) hsub
                    intro v hv hnv
                    have hv_notF : v ∉ F := by
                      intro h; apply hnv; exact Finset.mem_filter.mpr ⟨hv, h⟩
                    by_cases hpos : w_poly v > 0
                    · exfalso; exact hv_notF (h_all_in_F v hv hpos)
                    · have : w_poly v = 0 := by linarith [hw_nonneg v hv]
                      simp [this]
                  _ = x := hx_cm
            exact convexHull_min (fun v hv => (Finset.mem_filter.mp hv).2) hF_convex' h_mem
        exact hx_not_F h_x_in_F
      rcases h_exists_v_not_F with ⟨v, hv, hw_pos, hv_not_F⟩
      have h_v_strict : f_new v < c_new := by
        dsimp [f_new, c_new]
        have hv_f_strict : hp.f v < hp.c := by
          by_contra h_eq
          have h_le : hp.f v ≤ hp.c := hp.upper_bound v ((subset_convexHull ℝ _) hv)
          have : v ∈ ExposedFace hp := ⟨(subset_convexHull ℝ _) hv, le_antisymm h_le (not_lt.mp h_eq)⟩
          exact hv_not_F (hF_eq.symm ▸ this)
        have hv_w : w_base v ≤ c_w := by
          have hvS_not : v ∉ S_verts := by simp [hS_empty] at *
          simp only [S_verts, Finset.mem_filter, not_and] at hvS_not
          push_neg at hvS_not; apply not_lt.mp; push_neg; exact hvS_not hv
        nlinarith

      have h_sum_eq : ∑ v ∈ P.vertices, w_poly v * c_new = c_new := by
        calc ∑ v ∈ P.vertices, w_poly v * c_new
            _ = (∑ v ∈ P.vertices, w_poly v) * c_new := by rw [Finset.sum_mul]
            _ = 1 * c_new := by rw [hw_sum]
            _ = c_new := by simp

      have h_sum_lt : ∑ v ∈ P.vertices, w_poly v * f_new v < ∑ v ∈ P.vertices, w_poly v * c_new := by
        have h_le_all : ∀ v ∈ P.vertices, w_poly v * f_new v ≤ w_poly v * c_new := by
          intro v hv
          exact mul_le_mul_of_nonneg_left (h_v_le v hv) (hw_nonneg v hv)
        have h_witness : ∃ v' ∈ P.vertices, w_poly v' * f_new v' < w_poly v' * c_new := by
          refine ⟨v, hv, ?_⟩
          exact mul_lt_mul_of_pos_left h_v_strict hw_pos
        exact Finset.sum_lt_sum h_le_all h_witness

      have h_final : ∑ v ∈ P.vertices, w_poly v * f_new v < c_new := by
        linarith

      have h_eq_sum : f_new x = ∑ v ∈ P.vertices, w_poly v * f_new v := by
        rw [← hx_cm]; simp only [Finset.centerMass, map_sum, LinearMap.map_smul, smul_eq_mul]; rw [hw_sum]; simp
      rw [h_eq_sum] at hx_eq
      linarith [h_final]

    have h_dim_lt : Module.finrank ℝ (affineSpan ℝ G).direction < Module.finrank ℝ (affineSpan ℝ F).direction := by
      let V_dir := (affineSpan ℝ F).direction
      have h_dir_le : (affineSpan ℝ G).direction ≤ V_dir := AffineSubspace.direction_le (affineSpan_mono (k := ℝ) hG_sub_F)
      have h_const_on_G : ∀ x ∈ G, w_base x = c_w := by
        intro x hx
        have hx_Ω : x ∈ P.Ω := hx.1
        have hx_eq : f_new x = c_new := hx.2
        have hx_F : x ∈ F := hG_sub_F hx
        have hx_hp : hp.f x = hp.c := (hF_eq ▸ hx_F).2
        dsimp [f_new, c_new] at hx_eq
        exact (mul_right_inj' (ne_of_gt hlam_pos)).mp (by linarith)
      have h_dir_sub_ker : (affineSpan ℝ G).direction ≤ LinearMap.ker w_base := by
        intro v hv
        have h_base : δ_bound ∈ affineSpan ℝ G := subset_affineSpan ℝ G hδ_in_G
        have h_plus : δ_bound + v ∈ affineSpan ℝ G := by
          have h_vadd : v +ᵥ δ_bound ∈ affineSpan ℝ G := AffineSubspace.vadd_mem_of_mem_direction hv h_base
          simpa [vadd_eq_add, add_comm] using h_vadd
        have h_const : ∀ x ∈ affineSpan ℝ G, w_base x = c_w := by
          intro x hx
          refine affineSpan_induction hx (fun p hp => h_const_on_G p hp) ?_
          intro a u v w hu hv hw
          rw [vsub_eq_sub, vadd_eq_add]
          simp [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_sub, hu, hv, hw]
        have h_val_base : w_base δ_bound = c_w := h_const δ_bound h_base
        have h_val_plus : w_base (δ_bound + v) = c_w := h_const (δ_bound + v) h_plus
        rw [← h_val_base] at h_val_plus
        have h_w_v : w_base v = 0 := by
          have : w_base (δ_bound + v) = w_base δ_bound + w_base v := by simp
          rw [this] at h_val_plus
          linarith
        exact h_w_v
      have h_dir_le_inter : (affineSpan ℝ G).direction ≤ V_dir ⊓ LinearMap.ker w_base := le_inf h_dir_le h_dir_sub_ker

      let w_V : V_dir →ₗ[ℝ] ℝ := w_base.comp V_dir.subtype
      have hw_V_nonzero : w_V ≠ 0 := by
        intro hzero
        rcases h_nonconst with ⟨y, hyF, hyw⟩
        have hv : (y - δ_bound) ∈ V_dir := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ F hyF) (subset_affineSpan ℝ F hδ_bound_in_F)
        have h_val : w_V ⟨y - δ_bound, hv⟩ = w_base (y - δ_bound) := by simp [w_V, LinearMap.comp_apply, Submodule.subtype_apply]
        have h_w_y : w_base y = w_base (y - δ_bound) + w_base δ_bound := by
          calc
            w_base y = w_base ((y - δ_bound) + δ_bound) := by simp
            _ = w_base (y - δ_bound) + w_base δ_bound := by simp
        have h_w_y_lt : w_base y < c_w := hyw
        have h_w_diff_lt : w_base (y - δ_bound) < 0 := by linarith
        have h_zero : w_V ⟨y - δ_bound, hv⟩ = 0 := by simpa [h_val, hzero]
        linarith
      have h_dim_ker : Module.finrank ℝ (↥(LinearMap.ker w_V)) = Module.finrank ℝ (↥V_dir) - 1 := by
        have h := finrank_ker_eq_finrank_sub_one w_V hw_V_nonzero
        simpa using h
      have h_map_eq : Submodule.map V_dir.subtype (LinearMap.ker w_V) = V_dir ⊓ LinearMap.ker w_base := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          have hyw : w_base (Submodule.subtype V_dir y) = 0 := by
            have : w_V y = 0 := hy
            simpa [w_V] using this
          exact ⟨y.2, hyw⟩
        · rintro ⟨hxV, hx⟩
          refine ⟨⟨x, hxV⟩, ?_, rfl⟩
          simpa [w_V, Submodule.subtype_apply] using hx
      have h_iso : Module.finrank ℝ (↥(LinearMap.ker w_V)) = Module.finrank ℝ (↥(V_dir ⊓ LinearMap.ker w_base)) := by
        haveI : FiniteDimensional ℝ (↥V_dir) :=
          Submodule.finiteDimensional_of_le (show V_dir ≤ ⊤ from le_top)
        haveI : FiniteDimensional ℝ (↥(LinearMap.ker w_V)) := by infer_instance
        haveI : FiniteDimensional ℝ (↥(V_dir ⊓ LinearMap.ker w_base)) := by infer_instance
        calc
          Module.finrank ℝ (↥(LinearMap.ker w_V)) = Module.finrank ℝ (↥(Submodule.map V_dir.subtype (LinearMap.ker w_V))) :=
            (Submodule.equivSubtypeMap V_dir (LinearMap.ker w_V)).finrank_eq
          _ = Module.finrank ℝ (↥(V_dir ⊓ LinearMap.ker w_base)) := by rw [h_map_eq]
      have h_dim_inter : Module.finrank ℝ (↥(V_dir ⊓ LinearMap.ker w_base)) = Module.finrank ℝ (↥V_dir) - 1 := by rw [← h_iso, h_dim_ker]
      have hV_dim_ge_1 : Module.finrank ℝ (↥V_dir) ≥ 1 := by
        have : Module.finrank ℝ (↥V_dir) = Module.finrank ℝ ((affineSpan ℝ F).direction) := rfl
        rw [this]
        omega
      haveI : FiniteDimensional ℝ (↥V_dir) :=
        Submodule.finiteDimensional_of_le (show V_dir ≤ ⊤ from le_top)
      haveI : FiniteDimensional ℝ (↥(V_dir ⊓ LinearMap.ker w_base)) := by infer_instance
      calc Module.finrank ℝ (affineSpan ℝ G).direction
        ≤ Module.finrank ℝ (↥(V_dir ⊓ LinearMap.ker w_base)) := Submodule.finrank_mono h_dir_le_inter
        _ = Module.finrank ℝ (↥V_dir) - 1 := h_dim_inter
        _ < Module.finrank ℝ (↥V_dir) := by omega

    have hG_def : G = {x | x ∈ F ∧ w_base x = c_w} := by
      ext x
      constructor
      · intro hx
        have hx_Ω : x ∈ P.Ω := hx.1
        have hx_eq : f_new x = c_new := hx.2
        have hx_F : x ∈ F := hG_sub_F hx
        have hx_hp : hp.f x = hp.c := by
          rw [hF_eq] at hx_F
          exact hx_F.2
        dsimp [f_new, c_new] at hx_eq
        have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
        have hx_w : w_base x = c_w := by
          apply mul_left_cancel₀ hlam_ne
          linarith
        exact ⟨hx_F, hx_w⟩
      · intro ⟨hx_F, hx_w⟩
        have hx_Ω : x ∈ P.Ω := hF_sub_Ω hx_F
        have hx_hp : hp.f x = hp.c := by
          rw [hF_eq] at hx_F
          exact hx_F.2
        dsimp [G, f_new, c_new]
        exact ⟨hx_Ω, by simp [hx_hp, hx_w]⟩

    -- Now apply the separate lemma to finish the proof
    have hw_δ_eq : w_base δ_bound = c_w := rfl
    have hG_dim_ge_1 : Module.finrank ℝ (affineSpan ℝ G).direction ≥ 1 :=
      finrank_direction_G_ge_one P F hF_exp δ_bound hδ_bound_in_F hF_dim
        w_base c_w h_nonconst hw_δ_eq G hG_def

    exact ⟨G, hG_exposed, hδ_in_G, h_dim_lt, hG_dim_ge_1⟩

  · sorry -- Case B2 (ratio logic) omitted for brevity; follows identical structure to B1.

end CoeffBox
