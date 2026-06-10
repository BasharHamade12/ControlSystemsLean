module

public import ControlSystems.DiscreteTime.EdgeTheoremDefs
public import Mathlib.Analysis.Convex.Intrinsic
public import ControlSystems.DiscreteTime.lemma61helper

@[expose] public section

open Polynomial
open Affine
open FiniteDimensional
open LinearMap

namespace CoeffBox

lemma direction_sub_ker_gΩ {n : ℕ} {P : Polytope n}
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

lemma direction_sub_inf_ker_gΩ {n : ℕ} {P : Polytope n}
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
