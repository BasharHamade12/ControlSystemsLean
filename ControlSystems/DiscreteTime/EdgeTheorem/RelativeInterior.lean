module

public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeTheoremDefs
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.LinearAlgebra.Dual.Lemmas


@[expose] public section

open Polynomial
open Affine
open FiniteDimensional
open LinearMap
open Set

/-! # Relative interior machinery

Everything here replaces ambient-interior reasoning (`interior P.Ω`, which is
*empty* for polytopes in a proper affine slice such as the `δ₃ = 1` box of
Example 6.2) with relative (intrinsic) interior reasoning.

- `RelGen.exists_supporting_strict`: for nonempty convex `s`, a point
  `δ ∈ s \ relint s` admits a *nonzero continuous* functional `f` strictly
  below `f δ` on the whole relative interior of `s`.
  Proof: transport the ambient Hahn–Banach theorem
  (`geometric_hahn_banach_open_point`) along the affine homeomorphism
  `v ↦ δ +ᵥ v` from the linear model `direction (affineSpan ℝ s)` - the same
  pull-back pattern already proven inside `SubfaceConstruction.lean`.
- `intrinsicInterior_add_smul`: convex segments ending in the relative
  interior stay inside it.
- `closure_relint_eq`, `strict_implies_upper`: closure/density packaging.
- `CoeffBox.polytope_relint_nonempty`,
  `CoeffBox.exists_supporting_hyperplane_relint`: polytope-level facade.

Throughout the chain, boundary points are threaded as the hypothesis pair
`δ ∈ P.Ω ∧ δ ∉ intrinsicInterior ℝ P.Ω` (for full-dimensional polytopes this is
exactly `δ ∈ frontier P.Ω`).
-/

namespace RelGen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The supporting functional on the relative interior of a convex set. -/
theorem exists_supporting_strict {s : Set E} (hs_cv : Convex ℝ s) (hs_ne : s.Nonempty)
    {δ : E} (hδ_in : δ ∈ s) (hδ_nrelint : δ ∉ intrinsicInterior ℝ s) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ intrinsicInterior ℝ s, f y < f δ := by
  -- Step B: Separate δ from relint s within aff s.
  -- This constructs a functional that is strictly larger at δ than at any
  -- point of the relative interior.
  let affS : AffineSubspace ℝ E := affineSpan ℝ s
  let V : Submodule ℝ E := affS.direction
  have hδ_aff : δ ∈ affS := subset_affineSpan ℝ s hδ_in

  -- Transport the problem to V using τ : V ≃ₜ affS (affine homeomorphism)
  let τ : V ≃ₜ affS := {
    toFun := fun v => ⟨δ +ᵥ (v : E), by
      have h := AffineSubspace.vadd_mem_of_mem_direction v.2 hδ_aff
      simpa [vadd_eq_add, add_comm] using h⟩
    invFun := fun p => ⟨(p : E) -ᵥ δ,
      AffineSubspace.vsub_mem_direction p.property hδ_aff⟩
    left_inv := by intro v; ext; simp [vadd_vsub]
    right_inv := by intro p; ext; simp [vsub_vadd]
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ ?_
      exact continuous_const.add continuous_subtype_val
  }

  let A : Set V := τ ⁻¹' ((Subtype.val : affS → E) ⁻¹' s)
  let intS_preimage : Set affS :=
    (Subtype.val : affS → E) ⁻¹' (intrinsicInterior ℝ s)
  let C : Set V := τ ⁻¹' intS_preimage

  have h_int_eq :
    (Subtype.val : affS → E) ⁻¹' (intrinsicInterior ℝ s) =
    interior ((Subtype.val : affS → E) ⁻¹' s) := by
    rw [intrinsicInterior]
    rw [Set.preimage_image_eq _ Subtype.coe_injective]

  have hC_eq_interior_A : C = interior A := by
    have hC_def : C = τ ⁻¹' ((Subtype.val : affS → E) ⁻¹' (intrinsicInterior ℝ s)) := by
      ext x
      simp only [C, intS_preimage, Set.mem_preimage]
    have h_step2 : τ ⁻¹' ((Subtype.val : affS → E) ⁻¹' (intrinsicInterior ℝ s)) =
                    τ ⁻¹' (interior ((Subtype.val : affS → E) ⁻¹' s)) := by
      rw [h_int_eq]
    have h_step3 : τ ⁻¹' (interior ((Subtype.val : affS → E) ⁻¹' s)) =
                    interior (τ ⁻¹' ((Subtype.val : affS → E) ⁻¹' s)) := by
      rw [τ.preimage_interior]
    have hA_def : τ ⁻¹' ((Subtype.val : affS → E) ⁻¹' s) = A := by
      ext x
      simp only [A, τ]
    rw [hC_def, h_step2, h_step3, hA_def]

  have hA_convex : Convex ℝ A := by
    dsimp [A]
    let φ : V →ᵃ[ℝ] E :=
      AffineMap.const ℝ V δ + (Submodule.subtype (V : Submodule ℝ E)).toAffineMap
    have h_equiv : τ ⁻¹' ((Subtype.val : affS → E)⁻¹' s) = φ⁻¹' s := by
      ext v; simp [τ, φ, vadd_eq_add]
    rw [h_equiv]
    exact hs_cv.affine_preimage φ
  have hC_convex : Convex ℝ (C : Set V) := by
    rw [hC_eq_interior_A]; exact hA_convex.interior
  have hC_open : IsOpen (C : Set V) := by
    rw [hC_eq_interior_A]; exact isOpen_interior
  have h0_notin_C : (0 : V) ∉ C := by
    intro h
    have hτ0 : (τ 0 : E) = δ := by
      simp [τ, vadd_eq_add]
    have h_mem_ambient : δ ∈ intrinsicInterior ℝ s := by
      simpa [C, intS_preimage, hτ0, Set.mem_preimage] using h
    exact hδ_nrelint h_mem_ambient

  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hC_convex hC_open h0_notin_C
  have hf_zero : f (0 : V) = 0 := by simp
  let f_lin : V →ₗ[ℝ] ℝ := f.toLinearMap
  obtain ⟨w_base, hw_base⟩ := LinearMap.exists_extend (p := V) f_lin
  let c_w := w_base δ

  have h_on_relint : ∀ y ∈ intrinsicInterior ℝ s, w_base y < c_w := by
    intro y hy
    have hv : (y - δ) ∈ V :=
      AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ s (intrinsicInterior_subset hy)) hδ_aff
    set v : V := ⟨y - δ, hv⟩ with hv_def
    have hv_C : v ∈ C := by
      dsimp [C, intS_preimage, v]
      simpa [τ, vadd_eq_add, Set.mem_preimage] using hy
    have hf_lt : f v < f 0 := hf v hv_C
    calc
      w_base y = w_base (y - δ) + w_base δ := by simp
      _ = w_base (v : E) + c_w := by simp [v, c_w]
      _ = (w_base.comp V.subtype) v + c_w := rfl
      _ = f_lin v + c_w := by rw [hw_base]
      _ = f v + c_w := rfl
      _ < 0 + c_w := by linarith
      _ = c_w := by simp

  -- Package as a nonzero continuous functional.
  rcases Set.Nonempty.intrinsicInterior hs_cv hs_ne with ⟨y0, hy0⟩
  have hlt0 : w_base y0 < w_base δ := h_on_relint y0 hy0
  have hw_nonzero : w_base ≠ 0 := by
    intro heq
    rw [heq] at hlt0
    simp at hlt0
  -- Convert the extension to a continuous linear map (finite-dimensional).
  refine ⟨(LinearMap.toContinuousLinearMap w_base : E →L[ℝ] ℝ), ?_, ?_⟩
  · intro heq
    have hz : w_base = 0 := by
      refine LinearMap.ext fun x => ?_
      have hx := ContinuousLinearMap.ext_iff.1 heq x
      simpa using hx
    exact hw_nonzero hz
  · intro y hy
    rw [LinearMap.coe_toContinuousLinearMap' w_base]
    exact h_on_relint y hy

end RelGen

/-! ### The polytope-level facade (inside `CoeffBox`) -/

namespace CoeffBox

/-- Segments into the relative interior stay inside it
(moved verbatim from `ExposedFaceLemmas.lean`, which nothing below imports). -/
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
      have hv_mem_preimage : (v : V) +ᵥ base ∈ ((↑)⁻¹' F : Set affF) := by
        simpa [h_eq] using hfp

      refine ⟨(v : V) +ᵥ base, hv_mem_preimage, ?_⟩
      ext x'
      show ((v +ᵥ base : affF) : CoeffVec n) x' - x x' = (v : CoeffVec n) x'
      have hv_val : ((v +ᵥ base : affF) : CoeffVec n) x' = (v : CoeffVec n) x' + x x' := by
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
    have h_A_y : A y_aff = (y_aff -ᵥ base : V) := by
      dsimp [A]; rfl
    rw [h_A_y] at h_mem'
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
          have h_symm_comp : A.symm ∘ A = _root_.id := by
            ext p; simp
          rw [h_symm_comp]
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
        have h_symm_comp : A.symm ∘ A = id := Homeomorph.symm_comp_self A
        rw [h_symm_comp, Set.image_id]
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

/-- The closure of the relative interior of a nonempty compact convex set of
coefficient vectors equals the set itself. -/
lemma closure_relint_eq {n : ℕ} (F : Set (CoeffVec n)) (hs_cv : Convex ℝ F)
    (hs_cl : IsClosed F) (hs_ne : F.Nonempty) :
    closure (intrinsicInterior ℝ F) = F := by
  apply subset_antisymm
  · exact closure_minimal intrinsicInterior_subset hs_cl
  · intro x hx
    rcases Set.Nonempty.intrinsicInterior hs_cv hs_ne with ⟨y, hy⟩
    have h_cont : Continuous (fun (t : ℝ) => (1 - t) • x + t • y) := by
      refine Continuous.add ?_ ?_
      · refine (continuous_const.sub continuous_id).smul continuous_const
      · exact continuous_id.smul continuous_const
    have h_tendsto' : Filter.Tendsto (fun (t : ℝ) => (1 - t) • x + t • y) (nhds (0 : ℝ)) (nhds x) := by
      simpa using h_cont.tendsto (0 : ℝ)
    have h_tendsto : Filter.Tendsto (fun (t : ℝ) => (1 - t) • x + t • y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds x) :=
      h_tendsto'.mono_left nhdsWithin_le_nhds
    have h_nhd : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Set.Ioo (-1 : ℝ) 1, IsOpen.mem_nhds isOpen_Ioo (by norm_num), ?_⟩
      rintro _ ⟨⟨hz1, hz2⟩, hzpos⟩
      exact ⟨hzpos, hz2⟩
    have h_event : Filter.Eventually (fun t => (1 - t) • x + t • y ∈ intrinsicInterior ℝ F) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
      refine Filter.mem_of_superset h_nhd ?_
      intro t ht
      exact mem_intrinsicInterior_add_smul F hs_cv hx hy ht.1 ht.2
    haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := by infer_instance
    exact mem_closure_of_tendsto h_tendsto h_event

/-- A functional strictly below `c` on the relative interior of a compact
convex set is `≤ c` on the whole set. -/
private lemma strict_implies_upper {n : ℕ} (F : Set (CoeffVec n)) (f : CoeffVec n →L[ℝ] ℝ)
    (c : ℝ) (hs_cl : IsClosed F) (hs_ne : F.Nonempty) (hs_cv : Convex ℝ F)
    (h_strict : ∀ y ∈ intrinsicInterior ℝ F, f y < c) :
    ∀ y ∈ F, f y ≤ c := by
  intro y hy
  have h_closed_half : IsClosed {z : CoeffVec n | f z ≤ c} :=
    isClosed_Iic.preimage f.continuous
  have h_relint_sub : intrinsicInterior ℝ F ⊆ {z : CoeffVec n | f z ≤ c} :=
    fun w hw => le_of_lt (h_strict w hw)
  have h_closure_sub := closure_mono h_relint_sub
  rw [closure_relint_eq F hs_cv hs_cl hs_ne] at h_closure_sub
  have h_mem : y ∈ closure {z : CoeffVec n | f z ≤ c} := h_closure_sub hy
  rwa [h_closed_half.closure_eq] at h_mem

/-- A supporting functional strictly below `f δ` on the relative interior of a
polytope is `≤ f δ` on the whole polytope. -/
lemma exists_supporting_hyperplane_relint {n : ℕ} (P : Polytope n) (δ : CoeffVec n)
    (hδ_in_Ω : δ ∈ P.Ω) (hδ_not_relint : δ ∉ intrinsicInterior ℝ P.Ω) :
    ∃ f : CoeffVec n →L[ℝ] ℝ, f ≠ 0 ∧
      (∀ y ∈ P.Ω, f y ≤ f δ) ∧ (∀ y ∈ intrinsicInterior ℝ P.Ω, f y < f δ) := by
  have hΩ_cv : Convex ℝ P.Ω := convex_convexHull ℝ (P.vertices : Set (CoeffVec n))
  have hΩ_ne : (P.Ω : Set (CoeffVec n)).Nonempty := by
    obtain ⟨v, hv⟩ := P.nonempty
    exact ⟨v, subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)⟩
  obtain ⟨f, hf_ne, hf_strict⟩ :=
    RelGen.exists_supporting_strict hΩ_cv hΩ_ne hδ_in_Ω hδ_not_relint
  have hf_upper := strict_implies_upper P.Ω f (f δ) P.isCompact.isClosed hΩ_ne hΩ_cv hf_strict
  exact ⟨f, hf_ne, hf_upper, hf_strict⟩

/-- A nonzero linear functional that vanishes on a proper submodule of the
coefficient space (used to expose degenerate polytopes through their affine
slice). -/
lemma exists_nonzero_lm_killing_dir {n : ℕ} {U : Submodule ℝ (CoeffVec n)}
    (hU_ne_top : U ≠ ⊤) :
    ∃ ℓ : CoeffVec n →ₗ[ℝ] ℝ, ℓ ≠ 0 ∧ ∀ x ∈ U, ℓ x = 0 := by
  obtain ⟨f, hf_ne, hf_map⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top
      (lt_top_iff_ne_top.mpr hU_ne_top) inferInstance
  refine ⟨f, hf_ne, ?_⟩
  intro x hx
  have hxm : f x ∈ Submodule.map f U := ⟨x, hx, rfl⟩
  rw [hf_map] at hxm
  exact (Submodule.mem_bot (R := ℝ)).mp hxm

/-- If the direction of `aff P.Ω` is proper in the coefficient space, then
`P.Ω` itself is an exposed face of `P` (kill the direction). -/
lemma isExposedFace_Ω_of_direction_ne_top {n : ℕ} (P : Polytope n)
    (hdir_ne_top : (affineSpan ℝ P.Ω).direction ≠ ⊤) :
    IsExposedFace P P.Ω := by
  obtain ⟨v, hv⟩ := P.nonempty
  have hv_in_Ω : v ∈ P.Ω :=
    subset_convexHull ℝ (P.vertices : Set (CoeffVec n)) (Finset.mem_coe.mpr hv)
  have hv_mem : v ∈ affineSpan ℝ P.Ω := subset_affineSpan ℝ P.Ω hv_in_Ω
  obtain ⟨ell, hell_ne, hell_kill⟩ := exists_nonzero_lm_killing_dir hdir_ne_top
  have hell_const : ∀ x ∈ P.Ω, ell x = ell v := by
    intro x hx
    have hx_mem : x ∈ affineSpan ℝ P.Ω := subset_affineSpan ℝ P.Ω hx
    have hdiff : x -ᵥ v ∈ (affineSpan ℝ P.Ω).direction :=
      AffineSubspace.vsub_mem_direction hx_mem hv_mem
    have hzero : ell (x -ᵥ v) = 0 := hell_kill (x -ᵥ v) hdiff
    have hvec : (x -ᵥ v : CoeffVec n) = x - v := by rw [vsub_eq_sub]
    rw [hvec] at hzero
    have hsum : ell x = ell v + ell (x - v) := by
      have hdec : x = v + (x - v) := by abel
      conv_lhs => rw [hdec]
      rw [map_add]
    linarith [hsum, hzero]
  refine ⟨⟨ell, ell v, hell_ne, ?_, ⟨v, hv_in_Ω, rfl⟩⟩, ?_⟩
  · intro x hx
    rw [hell_const x hx]
  · ext x
    constructor
    · intro hx
      have h_eq : ell x = ell v := by linarith [hell_const x hx]
      exact ⟨hx, h_eq⟩
    · intro hx
      exact hx.1

/-- The relative (intrinsic) interior of a polytope is always nonempty. -/
lemma polytope_relint_nonempty {n : ℕ} (P : Polytope n) :
    (intrinsicInterior ℝ P.Ω).Nonempty := by
  have hΩ_ne : (P.Ω : Set (CoeffVec n)).Nonempty := by
    obtain ⟨v, hv⟩ := P.nonempty
    exact ⟨v, subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)⟩
  exact Set.Nonempty.intrinsicInterior
    (convex_convexHull ℝ (P.vertices : Set (CoeffVec n))) hΩ_ne

end CoeffBox

end
