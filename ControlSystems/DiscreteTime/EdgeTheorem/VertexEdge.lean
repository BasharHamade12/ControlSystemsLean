module

public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeTheoremDefs
public import ControlSystems.DiscreteTime.EdgeTheorem.BasicLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.PreliminaryLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.ExposedFaceLemmas

-- Heavy `Finset`/real-arithmetic file: allow ample heartbeats.
set_option maxHeartbeats 1000000

@[expose] public section

open Polynomial Affine FiniteDimensional LinearMap Set

namespace CoeffBox

/-! # Vertex → edge (replacement for the false axiom)

The old axiom claimed every `v ∈ P.vertices` lies on an exposed edge.
That is false for redundant vertices (e.g. an interior point added to
`vertices` without changing `P.Ω`).

What the descent actually needs — and what is true — is the geometric
version: a singleton exposed face `{v}` lies on an exposed edge.
Both axiom call sites already have such a `G = {δ}` (dim 0), so they
can use this theorem directly with no `P.vertices` detour.
-/

/-- A dim-0 exposed face containing `x` is the singleton `{x}`.
Extracted from `exposed_face_dim_zero_mem_vertices` Step 1. -/
lemma exposed_face_dim_zero_singleton {n : ℕ} (G : Set (CoeffVec n))
    (hG_dim_0 : Module.finrank ℝ (affineSpan ℝ G).direction = 0)
    (x : CoeffVec n) (hx_in_G : x ∈ G) : G = {x} := by
  ext y
  constructor
  · intro hy_in_G
    have h_sub : y - x ∈ (affineSpan ℝ G).direction := by
      apply AffineSubspace.vsub_mem_direction
      · exact subset_affineSpan ℝ G hy_in_G
      · exact subset_affineSpan ℝ G hx_in_G
    have h_dir_eq_bot : (affineSpan ℝ G).direction = ⊥ :=
      (Submodule.finrank_eq_zero (R := ℝ) (M := CoeffVec n)).mp hG_dim_0
    rw [h_dir_eq_bot] at h_sub
    have h_y_sub_x_zero : y - x = 0 := by simpa [Submodule.mem_bot] using h_sub
    exact sub_eq_zero.mp h_y_sub_x_zero
  · intro hy_eq
    rw [hy_eq]
    exact hx_in_G

/-- The affine span of a two-point set has direction `ℝ ∙ (w -ᵥ v)`. -/
private lemma dir_affineSpan_pair {n : ℕ} (v w : CoeffVec n) :
    (affineSpan ℝ ({v, w} : Set (CoeffVec n))).direction = ℝ ∙ (w -ᵥ v) := by
  rw [direction_affineSpan, vectorSpan_pair_rev]

/-- A segment between distinct points has affine dimension 1. -/
lemma segment_affine_dim_one {n : ℕ} (v w : CoeffVec n) (hvw : v ≠ w) :
    Module.finrank ℝ (affineSpan ℝ (segment ℝ v w)).direction = 1 := by
  have hseg : segment ℝ v w = convexHull ℝ ({v, w} : Set (CoeffVec n)) := by
    rw [convexHull_pair]
  have haff : affineSpan ℝ (segment ℝ v w) = affineSpan ℝ ({v, w} : Set (CoeffVec n)) := by
    rw [hseg, affineSpan_convexHull]
  rw [haff, dir_affineSpan_pair]
  have hne : w -ᵥ v ≠ (0 : CoeffVec n) := by
    intro h
    apply hvw
    have : w -ᵥ v = (0 : CoeffVec n) ↔ w = v := vsub_eq_zero_iff_eq
    rw [this] at h
    exact h.symm
  exact finrank_span_singleton hne

/-- Sublevel `{y | f y ≤ c}` is convex. -/
private lemma convex_sublevel {n : ℕ} (f : CoeffVec n →ₗ[ℝ] ℝ) (c : ℝ) :
    Convex ℝ {y : CoeffVec n | f y ≤ c} := by
  intro y hy z hz a b ha hb hab
  simp only [Set.mem_setOf_eq, smul_eq_mul] at *
  calc f (a • y + b • z) = a * f y + b * f z := by simp [map_add, map_smul, smul_eq_mul]
    _ ≤ a * c + b * c := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hy ha
        · exact mul_le_mul_of_nonneg_left hz hb
    _ = (a + b) * c := by rw [← add_mul]
    _ = c := by simp [hab]

/-- A linear functional bounded above on vertices is bounded above on `P.Ω`. -/
private lemma upper_on_Ω_of_upper_on_vertices {n : ℕ} (P : Polytope n)
    (f : CoeffVec n →ₗ[ℝ] ℝ) (c : ℝ) (h : ∀ v ∈ P.vertices, f v ≤ c) :
    ∀ x ∈ P.Ω, f x ≤ c := by
  intro x hx
  have hsub : (P.vertices : Set (CoeffVec n)) ⊆ {y | f y ≤ c} := fun v hv => h v hv
  have hΩ : P.Ω ⊆ {y | f y ≤ c} := by
    unfold Polytope.Ω
    exact convexHull_min hsub (convex_sublevel f c)
  exact hΩ hx

/-- Full-dimensionality: interior nonempty forces `affineSpan P.Ω = ⊤`. -/
private lemma affΩ_eq_top {n : ℕ} (P : Polytope n) :
    affineSpan ℝ P.Ω = ⊤ := by
  have h_convex : Convex ℝ P.Ω := convex_convexHull ℝ _
  have := (Convex.interior_nonempty_iff_affineSpan_eq_top h_convex).mp (by
    simpa using P.interior_nonempty)
  exact this

/-- `P.Ω` has direction dimension `n+1`. -/
private lemma polytope_dir_finrank {n : ℕ} (P : Polytope n) :
    Module.finrank ℝ (affineSpan ℝ P.Ω).direction = n + 1 := by
  rw [affΩ_eq_top, AffineSubspace.direction_top, finrank_top, finrank_CoeffVec]

/-- A point of a singleton exposed face is on the frontier of `P.Ω`.
We show `v ∈ frontier G` (`G = {v}` closed with empty interior), then
transport via `frontier_of_exposed_face_implies_frontier_of_polytope`. -/
private lemma singleton_face_point_frontier {n : ℕ} (P : Polytope n)
    (v : CoeffVec n) (G : Set (CoeffVec n))
    (hG_exp : IsExposedFace P G) (hG1 : G = {v}) :
    v ∈ frontier P.Ω := by
  obtain ⟨hp, hG_eq⟩ := hG_exp
  have hv_in_G : v ∈ G := by rw [hG1]; rfl
  have hG_closed : IsClosed G := by
    rw [hG1]; exact isClosed_singleton
  have hv_not_int_G : v ∉ interior G := by
    rw [hG1]
    intro hmem
    obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.mp isOpen_interior v hmem
    obtain ⟨u, hu_ne⟩ := exists_ne (0 : CoeffVec n)
    have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    have hδ_pos : 0 < ε / (2 * ‖u‖) := by positivity
    set δ := ε / (2 * ‖u‖) with hδ_def
    have hy_ball : v + δ • u ∈ Metric.ball v ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : (v + δ • u) - v = δ • u := by abel
      rw [h1, norm_smul, Real.norm_of_nonneg hδ_pos.le]
      calc δ * ‖u‖ = ε / 2 := by rw [hδ_def]; field_simp
        _ < ε := by linarith
    have hy_in : v + δ • u ∈ ({v} : Set (CoeffVec n)) :=
      interior_subset (hB hy_ball)
    have hy_eq : v + δ • u = v := Set.mem_singleton_iff.mp hy_in
    have hsm : δ • u = 0 := by
      have : (v + δ • u) - v = 0 := by rw [hy_eq]; abel
      have h2 : (v + δ • u) - v = δ • u := by abel
      rw [h2] at this
      exact this
    have : u = 0 := by
      rcases smul_eq_zero.mp hsm with h | h
      · exact absurd h (ne_of_gt hδ_pos)
      · exact h
    exact hu_ne this
  have hv_front_G : v ∈ frontier G := by
    rw [frontier_eq_for_closed G hG_closed]
    exact ⟨hv_in_G, hv_not_int_G⟩
  exact frontier_of_exposed_face_implies_frontier_of_polytope P G hp hG_eq v hv_in_G hv_front_G

/-- Geometric vertex → exposed edge.

Given a singleton exposed face `G = {v}`, there is an exposed edge
`E` of `P` with `v ∈ E`. The proof tilts the exposing functional:
`ℓ* = ℓ + t*·p` where `t*` is the first time another vertex ties for
the maximum. If several vertices tie at once on different rays, a
coordinate-projection perturbation strictly shrinks the tying set;
strong induction on its cardinality leaves a collinear tying set,
whose convex hull with `v` is a segment.
-/
theorem exists_exposed_edge_of_singleton {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (v : CoeffVec n) (G : Set (CoeffVec n))
    (hG_exp : IsExposedFace P G) (hG1 : G = {v}) :
    ∃ E, IsExposedEdge P E ∧ v ∈ E := by
  obtain ⟨hp0, hG_eq⟩ := hG_exp
  have hv_in_Ω : v ∈ P.Ω := (hG_eq ▸ (by rw [hG1]; rfl : v ∈ G)).1
  have hv_val : hp0.f v = hp0.c := (hG_eq ▸ (by rw [hG1]; rfl : v ∈ G)).2
  have hfull : Module.finrank ℝ (affineSpan ℝ P.Ω).direction = n + 1 :=
    polytope_dir_finrank P
  -- Strict separation of all other vertices.
  have hbelow : ∀ u ∈ P.vertices, u ≠ v → hp0.f u < hp0.c := by
    intro u hu hne
    have hu_Ω : u ∈ P.Ω := subset_convexHull ℝ _ hu
    have hle : hp0.f u ≤ hp0.c := hp0.upper_bound u hu_Ω
    have hne' : hp0.f u ≠ hp0.c := by
      intro heq
      have hu_G : u ∈ G := by rw [hG_eq]; exact ⟨hu_Ω, heq⟩
      rw [hG1] at hu_G
      exact hne (Set.mem_singleton_iff.mp hu_G)
    exact lt_of_le_of_ne hle hne'
  -- An interior point differs from `v` (since `v` is frontier).
  have hv_front : v ∈ frontier P.Ω :=
    singleton_face_point_frontier P v G ⟨hp0, hG_eq⟩ hG1
  have hv_not_int : v ∉ interior P.Ω := frontier_point_not_interior P v hv_front
  obtain ⟨y0, hy0⟩ := P.interior_nonempty
  have hy0_ne : y0 ≠ v := fun h => hv_not_int (h ▸ hy0)
  -- A coordinate functional separating `y0 - v`.
  have hsep : ∃ j : Fin (n+1), y0 j ≠ v j := by
    by_contra h; push_neg at h
    exact hy0_ne (funext h)
  obtain ⟨j0, hj0⟩ := hsep
  -- `p` with `p y0 > p v`: oriented coordinate projection.
  let p : CoeffVec n →ₗ[ℝ] ℝ :=
    if _ : y0 j0 > v j0 then LinearMap.proj j0 else -LinearMap.proj j0
  have hp_gt : p y0 > p v := by
    unfold p
    by_cases h : y0 j0 > v j0
    · rw [dif_pos h]
      simpa [LinearMap.proj_apply] using h
    · rw [dif_neg h]
      simp only [LinearMap.neg_apply, LinearMap.proj_apply]
      have hlt : y0 j0 < v j0 := lt_of_le_of_ne (le_of_not_gt h) hj0
      linarith
  -- Some vertex exceeds `v` under `p` (else `y0` could not).
  have hvert_gt : ∃ u ∈ P.vertices, p v < p u := by
    by_contra hnone
    push_neg at hnone
    have hsub : (P.vertices : Set (CoeffVec n)) ⊆ {y | p y ≤ p v} :=
      fun u hu => hnone u hu
    have hΩ : ∀ x ∈ P.Ω, p x ≤ p v := fun x hx => by
      have := convexHull_min hsub (convex_sublevel p (p v)) (by unfold Polytope.Ω at hx; exact hx)
      exact this
    have := hΩ y0 (interior_subset hy0)
    linarith [hp_gt]
  classical
  -- Work with vertices as a filtered finset excluding `v` itself.
  let V' : Finset (CoeffVec n) := P.vertices.filter (fun u => u != v)
  have hmem_V' : ∀ u ∈ P.vertices, u ≠ v ↔ u ∈ V' := by
    intro u hu
    simp [V', hu]
  -- Strong induction on the tying-set cardinality, general over `p`.
  -- For `p` with a higher vertex, `S₊` is nonempty; `t*` is the first-tie
  -- time and `J` the tying set. Proved first; applied to the initial `p`
  -- at the end of this proof.
  have aux : ∀ k : ℕ, ∀ p : CoeffVec n →ₗ[ℝ] ℝ,
      ∀ (hgt : ∃ u ∈ P.vertices, p v < p u)
        (S : Finset (CoeffVec n))
        (hSeq : S = V'.filter (fun u => 0 < p u - p v))
        (hSne : S.Nonempty)
        (t : ℝ)
        (hteq : t = (S.image (fun u => (hp0.c - hp0.f u) / (p u - p v))).min'
          (Finset.image_nonempty.mpr hSne))
        (J : Finset (CoeffVec n))
        (hJeq : J = S.filter (fun u => (hp0.c - hp0.f u) / (p u - p v) = t)),
      J.card = k → ∃ E, IsExposedEdge P E ∧ v ∈ E := by
    -- Prove `aux` by strong induction on `k`.
    intro k
    refine Nat.strong_induction_on k fun k ih => ?_
    intro p hgt S hSeq hSne t hteq J hJeq hcard
      -- Keep `S,t,J` as variables with their equations; unfold selectively.
    -- `J` is nonempty (the minimum is attained).
    have hJne : J.Nonempty := by
      have hmin : t ∈ S.image (fun u => (hp0.c - hp0.f u) / (p u - p v)) := by
        rw [hteq]
        exact Finset.min'_mem _ _
      obtain ⟨u, huS, hu_eq⟩ := Finset.mem_image.mp hmin
      refine ⟨u, ?_⟩
      rw [hJeq]
      exact Finset.mem_filter.mpr ⟨huS, hu_eq⟩
    -- Pick the reference tying vertex (copy first: `obtain` consumes its source).
    have hj0ex := hJne
    obtain ⟨j0, hj0⟩ := hj0ex
    -- Unpack `j0 ∈ J`: tying, in `S`, in `V'`, a vertex `≠ v`.
    have hj0f : j0 ∈ S.filter
        (fun u => (hp0.c - hp0.f u) / (p u - p v) = t) := by
      rw [← hJeq]
      exact hj0
    have hj0S : j0 ∈ S := (Finset.mem_filter.mp hj0f).1
    have hj0tie : (hp0.c - hp0.f j0) / (p j0 - p v) = t :=
      (Finset.mem_filter.mp hj0f).2
    rw [hSeq] at hj0S
    have hj0V' : j0 ∈ V' := (Finset.mem_filter.mp hj0S).1
    have hj0β : 0 < p j0 - p v := (Finset.mem_filter.mp hj0S).2
    have hj0vert : j0 ∈ P.vertices := Finset.filter_subset _ _ hj0V'
    have hj0ne : j0 ≠ v := (hmem_V' j0 hj0vert).mpr hj0V'
    have hαj0 : 0 < hp0.c - hp0.f j0 := sub_pos.mpr (hbelow j0 hj0vert hj0ne)
    -- Gaps are positive on `V'`.
    have hαpos : ∀ u ∈ V', 0 < hp0.c - hp0.f u := by
      intro u hu
      have huv : u ∈ P.vertices := Finset.filter_subset _ _ hu
      have hne : u ≠ v := (hmem_V' u huv).mpr hu
      exact sub_pos.mpr (hbelow u huv hne)
    -- The first-tie time is positive.
    have htpos : 0 < t := by
      have hmem : t ∈ S.image (fun u => (hp0.c - hp0.f u) / (p u - p v)) := by
        rw [hteq]
        exact Finset.min'_mem _ _
      obtain ⟨u, huS, hu_eq⟩ := Finset.mem_image.mp hmem
      rw [hSeq] at huS
      have huV' : u ∈ V' := (Finset.mem_filter.mp huS).1
      have hβ : 0 < p u - p v := (Finset.mem_filter.mp huS).2
      rw [← hu_eq]
      exact div_pos (hαpos u huV') hβ
    -- Tilted functional and level.
    set ℓstar : CoeffVec n →ₗ[ℝ] ℝ := hp0.f + t • p with hℓdef
    set cstar : ℝ := hp0.c + t * p v with hcdef
    have hℓstar_eq : ∀ u : CoeffVec n,
        ℓstar u - cstar = t * (p u - p v) - (hp0.c - hp0.f u) := by
      intro u
      simp only [hℓdef, hcdef, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul]
      ring
    have hℓv : ℓstar v = cstar := by
      have : ℓstar v - cstar = t * (p v - p v) - (hp0.c - hp0.f v) := hℓstar_eq v
      rw [hv_val] at this
      simp only [sub_self, mul_zero, sub_zero] at this
      linarith [this]
    -- Tilted upper bound on vertices, hence on `Ω`.
    have hupperV : ∀ u ∈ P.vertices, ℓstar u ≤ cstar := by
      intro u hu
      by_cases huv : u = v
      · subst huv
        exact le_of_eq hℓv
      · have hα : 0 < hp0.c - hp0.f u := sub_pos.mpr (hbelow u hu huv)
        have hle : t * (p u - p v) - (hp0.c - hp0.f u) ≤ 0 := by
          by_cases hβ : 0 < p u - p v
          · have huV' : u ∈ V' := (hmem_V' u hu).mp huv
            have huS : u ∈ S := by
              rw [hSeq]
              exact Finset.mem_filter.mpr ⟨huV', hβ⟩
            have hmin : t ≤ (hp0.c - hp0.f u) / (p u - p v) := by
              rw [hteq]
              exact Finset.min'_le _ _
                (Finset.mem_image.mpr ⟨u, huS, rfl⟩)
            have hmul : t * (p u - p v) ≤ hp0.c - hp0.f u :=
              (le_div_iff₀ hβ).mp hmin
            linarith [hmul]
          · push_neg at hβ
            have hmul : t * (p u - p v) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos htpos.le hβ
            linarith [hmul, hα]
        have := hℓstar_eq u
        linarith [this, hle]
    have hupperΩ : ∀ x ∈ P.Ω, ℓstar x ≤ cstar :=
      upper_on_Ω_of_upper_on_vertices P ℓstar cstar (fun u hu => hupperV u hu)
    -- Collinearity test: all tying vertices on one ray from `v`?
    by_cases hcol : ∀ u ∈ J, (hp0.c - hp0.f j0) • (u - v)
        = (hp0.c - hp0.f u) • (j0 - v)
    · -- Collinear tying set: `E*` is a segment.
      -- The tilted face.
      set Estar : Set (CoeffVec n) := P.Ω ∩ {x | ℓstar x = cstar} with hEdef
      have hHconv : Convex ℝ {x : CoeffVec n | ℓstar x = cstar} := by
        intro x hx y hy a b ha hb hab
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        have e : ℓstar (a • x + b • y) = a * cstar + b * cstar := by
          simp [map_add, map_smul, smul_eq_mul, hx, hy]
        rw [e, ← add_mul, hab, one_mul]
      have hΩconv : Convex ℝ P.Ω := convex_convexHull ℝ _
      have hEconv : Convex ℝ Estar := hΩconv.inter hHconv
      have hvE : v ∈ Estar := ⟨hv_in_Ω, hℓv⟩
      -- Tying vertices lie in `Estar`.
      have hmaxE : ∀ u ∈ J, u ∈ Estar := by
        intro u hu
        have huS : u ∈ S := Finset.filter_subset _ _ (by rw [← hJeq]; exact hu)
        have huV : u ∈ V' := by
          have : u ∈ V'.filter (fun u => 0 < p u - p v) := by rw [← hSeq]; exact huS
          exact (Finset.mem_filter.mp this).1
        have huvert : u ∈ P.vertices := Finset.filter_subset _ _ huV
        have hβ : 0 < p u - p v := by
          have : u ∈ V'.filter (fun u => 0 < p u - p v) := by rw [← hSeq]; exact huS
          exact (Finset.mem_filter.mp this).2
        have hru : (hp0.c - hp0.f u) / (p u - p v) = t := by
          have : u ∈ S.filter
              (fun u => (hp0.c - hp0.f u) / (p u - p v) = t) := by
            rw [← hJeq]; exact hu
          exact (Finset.mem_filter.mp this).2
        have hαeq : hp0.c - hp0.f u = t * (p u - p v) :=
          (div_eq_iff (ne_of_gt hβ)).mp hru
        have hval : ℓstar u = cstar := by
          have h1 := hℓstar_eq u
          have h2 : t * (p u - p v) - (hp0.c - hp0.f u) = 0 := by linarith [hαeq]
          linarith [h1, h2]
        exact ⟨subset_convexHull ℝ _ huvert, hval⟩
      -- Every tying vertex is on the ray through `j0`.
      have hray : ∀ u ∈ J, u - v
          = ((hp0.c - hp0.f u) / (hp0.c - hp0.f j0)) • (j0 - v) := by
        intro u hu
        have hwu := hcol u hu
        have hαj : (hp0.c - hp0.f j0) ≠ 0 := ne_of_gt hαj0
        calc u - v
            = ((hp0.c - hp0.f j0))⁻¹ • (((hp0.c - hp0.f j0)) • (u - v)) := by
              rw [smul_smul, inv_mul_cancel₀ hαj, one_smul]
          _ = ((hp0.c - hp0.f j0))⁻¹ • (((hp0.c - hp0.f u)) • (j0 - v)) := by
              rw [hwu]
          _ = ((hp0.c - hp0.f u) / (hp0.c - hp0.f j0)) • (j0 - v) := by
              rw [smul_smul, div_eq_mul_inv, mul_comm]
      -- Farthest ratio gives the other endpoint.
      set T : Finset ℝ :=
        J.image (fun u => (hp0.c - hp0.f u) / (hp0.c - hp0.f j0)) with hTdef
      have hTne : T.Nonempty := Finset.image_nonempty.mpr hJne
      set tmax : ℝ := T.max' hTne with htmaxdef
      have htmax_pos : 0 < tmax := by
        have h1 : (1 : ℝ) ∈ T := by
          rw [hTdef]
          refine Finset.mem_image.mpr ⟨j0, hj0, ?_⟩
          rw [div_self (ne_of_gt hαj0)]
        have hle : (1 : ℝ) ≤ tmax := Finset.le_max' _ _ h1
        linarith [hle]
      have htmax_mem : tmax ∈ T := Finset.max'_mem _ _
      rw [hTdef] at htmax_mem
      obtain ⟨wmax, hwmaxJ, hwmax_eq⟩ := Finset.mem_image.mp htmax_mem
      have hwmax_eq' : (hp0.c - hp0.f wmax) / (hp0.c - hp0.f j0) = tmax :=
        hwmax_eq
      have hwmaxS : wmax ∈ S :=
        Finset.filter_subset _ _ (by rw [← hJeq]; exact hwmaxJ)
      have hwmaxV' : wmax ∈ V' := by
        have hmem : wmax ∈ V'.filter (fun u => 0 < p u - p v) := by
          rw [← hSeq]; exact hwmaxS
        exact (Finset.mem_filter.mp hmem).1
      have hwmax_vert : wmax ∈ P.vertices := Finset.filter_subset _ _ hwmaxV'
      have hwmax_ne : wmax ≠ v := (hmem_V' wmax hwmax_vert).mpr hwmaxV'
      have hwmaxE : wmax ∈ Estar := hmaxE wmax hwmaxJ
      -- Ratios lie in `[0, tmax]`.
      have hratnn : ∀ u ∈ J, 0 ≤ (hp0.c - hp0.f u) / (hp0.c - hp0.f j0) := by
        intro u hu
        have huS : u ∈ S :=
          Finset.filter_subset _ _ (by rw [← hJeq]; exact hu)
        have huV : u ∈ V' := by
          have hmem : u ∈ V'.filter (fun u => 0 < p u - p v) := by
            rw [← hSeq]; exact huS
          exact (Finset.mem_filter.mp hmem).1
        exact div_nonneg (le_of_lt (hαpos u huV)) (le_of_lt hαj0)
      have hratle : ∀ u ∈ J,
          (hp0.c - hp0.f u) / (hp0.c - hp0.f j0) ≤ tmax := by
        intro u hu
        have hmem : (hp0.c - hp0.f u) / (hp0.c - hp0.f j0) ∈ T := by
          rw [hTdef]
          exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
        exact Finset.le_max' _ _ hmem
      -- Every tying vertex lies on `segment v wmax`.
      have hsegmem : ∀ u ∈ J, u ∈ segment ℝ v wmax := by
        intro u hu
        set ru : ℝ := (hp0.c - hp0.f u) / (hp0.c - hp0.f j0) with hratdef
        set mu : ℝ := ru / tmax with hmudef
        have hratnn' : 0 ≤ ru := hratnn u hu
        have hratle' : ru ≤ tmax := hratle u hu
        have hmun : 0 ≤ mu := div_nonneg hratnn' htmax_pos.le
        have hmule : mu ≤ 1 := (div_le_one htmax_pos).mpr hratle'
        have hu_eq : u - v = ru • (j0 - v) := hray u hu
        have hw_eq : wmax - v = tmax • (j0 - v) := by
          have h := hray wmax hwmaxJ
          rw [hwmax_eq'] at h
          exact h
        have hmut : mu * tmax = ru := div_mul_cancel₀ _ (ne_of_gt htmax_pos)
        have hcomb : (1 - mu) • v + mu • wmax = u := by
          calc (1 - mu) • v + mu • wmax
              = v + mu • (wmax - v) := by
                rw [sub_smul, one_smul, smul_sub]; abel
            _ = v + (mu * tmax) • (j0 - v) := by rw [hw_eq, ← smul_smul]
            _ = v + ru • (j0 - v) := by rw [hmut]
            _ = u := by rw [← hu_eq]; abel
        rw [segment_eq_image]
        exact ⟨mu, Set.mem_Icc.mpr ⟨hmun, hmule⟩, hcomb⟩
      -- Hence `conv {v} ∪ J ⊆ segment`, and `segment ⊆ Estar`.
      have hMsub : ({v} ∪ ↑J : Set (CoeffVec n)) ⊆ segment ℝ v wmax := by
        intro x hx
        rcases hx with h | h
        · rw [Set.mem_singleton_iff.mp h]
          rw [segment_eq_image]
          refine ⟨0, Set.mem_Icc.mpr ⟨le_refl _, zero_le_one⟩, ?_⟩
          simp
        · have hxJ : x ∈ J := Finset.mem_coe.mp h
          exact hsegmem x hxJ
      have hconv_sub : convexHull ℝ ({v} ∪ ↑J : Set (CoeffVec n))
          ⊆ segment ℝ v wmax :=
        convexHull_min hMsub (convex_segment v wmax)
      have hseg_sub : segment ℝ v wmax ⊆ Estar := by
        have hpair : convexHull ℝ ({v, wmax} : Set (CoeffVec n)) ⊆ Estar :=
          convexHull_min (by
            intro x hx
            rcases Set.mem_insert_iff.mp hx with h | h
            · rw [h]; exact hvE
            · rw [Set.mem_singleton_iff.mp h]; exact hwmaxE) hEconv
        rw [convexHull_pair] at hpair
        exact hpair
      -- Support in maximizers: `Estar ⊆ conv {v} ∪ J`.
      have hsupp : Estar ⊆ convexHull ℝ ({v} ∪ ↑J : Set (CoeffVec n)) := by
        intro x hxE
        have hxΩ : x ∈ P.Ω := hxE.1
        have hxΩ' : x ∈ convexHull ℝ (P.vertices : Set (CoeffVec n)) := hxΩ
        obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.mp hxΩ'
        have hxeq : ℓstar x = cstar := hxE.2
        have hsum : ℓstar x = ∑ y ∈ P.vertices, w y * ℓstar y := by
          rw [← hwx, map_sum]
          apply Finset.sum_congr rfl
          intro y hy
          rw [map_smul, smul_eq_mul]
        have hc : cstar = ∑ y ∈ P.vertices, w y * cstar := by
          calc cstar = cstar * (∑ y ∈ P.vertices, w y) := by rw [hw1, mul_one]
            _ = ∑ y ∈ P.vertices, cstar * w y := by rw [Finset.mul_sum]
            _ = ∑ y ∈ P.vertices, w y * cstar := by
                apply Finset.sum_congr rfl; intro y hy; ring
        have hdiff : cstar - ℓstar x
            = ∑ y ∈ P.vertices, w y * (cstar - ℓstar y) := by
          have e1 : (∑ y ∈ P.vertices, w y * cstar)
              - (∑ y ∈ P.vertices, w y * ℓstar y)
              = ∑ y ∈ P.vertices, w y * (cstar - ℓstar y) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro y hy
            ring
          conv_lhs => rw [hc, hsum]
          exact e1
        -- Weights vanish off the maximizers.
        have hwMv : ∀ y ∈ P.vertices, ℓstar y ≠ cstar → w y = 0 := by
          intro y hy hne
          have hlt : ℓstar y < cstar := lt_of_le_of_ne (hupperV y hy) hne
          by_contra hwne
          have hwpos : 0 < w y := lt_of_le_of_ne (hw0 y hy) (Ne.symm hwne)
          have hnn : ∀ z ∈ P.vertices, 0 ≤ w z * (cstar - ℓstar z) :=
            fun z hz => mul_nonneg (hw0 z hz) (sub_nonneg.mpr (hupperV z hz))
          have hpos : 0 < w y * (cstar - ℓstar y) :=
            mul_pos hwpos (sub_pos.mpr hlt)
          have hsumpos : 0 < ∑ z ∈ P.vertices, w z * (cstar - ℓstar z) := by
            rw [← Finset.add_sum_erase _ _ hy]
            exact add_pos_of_pos_of_nonneg hpos
              (Finset.sum_nonneg (fun z hz => hnn z (Finset.mem_of_mem_erase hz)))
          linarith [hdiff, hsumpos, hxeq]
        -- Restrict to maximizer vertices, then widen to `{v} ∪ J`.
        set Mv : Finset (CoeffVec n) :=
          P.vertices.filter (fun y => ℓstar y = cstar) with hMvdef
        have hMvsub : Mv ⊆ P.vertices := Finset.filter_subset _ _
        have hsum1 : ∑ y ∈ Mv, w y = 1 := by
          have h := Finset.sum_subset hMvsub (fun y hy hyM => hwMv y hy
            (by intro heq; exact hyM (Finset.mem_filter.mpr ⟨hy, heq⟩)))
          rw [hw1] at h
          exact h
        have hsumx : ∑ y ∈ Mv, w y • y = x := by
          have h := Finset.sum_subset hMvsub (fun y hy hyM => by
            have h0 : w y = 0 := hwMv y hy
              (by intro heq; exact hyM (Finset.mem_filter.mpr ⟨hy, heq⟩))
            show w y • y = 0
            simp [h0])
          rw [hwx] at h
          exact h
        have hxMv : x ∈ convexHull ℝ (Mv : Set (CoeffVec n)) := by
          rw [Finset.mem_convexHull']
          exact ⟨w, fun y hy => hw0 y (hMvsub hy), hsum1, hsumx⟩
        apply convexHull_mono _ hxMv
        intro y hy
        have hyF : y ∈ Mv := Finset.mem_coe.mp hy
        have hyv := (Finset.mem_filter.mp hyF).1
        have hyeq := (Finset.mem_filter.mp hyF).2
        by_cases heq : y = v
        · exact Set.mem_union_left _ (Set.mem_singleton_iff.mpr heq)
        · apply Set.mem_union_right _
          have hyV' : y ∈ V' := (hmem_V' y hyv).mp heq
          have hαy : 0 < hp0.c - hp0.f y := sub_pos.mpr (hbelow y hyv heq)
          have heq_t : hp0.c - hp0.f y = t * (p y - p v) := by
            have he : t * (p y - p v) - (hp0.c - hp0.f y) = 0 := by
              have h1 := hℓstar_eq y
              have h2 : ℓstar y - cstar = 0 := sub_eq_zero.mpr hyeq
              linarith [h1, h2]
            linarith [he]
          have hβy : 0 < p y - p v := by
            have hpos : 0 < t * (p y - p v) := by linarith [heq_t, hαy]
            exact pos_of_mul_pos_right hpos htpos.le
          have hyS : y ∈ S := by
            rw [hSeq]
            exact Finset.mem_filter.mpr ⟨hyV', hβy⟩
          have hru : (hp0.c - hp0.f y) / (p y - p v) = t :=
            (div_eq_iff (ne_of_gt hβy)).mpr heq_t
          have : y ∈ S.filter
              (fun u => (hp0.c - hp0.f u) / (p u - p v) = t) :=
            Finset.mem_filter.mpr ⟨hyS, hru⟩
          rw [← hJeq] at this
          exact Finset.mem_coe.mpr this
      -- `Estar` is the segment: dimension 1, nonzero exposer.
      have hEeq : Estar = segment ℝ v wmax :=
        Subset.antisymm (fun x hx => hconv_sub (hsupp hx)) hseg_sub
      have hdim : Module.finrank ℝ (affineSpan ℝ Estar).direction = 1 := by
        rw [hEeq]
        exact segment_affine_dim_one v wmax (Ne.symm hwmax_ne)
      have hne_star : ℓstar ≠ 0 := by
        intro hzero
        have hEΩ : Estar = P.Ω := by
          ext x
          constructor
          · intro hx; exact hx.1
          · intro hx
            refine ⟨hx, ?_⟩
            show ℓstar x = cstar
            have hcv : cstar = 0 := by rw [← hℓv, hzero]; rfl
            rw [hzero, hcv]
            simp
        have hdimΩ : Module.finrank ℝ (affineSpan ℝ Estar).direction = n + 1 := by
          rw [hEΩ]; exact hfull
        rw [hdim] at hdimΩ
        omega
      obtain ⟨hpE, hEface⟩ : IsExposedFace P Estar :=
        ⟨⟨ℓstar, cstar, hne_star,
          fun x hx => hupperΩ x hx, ⟨v, hv_in_Ω, hℓv⟩⟩, rfl⟩
      exact ⟨Estar, ⟨hpE, hEface, hEface ▸ hdim⟩, hvE⟩
    · -- Non-collinear: shrink the tying set and apply `ih`.
      -- Get two tying vertices on different rays.
      push_neg at hcol
      obtain ⟨i1, hi1J, hi1w⟩ := hcol
      have hi1copy : i1 ∈ J := hi1J
      -- Separating coordinate for `w = αj₀(i₁-v) - αi₁(j₀-v) ≠ 0`.
      set wvec : CoeffVec n :=
        (hp0.c - hp0.f j0) • (i1 - v) - (hp0.c - hp0.f i1) • (j0 - v) with hwdef
      have hw_ne : wvec ≠ 0 := sub_ne_zero.mpr hi1w
      have hco : ∃ jc : Fin (n + 1), wvec jc ≠ 0 := by
        by_contra h
        push_neg at h
        exact hw_ne (funext h)
      obtain ⟨jc, hjc⟩ := hco
      set q : CoeffVec n →ₗ[ℝ] ℝ := LinearMap.proj jc with hqdef
      have hqw : q wvec ≠ 0 := by
        have e : q wvec = wvec jc := by simp only [hqdef, LinearMap.proj_apply]
        rw [e]
        exact hjc
      have hqw' : (hp0.c - hp0.f j0) * (q i1 - q v)
          - (hp0.c - hp0.f i1) * (q j0 - q v) ≠ 0 := by
        have e : q wvec = (hp0.c - hp0.f j0) * (q i1 - q v)
            - (hp0.c - hp0.f i1) * (q j0 - q v) := by
          simp only [hwdef, map_sub, map_smul, smul_eq_mul, map_sub]
        rw [← e]
        exact hqw
      -- `i1` facts.
      have hi1S : i1 ∈ S :=
        Finset.filter_subset _ _ (by rw [← hJeq]; exact hi1copy)
      have hi1V : i1 ∈ V' := by
        have hmem : i1 ∈ V'.filter (fun u => 0 < p u - p v) := by
          rw [← hSeq]; exact hi1S
        exact (Finset.mem_filter.mp hmem).1
      have hi1β : 0 < p i1 - p v := by
        have hmem : i1 ∈ V'.filter (fun u => 0 < p u - p v) := by
          rw [← hSeq]; exact hi1S
        exact (Finset.mem_filter.mp hmem).2
      have hi1tie : (hp0.c - hp0.f i1) / (p i1 - p v) = t := by
        have hmem : i1 ∈ S.filter
            (fun u => (hp0.c - hp0.f u) / (p u - p v) = t) := by
          rw [← hJeq]; exact hi1copy
        exact (Finset.mem_filter.mp hmem).2
      have hαi1 : 0 < hp0.c - hp0.f i1 := hαpos i1 hi1V
      -- Gap below which outsiders stay above (`1` dummy avoids emptiness).
      set gapSet : Finset ℝ := insert (1 : ℝ) ((S \ J).image
        (fun u => (hp0.c - hp0.f u) / (p u - p v) - t)) with hgapdef
      have hgappos : ∀ b ∈ gapSet, 0 < b := by
        intro b hb
        rw [hgapdef] at hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact one_pos
        · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
          have huS : u ∈ S := (Finset.mem_sdiff.mp hu).1
          have huJ : u ∉ J := (Finset.mem_sdiff.mp hu).2
          have huV : u ∈ V' := by
            have hmem : u ∈ V'.filter (fun u => 0 < p u - p v) := by
              rw [← hSeq]; exact huS
            exact (Finset.mem_filter.mp hmem).1
          have hβ : 0 < p u - p v := by
            have hmem : u ∈ V'.filter (fun u => 0 < p u - p v) := by
              rw [← hSeq]; exact huS
            exact (Finset.mem_filter.mp hmem).2
          have hge : t ≤ (hp0.c - hp0.f u) / (p u - p v) := by
            rw [hteq]
            exact Finset.min'_le _ _
              (Finset.mem_image.mpr ⟨u, huS, rfl⟩)
          have hne : (hp0.c - hp0.f u) / (p u - p v) ≠ t := by
            intro heq
            exact huJ (by
              rw [hJeq]
              exact Finset.mem_filter.mpr ⟨huS, heq⟩)
          have hgt : t < (hp0.c - hp0.f u) / (p u - p v) :=
            lt_of_le_of_ne hge (Ne.symm hne)
          linarith [hgt]
      set δgap : ℝ := gapSet.min' (Finset.insert_nonempty _ _) with hδdef
      have h1mem : (1 : ℝ) ∈ gapSet := by
        rw [hgapdef]
        exact Finset.mem_insert_self _ _
      have hδpos : 0 < δgap := by
        have hmem : δgap ∈ gapSet := Finset.min'_mem _ _
        exact hgappos _ hmem
      have hδle1 : δgap ≤ 1 := Finset.min'_le _ _ h1mem
      have hδgap : ∀ u ∈ S \ J,
          δgap ≤ (hp0.c - hp0.f u) / (p u - p v) - t := by
        intro u hu
        have hmem : (hp0.c - hp0.f u) / (p u - p v) - t ∈ gapSet := by
          rw [hgapdef]
          exact Finset.mem_insert_of_mem
            (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
        exact Finset.min'_le _ _ hmem
      -- Per-case epsilon bounds (explicitly parenthesized union).
      set Gf : CoeffVec n → ℝ := fun u => |q u - q v| + 1 with hGdef
      have hGpos : ∀ u, 0 < Gf u := by
        intro u
        rw [hGdef]
        have := abs_nonneg (q u - q v)
        linarith
      set B1 : Finset ℝ := (V'.filter (fun u => 0 < p u - p v)).image
        (fun u => (p u - p v) / (2 * Gf u)) with hB1def
      set B2 : Finset ℝ := (V'.filter (fun u => 0 < p u - p v)).image
        (fun u => δgap * (p u - p v) * (p u - p v)
          / (8 * (hp0.c - hp0.f u) * Gf u)) with hB2def
      set B3 : Finset ℝ := (V'.filter (fun u => p u - p v < 0)).image
        (fun u => -(p u - p v) / (2 * Gf u)) with hB3def
      set B4 : Finset ℝ := (V'.filter
        (fun u => p u - p v = 0 ∧ 0 < q u - q v)).image
        (fun u => (hp0.c - hp0.f u) / ((q u - q v) * (t + 1))) with hB4def
      set B : Finset ℝ := insert (1 : ℝ) ((B1 ∪ B2) ∪ (B3 ∪ B4)) with hBdef
      have hB1sub : B1 ⊆ B := by
        intro b hb
        rw [hBdef]
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_union_left _ hb))
      have hB2sub : B2 ⊆ B := by
        intro b hb
        rw [hBdef]
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_union_right _ hb))
      have hB3sub : B3 ⊆ B := by
        intro b hb
        rw [hBdef]
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_right _ (Finset.mem_union_left _ hb))
      have hB4sub : B4 ⊆ B := by
        intro b hb
        rw [hBdef]
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_right _ (Finset.mem_union_right _ hb))
      have hBpos : ∀ b ∈ B, 0 < b := by
        intro b hb
        have hmem : b = 1 ∨ b ∈ B1 ∪ B2 ∪ (B3 ∪ B4) := by
          have h : b ∈ insert (1 : ℝ) ((B1 ∪ B2) ∪ (B3 ∪ B4)) := by
            rw [← hBdef]; exact hb
          exact Finset.mem_insert.mp h
        rcases hmem with rfl | hb
        · exact one_pos
        · rcases Finset.mem_union.mp hb with h | h
          · rcases Finset.mem_union.mp h with h | h
            · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h
              have hβ : 0 < p u - p v := (Finset.mem_filter.mp hu).2
              have hG : 0 < 2 * Gf u :=
                mul_pos (by norm_num) (hGpos u)
              exact div_pos hβ hG
            · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h
              have hβ : 0 < p u - p v := (Finset.mem_filter.mp hu).2
              have huV : u ∈ V' := (Finset.mem_filter.mp hu).1
              have hα : 0 < hp0.c - hp0.f u := hαpos u huV
              have hG : 0 < Gf u := hGpos u
              have hnum : 0 < δgap * (p u - p v) * (p u - p v) :=
                mul_pos (mul_pos hδpos hβ) hβ
              have hden : 0 < 8 * (hp0.c - hp0.f u) * Gf u :=
                mul_pos (mul_pos (by norm_num) hα) hG
              exact div_pos hnum hden
          · rcases Finset.mem_union.mp h with h | h
            · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h
              have hβ : p u - p v < 0 := (Finset.mem_filter.mp hu).2
              have hG : 0 < 2 * Gf u :=
                mul_pos (by norm_num) (hGpos u)
              exact div_pos (by linarith [hβ]) hG
            · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h
              have hmem := Finset.mem_filter.mp hu
              have huV : u ∈ V' := hmem.1
              have hγ : 0 < q u - q v := hmem.2.2
              have hα : 0 < hp0.c - hp0.f u := hαpos u huV
              have ht1 : 0 < t + 1 := by linarith [htpos]
              exact div_pos hα (mul_pos hγ ht1)
      have hBne : B.Nonempty := ⟨1, by
        rw [hBdef]; exact Finset.mem_insert_self _ _⟩
      set ε₀ : ℝ := B.min' hBne / 2 with hεdef
      have hεpos : 0 < ε₀ := by
        have hmin : 0 < B.min' hBne := by
          have hmem : B.min' hBne ∈ B := Finset.min'_mem _ _
          exact hBpos _ hmem
        linarith [hεdef, hmin]
      have hεlt : ∀ b ∈ B, ε₀ < b := by
        intro b hb
        have hle : B.min' hBne ≤ b := Finset.min'_le _ _ hb
        linarith [hεdef, hεpos, hle]
      -- Bound application helpers.
      have happ1 : ∀ u ∈ V', 0 < p u - p v →
          ε₀ < (p u - p v) / (2 * Gf u) := by
        intro u hu hβ
        have hmem : (p u - p v) / (2 * Gf u) ∈ B1 := by
          rw [hB1def]
          exact Finset.mem_image.mpr
            ⟨u, Finset.mem_filter.mpr ⟨hu, hβ⟩, rfl⟩
        exact hεlt _ (hB1sub hmem)
      have happ2 : ∀ u ∈ V', 0 < p u - p v →
          ε₀ < δgap * (p u - p v) * (p u - p v)
            / (8 * (hp0.c - hp0.f u) * Gf u) := by
        intro u hu hβ
        have hmem : δgap * (p u - p v) * (p u - p v)
            / (8 * (hp0.c - hp0.f u) * Gf u) ∈ B2 := by
          rw [hB2def]
          exact Finset.mem_image.mpr
            ⟨u, Finset.mem_filter.mpr ⟨hu, hβ⟩, rfl⟩
        exact hεlt _ (hB2sub hmem)
      have happ3 : ∀ u ∈ V', p u - p v < 0 →
          ε₀ < -(p u - p v) / (2 * Gf u) := by
        intro u hu hβ
        have hmem : -(p u - p v) / (2 * Gf u) ∈ B3 := by
          rw [hB3def]
          exact Finset.mem_image.mpr
            ⟨u, Finset.mem_filter.mpr ⟨hu, hβ⟩, rfl⟩
        exact hεlt _ (hB3sub hmem)
      have happ4 : ∀ u ∈ V', p u - p v = 0 → 0 < q u - q v →
          ε₀ < (hp0.c - hp0.f u) / ((q u - q v) * (t + 1)) := by
        intro u hu hβ hγ
        have hmem : (hp0.c - hp0.f u) / ((q u - q v) * (t + 1)) ∈ B4 := by
          rw [hB4def]
          exact Finset.mem_image.mpr
            ⟨u, Finset.mem_filter.mpr ⟨hu, hβ, hγ⟩, rfl⟩
        exact hεlt _ (hB4sub hmem)
      -- Perturbed functional.
      set pε : CoeffVec n →ₗ[ℝ] ℝ := p + ε₀ • q with hpεdef
      have hpexp : ∀ u, pε u - pε v
          = (p u - p v) + ε₀ * (q u - q v) := by
        intro u
        have e1 : pε u = p u + ε₀ * q u := by
          simp [hpεdef, LinearMap.add_apply, LinearMap.smul_apply,
            smul_eq_mul]
        have e2 : pε v = p v + ε₀ * q v := by
          simp [hpεdef, LinearMap.add_apply, LinearMap.smul_apply,
            smul_eq_mul]
        rw [e1, e2]
        ring
      -- `J₀ ⊆ S₊(ε)`: positivity persists.
      have hJsubSε : J ⊆ V'.filter (fun u => 0 < pε u - pε v) := by
        intro j hj
        have hjS : j ∈ S :=
          Finset.filter_subset _ _ (by rw [← hJeq]; exact hj)
        have hjV : j ∈ V' := by
          have hmem : j ∈ V'.filter (fun u => 0 < p u - p v) := by
            rw [← hSeq]; exact hjS
          exact (Finset.mem_filter.mp hmem).1
        have hβ : 0 < p j - p v := by
          have hmem : j ∈ V'.filter (fun u => 0 < p u - p v) := by
            rw [← hSeq]; exact hjS
          exact (Finset.mem_filter.mp hmem).2
        have hG : 0 < Gf j := hGpos j
        have hG1 : 0 < |q j - q v| + 1 := by
          have := abs_nonneg (q j - q v); linarith
        have hbound := happ1 j hjV hβ
        -- `β + ε₀γ ≥ β - ε₀|γ| > β/2 > 0`.
        have hγle : -( |q j - q v|) ≤ q j - q v := neg_abs_le _
        have hmul : -(ε₀ * (|q j - q v| + 1)) ≤ ε₀ * (q j - q v) := by
          have : ε₀ * (-(|q j - q v| + 1)) ≤ ε₀ * (q j - q v) :=
            mul_le_mul_of_nonneg_left (by linarith [hγle]) hεpos.le
          linarith [this]
        have hsmall : ε₀ * (|q j - q v| + 1) < (p j - p v) / 2 := by
          have h2G : 0 < 2 * Gf j := mul_pos (by norm_num) hG
          have hmul2 : ε₀ * (2 * Gf j) < p j - p v :=
            (lt_div_iff₀ h2G).mp hbound
          -- `ε₀ < β/(2G)` gives `ε₀*(2G) < β`; massage to `ε₀*G < β/2`.
          have hGf : Gf j = |q j - q v| + 1 := rfl
          linarith [hmul2, hGf]
        refine Finset.mem_filter.mpr ⟨hjV, ?_⟩
        show 0 < pε j - pε v
        rw [hpexp j]
        linarith [hβ, hmul, hsmall]
      -- Half-persistence for all of `S₊`.
      have hβhalf : ∀ u ∈ V', 0 < p u - p v → (p u - p v) / 2 < pε u - pε v := by
        intro u hu hβ
        have hb := happ1 u hu hβ
        have hG : 0 < Gf u := hGpos u
        have h2G : 0 < 2 * Gf u := mul_pos (by norm_num) hG
        have hmul2 : ε₀ * (2 * Gf u) < p u - p v := (lt_div_iff₀ h2G).mp hb
        have hGf : Gf u = |q u - q v| + 1 := rfl
        have h1 : ε₀ * Gf u < (p u - p v) / 2 := by linarith [hmul2, hGf]
        have hγle : -(|q u - q v|) ≤ q u - q v := neg_abs_le _
        have h2 : -(ε₀ * |q u - q v|) ≤ ε₀ * (q u - q v) := by
          have hle : ε₀ * (-(|q u - q v|)) ≤ ε₀ * (q u - q v) :=
            mul_le_mul_of_nonneg_left hγle hεpos.le
          linarith [hle]
        have h3 : ε₀ * |q u - q v| ≤ ε₀ * Gf u := by
          have hle : |q u - q v| ≤ Gf u := by
            rw [hGf]; linarith [abs_nonneg (q u - q v)]
          exact mul_le_mul_of_nonneg_left hle hεpos.le
        have hβεu := hpexp u
        linarith [hβεu, h1, h2, h3, hβ]
      -- Key product estimate.
      have hkey : ∀ u ∈ V', ∀ hβ : 0 < p u - p v, ∀ hβε : 0 < pε u - pε v,
          (hp0.c - hp0.f u) * ε₀ * |q u - q v|
            < (δgap / 4) * ((pε u - pε v) * (p u - p v)) := by
        intro u hu hβ hβε
        have hα : 0 < hp0.c - hp0.f u := hαpos u hu
        have hb := happ2 u hu hβ
        have hDen : 0 < 8 * (hp0.c - hp0.f u) * Gf u :=
          mul_pos (mul_pos (by norm_num) hα) (hGpos u)
        have hmul : ε₀ * (8 * (hp0.c - hp0.f u) * Gf u)
            < δgap * (p u - p v) * (p u - p v) :=
          (lt_div_iff₀ hDen).mp hb
        have hhalf := hβhalf u hu hβ
        have hBeB : ((p u - p v) * (p u - p v)) / 2 ≤ (pε u - pε v) * (p u - p v) :=
          by
          have h1 : ((p u - p v) / 2) * (p u - p v) ≤ (pε u - pε v) * (p u - p v) :=
            mul_le_mul_of_nonneg_right hhalf.le hβ.le
          linarith [h1]
        have hGle : |q u - q v| ≤ Gf u := by
          have hGf : Gf u = |q u - q v| + 1 := rfl
          linarith [abs_nonneg (q u - q v), hGf]
        have hpos : (0 : ℝ) ≤ (hp0.c - hp0.f u) * ε₀ := mul_nonneg hα.le hεpos.le
        have h1 : (hp0.c - hp0.f u) * ε₀ * |q u - q v|
            ≤ (hp0.c - hp0.f u) * ε₀ * Gf u :=
          mul_le_mul_of_nonneg_left hGle hpos
        have h2 : (hp0.c - hp0.f u) * ε₀ * Gf u
            < (δgap * (p u - p v) * (p u - p v)) / 8 := by
          rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 8)]
          linear_combination hmul
        have hpos4 : (0 : ℝ) ≤ δgap / 4 := by linarith [hδpos]
        have h3 : (δgap / 4) * (((p u - p v) * (p u - p v)) / 2)
            ≤ (δgap / 4) * ((pε u - pε v) * (p u - p v)) :=
          mul_le_mul_of_nonneg_left hBeB hpos4
        calc (hp0.c - hp0.f u) * ε₀ * |q u - q v|
            ≤ (hp0.c - hp0.f u) * ε₀ * Gf u := h1
          _ < (δgap * (p u - p v) * (p u - p v)) / 8 := h2
          _ = (δgap / 4) * (((p u - p v) * (p u - p v)) / 2) := by ring
          _ ≤ (δgap / 4) * ((pε u - pε v) * (p u - p v)) := h3
      -- One-sided ratio closeness (no absolute values).
      have hclose_up : ∀ u ∈ V', ∀ hβ : 0 < p u - p v, ∀ hβε : 0 < pε u - pε v,
          (hp0.c - hp0.f u) / (pε u - pε v)
            < (hp0.c - hp0.f u) / (p u - p v) + δgap / 4 := by
        intro u hu hβ hβε
        have hα := hαpos u hu
        have hpos : 0 < (pε u - pε v) * (p u - p v) := mul_pos hβε hβ
        have hnum : (hp0.c - hp0.f u) * ((p u - p v) - (pε u - pε v))
            < (δgap / 4) * ((pε u - pε v) * (p u - p v)) := by
          have hle : (p u - p v) - (pε u - pε v) ≤ ε₀ * |q u - q v| := by
            have h1 : (p u - p v) - (pε u - pε v) = -(ε₀ * (q u - q v)) := by
              rw [hpexp u]; ring
            have h2 : -(ε₀ * (q u - q v)) ≤ ε₀ * |q u - q v| := by
              have hγle : -(|q u - q v|) ≤ q u - q v := neg_abs_le _
              have hle : ε₀ * (-(|q u - q v|)) ≤ ε₀ * (q u - q v) :=
                mul_le_mul_of_nonneg_left hγle hεpos.le
              linarith [hle]
            linarith [h1, h2]
          have hmul := hkey u hu hβ hβε
          have hle2 : (hp0.c - hp0.f u) * ((p u - p v) - (pε u - pε v))
              ≤ (hp0.c - hp0.f u) * (ε₀ * |q u - q v|) :=
            mul_le_mul_of_nonneg_left hle hα.le
          have hmul2 : (hp0.c - hp0.f u) * (ε₀ * |q u - q v|)
              = (hp0.c - hp0.f u) * ε₀ * |q u - q v| := by ring
          linarith [hle2, hmul2, hmul]
        have e : ((hp0.c - hp0.f u) / (pε u - pε v)
              - (hp0.c - hp0.f u) / (p u - p v)) * ((pε u - pε v) * (p u - p v))
            = (hp0.c - hp0.f u) * ((p u - p v) - (pε u - pε v)) := by
          have h1 : (pε u - pε v) ≠ 0 := ne_of_gt hβε
          have h2 : (p u - p v) ≠ 0 := ne_of_gt hβ
          rw [div_sub_div _ _ h1 h2, div_mul_cancel₀ _ (mul_ne_zero h1 h2)]
          ring
        have hfin : ((hp0.c - hp0.f u) / (pε u - pε v)
              - (hp0.c - hp0.f u) / (p u - p v)) * ((pε u - pε v) * (p u - p v))
            < (δgap / 4) * ((pε u - pε v) * (p u - p v)) := by
          rw [e]
          exact hnum
        have hlt := lt_of_mul_lt_mul_right hfin hpos.le
        linarith [hlt]
      have hclose_lo : ∀ u ∈ V', ∀ hβ : 0 < p u - p v, ∀ hβε : 0 < pε u - pε v,
          (hp0.c - hp0.f u) / (p u - p v) - δgap / 4
            < (hp0.c - hp0.f u) / (pε u - pε v) := by
        intro u hu hβ hβε
        have hα := hαpos u hu
        have hpos : 0 < (pε u - pε v) * (p u - p v) := mul_pos hβε hβ
        have hnum : (hp0.c - hp0.f u) * ((pε u - pε v) - (p u - p v))
            < (δgap / 4) * ((pε u - pε v) * (p u - p v)) := by
          have hle : (pε u - pε v) - (p u - p v) ≤ ε₀ * |q u - q v| := by
            have h1 : (pε u - pε v) - (p u - p v) = ε₀ * (q u - q v) := by
              rw [hpexp u]; ring
            have h2 : ε₀ * (q u - q v) ≤ ε₀ * |q u - q v| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) hεpos.le
            linarith [h1, h2]
          have hmul := hkey u hu hβ hβε
          have hle2 : (hp0.c - hp0.f u) * ((pε u - pε v) - (p u - p v))
              ≤ (hp0.c - hp0.f u) * (ε₀ * |q u - q v|) :=
            mul_le_mul_of_nonneg_left hle hα.le
          have hmul2 : (hp0.c - hp0.f u) * (ε₀ * |q u - q v|)
              = (hp0.c - hp0.f u) * ε₀ * |q u - q v| := by ring
          linarith [hle2, hmul2, hmul]
        have e : ((hp0.c - hp0.f u) / (p u - p v)
              - (hp0.c - hp0.f u) / (pε u - pε v)) * ((pε u - pε v) * (p u - p v))
            = (hp0.c - hp0.f u) * ((pε u - pε v) - (p u - p v)) := by
          have h1 : (pε u - pε v) ≠ 0 := ne_of_gt hβε
          have h2 : (p u - p v) ≠ 0 := ne_of_gt hβ
          rw [mul_comm (pε u - pε v) (p u - p v), div_sub_div _ _ h2 h1,
            div_mul_cancel₀ _ (mul_ne_zero h2 h1)]
          ring
        have hfin : ((hp0.c - hp0.f u) / (p u - p v)
              - (hp0.c - hp0.f u) / (pε u - pε v)) * ((pε u - pε v) * (p u - p v))
            < (δgap / 4) * ((pε u - pε v) * (p u - p v)) := by
          rw [e]
          exact hnum
        have hlt := lt_of_mul_lt_mul_right hfin hpos.le
        linarith [hlt]
      -- New slices for the perturbed functional.
      set Sε : Finset (CoeffVec n) :=
        V'.filter (fun u => 0 < pε u - pε v) with hSεdef
      have hSεne : Sε.Nonempty := hJne.mono hJsubSε
      set tε : ℝ := (Sε.image
        (fun u => (hp0.c - hp0.f u) / (pε u - pε v))).min'
        (Finset.image_nonempty.mpr hSεne) with htεdef
      set Jε : Finset (CoeffVec n) := Sε.filter
        (fun u => (hp0.c - hp0.f u) / (pε u - pε v) = tε) with hJεdef
      -- Supremum bound: `tε < t + δgap/4` via `j0`.
      have htmε : tε < t + δgap / 4 := by
        have hj0ε : j0 ∈ Sε := hJsubSε hj0
        have hmem : (hp0.c - hp0.f j0) / (pε j0 - pε v)
            ∈ Sε.image (fun u => (hp0.c - hp0.f u) / (pε u - pε v)) :=
          Finset.mem_image.mpr ⟨j0, hj0ε, rfl⟩
        have hmin : tε ≤ (hp0.c - hp0.f j0) / (pε j0 - pε v) := by
          rw [htεdef]
          exact Finset.min'_le _ _ hmem
        have hj0Vε : j0 ∈ V'.filter (fun u => 0 < pε u - pε v) := hj0ε
        have hβεj0 : 0 < pε j0 - pε v := (Finset.mem_filter.mp hj0Vε).2
        have hclose := hclose_up j0 hj0V' hj0β hβεj0
        linarith only [hmin, hclose, hj0tie]
      -- `Jε ⊆ J`: outsiders stay above or leave.
      have hJsub : Jε ⊆ J := by
        intro y hy
        have hyε : y ∈ Sε.filter
            (fun u => (hp0.c - hp0.f u) / (pε u - pε v) = tε) := hy
        have hySε : y ∈ Sε := (Finset.mem_filter.mp hyε).1
        have hyrε : (hp0.c - hp0.f y) / (pε y - pε v) = tε :=
          (Finset.mem_filter.mp hyε).2
        have hyVε : y ∈ V'.filter (fun u => 0 < pε u - pε v) := hySε
        have hβεy : 0 < pε y - pε v := (Finset.mem_filter.mp hyVε).2
        have hyV' : y ∈ V' := (Finset.mem_filter.mp hyVε).1
        by_cases hβy : 0 < p y - p v
        · -- Was already in `S₊`: gap forces membership in `J`.
          have hyS : y ∈ S := by
            rw [hSeq]
            exact Finset.mem_filter.mpr ⟨hyV', hβy⟩
          by_cases hJy : y ∈ J
          · exact hJy
          · -- Outside `J`: ratio was `≥ t + δgap`, still above `tε`.
            exfalso
            have hySD : y ∈ S \ J :=
              Finset.mem_sdiff.mpr ⟨hyS, hJy⟩
            have hgap := hδgap y hySD
            have hlo := hclose_lo y hyV' hβy hβεy
            -- `t_y(0) ≥ t + δgap`, so `t_y(ε) > t + 3δgap/4 > tε`.
            have hge : t + δgap ≤ (hp0.c - hp0.f y) / (p y - p v) := by
              linarith [hgap]
            linarith only [hlo, hge, hyrε, htmε, hδpos]
        · -- Left `S₊`: `β ≤ 0` but `βε > 0` forces a huge ratio.
          push_neg at hβy
          by_cases hβ0 : p y - p v = 0
          · -- `β = 0`: huge ratio `> t + 1 > tε`.
            have hγy : 0 < q y - q v := by
              by_contra hγ
              push_neg at hγ
              have hβε0 : pε y - pε v ≤ 0 := by
                have h := hpexp y
                have hγ0 : ε₀ * (q y - q v) ≤ 0 :=
                  mul_nonpos_of_nonneg_of_nonpos hεpos.le hγ
                linarith [h, hβ0, hγ0]
              linarith only [hβεy, hβε0]
            have hb := happ4 y hyV' hβ0 hγy
            have hαy := hαpos y hyV'
            have ht1 : 0 < t + 1 := by linarith [htpos]
            have hhuge : t + 1 < (hp0.c - hp0.f y) / (pε y - pε v) := by
              have hβe : pε y - pε v = ε₀ * (q y - q v) := by
                have h := hpexp y
                linarith [h, hβ0]
              have hden2 : 0 < ε₀ * (q y - q v) := mul_pos hεpos hγy
              rw [hβe]
              apply (lt_div_iff₀ hden2).mpr
              have hden : 0 < (q y - q v) * (t + 1) := mul_pos hγy ht1
              have hmul0 : ε₀ * ((q y - q v) * (t + 1))
                  < hp0.c - hp0.f y :=
                (lt_div_iff₀ hden).mp hb
              linear_combination hmul0
            exfalso
            have hle1 : t + δgap / 4 ≤ t + 1 := by linarith [hδle1]
            linarith only [hhuge, hyrε, htmε, hle1]
          · -- `β < 0`: would have stayed out.
            exfalso
            have hβneg : p y - p v < 0 := lt_of_le_of_ne hβy hβ0
            have hb := happ3 y hyV' hβneg
            have hG : 0 < Gf y := hGpos y
            have h2G : 0 < 2 * Gf y := mul_pos (by norm_num) hG
            have hmul : ε₀ * (2 * Gf y) < -(p y - p v) := (lt_div_iff₀ h2G).mp hb
            have hγle : (q y - q v) ≤ |q y - q v| := le_abs_self _
            have hle : ε₀ * (q y - q v) ≤ ε₀ * |q y - q v| :=
              mul_le_mul_of_nonneg_left hγle hεpos.le
            have hGf : Gf y = |q y - q v| + 1 := rfl
            have hsmall : ε₀ * Gf y < -(p y - p v) / 2 := by linarith [hmul, hGf]
            have hβε0 : pε y - pε v ≤ (p y - p v) / 2 := by
              have h := hpexp y
              linarith [h, hle, hsmall]
            linarith only [hβεy, hβε0, hβneg]
      -- `j0`, `i1` separate: one of them misses `Jε`.
      have hsep : (hp0.c - hp0.f j0) / (pε j0 - pε v)
          ≠ (hp0.c - hp0.f i1) / (pε i1 - pε v) := by
        intro heq
        have hj0ε : j0 ∈ Sε := hJsubSε hj0
        have hi1ε : i1 ∈ Sε := hJsubSε hi1J
        have hβj : 0 < pε j0 - pε v := by
          have hmem : j0 ∈ V'.filter (fun u => 0 < pε u - pε v) := hj0ε
          exact (Finset.mem_filter.mp hmem).2
        have hβi : 0 < pε i1 - pε v := by
          have hmem : i1 ∈ V'.filter (fun u => 0 < pε u - pε v) := hi1ε
          exact (Finset.mem_filter.mp hmem).2
        have hcross : (hp0.c - hp0.f j0) * (pε i1 - pε v)
            = (hp0.c - hp0.f i1) * (pε j0 - pε v) :=
          (div_eq_div_iff (ne_of_gt hβj) (ne_of_gt hβi)).mp heq
        have hbej : pε j0 - pε v = (p j0 - p v) + ε₀ * (q j0 - q v) := hpexp j0
        have hbei : pε i1 - pε v = (p i1 - p v) + ε₀ * (q i1 - q v) := hpexp i1
        have hbase : (hp0.c - hp0.f j0) * (p i1 - p v)
            = (hp0.c - hp0.f i1) * (p j0 - p v) := by
          have ej : hp0.c - hp0.f j0 = t * (p j0 - p v) :=
            (div_eq_iff (ne_of_gt hj0β)).mp hj0tie
          have ei : hp0.c - hp0.f i1 = t * (p i1 - p v) := by
            have hr : (hp0.c - hp0.f i1) / (p i1 - p v) = t := hi1tie
            exact (div_eq_iff (ne_of_gt hi1β)).mp hr
          rw [ej, ei]
          ring
        have hkey0 : ε₀ * ((hp0.c - hp0.f j0) * (q i1 - q v)
            - (hp0.c - hp0.f i1) * (q j0 - q v)) = 0 := by
          rw [hbej, hbei] at hcross
          linear_combination hcross - hbase
        have hne : (hp0.c - hp0.f j0) * (q i1 - q v)
            - (hp0.c - hp0.f i1) * (q j0 - q v) ≠ 0 := hqw'
        exact hne (by
          rcases mul_eq_zero.mp hkey0 with h | h
          · exact absurd h (ne_of_gt hεpos)
          · exact h)
      -- Missing element and strict card drop.
      have hmiss : ∃ x ∈ J, x ∉ Jε := by
        by_cases hlt : (hp0.c - hp0.f j0) / (pε j0 - pε v)
            < (hp0.c - hp0.f i1) / (pε i1 - pε v)
        · refine ⟨i1, hi1J, ?_⟩
          intro hmem
          have h1 : (hp0.c - hp0.f i1) / (pε i1 - pε v) = tε := by
            have : i1 ∈ Sε.filter
                (fun u => (hp0.c - hp0.f u) / (pε u - pε v) = tε) := hmem
            exact (Finset.mem_filter.mp this).2
          have h3 : tε ≤ (hp0.c - hp0.f j0) / (pε j0 - pε v) := by
            have hj0ε' : j0 ∈ Sε := hJsubSε hj0
            have hm : (hp0.c - hp0.f j0) / (pε j0 - pε v)
                ∈ Sε.image (fun u => (hp0.c - hp0.f u) / (pε u - pε v)) :=
              Finset.mem_image.mpr ⟨j0, hj0ε', rfl⟩
            rw [htεdef]
            exact Finset.min'_le _ _ hm
          linarith only [h1, h3, hlt]
        · -- `¬ j0-ratio < i1-ratio`, with `≠`, gives `i1-ratio < j0-ratio`.
          have hgt : (hp0.c - hp0.f i1) / (pε i1 - pε v)
              < (hp0.c - hp0.f j0) / (pε j0 - pε v) :=
            lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hsep)
          refine ⟨j0, hj0, ?_⟩
          intro hmem
          have h1 : (hp0.c - hp0.f j0) / (pε j0 - pε v) = tε := by
            have : j0 ∈ Sε.filter
                (fun u => (hp0.c - hp0.f u) / (pε u - pε v) = tε) := hmem
            exact (Finset.mem_filter.mp this).2
          have h3 : tε ≤ (hp0.c - hp0.f i1) / (pε i1 - pε v) := by
            have hi1ε : i1 ∈ Sε := hJsubSε hi1J
            have hm : (hp0.c - hp0.f i1) / (pε i1 - pε v)
                ∈ Sε.image (fun u => (hp0.c - hp0.f u) / (pε u - pε v)) :=
              Finset.mem_image.mpr ⟨i1, hi1ε, rfl⟩
            rw [htεdef]
            exact Finset.min'_le _ _ hm
          linarith only [h1, h3, hgt]
      obtain ⟨xmiss, hxJ, hxmiss⟩ := hmiss
      have hcardlt : Jε.card < J.card := by
        have hsub2 : Jε ⊆ J.erase xmiss := by
          intro y hy
          rw [Finset.mem_erase]
          refine ⟨?_, hJsub hy⟩
          intro heq
          exact hxmiss (heq ▸ hy)
        have hle := Finset.card_le_card hsub2
        rw [Finset.card_erase_of_mem hxJ] at hle
        have hJpos : 0 < J.card := Finset.card_pos.mpr ⟨xmiss, hxJ⟩
        omega
      have hcard_eq : J.card = k := hcard
      have hlt : Jε.card < k := hcard_eq ▸ hcardlt
      -- The perturbed slice is still inhabited; apply `ih`.
      have hgtε : ∃ u ∈ P.vertices, pε v < pε u := by
        refine ⟨j0, hj0vert, ?_⟩
        have hj0ε : j0 ∈ Sε := hJsubSε hj0
        have hmem : j0 ∈ V'.filter (fun u => 0 < pε u - pε v) := hj0ε
        have := (Finset.mem_filter.mp hmem).2
        linarith [this]
      exact ih (Jε.card) hlt pε hgtε Sε hSεdef hSεne tε htεdef Jε hJεdef rfl
  -- Apply `aux` to the initial `p`: `S₊` is nonempty from `hvert_gt`.
  refine aux _ p hvert_gt _ rfl ?_ _ rfl _ rfl rfl
  obtain ⟨u0, hu0mem, hu0gt⟩ := hvert_gt
  have hu0ne : u0 ≠ v := by
    intro heq
    subst heq
    exact lt_irrefl _ hu0gt
  have hu0V' : u0 ∈ V' := (hmem_V' u0 hu0mem).mp hu0ne
  refine ⟨u0, Finset.mem_filter.mpr ⟨hu0V', ?_⟩⟩
  show 0 < p u0 - p v
  linarith [hu0gt]

end CoeffBox
