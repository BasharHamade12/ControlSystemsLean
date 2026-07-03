# Plan: Formalizing `lemma61_complex`

## Goal

Prove the complex case of Lemma 6.1:

```
theorem lemma61_complex (hn : n ≥ 1) (P : Polytope n) (s : ℂ) (hs : s ∈ RootSpace P) :
    s.im ≠ 0 → ∃ F, IsExposedFace P F ∧ s ∈ RootSpaceSet F
```

## Textbook proof (verbatim)

> For the case of a complex root $s_c$, it suffices to know that the set of all real polynomials having $s_c$ among their roots is a vector space $\mathcal{P}_{s_c}$ of dimension $n-1$. As a consequence **the same reasoning as above holds**, yielding eventually an exposed face $\Omega_2$ of $\Omega$ for which $s_c \in R(\Omega_2)$.

The plan follows the textbook faithfully: the proof is identical to the real case, with only two differences:

1. $\mathcal{P}_{s_c}$ has dimension $n-1$ instead of $n$
2. The descent stops at dimension $2$ (an exposed face) instead of dimension $1$ (an exposed edge)

---

## Step 1: Define `P_sc` — the subspace for complex roots

**File:** `EdgeTheoremDefs.lean`

A real polynomial vanishing at a non-real $s = a+bi$ imposes **two real linear constraints** (real and imaginary parts both zero). Define:

```lean4
noncomputable def evalAtComplex (n : ℕ) (s : ℂ) : CoeffVec n →ₗ[ℝ] ℂ :=
{ toFun := λ δ => ((polyOfVec δ).map (algebraMap ℝ ℂ)).eval s
  map_add' := ...
  map_smul' := ... }

noncomputable def P_sc (n : ℕ) (s : ℂ) : Submodule ℝ (CoeffVec n) :=
  LinearMap.ker (evalAtComplex n s)
```

## Step 2: `P_sc_dimension` lemma

**File:** `PreliminaryLemmas.lean`

```lean4
lemma P_sc_dimension {n : ℕ} (hn : n ≥ 1) (s : ℂ) (hs : s.im ≠ 0) :
    Module.finrank ℝ (P_sc n s) = n - 1 := ...
```

**Proof:** `evalAtComplex n s : CoeffVec n →ₗ[ℝ] ℂ` is surjective (we can find coefficient vectors achieving any complex value at $s$). By rank-nullity:

```
dim(ker) = dim(CoeffVec) - dim_ℝ(ℂ) = (n+1) - 2 = n-1
```

For $n=1$, this gives dimension $0$ (consistent: a degree-1 real polynomial cannot have a non-real root except the zero polynomial, which is excluded by Assumption 6.1).

## Step 3: `mem_P_sc_of_isRoot` lemma

**File:** `ExposedFaceLemmas.lean`

```lean4
lemma mem_P_sc_of_isRoot {n : ℕ} (s : ℂ) (δ : CoeffVec n)
    (h : ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s) :
    δ ∈ (P_sc n s : Set (CoeffVec n)) := by
  unfold P_sc
  have hzero : ((polyOfVec δ).map (algebraMap ℝ ℂ)).eval s = 0 := h
  simp [hzero]
```

Also add a helper to produce `s ∈ RootSpaceSet F` directly:

```lean4
lemma rootspace_mem_of_isRoot {n : ℕ} (s : ℂ) (δ : CoeffVec n)
    (h : ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s)
    (F : Set (CoeffVec n)) (hδ_in_F : δ ∈ F) : s ∈ RootSpaceSet F :=
  ⟨δ, hδ_in_F, h⟩
```

## Step 4: Parallel lemma `exists_boundary_point_in_Psc`

**File:** `PreliminaryLemmas.lean`

The textbook says *"the same reasoning as above holds"* — so we duplicate `exists_boundary_point_in_Psr` with `P_sc` replacing `P_sr`. The proof is line-for-line identical; only the subspace changes:

```lean4
lemma exists_boundary_point_in_Psc {n : ℕ} (P : Polytope n) (s : ℂ) (δ : CoeffVec n)
    (hδ_in_Ω : δ ∈ P.Ω) (hδ_in_Psc : δ ∈ (P_sc n s : Set (CoeffVec n)))
    (affΩ : AffineSubspace ℝ (CoeffVec n)) (hδ_aff : δ ∈ affΩ)
    (hA_dim : Module.finrank ℝ ↥(affineSpan ℝ ((P_sc n s : Set (CoeffVec n)) ∩
      (affΩ : Set (CoeffVec n)))).direction ≥ 1) :
    ∃ δ_bound, δ_bound ∈ (P_sc n s : Set (CoeffVec n)) ∩ frontier P.Ω :=
  -- same proof as exists_boundary_point_in_Psr, with P_sr → P_sc
```

## Step 5: Parallel lemma `exists_boundary_point_in_face_rootspace_complex`

**File:** `EdgeDescent.lean`

Similarly duplicate `exists_boundary_point_in_face_rootspace` for `P_sc`:

```lean4
lemma exists_boundary_point_in_face_rootspace_complex {n : ℕ} (P : Polytope n) (s : ℂ)
    (δ_F : CoeffVec n) (F : Set (CoeffVec n)) (hF_exposed : IsExposedFace P F)
    (hδ_F_in_F : δ_F ∈ F) (hδ_F_root : δ_F ∈ (P_sc n s : Set (CoeffVec n)))
    (h_inter_dim : Module.finrank ℝ ↥(affineSpan ℝ
      (((P_sc n s : Set (CoeffVec n)) ∩ (affineSpan ℝ F : Set (CoeffVec n))))).direction ≥ 1) :
    ∃ δ_bound, δ_bound ∈ F ∩ (P_sc n s : Set (CoeffVec n))
    ∧ δ_bound ∈ frontier F ∧ δ_bound ∉ intrinsicInterior ℝ F :=
  -- same proof as exists_boundary_point_in_face_rootspace, with P_sr → P_sc
```

## Step 6: Parallel lemma `exists_exposed_face_containing_boundary_point_complex`

**File:** `ExposedFaceLemmas.lean`

Duplicate `exists_exposed_face_containing_boundary_point` for a complex root. The Hahn-Banach construction is identical; only the final `RootSpaceSet` membership changes:

```lean4
lemma exists_exposed_face_containing_boundary_point_complex {n : ℕ} (P : Polytope n)
    (s : ℂ) (δ_bound : CoeffVec n)
    (hδ_bound_front : δ_bound ∈ frontier P.Ω)
    (hδ_bound_Psc : δ_bound ∈ (P_sc n s : Set (CoeffVec n)))
    (h_int_nonempty : (interior P.Ω).Nonempty) :
    ∃ F : Set (CoeffVec n), IsExposedFace P F ∧ δ_bound ∈ F ∧ s ∈ RootSpaceSet F :=
  -- same proof as exists_exposed_face_containing_boundary_point (same Hahn-Banach argument),
  -- then use rootspace_mem_of_isRoot instead of rootspace_mem_of_eval_zero
```

## Step 7: Parameterize the descent lemma

**File:** `EdgeDescent.lean`

The textbook's real and complex descents are the same algorithm with a different stopping dimension. Rather than duplicating `descend_to_exposed_edge`, add a `target_dim` parameter:

```lean4
lemma descend_to_exposed_face_of_dim {n : ℕ} (P : Polytope n) (s : ℂ)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hs_F : s ∈ RootSpaceSet F)
    (hF_dim_ge : Module.finrank ℝ (affineSpan ℝ F).direction ≥ target_dim + 1)
    (subspace : Submodule ℝ (CoeffVec n))
    (h_dim_subspace : Module.finrank ℝ subspace = n - 1)
    (h_mem_boundary : ... )  -- boundary point lemmas parameterized by subspace
    : ∃ F', IsExposedFace P F' ∧ s ∈ RootSpaceSet F' := ...
```

But this is over-engineering. More faithful to the textbook: just write `descend_to_exposed_face` as a direct adaptation of `descend_to_exposed_edge` with:

- Uses `P_sc` instead of `P_sr n r`
- Uses `hF_dim_ge_3` instead of `hF_dim_ge_2`
- Calls `exists_boundary_point_in_face_rootspace_complex` instead of `exists_boundary_point_in_face_rootspace`
- Stops at dim ≤ 2 and returns `F` (no need for the vertex-edge axiom)

```lean4
lemma descend_to_exposed_face {n : ℕ} (P : Polytope n) (s : ℂ)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hs_F : s ∈ RootSpaceSet F)
    (hF_dim_ge_3 : Module.finrank ℝ (affineSpan ℝ F).direction ≥ 3) :
    ∃ F', IsExposedFace P F' ∧ s ∈ RootSpaceSet F' :=
```

**Proof structure** (identical to `descend_to_exposed_edge` except as noted):

1. `hF_dim_ge_3` ensures `dim(F) ≥ 3`.
2. Obtain `δ_F ∈ F` with root `s`. Then `hδ_F_Psc : δ_F ∈ P_sc n s`.
3. `dim(P_sc) = n-1` and `dim(F) ≥ 3` → intersection dimension `≥ 1`.
4. Get boundary point via `exists_boundary_point_in_face_rootspace_complex`.
5. Construct proper exposed subface `G ⊂ F` via `exists_proper_subface_of_boundary_point` (already exists—no changes needed).
6. Recurse on `G` if `dim(G) ≥ 3`; otherwise return `G` (since any face of dim ≤ 2 is an exposed face).
7. **Termination:** `dim(affSpan G).direction < dim(affSpan F).direction` (strictly decreasing).

No vertex-edge axiom needed (unlike the real case).

## Step 8: `no_complex_root_degree_one` lemma

**File:** `Lemma61.lean`

A formalization detail (implicit in the textbook): degree-1 real polynomials have only real roots:

```lean4
lemma no_complex_root_degree_one (P : Polytope 1) (s : ℂ) (hs : s ∈ RootSpace P) :
    s.im = 0 := by
  obtain ⟨δ, hδ_in_Ω, hδ_root⟩ := hs
  have h_leading_nonzero : δ 1 ≠ 0 := ... -- from Assumption 6.1 (constant leading coefficient sign)
  have h_root : s = -((δ 0 : ℂ) / (δ 1 : ℂ)) := by
    -- polyOfVec δ = δ 0 + δ 1·s, solve for s
    have h_eq : (δ 0 : ℂ) + (δ 1 : ℂ) * s = 0 := hδ_root
    field_simp [h_leading_nonzero] at h_eq ⊢
    linarith
  simp [h_root]
```

## Step 9: Assemble `lemma61_complex`

**File:** `Lemma61.lean`

```lean4
theorem lemma61_complex (hn : n ≥ 1) (P : Polytope n) (s : ℂ) (hs : s ∈ RootSpace P) :
    s.im ≠ 0 → ∃ F, IsExposedFace P F ∧ s ∈ RootSpaceSet F := by
  intro hcomplex
  by_cases hn2 : n ≥ 2
  · unfold RootSpace RootSpaceSet at hs
    obtain ⟨δ, hδ_in_Ω, hδ_root⟩ := hs
    have hδ_in_Psc : δ ∈ (P_sc n s : Set (CoeffVec n)) :=
      mem_P_sc_of_isRoot s δ hδ_root
    let m := Module.finrank ℝ (affineSpan ℝ (P.Ω)).direction
    have hm_ge_3 : m ≥ 3 := by
      -- affSpan = ⊤ (interior nonempty), so dim = n+1 ≥ 3
      ...
    let affΩ : AffineSubspace ℝ (CoeffVec n) := affineSpan ℝ (P.Ω)
    have hdim_Psc : Module.finrank ℝ (P_sc n s) = n - 1 :=
      P_sc_dimension hn s hcomplex
    have hδ_aff : δ ∈ affΩ := subset_affineSpan ℝ P.Ω hδ_in_Ω
    let dir' := (affineSpan ℝ ((P_sc n s : Set (CoeffVec n)) ∩ (affΩ : Set (CoeffVec n)))).direction
    have hA_dim : Module.finrank ℝ (↥dir') ≥ 1 :=
      intersection_affine_dim_ge_one (P_sc n s) affΩ δ hδ_in_Psc hδ_aff
        hdim_Psc hm_ge_3
    obtain ⟨δ_bound, hδ_bound⟩ :=
      exists_boundary_point_in_Psc P s δ hδ_in_Ω hδ_in_Psc affΩ hδ_aff hA_dim
    have hδ_bound_front : δ_bound ∈ frontier P.Ω := hδ_bound.2
    have hδ_bound_Psc : δ_bound ∈ (P_sc n s : Set (CoeffVec n)) := hδ_bound.1
    obtain ⟨F, hF_exposed, hδ_in_F, hs_in_RF⟩ :=
      exists_exposed_face_containing_boundary_point_complex P s δ_bound
        hδ_bound_front hδ_bound_Psc P.interior_nonempty
    let m_F := Module.finrank ℝ (affineSpan ℝ F).direction
    by_cases hm_F_ge_3 : m_F ≥ 3
    · exact descend_to_exposed_face P s F hF_exposed hs_in_RF hm_F_ge_3
    · exact ⟨F, hF_exposed, hs_in_RF⟩
  · -- n = 1: impossible by degree-1 argument
    have hn1 : n = 1 := by omega
    subst hn1
    have : s.im = 0 := no_complex_root_degree_one P s hs
    exact absurd this hcomplex
```

---

## Files modified (summary)

| File | Changes |
|------|---------|
| `EdgeTheoremDefs.lean` | Add `evalAtComplex`, `P_sc`, `rootspace_mem_of_isRoot` |
| `PreliminaryLemmas.lean` | Add `P_sc_dimension`, `exists_boundary_point_in_Psc` |
| `ExposedFaceLemmas.lean` | Add `mem_P_sc_of_isRoot`, `exists_exposed_face_containing_boundary_point_complex` |
| `EdgeDescent.lean` | Add `exists_boundary_point_in_face_rootspace_complex`, `descend_to_exposed_face` |
| `Lemma61.lean` | Add `no_complex_root_degree_one`, fill `lemma61_complex` body |

The real-case lemmas (`exists_boundary_point_in_Psr`, `exists_boundary_point_in_face_rootspace`, `descend_to_exposed_edge`) are **unchanged**. The complex case follows the textbook by duplicating them with `P_sc` and a different stopping dimension, rather than generalizing.
