module

public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeTheoremDefs
public import ControlSystems.DiscreteTime.EdgeTheorem.BasicLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.Lemma61
public import ControlSystems.DiscreteTime.EdgeTheorem.Lemma62
public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeDescent

@[expose] public section

open Polynomial Affine FiniteDimensional LinearMap Set

namespace CoeffBox

/-! # Theorem 6.1 — Edge Theorem (edgetheorem.md, §6.2)

Textbook statement: for a polytope `Ω` satisfying Assumption 6.1,
`∂ R(Ω)` is contained in the root space of the exposed edges of `Ω`.
With (6.5), `R(Ω) = ∪ᵢ R(Fᵢ)` over exposed faces, and Lemma 6.2,
`∂ R(Fᵢ) ⊆ R(∂Fᵢ)`, where each `∂Fᵢ` is a union of exposed edges.

What is assembled here from the formalized lemmas:
- `edge_real`: real `s ∈ R(Ω)` lies in `R(E)` for an exposed edge
  (Lemma 6.1, real case) — hence real boundary points need only edges.
- `edge_face_complex`: non-real `s ∈ R(Ω)` lies in `R(F)` for an exposed
  face, descended to `dim aff(F) ≤ 2` (Lemma 6.1 + `descend_to_exposed_face`).
- `face_boundary_subset`: for 2-dimensional exposed `F`,
  `∂ R(F) ⊆ R(relativeBoundary F)` (Lemma 6.2).
The full boundary-to-edge statement is `edge_theorem` below. Real boundary
roots use Lemma 6.1 directly. A non-real boundary root is first carried to an
exposed face of dimension at most two; if that face is two-dimensional,
closedness forces the root to be on the boundary of its root space, so Lemma
6.2 moves it to the face boundary and exposed-face descent finishes at an edge.
-/

/-- Real case of Theorem 6.1: a real root in `R(Ω)` is already an edge root. -/
theorem edge_real {n : ℕ} (hn : n ≥ 1) (P : Polytope n) (s : ℂ)
    (hs : s ∈ RootSpace P) (hreal : s.im = 0) :
    ∃ E, IsExposedEdge P E ∧ s ∈ RootSpaceSet E :=
  lemma61_real hn P s hs hreal

/-- Complex case to a face: a non-real root in `R(Ω)` lies in `R(F)`
for an exposed face (Lemma 6.1, complex case). Feeding `F` to
`descend_to_exposed_face` lowers `dim aff(F)` below 3; feeding a
2-dimensional face to Lemma 6.2 (`face_boundary_subset`) moves boundary
roots to `R(relativeBoundary F)`. -/
theorem edge_face_complex {n : ℕ} (hn : n ≥ 1) (P : Polytope n) (s : ℂ)
    (hs : s ∈ RootSpace P)
    (hleading : ∀ v ∈ P.vertices, 0 < v (Fin.last n))
    (hcomplex : s.im ≠ 0) :
    ∃ F, IsExposedFace P F ∧ s ∈ RootSpaceSet F :=
  lemma61_complex hn P s hs hleading hcomplex

/-- Lemma 6.2 restated for the assembly: face-boundary roots lie on the
relative boundary (`∂F` in the textbook). -/
theorem face_boundary_subset {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hF_dim_2 : dim (affineSpan ℝ F).direction = 2) :
    frontier (RootSpaceSet F) ⊆ RootSpaceSet (relativeBoundary F) :=
  lemma62 hn P F hF_exp hF_dim_2


/-- A root on an exposed face of dimension at most one is a root on an exposed
edge: one-dimensional faces are edges, and zero-dimensional exposed faces are
singletons covered by `exists_exposed_edge_of_singleton`. -/
private theorem exposed_face_root_dim_le1_to_edge {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (s : ℂ) (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hsF : s ∈ RootSpaceSet F)
    (hF_dim : Module.finrank ℝ (affineSpan ℝ F).direction ≤ 1) :
    ∃ E, IsExposedEdge P E ∧ s ∈ RootSpaceSet E := by
  let m := Module.finrank ℝ (affineSpan ℝ F).direction
  by_cases hm1 : m = 1
  · exact ⟨F, isExposedEdge_of_dim_1 hF_exp (by simpa [m] using hm1), hsF⟩
  · have hm0 : m = 0 := by omega
    obtain ⟨δ, hδF, hδroot⟩ := hsF
    have hF_single : F = {δ} :=
      exposed_face_dim_zero_singleton F (by simpa [m] using hm0) δ hδF
    obtain ⟨E, hE, hδE⟩ :=
      exists_exposed_edge_of_singleton hn P δ F hF_exp hF_single
    exact ⟨E, hE, rootspace_mem_of_isRoot s δ hδroot E hδE⟩

/-- **Edge Theorem (Theorem 6.1).** If all polynomials in `P` have the same
degree (here ensured by a positive leading coefficient on every vertex),
then every boundary root of the family is a root of a polynomial on an exposed
edge of `P`. -/
theorem edge_theorem {n : ℕ} (hn : n ≥ 1) (P : Polytope n) (s : ℂ)
    (hleading : ∀ v ∈ P.vertices, 0 < v (Fin.last n))
    (hs : s ∈ frontier (RootSpace P)) :
    ∃ E, IsExposedEdge P E ∧ s ∈ RootSpaceSet E := by
  have hroot_closed : IsClosed (RootSpace P) := by
    change IsClosed (RootSpaceSet P.Ω)
    exact rootSpaceSet_isClosed_of_isCompact P.isCompact
  have hs_mem : s ∈ RootSpace P := by
    have hcl : s ∈ closure (RootSpace P) := frontier_subset_closure hs
    rw [hroot_closed.closure_eq] at hcl
    exact hcl
  have hs_not_int : s ∉ interior (RootSpace P) := by
    change s ∈ closure (RootSpace P) \ interior (RootSpace P) at hs
    exact hs.2
  by_cases hreal : s.im = 0
  · exact edge_real hn P s hs_mem hreal
  · obtain ⟨F, hF_exp, hsF, hF_dim⟩ :=
      lemma61_complex_with_dim hn P s hs_mem hleading hreal
    by_cases hdim2 : Module.finrank ℝ (affineSpan ℝ F).direction = 2
    · have hroot_closed_F : IsClosed (RootSpaceSet F) :=
        rootSpaceSet_isClosed_of_isCompact (isExposedFace_isCompact P hF_exp)
      
      have hsF_not_int : s ∉ interior (RootSpaceSet F) := by
        intro hInt
        have hsub : RootSpaceSet F ⊆ RootSpace P := by
          intro z hz
          obtain ⟨δ, hδF, hδroot⟩ := hz
          exact rootspace_mem_of_isRoot z δ hδroot P.Ω
            (isExposedFace_subset_Ω hF_exp hδF)
        exact hs_not_int (interior_mono hsub hInt)
      have hsF_front : s ∈ frontier (RootSpaceSet F) := by
        have hsF_mem : s ∈ closure (RootSpaceSet F) := by
          rw [hroot_closed_F.closure_eq]
          exact hsF
        change s ∈ closure (RootSpaceSet F) \ interior (RootSpaceSet F)
        exact ⟨hsF_mem, hsF_not_int⟩
      have hs_rel : s ∈ RootSpaceSet (relativeBoundary F) :=
        face_boundary_subset hn P F hF_exp hdim2 hsF_front
      obtain ⟨δ, hδrel, hδroot⟩ := hs_rel
      have hδF : δ ∈ F := hδrel.1
      have hδ_not_relint : δ ∉ intrinsicInterior ℝ F := hδrel.2
      have hF_compact : IsCompact F := isExposedFace_isCompact P hF_exp
      have hδ_not_int : δ ∉ interior F := by
        intro hInt
        exact hδ_not_relint
          (interior_subset_intrinsicInterior (𝕜 := ℝ) (s := F) hInt)
      have hδ_front : δ ∈ frontier F := by
        rw [frontier_eq_for_closed F hF_compact.isClosed]
        exact ⟨hδF, hδ_not_int⟩
      obtain ⟨G, hG_exp, hδG, hG_dim_lt⟩ :=
        exists_proper_subface_of_boundary_point P F hF_exp δ hδF hδ_front
          hδ_not_relint (by omega)
      have hsG : s ∈ RootSpaceSet G :=
        rootspace_mem_of_isRoot s δ hδroot G hδG
      by_cases hG1 : Module.finrank ℝ (affineSpan ℝ G).direction = 1
      · exact ⟨G, isExposedEdge_of_dim_1 hG_exp hG1, hsG⟩
      · have hG0 : Module.finrank ℝ (affineSpan ℝ G).direction = 0 := by omega
        obtain ⟨δ', hδ'G, hδ'root⟩ := hsG
        have hG_single : G = {δ'} :=
          exposed_face_dim_zero_singleton G hG0 δ' hδ'G
        obtain ⟨E, hE, hδ'E⟩ :=
          exists_exposed_edge_of_singleton hn P δ' G hG_exp hG_single
        exact ⟨E, hE, rootspace_mem_of_isRoot s δ' hδ'root E hδ'E⟩
    · -- In dimension zero or one, the exposed face itself is a singleton or edge.
      have hdim_le1 : Module.finrank ℝ (affineSpan ℝ F).direction ≤ 1 := by omega
      exact exposed_face_root_dim_le1_to_edge hn P s F hF_exp hsF hdim_le1

end CoeffBox
