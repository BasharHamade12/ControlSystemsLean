module

public import ControlSystems.DiscreteTime.Basic
public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeTheoremDefs
public import ControlSystems.DiscreteTime.EdgeTheorem.BasicLemmas
public import ControlSystems.DiscreteTime.EdgeTheorem.Lemma61
public import ControlSystems.DiscreteTime.EdgeTheorem.Lemma62
public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeDescent

@[expose] public section

open Polynomial Affine FiniteDimensional LinearMap Set

namespace CoeffBox

/-! ## Bridge from a transfer function to coefficient space

The Edge Theorem lives in coefficient space `CoeffVec n = ℝ^{n+1}`, whereas a transfer
function is a rational function `RatFunc ℂ`. `denomCoeffVec` reads off the coefficient
vector of the denominator, which is the object the Edge Theorem is applied to: the roots
of the denominator are the poles of the system. -/

/-- The coefficient vector `(δ₀, …, δₙ) : CoeffVec n` of the denominator of `H`: the
coefficient of `s ^ j` is the real part of the `j`-th coefficient of `H.denom`.

`H.denom` is the normalized (monic, gcd-reduced) denominator of `H`, so these are the
coefficients of the actual pole set. Coefficients past the degree of `H.denom` are `0`
(`Polynomial.coeff` vanishes there), so a denominator of degree `< n` is padded by zeros.
For a denominator with real coefficients this loses no information
(`polyOfVec_denomCoeffVec`); a genuinely complex-coefficient denominator is *not*
captured by a single `CoeffVec` — it needs the real and imaginary parts as separate real
parameters. -/
noncomputable def denomCoeffVec {n : ℕ} (H : TransferFunction) : CoeffVec n :=
  fun j => (H.denom.coeff j.val).re

/-- `denomCoeffVec` reconstructs the denominator, for a denominator with real
coefficients of `natDegree ≤ n`. -/
lemma polyOfVec_denomCoeffVec {n : ℕ} (H : TransferFunction)
    (hdeg : H.denom.natDegree ≤ n)
    (hreal : ∀ m, (H.denom.coeff m).im = 0) :
    (polyOfVec (denomCoeffVec (n := n) H)).map (algebraMap ℝ ℂ) = H.denom := by
  have hre : ∀ m, ((H.denom.coeff m).re : ℂ) = H.denom.coeff m := by
    intro m
    apply Complex.ext <;> simp [hreal m]
  have hmap : (polyOfVec (denomCoeffVec (n := n) H)).map (algebraMap ℝ ℂ)
      = ∑ j : Fin (n + 1), monomial j.val (H.denom.coeff j.val) := by
    simp only [polyOfVec, Polynomial.map_sum, Polynomial.map_monomial]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [denomCoeffVec]
    exact congrArg (monomial j.val) (hre j.val)
  calc (polyOfVec (denomCoeffVec (n := n) H)).map (algebraMap ℝ ℂ)
      = ∑ j : Fin (n + 1), monomial j.val (H.denom.coeff j.val) := hmap
    _ = H.denom := by
        rw [Fin.sum_univ_eq_sum_range (fun i => monomial i (H.denom.coeff i))]
        exact (Polynomial.as_sum_range' H.denom (n + 1) (by omega)).symm

/-! ### From the Edge Theorem to Schur stability

Reduction of Schur stability of the family to stability of its exposed edges — the
book's Corollary 6.1 with `Γ` the open unit disc. The two analytic inputs are supplied
by the lemmas below:

1. `norm_root_le_of_one_lt` is the Cauchy root bound `‖s‖ ≤ n * max|δⱼ| / δₙ`,
   uniform over the compact `P.Ω` (`hleading` = Assumption 6.1 makes the leading
   coefficient bounded below on all of `Ω`); with `rootSpaceSet_isClosed_of_isCompact`
   it yields `rootSpace_isCompact`, i.e. `RootSpace P` is compact.
2. `frontier_disc_of_compact` is the topological step: for the compact set `RootSpace P`,
   `frontier (RootSpace P) ⊆ {z | ‖z‖ < 1} ⟹ RootSpace P ⊆ {z | ‖z‖ < 1}`
   (ray escape: a point of norm `≥ 1` in a compact set forces a frontier point of
   norm `≥ 1`).

The edge-wise stability hypothesis is packaged as `EdgewiseSchur P` below; its proof
for a concrete family reduces, edge by edge, to a segment problem: an exposed edge is
`δ(t) = δ⁰ + t (δ¹ - δ⁰)`, so `RootSpaceSet E ⊆ unitDisc` is a one-parameter root-locus
condition (Jury's segment criterion).

Given those, the assembly is three lines: `edge_theorem` bounds the frontier by the
exposed edges, hypothesis (2) transports the union into the disc, and a root of
`H.denom` lies in `RootSpace P` via `denomCoeffVec` / `polyOfVec_denomCoeffVec`.
-/



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

/-- Real case of Theorem 6.1: a real root in `R(Ω)` is already an edge root.
Requires the non-degenerate family hypothesis `dir (aff Ω) ≠ 0`. -/
theorem edge_real {n : ℕ} (hn : n ≥ 1) (P : Polytope n) (s : ℂ)
    (hs : s ∈ RootSpace P)
    (hdir_ne0 : Module.finrank ℝ ↥(affineSpan ℝ P.Ω).direction ≠ 0)
    (hreal : s.im = 0) :
    ∃ E, IsExposedEdge P E ∧ s ∈ RootSpaceSet E :=
  lemma61_real hn P s hs hdir_ne0 hreal

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
    (hF_dim : Module.finrank ℝ (affineSpan ℝ F).direction ≤ 1)
    (hdir_ne0 : Module.finrank ℝ ↥(affineSpan ℝ P.Ω).direction ≠ 0) :
    ∃ E, IsExposedEdge P E ∧ s ∈ RootSpaceSet E := by
  let m := Module.finrank ℝ (affineSpan ℝ F).direction
  by_cases hm1 : m = 1
  · exact ⟨F, isExposedEdge_of_dim_1 hF_exp (by simpa [m] using hm1), hsF⟩
  · have hm0 : m = 0 := by omega
    obtain ⟨δ, hδF, hδroot⟩ := hsF
    have hF_single : F = {δ} :=
      exposed_face_dim_zero_singleton F (by simpa [m] using hm0) δ hδF
    obtain ⟨E, hE, hδE⟩ :=
      exists_exposed_edge_of_singleton hn P δ F hF_exp hF_single hdir_ne0
    exact ⟨E, hE, rootspace_mem_of_isRoot s δ hδroot E hδE⟩

/-- **Edge Theorem (Theorem 6.1).** If all polynomials in `P` have the same
degree (here ensured by a positive leading coefficient on every vertex),
then every boundary root of the family is a root of a polynomial on an exposed
edge of `P`. -/
theorem edge_theorem {n : ℕ} (hn : n ≥ 1) (P : Polytope n) (s : ℂ)
    (hleading : ∀ v ∈ P.vertices, 0 < v (Fin.last n))
    (hs : s ∈ frontier (RootSpace P))
    (hdir_ne0 : Module.finrank ℝ ↥(affineSpan ℝ P.Ω).direction ≠ 0) :
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
  · exact edge_real hn P s hs_mem hdir_ne0 hreal
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
          exists_exposed_edge_of_singleton hn P δ' G hG_exp hG_single hdir_ne0
        exact ⟨E, hE, rootspace_mem_of_isRoot s δ' hδ'root E hδ'E⟩
    · -- In dimension zero or one, the exposed face itself is a singleton or edge.
      have hdim_le1 : Module.finrank ℝ (affineSpan ℝ F).direction ≤ 1 := by omega
      exact exposed_face_root_dim_le1_to_edge hn P s F hF_exp hsF hdim_le1 hdir_ne0

/-- The edge-wise stability hypothesis of the Schur corollary: the root space of
every exposed edge of `P` lies in the open unit disc `{z | ‖z‖ < 1}`.

This is the finite, checkable part of the corollary: `P` has finitely many exposed
edges, each a segment `δ(t) = δ⁰ + t (δ¹ - δ⁰)` in coefficient space, so the condition
is decided edge by edge on one-parameter families. It is also conservative in the sense
needed for the theorem: `edge_theorem` confines `frontier (RootSpace P)` to these edge
root spaces. -/
def EdgewiseSchur {n : ℕ} (P : Polytope n) : Prop :=
  ∀ E, IsExposedEdge P E → RootSpaceSet E ⊆ { z : ℂ | ‖z‖ < 1 }


theorem edge_theorem_union {n : ℕ} (hn : n ≥ 1) (P : Polytope n) (s : ℂ)
    (hleading : ∀ v ∈ P.vertices, 0 < v (Fin.last n))
    (hs : s ∈ frontier (RootSpace P))
    (hdir_ne0 : Module.finrank ℝ ↥(affineSpan ℝ P.Ω).direction ≠ 0) :
    s ∈ ⋃ (E : Set (CoeffVec n)) (_ : IsExposedEdge P E), RootSpaceSet E := by
  obtain ⟨E, hE, hsE⟩ := edge_theorem hn P s hleading hs hdir_ne0
  exact mem_iUnion₂.mpr ⟨E, hE, hsE⟩


/-- Cauchy-type root bound: if the leading coefficient of `δ` is at least `Δ > 0` and
every coefficient is bounded by `Mv` in absolute value, then every complex root `s` of
`polyOfVec δ` outside the unit circle satisfies `‖s‖ ≤ n * Mv / Δ`.

Uniform over the family: `Δ` and `Mv` are the same for all members of a compact family,
which is what makes `RootSpace P` bounded (`rootSpace_isCompact`). -/
lemma norm_root_le_of_one_lt {n : ℕ} (hn : 1 ≤ n) {δ : CoeffVec n} {s : ℂ} {Δ Mv : ℝ}
    (hΔpos : 0 < Δ) (hΔ : Δ ≤ δ (Fin.last n)) (hMv : ∀ i : Fin (n + 1), |δ i| ≤ Mv)
    (hroot : evalAtComplex (n := n) s δ = 0) (hs : 1 < ‖s‖) :
    ‖s‖ ≤ (n : ℝ) * Mv / Δ := by
  have hexp := evalAtComplex_eq_sum δ s
  rw [hexp] at hroot
  rw [Fin.sum_univ_castSucc] at hroot
  simp only [Fin.val_castSucc, Fin.val_last] at hroot
  -- The whole estimate is contained in one chain: taking norms in
  -- `δₙ · sⁿ = -∑ᵢₙ δᵢ sⁱ` and bounding each tail term by `|δᵢ| · ‖s‖^(n-1)`.
  have h2 : Δ * ‖s‖ ^ n ≤ (∑ i : Fin n, |δ (Fin.castSucc i)|) * ‖s‖ ^ (n - 1) := by
    calc Δ * ‖s‖ ^ n ≤ |δ (Fin.last n)| * ‖s‖ ^ n :=
          mul_le_mul_of_nonneg_right (le_trans hΔ (le_abs_self _))
            (pow_nonneg (norm_nonneg s) n)
      _ = ‖(algebraMap ℝ ℂ) (δ (Fin.last n)) * s ^ n‖ := by
          rw [norm_mul, norm_pow]
          simp
      _ = ‖∑ i : Fin n, (algebraMap ℝ ℂ) (δ (Fin.castSucc i)) * s ^ (i.val : ℕ)‖ := by
          rw [eq_neg_of_add_eq_zero_left hroot, norm_neg]
      _ ≤ ∑ i : Fin n, |δ (Fin.castSucc i)| * ‖s‖ ^ (n - 1) := by
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
          have hnorm_i : ‖(algebraMap ℝ ℂ) (δ (Fin.castSucc i)) * s ^ (i.val : ℕ)‖
              = |δ (Fin.castSucc i)| * ‖s‖ ^ (i.val : ℕ) := by
            rw [norm_mul, norm_pow]
            simp
          exact (le_of_eq hnorm_i).trans
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hs.le (by have := i.isLt; omega)) (abs_nonneg _))
      _ = (∑ i : Fin n, |δ (Fin.castSucc i)|) * ‖s‖ ^ (n - 1) := by
          rw [Finset.sum_mul]
  have h3 : (∑ i : Fin n, |δ (Fin.castSucc i)|) ≤ (n : ℝ) * Mv :=
    (Finset.sum_le_sum fun i _ => hMv _).trans (by simp)
  have hA : ‖s‖ ^ n = ‖s‖ * ‖s‖ ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ']
  have h4 : ((Δ:ℝ) * ‖s‖) * ‖s‖ ^ (n - 1) ≤ ((n : ℝ) * Mv) * ‖s‖ ^ (n - 1) :=
    (le_of_eq (by rw [mul_assoc, ← hA])).trans (le_trans h2
      (mul_le_mul_of_nonneg_right h3 (pow_nonneg (norm_nonneg s) _)))
  rw [le_div_iff₀ hΔpos]
  exact le_trans (le_of_eq (by rw [mul_comm])) (le_of_mul_le_mul_right h4
    (pow_pos (zero_lt_one.trans_le hs.le) _))

/-- Uniform bound on the size of the coefficients of all `δ ∈ P.Ω`: the function
`δ ↦ ∑ i, |δ i|` is continuous on the compact `Ω`, so it is bounded by some `M ≥ 0`
dominating each individual coefficient. -/
lemma uniformMaxAbs_polytope {n : ℕ} (P : Polytope n) :
    ∃ M : ℝ, (0:ℝ) ≤ M ∧ ∀ δ ∈ P.Ω, ∀ i : Fin (n + 1), |δ i| ≤ M := by
  have hcont : ContinuousOn (fun δ : CoeffVec n => ∑ i : Fin (n + 1), |δ i|) P.Ω := by
    refine continuousOn_finset_sum Finset.univ fun i _ =>
      (continuous_apply i).abs.continuousOn
  obtain ⟨Mv, hMv⟩ := P.isCompact.exists_bound_of_continuousOn hcont
  obtain ⟨v0, hv0⟩ := P.nonempty
  have hv0Ω : v0 ∈ P.Ω :=
    subset_convexHull ℝ (P.vertices : Set (CoeffVec n)) (Finset.mem_coe.mpr hv0)
  refine ⟨Mv, ?_, fun δ hδ i => ?_⟩
  · have h := hMv v0 hv0Ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at h
    exact le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) h
  · have h1 : |δ i| ≤ ∑ i' : Fin (n + 1), |δ i'| :=
      Finset.single_le_sum (f := fun i' : Fin (n + 1) => |δ i'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)
    have h := hMv δ hδ
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at h
    exact le_trans h1 h

/-- Uniform Cauchy-type bound: if every `δ ∈ P.Ω` has leading coefficient `≥ Δ > 0` and
coefficients bounded by `Mv ≥ 0`, then every root of the family lies in
`closedBall 0 (1 + (n·Mv)/Δ)`. -/
lemma rootSpaceSet_bounded {n : ℕ} (hn : 1 ≤ n) (P : Polytope n)
    {Mv Δ : ℝ} (hMv_nn : 0 ≤ Mv) (hΔpos : 0 < Δ)
    (hΔmin : ∀ δ ∈ P.Ω, Δ ≤ δ (Fin.last n))
    (hM : ∀ δ ∈ P.Ω, ∀ i : Fin (n + 1), |δ i| ≤ Mv) :
    RootSpaceSet P.Ω ⊆ Metric.closedBall (0:ℂ) (1 + (n:ℝ) * Mv / Δ) := by
  intro z hz
  obtain ⟨δ, hδΩ, hroot⟩ := hz
  have hroot_eval : evalAtComplex (n := n) z δ = 0 := by
    simpa [evalAtComplex] using hroot
  have hd : dist z (0:ℂ) = ‖z‖ := by simp [dist_eq_norm]
  rw [Metric.mem_closedBall, hd]
  by_cases hbig : 1 < ‖z‖
  · have hbound := norm_root_le_of_one_lt hn hΔpos (hΔmin δ hδΩ)
      (hM δ hδΩ) hroot_eval hbig
    linarith
  · push_neg at hbig
    have hq : (0:ℝ) ≤ (n:ℝ) * Mv / Δ :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ)) hMv_nn) hΔpos.le
    linarith

/-- **Compactness of the root space.** `RootSpace P` is closed
(`rootSpaceSet_isClosed_of_isCompact`) and bounded, by the uniform Cauchy bound
`rootSpaceSet_bounded`: the leading coefficient attains a positive minimum `Δ` on the
compact `Ω` (Assumption 6.1, `hleading`, via convexity of the half-space `0 < δₙ`,
`convex_coeff_pos`), and `uniformMaxAbs_polytope` bounds the other coefficients. -/
theorem rootSpace_isCompact {n : ℕ} (hn : 1 ≤ n) (P : Polytope n)
    (hleading : ∀ v ∈ P.vertices, 0 < v (Fin.last n)) :
    IsCompact (RootSpace P) := by
  obtain ⟨v0, hv0⟩ := P.nonempty
  have hv0Ω : v0 ∈ P.Ω :=
    subset_convexHull ℝ (P.vertices : Set (CoeffVec n)) (Finset.mem_coe.mpr hv0)
  obtain ⟨δstar, hδΩstar, hΔmin⟩ :=
    P.isCompact.exists_isMinOn ⟨v0, hv0Ω⟩ ((continuous_apply (Fin.last n)).continuousOn)
  have hΔpos : (0:ℝ) < δstar (Fin.last n) :=
    convexHull_min (fun v hv => hleading v hv) (convex_coeff_pos (Fin.last n)) hδΩstar
  obtain ⟨Mv, hMv_nn, hM⟩ := uniformMaxAbs_polytope P
  exact Metric.isCompact_of_isClosed_isBounded
    (rootSpaceSet_isClosed_of_isCompact P.isCompact)
    (Metric.isBounded_closedBall.subset
      (rootSpaceSet_bounded hn P hMv_nn hΔpos hΔmin hM))

/-- A compact set whose frontier lies in the open unit disc is itself contained in it.

If `w` maximizes the norm on the compact set `R`, then points just outside `w` along the
ray through the origin have larger norm, hence are not in `R`, so `w ∈ frontier R`. -/
theorem frontier_disc_of_compact {R : Set ℂ}
    (hcomp : IsCompact R)
    (hfront : frontier R ⊆ { z : ℂ | ‖z‖ < 1 }) :
    R ⊆ { z : ℂ | ‖z‖ < 1 } := by
  intro x hxR
  by_contra hx
  have hx1 : 1 ≤ ‖x‖ := not_lt.mp hx
  have hne : R.Nonempty := ⟨x, hxR⟩
  obtain ⟨w, hwR, hwmax⟩ := hcomp.exists_isMaxOn hne continuous_norm.continuousOn
  have hw1 : 1 ≤ ‖w‖ := le_trans hx1 (hwmax hxR)
  have hwfront : w ∈ frontier R := by
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hwR, ?_⟩
    rw [mem_closure_iff]
    intro o ho hwo
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hwo)
    refine ⟨((1 + ε / (2 * (‖w‖ + 1))) : ℝ) • w, ?_, ?_⟩
    · exact hball (by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : ((1 + ε / (2 * (‖w‖ + 1))) : ℝ) • w - w
            = (ε / (2 * (‖w‖ + 1))) • w := by
          rw [add_smul, one_smul]
          abel
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have hgt : (ε / (2 * (‖w‖ + 1))) * ‖w‖ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg w]
        exact hgt)
    · intro hyR
      have hle : ‖((1 + ε / (2 * (‖w‖ + 1))) : ℝ) • w‖ ≤ ‖w‖ := by
        simpa using hwmax hyR
      have hpw : (0:ℝ) < 1 + ε / (2 * (‖w‖ + 1)) := by positivity
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hpw] at hle
      have htpos : (0:ℝ) < ε / (2 * (‖w‖ + 1)) := by positivity
      have hwpos : (0:ℝ) < ‖w‖ := zero_lt_one.trans_le hw1
      have hprod : (0:ℝ) < ε / (2 * (‖w‖ + 1)) * ‖w‖ := mul_pos htpos hwpos
      have hsub : ((1 + ε / (2 * (‖w‖ + 1))) : ℝ) * ‖w‖
          = ‖w‖ + ε / (2 * (‖w‖ + 1)) * ‖w‖ := by
        ring
      linarith
  have hw_disc := hfront hwfront
  simp only [Set.mem_setOf_eq] at hw_disc
  linarith

/-- **From the Edge Theorem to Schur stability.** A transfer function whose denominator's
coefficient vector lies in a polytope `P` obeying Assumption 6.1 is Schur stable provided
every exposed edge of `P` has its root space in the open unit disc (`EdgewiseSchur P`). -/
theorem edge_theorem_to_schur_stability {n : ℕ} (hn : 1 ≤ n) (P : Polytope n)
    (H : TransferFunction)
    (hδ : denomCoeffVec (n := n) H ∈ P.Ω)
    (hdeg : H.denom.natDegree ≤ n)
    (hreal : ∀ m, (H.denom.coeff m).im = 0)
    (hleading : ∀ v ∈ P.vertices, 0 < v (Fin.last n))
    (hdir_ne0 : Module.finrank ℝ ↥(affineSpan ℝ P.Ω).direction ≠ 0)
    (hedge : EdgewiseSchur P) :
    H.IsSchurStable := by
  intro z hz
  have hroot : ((polyOfVec (denomCoeffVec (n := n) H)).map (algebraMap ℝ ℂ)).IsRoot z := by
    rw [polyOfVec_denomCoeffVec H hdeg hreal]
    exact hz
  have hzR : z ∈ RootSpaceSet ({denomCoeffVec (n := n) H} : Set (CoeffVec n)) :=
    rootspace_mem_of_isRoot z (denomCoeffVec (n := n) H) hroot _ rfl
  have hzP : z ∈ RootSpace P := by
    obtain ⟨δ, hδs, hδroot⟩ := hzR
    rw [Set.mem_singleton_iff] at hδs
    subst hδs
    exact ⟨_, hδ, hδroot⟩
  have hfront : frontier (RootSpace P) ⊆ { z : ℂ | ‖z‖ < 1 } := by
    intro s hs
    obtain ⟨E, hE, hsE⟩ := edge_theorem hn P s hleading hs hdir_ne0
    exact hedge E hE hsE
  exact frontier_disc_of_compact (rootSpace_isCompact hn P hleading) hfront hzP




end CoeffBox
