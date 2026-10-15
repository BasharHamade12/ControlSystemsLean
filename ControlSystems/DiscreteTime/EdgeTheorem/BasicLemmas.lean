module

public import ControlSystems.DiscreteTime.EdgeTheorem.EdgeTheoremDefs
public import Mathlib.Analysis.Convex.Intrinsic


@[expose] public section

open Polynomial Affine FiniteDimensional LinearMap Set

namespace CoeffBox

/-! # Single-copy helpers (segments, frontiers, evaluation)

Textbook: §6.2. These are the only copies — all other files reuse them:
- `frontier_eq_for_closed`: `∂S = S \ interior S` for closed `S`.
- `segment_is_connected`, `segment_point_rewrite`: parametrize
  `(1-c)•δ + c•(δ+t•v) = δ+(c*t)•v` along §6.2 descent rays.
- `eval_root_comm`: real/complex evaluation commutes with `algebraMap ℝ ℂ`.
- `ray_escapes_of_bounded`: any ray from a point of a bounded set exits it;
  replaces `ray_escapes_polytope` / `ray_escapes_compact_convex`.
-/

/-- `s ∈ R(W)` iff some `δ ∈ W` has `s` as a complex root. -/
@[simp] lemma mem_RootSpaceSet_iff {n : ℕ} (W : Set (CoeffVec n)) (s : ℂ) :
    s ∈ RootSpaceSet W ↔ ∃ δ ∈ W, ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s :=
  Iff.rfl

/-- `δ ∈ P_sr n r` iff `evalLinear r δ = 0`. -/
@[simp] lemma mem_P_sr_iff {n : ℕ} (r : ℝ) (δ : CoeffVec n) :
    δ ∈ (P_sr n r : Set (CoeffVec n)) ↔ evalLinear r δ = 0 :=
  Iff.rfl

/-- `δ ∈ P_sc n s` iff `evalAtComplex s δ = 0`. -/
@[simp] lemma mem_P_sc_iff {n : ℕ} (s : ℂ) (δ : CoeffVec n) :
    δ ∈ (P_sc n s : Set (CoeffVec n)) ↔ evalAtComplex (n := n) s δ = 0 :=
  Iff.rfl

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

/-- Evaluation at `(r : ℂ)` of the complexified polynomial commutes with the
algebraic embedding of the real evaluation. Single shared copy. -/
lemma eval_root_comm {n : ℕ} (r : ℝ) (δ : CoeffVec n) :
    eval (↑r) (map (algebraMap ℝ ℂ) (polyOfVec δ)) = (algebraMap ℝ ℂ) (eval r (polyOfVec δ)) := by
  simp [polyOfVec, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
    map_sum, map_mul, map_pow]

/-- Any ray from a point of a bounded set `S` along `v ≠ 0` exits `S`.
Generic form of `ray_escapes_polytope` / `ray_escapes_compact_convex`. -/
lemma ray_escapes_of_bounded {n : ℕ} {S : Set (CoeffVec n)}
    (hB : Bornology.IsBounded S) (δ v : CoeffVec n)
    (hδ : δ ∈ S) (hv : v ≠ 0) : ∃ t : ℝ, 0 < t ∧ δ + t • v ∉ S := by
  rcases Metric.isBounded_iff.mp hB with ⟨C, hC⟩
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  refine ⟨(|C| + 1) / ‖v‖, div_pos (by positivity) hv_norm_pos, ?_⟩
  intro h_contra
  have ht_nonneg : (0 : ℝ) ≤ (|C| + 1) / ‖v‖ := (div_pos (by positivity) hv_norm_pos).le
  have h_dist : dist (δ + ((|C| + 1) / ‖v‖) • v) δ = ((|C| + 1) / ‖v‖) * ‖v‖ := by
    rw [dist_eq_norm]
    have h_sub : δ + ((|C| + 1) / ‖v‖) • v - δ = ((|C| + 1) / ‖v‖) • v := by abel
    rw [h_sub, norm_smul, Real.norm_eq_abs _,
      abs_of_nonneg ht_nonneg]
  have h_le : dist (δ + ((|C| + 1) / ‖v‖) • v) δ ≤ C := hC h_contra hδ
  have h_t_mul : ((|C| + 1) / ‖v‖) * ‖v‖ = |C| + 1 :=
    div_mul_cancel₀ _ (ne_of_gt hv_norm_pos)
  rw [h_dist, h_t_mul] at h_le
  have : C ≤ |C| := le_abs_self C
  linarith

lemma not_mem_intrinsicInterior_of_escapes_along_direction {n : ℕ}
    (F : Set (CoeffVec n))
    (hF_convex : Convex ℝ F)
    (δ_F : CoeffVec n) (hδ_F_in_F : δ_F ∈ F)
    (v : CoeffVec n) (hv_ne : v ≠ 0) (hv_affF_dir : v ∈ (affineSpan ℝ F).direction)
    (S : Set ℝ) (hS_def : S = {t | 0 ≤ t ∧ δ_F + t • v ∈ F})
    (hS_nonempty : S.Nonempty) (h_bdd_above : BddAbove S)
    (t1 : ℝ) (ht1_t1_is_sup : t1 = sSup S) (ht1_nonneg : 0 ≤ t1)
    (hδ_bound_in_F : (δ_F + t1 • v) ∈ F)
    (t_out : ℝ) (ht_out_pos : 0 < t_out) (ht_out : δ_F + t_out • v ∉ F) :
    (δ_F + t1 • v) ∉ intrinsicInterior ℝ F := by
  let δ_bound : CoeffVec n := δ_F + t1 • v
  let affF : AffineSubspace ℝ (CoeffVec n) := affineSpan ℝ F
  have h_upper_bound : ∀ x ∈ S, x ≤ t_out := by
    intro x hx
    rw [hS_def] at hx
    rcases hx with ⟨hx_nonneg, hx_mem⟩
    by_contra! h_gt
    have hdiv_nonneg : 0 ≤ t_out / x := div_nonneg (by linarith) (by linarith)
    have hdiv_le_one : t_out / x ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have hb_nonneg : 0 ≤ 1 - t_out / x := by linarith
    have hsum : (t_out / x : ℝ) + (1 - t_out / x) = 1 := by ring
    have hstar : StarConvex ℝ (δ_F + x • v) F := hF_convex hx_mem
    have h_mem_conv : (t_out / x : ℝ) • (δ_F + x • v) + (1 - t_out / x) • δ_F ∈ F :=
      hstar hδ_F_in_F hdiv_nonneg hb_nonneg hsum
    have h_conv : (t_out / x : ℝ) • (δ_F + x • v) + (1 - t_out / x) • δ_F = δ_F + t_out • v := by
      calc
        (t_out / x : ℝ) • (δ_F + x • v) + (1 - t_out / x) • δ_F
            = (t_out / x) • δ_F + (t_out / x) • (x • v) + (1 - t_out / x) • δ_F := by rw [smul_add]
        _ = ((t_out / x) • δ_F + (1 - t_out / x) • δ_F) + (t_out / x) • (x • v) := by abel
        _ = ((t_out / x + (1 - t_out / x)) • δ_F) + ((t_out / x) * x) • v := by
          simp [smul_smul]
        _ = (1 • δ_F) + (t_out • v) := by
          have h_x_ne_zero : x ≠ 0 := by linarith
          have h_sum : t_out / x + (1 - t_out / x) = 1 := by ring
          have h_mul : (t_out / x) * x = t_out := by field_simp [h_x_ne_zero]
          simp [h_sum, h_mul]
        _ = δ_F + t_out • v := by simp
    rw [h_conv] at h_mem_conv
    exact ht_out h_mem_conv
  have h_t1_le_t_out : t1 ≤ t_out := by
    rw [ht1_t1_is_sup]
    exact csSup_le hS_nonempty h_upper_bound
  have ht_out_gt_t1 : t1 < t_out := by
    by_contra! h_ge
    have h_eq : t1 = t_out := le_antisymm h_t1_le_t_out h_ge
    have h_t_out_mem_F : δ_F + t_out • v ∈ F := by
      rw [← h_eq]
      exact hδ_bound_in_F
    exact ht_out h_t_out_mem_F
  by_contra h_relint
  rcases h_relint with ⟨x, hx_int, hx_eq⟩
  have hx_val : (x : CoeffVec n) = δ_bound := hx_eq
  have h_open_int : IsOpen (interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF)) :=
    isOpen_interior
  haveI : Nonempty affF := ⟨⟨δ_F, subset_affineSpan ℝ F hδ_F_in_F⟩⟩
  let v_dir : (affineSpan ℝ F).direction := ⟨v, hv_affF_dir⟩
  have h_cont_ambient : Continuous (fun (t : ℝ) => (t • v : CoeffVec n) + (x : CoeffVec n)) := by
    continuity
  have h_mem_affF : ∀ (t : ℝ), (t • v : CoeffVec n) + (x : CoeffVec n) ∈ affF := by
    intro t
    simpa using
      AffineSubspace.vadd_mem_of_mem_direction (s := affF) (hv := affF.direction.smul_mem t hv_affF_dir)
        (hp := x.property)
  have h_cont : Continuous (fun (t : ℝ) => (t • v_dir) +ᵥ (x : affF)) := by
    have h_eq : (fun (t : ℝ) => ((t • v_dir) +ᵥ (x : affF) : CoeffVec n)) =
      (fun (t : ℝ) => (t • v : CoeffVec n) + (x : CoeffVec n)) := by
      ext t
      simp [v_dir, vadd_eq_add]
    have h_cont' : Continuous (fun (t : ℝ) => ((t • v_dir) +ᵥ (x : affF) : CoeffVec n)) := by
      simpa [h_eq] using h_cont_ambient
    exact h_cont'.subtype_mk (fun t => h_mem_affF t)
  have h_preimage_open : IsOpen ((fun (t : ℝ) => (t • v_dir) +ᵥ (x : affF))⁻¹'
      (interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF))) :=
    h_open_int.preimage h_cont
  have h_zero_mem : (0 : ℝ) ∈ (fun (t : ℝ) => (t • v_dir) +ᵥ (x : affF))⁻¹'
      (interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF)) := by
    show (0 • v_dir) +ᵥ (x : affF) ∈ interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF)
    simpa using hx_int
  have h_nhds : (fun (t : ℝ) => (t • v_dir) +ᵥ (x : affF))⁻¹'
      (interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF)) ∈ nhds (0 : ℝ) :=
    h_preimage_open.mem_nhds h_zero_mem
  rcases Metric.mem_nhds_iff.mp h_nhds with ⟨ε, hε_pos, h_ball⟩
  let t_small := min (ε / 2) ((t_out - t1) / 2)
  have ht_small_pos : 0 < t_small := by
    refine lt_min_iff.mpr ⟨by nlinarith, by nlinarith⟩
  have h_ball_mem : t_small ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have ht_small_lt_ε : t_small < ε := by
      have h1 : t_small ≤ ε / 2 := min_le_left _ _
      have h2 : ε / 2 < ε := by nlinarith
      linarith
    calc
      |t_small| = t_small := abs_of_pos ht_small_pos
      _ < ε := ht_small_lt_ε
  have h_mem_interior : t_small • v_dir +ᵥ (x : affF) ∈
      interior ((Subtype.val : affF → CoeffVec n)⁻¹' F : Set affF) :=
    h_ball h_ball_mem
  have h_mem_preimage : t_small • v_dir +ᵥ (x : affF) ∈
      (Subtype.val : affF → CoeffVec n)⁻¹' F :=
    interior_subset h_mem_interior
  have h_mem_F : ((t_small • v_dir +ᵥ (x : affF) : affF) : CoeffVec n) ∈ F :=
    h_mem_preimage
  have h_coord : ((t_small • v_dir +ᵥ (x : affF) : affF) : CoeffVec n) =
      δ_F + (t1 + t_small) • v := by
    calc
      ((t_small • v_dir +ᵥ (x : affF) : affF) : CoeffVec n) = (t_small • v : CoeffVec n) + (x : CoeffVec n) := by
        simp [v_dir, vadd_eq_add]
      _ = (t_small • v : CoeffVec n) + δ_bound := by rw [hx_val]
      _ = t_small • v + (δ_F + t1 • v) := by simp [δ_bound]
      _ = δ_F + t1 • v + t_small • v := by abel
      _ = δ_F + (t1 + t_small) • v := by
        simp [add_smul]
        abel
  rw [h_coord] at h_mem_F
  have h_contra : δ_F + (t1 + t_small) • v ∉ F := by
    intro hF
    have hS : (t1 + t_small) ∈ S := by
      rw [hS_def]
      exact ⟨by nlinarith, hF⟩
    have h_sup_le : t1 + t_small ≤ sSup S := le_csSup h_bdd_above hS
    rw [ht1_t1_is_sup] at h_sup_le
    nlinarith
  exact h_contra h_mem_F

end CoeffBox
