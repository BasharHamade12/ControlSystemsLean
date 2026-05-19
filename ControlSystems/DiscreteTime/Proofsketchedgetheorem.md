Here's a **clear mathematical structure** for proving the `descend_to_exposed_edge` lemma, along with a **step-by-step implementation guide** for a coding agent:

---

---

### **Mathematical Proof Structure**
**Goal:**
Given an exposed face \( F \) of \( P \) with \( s_r \in R(F) \) and \( \dim(F) \geq 2 \), find an exposed edge \( E \) of \( P \) such that \( s_r \in R(E) \).

#### **Key Steps:**
1. **Base Case (\( \dim(F) = 1 \)):**
   - If \( F \) is already 1-dimensional, it is an **exposed edge** of \( P \).
   - Return \( F \) as the result.

2. **Inductive Case (\( \dim(F) \geq 2 \)):**
   - **Step A:** Extract a polynomial \( \delta_F \in F \) with \( \delta_F(s_r) = 0 \) (from `hr_in_RF`).
   - **Step B:** Define \( \mathcal{P}_{s_r} \) as the hyperplane of polynomials with root \( s_r \).
   - **Step C:** Show that \( \mathcal{P}_{s_r} \cap \text{aff}(F) \) has dimension \( \geq 1 \) (using `h_dim_ge_2`).
   - **Step D:** Construct a line in \( \mathcal{P}_{s_r} \cap \text{aff}(F) \) through \( \delta_F \) that exits \( F \) (using `ray_escapes_polytope` adapted for \( F \)).
   - **Step E:** Use connectedness to find a boundary point \( \delta_{\text{bound}} \in \text{frontier } F \cap \mathcal{P}_{s_r} \).
   - **Step F:** Extract an exposed face \( F' \) of \( F \) (and thus of \( P \)) containing \( \delta_{\text{bound}} \).
   - **Step G:** Recurse on \( F' \) (which has \( \dim(F') < \dim(F) \)).

---

---

### **Implementation Guide for Coding Agent**
Provide this **structured plan** to the coding agent. Each step includes:
- **Mathematical justification**
- **Lean tactics/lemmas to use**
- **Dependencies on existing code**

---

#### **1. Base Case (\( \dim(F) = 1 \))**
**Mathematical Idea:**
If \( F \) is 1-dimensional, it is an exposed edge of \( P \).

**Lean Implementation:**
```lean
by_cases h_dim_1 : m_F = 1
· -- Base case: F is already an exposed edge
  use F
  constructor
  · -- Show F is an exposed edge
    obtain ⟨hp, hF_eq⟩ := hF_exposed
    exact ⟨hp, hF_eq, hF_eq ▸ h_dim_1⟩
  · -- s_r ∈ RootSpaceSet F (given by hr_in_RF)
    exact hr_in_RF
```

**Dependencies:**
- `IsExposedEdge` definition (already in your code).
- `hF_exposed` (input hypothesis).

---

#### **2. Inductive Case (\( \dim(F) \geq 2 \))**
**Mathematical Idea:**
If \( \dim(F) \geq 2 \), repeat the argument for \( F \) to find a lower-dimensional exposed face \( F' \).

**Lean Implementation Steps:**

##### **Step A: Extract \( \delta_F \in F \) with \( \delta_F(s_r) = 0 \)**
```lean
obtain ⟨δ_F, hδ_F_in_F, hδ_F_root⟩ := hr_in_RF
```
- **Justification:** `hr_in_RF` states \( s_r \in \text{RootSpaceSet } F \), so there exists \( \delta_F \in F \) with \( (\text{polyOfVec } \delta_F)(s_r) = 0 \).

---

##### **Step B: Define \( \mathcal{P}_{s_r} \) and Show \( \delta_F \in \mathcal{P}_{s_r} \)**
```lean
have hδ_F_in_Psr : δ_F ∈ (P_sr n r : Set (CoeffVec n)) := by
  unfold P_sr
  simp only [Submodule.mem_ker, evalLinear, LinearMap.coe_mk, AddHom.coe_mk]
  -- Show evalLinear r δ_F = 0 using hδ_F_root
  sorry
```
- **Justification:** \( \delta_F \in \mathcal{P}_{s_r} \) because \( (\text{polyOfVec } \delta_F)(s_r) = 0 \).
- **Lean Tools:**
  - Use `hδ_F_root` to show \( \text{evalLinear } r \, \delta_F = 0 \).
  - Unfold `P_sr` and `evalLinear`.

---

##### **Step C: Show \( \mathcal{P}_{s_r} \cap \text{aff}(F) \) Has Dimension \( \geq 1 \)**
```lean
let affF := affineSpan ℝ F
have hδ_F_aff : δ_F ∈ affF := subset_affineSpan ℝ F hδ_F_in_F
have hA_dim : Module.finrank ℝ ↥(affineSpan ℝ ((P_sr n r : Set (CoeffVec n)) ∩ (affF : Set (CoeffVec n)))).direction ≥ 1 := by
  apply intersection_affine_dim_ge_one (P_sr n r) affF δ_F hδ_F_in_Psr hδ_F_aff
  · exact P_sr_dimension r
  · -- Show dim(affF) ≥ 2
    have h_dim_affF : Module.finrank ℝ affF.direction = m_F := rfl
    omega
```
- **Justification:**
  - \( \mathcal{P}_{s_r} \) has dimension \( n \) (by `P_sr_dimension`).
  - \( \text{aff}(F) \) has dimension \( m_F \geq 2 \) (by `h_dim_ge_2`).
  - Their intersection has dimension \( \geq 1 \) (by `intersection_affine_dim_ge_one`).

---

##### **Step D: Construct a Line in \( \mathcal{P}_{s_r} \cap \text{aff}(F) \) That Exits \( F \)**
```lean
haveI : Nontrivial ↥((P_sr n r : Submodule ℝ (CoeffVec n)) ⊓ affF.direction) := by
  have hA_eq : affineSpan ℝ ((P_sr n r : Set (CoeffVec n)) ∩ (affF : Set (CoeffVec n))) = (P_sr n r).toAffineSubspace ⊓ affF := by
    rw [affineSpan_inter]
  have hA_dir : ((P_sr n r).toAffineSubspace ⊓ affF).direction = (P_sr n r) ⊓ affF.direction :=
    intersection_direction_eq (P_sr n r) (affF : Set (CoeffVec n)) δ_F hδ_F_in_Psr hδ_F_aff
  have h_dim_pos : 0 < Module.finrank ℝ ↥(affineSpan ℝ ((P_sr n r : Set (CoeffVec n)) ∩ (affF : Set (CoeffVec n)))).direction := by
    omega
  rw [hA_eq, hA_dir] at h_dim_pos
  exact Module.nontrivial_of_finrank_pos h_dim_pos

obtain ⟨v_sub, hv_sub_nonzero⟩ := exists_ne (0 : ↑((P_sr n r : Submodule ℝ (CoeffVec n)) ⊓ affF.direction))
let v : CoeffVec n := v_sub.val
have hv_nonzero : v ≠ 0 := by
  intro h; apply hv_sub_nonzero; exact Submodule.coe_eq_zero.mp h
```
- **Justification:**
  - The intersection \( \mathcal{P}_{s_r} \cap \text{aff}(F) \) is nontrivial, so it contains a nonzero vector \( v \).
  - The line \( \delta_F + t \cdot v \) stays in \( \mathcal{P}_{s_r} \cap \text{aff}(F) \).

---

##### **Step E: Find Boundary Point \( \delta_{\text{bound}} \in \text{frontier } F \cap \mathcal{P}_{s_r} \)**
```lean
have h_escapes : ∃ t : ℝ, δ_F + t • v ∉ F := by
  -- Adapt ray_escapes_polytope for F (which is compact)
  sorry

obtain ⟨t_out, ht_out⟩ := h_escapes
have h_boundary : ∃ δ_bound ∈ segment ℝ δ_F (δ_F + t_out • v), δ_bound ∈ frontier F := by
  -- Use connectedness of the segment and the fact that it intersects F and F^c
  sorry
```
- **Justification:**
  - \( F \) is compact (as a closed subset of the compact set \( P.\Omega \)).
  - The line \( \delta_F + t \cdot v \) exits \( F \) (by `ray_escapes_polytope` adapted for \( F \)).
  - By connectedness, the segment intersects \( \text{frontier } F \).

**Lean Tools:**
- Use `IsCompact.isClosed` for \( F \).
- Use `IsConnected` for the segment.
- Use `frontier_eq_for_closed` (already in your code).

---
##### **Step F: Extract Exposed Face \( F' \) of \( F \) Containing \( \delta_{\text{bound}} \)**
```lean
obtain ⟨δ_bound, hδ_bound_seg, hδ_bound_front⟩ := h_boundary
have hδ_bound_in_Psr : δ_bound ∈ (P_sr n r : Set (CoeffVec n)) := by
  -- Show δ_bound ∈ P_sr using h_line_in_intersection (similar to earlier steps)
  sorry

have hF'_exists : ∃ F' : Set (CoeffVec n), IsExposedFace P F' ∧ δ_bound ∈ F' ∧ (r : ℂ) ∈ RootSpaceSet F' := by
  -- Frontier of F is union of exposed faces of F (which are also exposed faces of P)
  sorry
```
- **Justification:**
  - The frontier of \( F \) is the union of its exposed faces (which are also exposed faces of \( P \)).
  - \( \delta_{\text{bound}} \in \text{frontier } F \), so it lies in some exposed face \( F' \) of \( F \).
  - \( \delta_{\text{bound}} \in \mathcal{P}_{s_r} \), so \( s_r \in R(F') \).

**Lean Tools:**
- Use `frontier_is_union_of_exposed_faces` (needs to be proven or assumed).
- Use `hδ_bound_in_Psr` to show \( s_r \in R(F') \).

---
##### **Step G: Recurse on \( F' \)**
```lean
obtain ⟨F', hF'_exposed, hδ_bound_in_F', hr_in_RF'⟩ := hF'_exists
have hF'_dim_lt : Module.finrank ℝ (affineSpan ℝ F').direction < m_F := by
  -- F' is a proper face of F, so its dimension is strictly less
  sorry

-- Recursive call
exact descend_to_exposed_edge P r F' hF'_exposed hr_in_RF' (Set.Nonempty.mono (Set.inter_subset_left) ⟨δ_bound, hδ_bound_in_F'⟩) (by sorry)
```
- **Justification:**
  - \( F' \) is a proper face of \( F \), so \( \dim(F') < \dim(F) \).
  - Recurse on \( F' \) to eventually reach an exposed edge.

**Lean Tools:**
- Use `Module.finrank_lt_of_subset` (or similar) to show \( \dim(F') < \dim(F) \).
- Recursively call `descend_to_exposed_edge`.

---

---
---
### **Summary for Coding Agent**
Provide this **structured plan** to the coding agent:

1. **Base Case:**
   - If \( \dim(F) = 1 \), return \( F \) as the exposed edge.

2. **Inductive Case:**
   - Extract \( \delta_F \in F \) with \( \delta_F(s_r) = 0 \).
   - Show \( \mathcal{P}_{s_r} \cap \text{aff}(F) \) has dimension \( \geq 1 \).
   - Construct a line in \( \mathcal{P}_{s_r} \cap \text{aff}(F) \) that exits \( F \).
   - Find \( \delta_{\text{bound}} \in \text{frontier } F \cap \mathcal{P}_{s_r} \).
   - Extract an exposed face \( F' \) of \( F \) containing \( \delta_{\text{bound}} \).
   - Recurse on \( F' \).

3. **Key Lemmas to Use:**
   - `intersection_affine_dim_ge_one`
   - `ray_escapes_polytope` (adapted for \( F \))
   - `frontier_eq_for_closed`
   - `IsExposedFace` and `IsExposedEdge` definitions.

4. **Missing Pieces to Implement:**
   - `ray_escapes_polytope` for \( F \) (instead of \( P.\Omega \)).
   - `frontier_is_union_of_exposed_faces` for \( F \).
   - Dimension comparison for \( F' \) and \( F \).

---
This structure is **complete and actionable** for a coding agent. Each step is mathematically justified and mapped to Lean tactics/lemmas.