# Lemma 6.2 — Formal Proof Blueprint

**Statement (Lemma 6.2):** Let `F` be an **exposed face** of a polytope `Ω` (satisfying Assumption 6.1, i.e., constant-sign leading coefficient). Then

```
∂ R(F) ⊆ R(∂ F)
```

where `∂ X` denotes the **boundary** of `X` in the complex plane, and `R(W) = {s ∈ ℂ | ∃ δ ∈ W, polyOfVec δ(s) = 0}` is the root space.

---

## 1. Setup and Preliminary Facts

### 1.1. What we know about `F`

- `F` is an exposed face of `P` (the polytope `Ω`). In Lean we have `hF_exp : IsExposedFace P F`.
- `F` is **compact** (`hF_compact : IsCompact F` — from `isExposedFace_isCompact`).
- `F` is **convex** (`hF_convex : Convex ℝ F` — from `isExposedFace_convex`).
- `F ⊆ P.Ω` (`isExposedFace_subset_Ω`).
- `F` is **two-dimensional** in the textbook proof:
  ```
  hF_dim_2 : Module.finrank ℝ (affineSpan ℝ F).direction = 2
  ```
  In Lean we parametrize `affineSpan ℝ F` as an affine subspace `affF` and its direction as `V := affF.direction`, so `dim(V) = 2`.

### 1.2. The space `R(F)` is closed

Since `F` is compact and the evaluation map `(δ, s) ↦ polyOfVec δ(s)` is continuous, the root set
```
R(F) = π₂( (F × ℂ) ∩ { (δ, s) | polyOfVec δ(s) = 0 } )
```
is the continuous image of a closed subset of a compact set, and the projection `π₂` is a closed map (`IsClosedMap` of a compact space onto a Hausdorff space). Hence:

```
lemma rootSpaceSet_isClosed_of_isCompact {W : Set (CoeffVec n)} (hW : IsCompact W) :
    IsClosed (RootSpaceSet W) := ...
```

**Corollary:** If `s* ∈ ∂ R(F)`, then `s* ∈ R(F)` because `∂ R(F) ⊆ closure R(F) = R(F)` (since `R(F)` is closed). So there exists `δ* ∈ F` with `polyOfVec δ*(s*) = 0`.

---

## 2. Root Subspaces: `P_sr` and `P_sc`

From the existing formalization:

| Subspace | Definition | Real dimension | Condition |
|----------|-----------|----------------|-----------|
| `P_sr n r` | `ker(evalLinear r)` | `n` | `r ∈ ℝ` |
| `P_sc n s` | `ker(evalAtComplex s)` | `n-1` | `s.im ≠ 0` |

**Important:** `P_sc n s` is only an ℝ-linear subspace of `CoeffVec n` (not ℂ-linear). It has codimension 2 in the ℝ-vector space `CoeffVec n`, hence dimension `(n+1) - 2 = n-1`. This is proved in `P_sc_dimension`.

---

## 3. Real Case (`s*.im = 0`)

**Given:** `s* ∈ ∂ R(F)` with `s*.im = 0`. So `s* = (s*.re : ℂ)` is actually real.

**Step 3.1 — Find δ*:** Since `s* ∈ R(F)`, there exists `δ* ∈ F` such that `(polyOfVec δ*)(s*) = 0`.

**Step 3.2 — δ* ∈ P_sr n s*.re:**
```
hδ*_in_Psr : δ* ∈ (P_sr n s*.re : Set (CoeffVec n))
```
This follows from `mem_P_sr_of_isRoot` (in `ExposedFaceLemmas`).

**Step 3.3 — The intersection `U ∩ V` has dimension ≥ 1.**

Let `U := P_sr n s*.re` (dimension `n`).
Let `V := (affineSpan ℝ F).direction` (dimension `2`). The key dimension estimate:

```
finrank_inf_ge_one U V hU_dim hV_dim
```
where `hU_dim : finrank ℝ U = n` and `hV_dim : finrank ℝ V ≥ 2`.

Why this holds: by `Submodule.finrank_sup_add_finrank_inf_eq`, we have
```
finrank(U ⊔ V) + finrank(U ⊓ V) = finrank(U) + finrank(V)
finrank(U ⊔ V) ≤ finrank(⊤) = n+1
```
Since `finrank U = n` and `finrank V = 2`, we get `finrank(U ⊓ V) ≥ 1`.

**Conclusion:** There exists a nonzero `v ∈ U ⊓ V`. This vector lies both in `P_sr n s*.re` (so `polyOfVec` of any `δ` plus multiples of `v` still has root `s*`) and in `(affineSpan ℝ F).direction` (so the line `δ* + t·v` stays in the affine hull of `F`).

**Step 3.4 — The ray exits F.**

Since `F` is bounded (compact), for any nonzero `v`, the ray `δ* + t·v` must eventually exit `F`. Let
```
t_out := sup { t ≥ 0 | δ* + t·v ∈ F }
```
Because `F` is compact, `t_out` is finite, the supremum is attained (by closedness of `F`), and
- `δ_bound := δ* + t_out·v ∈ F` (or possibly `δ_bound ∈ ∂F`),
- For all `t > t_out`, `δ* + t·v ∉ F`.

**If `δ*` is already on the boundary of `F`** (i.e., `δ* ∈ frontier F`), then `δ* ∈ ∂F` and we already have `s* ∈ R(δ*)`, so `s* ∈ R(∂F)` and we are done.

**If `δ* ∉ frontier F`** (i.e., `δ* ∈ intrinsicInterior ℝ F`), then `δ*` is in the relative interior. The point `δ* + t_out·v` will be on the relative boundary `frontier F` (by a segment-crossing argument: the segment from `δ*` to `δ* + (t_out+ε)·v` must intersect the frontier, since `δ* ∈ int(F)` and `δ* + (t_out+ε)·v ∉ F`).

Let `δ_bound` be this frontier intersection point. Since `v ∈ U = P_sr n s*.re`, the whole line `δ* + ℝ·v` lies in `δ* + U`. Therefore `δ_bound ∈ δ* + U`, so `δ_bound ∈ P_sr n s*.re`, meaning `polyOfVec δ_bound(s*) = 0`. Hence `s* ∈ R(δ_bound) ⊆ R(∂F)`.

---

## 4. Complex Case (`s*.im ≠ 0`)

**Given:** `s* ∈ ∂ R(F)` with `s*.im ≠ 0`. Again there exists `δ* ∈ F` with `polyOfVec δ*(s*) = 0`.

**Step 4.1 — δ* ∈ P_sc n s*:**
```
hδ*_in_Psc : δ* ∈ (P_sc n s* : Set (CoeffVec n))
```
by `mem_P_sc_of_isRoot`.

Let `U := P_sc n s*` (dimension `n-1`) and `V := (affineSpan ℝ F).direction` (dimension `2`).

We now branch into two cases depending on the dimension of `U ⊓ V`.

---

### 4.1. Case A: `dim(U ⊓ V) ≥ 1`

Same argument as the real case, but using the complex root subspace `P_sc` instead of `P_sr`.

There exists `v ∈ U ⊓ V`, `v ≠ 0`. The ray `δ* + t·v` stays in `affineSpan ℝ F` (since `v ∈ V`) and every point on the ray remains in `P_sc n s*` (since `v ∈ U`). The exit point on the boundary of `F` gives `s* ∈ R(∂F)`.

---

### 4.2. Case B: `dim(U ⊓ V) = 0`

Equivalently, `U ∩ V = {0}`. Since `dim V = 2`, `dim U = n-1`, and `dim(U ⊓ V) = 0`, the sum `U + V` has dimension `(n-1) + 2 - 0 = n+1` = total dimension, so `U + V = CoeffVec n`.

This means **every coefficient vector `δ` can be uniquely decomposed as `δ = δ_U + δ_V`** with `δ_U ∈ U` and `δ_V ∈ V` (direct sum decomposition `CoeffVec n = U ⊕ V`).

#### 4.2.1. The restricted evaluation map `evalAtComplex s*|_V : V → ℂ` is invertible

Since `CoeffVec n = U ⊕ V` and `U = ker(evalAtComplex s*)`, the restriction of `evalAtComplex s*` to `V` is injective and both have ℝ-dimension 2, so it is an ℝ-linear isomorphism `V ≅ ℂ`.

Concretely: For each `s ∈ ℂ`, there exists a unique `v(s) ∈ V` such that `evalAtComplex s* (v(s)) = s` (since `evalAtComplex s*` is an ℝ-linear map from `V` onto ℂ, and `dim(V) = 2 = dim_ℝ(ℂ)`).

#### 4.2.2. The frontier condition gives a sequence `sₖ → s*`, `sₖ ∉ R(F)`

Since `s* ∈ ∂ R(F)` and `R(F)` is closed, `s*` is on the boundary, so there exists a sequence `(sₖ)` in `ℂ \ R(F)` with `sₖ → s*`.

#### 4.2.3. For large `k`, `evalAtComplex sₖ|_V` is also invertible

The space `GL(V, ℂ)` of ℝ-linear isomorphisms `V → ℂ` is open in the space `L(V, ℂ)` of all ℝ-linear maps. Since `evalAtComplex sₖ → evalAtComplex s*` as `k → ∞` (in the operator norm, because the defining matrices `Wₙ → W` as in the textbook), and `evalAtComplex s*|_V` is invertible, for sufficiently large `k`, `evalAtComplex sₖ|_V` is also invertible.

#### 4.2.4. Construct `δₖ ∈ affF` with root `sₖ`

For large `k`, solve for `vₖ ∈ V` such that
```
evalAtComplex sₖ (δ* + vₖ) = 0
```
Equivalently:
```
evalAtComplex sₖ (δ*) + evalAtComplex sₖ (vₖ) = 0
evalAtComplex sₖ (vₖ) = - evalAtComplex sₖ (δ*)
```
Since `evalAtComplex sₖ|_V` is invertible, there is a unique solution `vₖ ∈ V`. Set `δₖ := δ* + vₖ`.

**Properties of `δₖ`:**
- `δₖ ∈ aff(F)` because `δ* ∈ F ⊆ aff(F)` and `vₖ ∈ V = aff(F).direction`.
- `polyOfVec δₖ(sₖ) = 0` by construction.
- `sₖ ∉ R(F)` by construction, so `δₖ ∉ F` (otherwise `sₖ ∈ R(F)`).

#### 4.2.5. Show `vₖ → 0` as `k → ∞`

Because `evalAtComplex sₖ → evalAtComplex s*` and `evalAtComplex s*(δ*) = 0`, the right-hand side satisfies `evalAtComplex sₖ(δ*) → 0`. Since `evalAtComplex sₖ|_V` is invertible with inverse converging to `(evalAtComplex s*|_V)⁻¹`, we get `vₖ → 0`, hence `δₖ → δ*`.

#### 4.2.6. Conclude `δ* ∈ ∂F`

We have a sequence `δₖ → δ*` with `δₖ ∈ aff(F)` but `δₖ ∉ F`. Therefore every ball around `δ*` in `aff(F)` contains points not in `F`, meaning `δ*` is on the **relative boundary** of `F`:
```
δ* ∈ frontier_relative F = F \ intrinsicInterior ℝ F
```
Thus `δ* ∈ ∂F`, and since `polyOfVec δ*(s*) = 0`, we have `s* ∈ R(∂F)`.

---

## 5. Summary of the Overall Proof

```
Theorem lemma62 (hn : n ≥ 1) (P : Polytope n) (F : Set (CoeffVec n))
    (hF_exp : IsExposedFace P F)
    (hF_dim_2 : Module.finrank ℝ (affineSpan ℝ F).direction = 2) :
    frontier (RootSpaceSet F) ⊆ RootSpaceSet (F \ intrinsicInterior ℝ F)
```

**Input:** `s* ∈ frontier (RootSpaceSet F)`

| Step | Action | Key Lean Function |
|------|--------|-------------------|
| 1 | `F` is compact, convex | `isExposedFace_isCompact`, `isExposedFace_convex` |
| 2 | `RootSpaceSet F` is closed | `rootSpaceSet_isClosed_of_isCompact` |
| 3 | Hence `s* ∈ RootSpaceSet F` | `frontier_subset` `h_closed` |
| 4 | Get `δ* ∈ F` with root `s*` | `hδ*_in_RF` |
| 5 | Branch on `s*.im = 0` | `by_cases hreal` |

**Real case (s*.im = 0):**
| Step | Action | Key Lean Function |
|------|--------|-------------------|
| R6 | `δ* ∈ P_sr n s*.re` | `mem_P_sr_of_isRoot` |
| R7 | `dim(U) = n`, `dim(V) = 2` | `P_sr_dimension`, `hF_dim_2` |
| R8 | `dim(U ⊓ V) ≥ 1` | `finrank_inf_ge_one` |
| R9 | Get nonzero `v ∈ U ⊓ V` | `exists_ne (0 : ⊤(U ⊓ V))` |
| R10 | Exit ray from `δ*` along `v` | `ray_escapes_compact_convex` |
| R11 | Find boundary point `δ_bound` | `segment_crosses_frontier` |
| R12 | `δ_bound ∈ P_sr` (so `s*` is root) | `Submodule.add_mem`, `Submodule.smul_mem` |
| R13 | `δ_bound ∈ ∂F` | `frontier_eq_for_closed` |

**Complex case (s*.im ≠ 0):**
| Step | Action | Key Lean Function |
|------|--------|-------------------|
| C6 | `δ* ∈ P_sc n s*` | `mem_P_sc_of_isRoot` |
| C7 | `dim(U) = n-1`, `dim(V) = 2` | `P_sc_dimension`, `hF_dim_2` |
| C8 | Branch on `dim(U ⊓ V)` | `by_cases h_inter_trivial` |
| C9a | Case A (dim≥1): same as R9–R13 with `P_sc` | (same structure) |
| C9b | Case B (dim=0): direct sum `U ⊕ V = CoeffVec n` | — |
| C10b | `evalAtComplex s*|_V` is invertible | `finrank V = 2 = finrank_ℝ ℂ` + injectivity |
| C11b | Sequence `sₖ → s*`, `sₖ ∉ R(F)` from frontier | `Metric.frontier_seq_tendsto` |
| C12b | For large `k`, `evalAtComplex sₖ|_V` is invertible | continuity + openness of `GL(V,ℂ)` |
| C13b | Solve `δₖ = δ* + vₖ` with `δₖ(sₖ) = 0` | `evalAtComplex sₖ(vₖ) = -evalAtComplex sₖ(δ*)` |
| C14b | `δₖ → δ*`, `δₖ ∉ F` | continuity + `sₖ ∉ R(F)` |
| C15b | `δ* ∈ ∂F` | definition of relative boundary |

---

## 6. Lean Translation Plan — New File `Lemma62.lean`

### 6.1. Axioms / New Lemmas Needed

Some of the analytical/geometric facts used above are not in the existing codebase and may need to be added. We list them here as **assumptions / to-be-proven lemmas**, with a clear specification of what they state.

#### 6.1.1. `rootSpaceSet_isClosed_of_isCompact`

```lean4
lemma rootSpaceSet_isClosed_of_isCompact {n : ℕ} {W : Set (CoeffVec n)} (hW : IsCompact W) :
    IsClosed (RootSpaceSet W) :=
  ...
```

**Input:** `W` compact set of coefficient vectors.  
**Output:** `RootSpaceSet W` is closed in ℂ.  
**Proof sketch:** The map `φ : W × ℂ → ℂ` given by `(δ, s) ↦ ((polyOfVec δ).map (algebraMap ℝ ℂ)).eval s` is continuous. The preimage `φ⁻¹({0})` is closed in `W × ℂ`. Since `W` is compact, the projection `π₂ : W × ℂ → ℂ` is a closed map (`IsCompact.isClosedMap`), and `RootSpaceSet W = π₂(φ⁻¹({0}))`.

#### 6.1.2. `ray_escapes_compact_convex`

```lean4
lemma ray_escapes_compact_convex {F : Set (CoeffVec n)} (hF_compact : IsCompact F)
    (hF_convex : Convex ℝ F) (δ_F : CoeffVec n) (hδ_in_F : δ_F ∈ F) (v : CoeffVec n)
    (hv_ne : v ≠ 0) : ∃ (t : ℝ), 0 < t ∧ δ_F + t • v ∉ F :=
  ...
```

**Input:** compact convex `F`, `δ_F ∈ F`, `v ≠ 0`.  
**Output:** a positive `t` such that `δ_F + t • v ∉ F`.  
**Proof:** Since `F` is bounded (`hF_compact.isBounded`), pick `t > sup { ‖x - δ_F‖ | x ∈ F } / ‖v‖`.

#### 6.1.3. `segment_crosses_frontier` (for compact convex sets)

```lean4
lemma segment_crosses_frontier {F : Set (CoeffVec n)} (hF_compact : IsCompact F)
    (hF_convex : Convex ℝ F) (δ_F : CoeffVec n) (hδ_in_F : δ_F ∈ F)
    (hδ_not_front : δ_F ∉ frontier F) (v : CoeffVec n) (hv_ne : v ≠ 0) (t_out : ℝ)
    (ht_out_pos : 0 < t_out) (ht_out : δ_F + t_out • v ∉ F) :
    ∃ δ_bound ∈ segment ℝ δ_F (δ_F + t_out • v), δ_bound ∈ frontier F :=
  ...
```

**Input:** `δ_F` is in `F` but not on its frontier, `v ≠ 0`, and `δ_F + t_out • v ∉ F`.  
**Output:** a point on the segment from `δ_F` to `δ_F + t_out • v` that lies on the frontier of `F`.  
**Proof:** The segment is connected. The `interior F` and `interior (Fᶜ)` are open disjoint sets covering the segment except the frontier. Since `δ_F ∈ interior F` and `δ_F + t_out • v ∈ interior (Fᶜ)` (since `F` is closed), connectedness forces the segment to intersect the frontier. This is essentially the argument from `PreliminaryLemmas.segment_boundary_intersection`, which already exists for a polytope `P`. We can generalize it.

#### 6.1.4. `metric_frontier_seq_tendsto`

```lean4
lemma metric_frontier_seq_tendsto {X : Type*} [MetricSpace X] {S : Set X} {x : X}
    (hx : x ∈ frontier S) : ∃ (s_seq : ℕ → X), (∀ n, s_seq n ∉ S) ∧ Filter.Tendsto s_seq Filter.atTop (nhds x) :=
  ...
```

**Input:** `x` in the frontier of `S` in a metric space.  
**Output:** a sequence outside `S` converging to `x`.  
**Proof:** Use `Metric.mem_closure_iff` to get points arbitrarily close.

#### 6.1.5. `finrank_inf_ge_one` (already exists in `PreliminaryLemmas`)

This is already in the codebase; we use it as is.

#### 6.1.6. `inverse_tendsto` lemma for the linear maps

```lean4
lemma evalAtComplex_tendsto {n : ℕ} (s : ℂ) (s_seq : ℕ → ℂ) (hs_seq : Filter.Tendsto s_seq Filter.atTop (nhds s)) :
    Filter.Tendsto (fun k : ℕ => evalAtComplex (n := n) (s_seq k)) Filter.atTop
      (nhds (evalAtComplex (n := n) s)) :=
  ...
```

**Input:** `s_seq → s`.  
**Output:** `evalAtComplex (s_seq k) → evalAtComplex s` in the operator norm topology.  
**Proof:** Uniform convergence follows from the explicit matrix representation of `evalAtComplex` — the entries are either `0`, `1`, powers of `s`, or powers of `Re(s)`/`|s|²`, all of which depend continuously on `s`.

#### 6.1.7. Openness of `GL(V, ℂ)` in `L(V, ℂ)`

```lean4
lemma isOpen_invertible_restriction {n : ℕ} (V : Submodule ℝ (CoeffVec n))
    (hV_dim : Module.finrank ℝ V = 2) (s : ℂ) (h_inv : Function.Bijective ((evalAtComplex s).restrict₁ V)) :
    ∃ ε > 0, ∀ t : ℂ, dist t s < ε → Function.Bijective ((evalAtComplex t).restrict₁ V) :=
  ...
```

**Proof sketch:** Choose a basis `{e₁, e₂}` of `V`. The matrix of `(evalAtComplex t).restrict₁ V` in this basis (over ℝ) relative to the ℝ-basis `{1, i}` of ℂ has determinant that varies continuously in `t`. At `t = s`, the determinant is nonzero (invertibility). Since `det` is continuous, it remains nonzero in a neighborhood of `s`.

#### 6.1.8. `direct_sum_decomposition` (optional)

```lean4
lemma direct_sum_of_dim_sum_eq_total {U V : Submodule ℝ (CoeffVec n)}
    (hU_dim : Module.finrank ℝ U = n - 1) (hV_dim : Module.finrank ℝ V = 2)
    (h_inter_dim : Module.finrank ℝ (↥(U ⊓ V)) = 0) : U ⊔ V = ⊤ :=
  ...
```

**Proof:** From `Submodule.finrank_sup_add_finrank_inf_eq`, we have:
```
finrank(U ⊔ V) + 0 = (n-1) + 2 = n+1
```
so `finrank(U ⊔ V) = n+1 = finrank(⊤)`, hence `U ⊔ V = ⊤`.

### 6.2. Overall Architecture

```
Lemma62.lean
├── Imports (EdgeTheoremDefs, BasicLemmas, PreliminaryLemmas, ExposedFaceLemmas, EdgeDescent, Lemma61)
├── Section 1: General lemmas
│   ├── rootSpaceSet_isClosed_of_isCompact
│   ├── ray_escapes_compact_convex
│   ├── segment_crosses_frontier
│   ├── metric_frontier_seq_tendsto
│   └── evalAtComplex_restrict_invertible + openness
│
├── Section 2: Real case helper
│   ├── lemma62_real_case
│
├── Section 3: Complex case helper
│   ├── case_A_ray_exit
│   └── case_B_sequence_construction
│
└── Section 4: Main theorem
    └── lemma62
```

### 6.3. Detailed Lean Signatures

```lean4
@[expose] public section

open Polynomial Affine FiniteDimensional LinearMap Set
open Complex
open Filter

namespace CoeffBox

/-- 1. Root space closedness --/
lemma rootSpaceSet_isClosed_of_isCompact {n : ℕ} {W : Set (CoeffVec n)}
    (hW : IsCompact W) : IsClosed (RootSpaceSet W) := ...

/-- 2. Ray escapes compact convex set --/
lemma ray_escapes_compact_convex {n : ℕ} {F : Set (CoeffVec n)}
    (hF_compact : IsCompact F) (hF_convex : Convex ℝ F)
    (δ_F : CoeffVec n) (hδ_in_F : δ_F ∈ F) (v : CoeffVec n) (hv_ne : v ≠ 0) :
    ∃ (t : ℝ), 0 < t ∧ δ_F + t • v ∉ F := ...

/-- 3. Segment crosses frontier --/
lemma segment_crosses_frontier {n : ℕ} {F : Set (CoeffVec n)}
    (hF_compact : IsCompact F) (hF_convex : Convex ℝ F)
    (δ_F : CoeffVec n) (hδ_in_F : δ_F ∈ F) (hδ_not_front : δ_F ∉ frontier F)
    (v : CoeffVec n) (hv_ne : v ≠ 0) (t_out : ℝ)
    (ht_out_pos : 0 < t_out) (ht_out : δ_F + t_out • v ∉ F) :
    ∃ δ_bound ∈ segment ℝ δ_F (δ_F + t_out • v), δ_bound ∈ frontier F := ...

/-- 4. Sequence from frontier in a metric space --/
lemma metric_frontier_seq_tendsto {X : Type*} [MetricSpace X] {S : Set X} {x : X}
    (hx : x ∈ frontier S) : ∃ (s_seq : ℕ → X), (∀ n, s_seq n ∉ S) ∧
      Filter.Tendsto s_seq Filter.atTop (nhds x) := ...

/-- 5. The restriction of evalAtComplex s to V is invertible when dim(V) = 2 and U ∩ V = {0} --/
lemma evalAtComplex_restrict_bijective {n : ℕ} (V : Submodule ℝ (CoeffVec n))
    (hV_dim : Module.finrank ℝ V = 2) (s : ℂ) (hδ*_in_Psc : δ* ∈ (P_sc n s : Set (CoeffVec n)))
    (hV_direct_sum : P_sc n s ⊔ V = ⊤) (h_inter_dim_0 : Module.finrank ℝ (↥(P_sc n s ⊓ V)) = 0) :
    Function.Bijective ((evalAtComplex s).restrict₁ V) := ...

/-- 6. Openness: if (evalAtComplex s).restrict₁ V is bijective, so is
   (evalAtComplex t).restrict₁ V for t near s --/
lemma exists_nhd_invertible {n : ℕ} (V : Submodule ℝ (CoeffVec n))
    (hV_dim : Module.finrank ℝ V = 2) (s : ℂ)
    (h_bij : Function.Bijective ((evalAtComplex s).restrict₁ V)) :
    ∃ ε > 0, ∀ (t : ℂ), dist t s < ε →
      Function.Bijective ((evalAtComplex t).restrict₁ V) := ...

/-- 7. Dimension inequality for intersection when total dimension is exceeded --/
lemma finrank_inf_ge_one_of_dim_2 {n : ℕ} (U : Submodule ℝ (CoeffVec n))
    (hU_dim : Module.finrank ℝ U = n) (V : Submodule ℝ (CoeffVec n))
    (hV_dim : Module.finrank ℝ V = 2) :
    Module.finrank ℝ (↥(U ⊓ V)) ≥ 1 := ...

/-- 8. Direct sum decomposition --/
lemma direct_sum_of_dim_sum_eq_total {n : ℕ} (U V : Submodule ℝ (CoeffVec n))
    (hU_dim : Module.finrank ℝ U = n - 1) (hV_dim : Module.finrank ℝ V = 2)
    (h_inter_dim : Module.finrank ℝ (↥(U ⊓ V)) = 0) : U ⊔ V = ⊤ := ...

/-- REAL CASE of Lemma 6.2 --/
lemma lemma62_real_case {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hF_dim_2 : Module.finrank ℝ (affineSpan ℝ F).direction = 2)
    (s* : ℂ) (hs*_front : s* ∈ frontier (RootSpaceSet F)) (hreal : s*.im = 0) :
    s* ∈ RootSpaceSet (F \ intrinsicInterior ℝ F) := ...

/-- COMPLEX CASE of Lemma 6.2 --/
lemma lemma62_complex_case {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hF_dim_2 : Module.finrank ℝ (affineSpan ℝ F).direction = 2)
    (s* : ℂ) (hs*_front : s* ∈ frontier (RootSpaceSet F)) (hcomplex : s*.im ≠ 0) :
    s* ∈ RootSpaceSet (F \ intrinsicInterior ℝ F) := ...

/-- MAIN THEOREM: Lemma 6.2 --/
theorem lemma62 {n : ℕ} (hn : n ≥ 1) (P : Polytope n)
    (F : Set (CoeffVec n)) (hF_exp : IsExposedFace P F)
    (hF_dim_2 : Module.finrank ℝ (affineSpan ℝ F).direction = 2) :
    frontier (RootSpaceSet F) ⊆ RootSpaceSet (F \ intrinsicInterior ℝ F) :=
  by
    intro s* hs*_front
    by_cases hreal : s*.im = 0
    · exact lemma62_real_case hn P F hF_exp hF_dim_2 s* hs*_front hreal
    · exact lemma62_complex_case hn P F hF_exp hF_dim_2 s* hs*_front hreal

end CoeffBox
```

---

## 7. Dependencies and Prerequisites

The following existing lemmas are expected to be available; check they are in the current codebase:

| Existing Lemma | File | What it provides |
|---------------|------|-----------------|
| `isExposedFace_isCompact` | `ExposedFaceLemmas` | Compactness of exposed face |
| `isExposedFace_convex` | `ExposedFaceLemmas` | Convexity of exposed face |
| `mem_P_sr_of_isRoot` | `ExposedFaceLemmas` | `δ ∈ P_sr` from root condition |
| `mem_P_sc_of_isRoot` | `EdgeTheoremDefs` | `δ ∈ P_sc` from root condition |
| `P_sr_dimension` | `PreliminaryLemmas` | `finrank(P_sr n r) = n` |
| `P_sc_dimension` | `PreliminaryLemmas` | `finrank(P_sc n s) = n-1` (for non-real s) |
| `finrank_inf_ge_one` | `PreliminaryLemmas` | Dimension bound for intersection |
| `segment_boundary_intersection` | `PreliminaryLemmas` | Segment crosses polytope frontier (needs generalization to arbitrary compact convex) |

---

## 8. Verification Plan

Once `Lemma62.lean` is implemented, it should be verified that:

1. All lemmas typecheck and compile.
2. The `rootSpaceSet_isClosed_of_isCompact` lemma can be tested with a simple compact set (e.g., a single point) to ensure the argument works.
3. The `ray_escapes_compact_convex` and `segment_crosses_frontier` lemmas can be tested with simple convex sets in `ℝ²` (e.g., a triangle) to confirm the geometric reasoning.
4. The `metric_frontier_seq_tendsto` lemma can be tested in ℂ with e.g. `S = {z : |z| < 1}`.
5. The `evalAtComplex_restrict_bijective` lemma can be tested with `V = span{e₀, e₁}` (the subspace spanned by the first two basis vectors).

The formalization is now ready to be written in Lean.
