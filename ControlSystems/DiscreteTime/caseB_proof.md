# Case B Proof: g_Ω is constant on the exposed face F

## Setup
- F = ExposedFace hp where hp.f supports P.Ω at F
- g_Ω is constant on F: ∀ x ∈ F, g_Ω x = g_c = g_Ω δ_bound
- g_Ω strictly separates interior P.Ω from δ_bound: ∀ y ∈ int(P.Ω), g_Ω y < g_c
- δ_bound ∈ frontier F, δ_bound ∉ intrinsicInterior ℝ F
- dim(F) ≥ 2

## Goal
Find G ⊊ F, an exposed face of P.Ω, containing δ_bound, with dim(G) < dim(F).

## Proof Sketch

### Step 1: Translate into dir(F) and separate δ_bound from intF

Let V := (affSpan ℝ F).direction be the direction space of F.
Let T : V → affSpan ℝ F be translation by δ_bound: T(v) = δ_bound + v.
Let C := T⁻¹(intrinsicInterior ℝ F) = {v ∈ V | δ_bound + v ∈ intrinsicInterior ℝ F}.

Properties:
- C is open in V (intF is open in affSpan ℝ F, T is homeomorphism)
- C is convex (intF is convex, T is affine)
- 0 ∉ C (δ_bound ∉ intF)
- C ≠ ∅ (intF ≠ ∅ because dim(F) ≥ 1)

Apply `geometric_hahn_banach_open_point` in V:
  ∃ f : V →ₗ[ℝ] ℝ, ∀ v ∈ C, f(v) < f(0) = 0.

### Step 2: Extend f to the whole space

In finite dimension, any linear functional on a subspace extends.
Let π : CoeffVec n → V be a linear projection onto V (exists via
Submodule.exists_isCompl of V and a complement W).
Define w_ext : CoeffVec n →ₗ[ℝ] ℝ by w_ext(x) := f(π(x - δ_bound)).

Properties:
- w_ext is linear (composition of linear maps)
- For v ∈ V: w_ext(δ_bound + v) = f(v) (since π(v) = v)
- w_ext(δ_bound) = f(0) = 0
- For x ∈ intF: w_ext(x) < 0
- By continuity + density of intF in F: ∀ x ∈ F, w_ext(x) ≤ 0

### Step 3: Choose a small coefficient λ > 0

Define g_new := hp.f + λ · w_ext for some λ > 0 to be chosen.

For x ∈ P.Ω:
- g_new δ_bound = hp.f δ_bound + λ·w_ext(δ_bound) = hp.c + 0 = hp.c

We need g_new to support P.Ω (g_new x ≤ g_new δ_bound ∀ x ∈ P.Ω):

**Case x ∈ F:**
  hp.f x = hp.c, w_ext x ≤ 0 (from Step 2).
  g_new x = hp.c + λ·w_ext x ≤ hp.c = g_new δ_bound.

**Case x ∈ P.Ω \ F:**
  hp.f x < hp.c (since F = {y ∈ P.Ω | hp.f y = hp.c} and x ∉ F).
  Let ε := min_{x ∈ P.Ω} (hp.c - hp.f x) over the compact set P.Ω \ F.
  Since P.Ω\F is compact (P.Ω compact, F closed), and hp.c - hp.f x is continuous
  and positive on P.Ω\F, the minimum ε > 0 exists.

  Let M := max_{x ∈ P.Ω} |w_ext x| (exists by compactness + continuity).
  
  For x ∈ P.Ω \ F:
    g_new x = hp.f x + λ·w_ext x ≤ (hp.c - ε) + λ·M
  
  We need (hp.c - ε) + λ·M ≤ hp.c ⇔ λ·M ≤ ε ⇔ λ ≤ ε/M.
  
  Choose any 0 < λ ≤ ε/M (positive).

### Step 4: Construct G

G := {x ∈ P.Ω | g_new x = g_new δ_bound} = {x ∈ P.Ω | g_new x = hp.c}

G is an exposed face of P.Ω (exposed by g_new). δ_bound ∈ G.

By Step 3, for x ∈ P.Ω\F: g_new x < hp.c, so G ⊆ F.

For x ∈ F: g_new x = hp.c ⇔ λ·w_ext x = 0 ⇔ w_ext x = 0.
So G = {x ∈ F | w_ext x = 0}.

### Step 5: dim(G) < dim(F)

Since f ≠ 0 on V (f separates 0 from C ≠ ∅), w_ext is not constant zero on F.
Thus ker(w_ext) ∩ dir(F) is a proper subspace of dir(F).

By rank-nullity: dim(ker(w_ext) ∩ dir(F)) = dim(dir(F)) - dim(im(w_ext|dir(F))).
Since w_ext ≠ 0 on dir(F), im(w_ext|dir(F)) = ℝ (1-dim), so:
dim(ker(w_ext) ∩ dir(F)) = dim(dir(F)) - 1.

dir(G) = dir(F) ∩ ker(w_ext), so dim(dir(G)) = dim(dir(F)) - 1.
Therefore dim(G) = dim(F) - 1 < dim(F).

## Lemmas needed from mathlib

1. `intrinsicInterior_nonempty` (or similar) for nonempty convex finite-dim set
2. `geometric_hahn_banach_open_point` in a subspace (works for any TVS)
3. `Submodule.exists_isCompl` for extension of linear functional
4. `closure_intrinsicInterior` (or closure of relint = closure of set)
5. `Submodule.finrank_add_finrank_ker` (rank-nullity)
6. `IsCompact.exists_min` for continuous function on compact set
