# ControlSystems

A **Lean 4** formalization of control theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Project Structure

```
ControlSystems/
├── ControlSystems.lean              # Library root
├── lakefile.toml                    # Lake build configuration
├── lean-toolchain                   # Lean version pinning
├── ControlSystems/
│   ├── DiscreteTime/
│   │   ├── Basic.lean               # Discrete-time linear system state-space representation
│   │   ├── zTransform.lean          # Z-transform: definitions, linearity, delay, final value theorem
│   │   ├── AsymptoticStability.lean # Gelfand spectral radius & asymptotic stability
│   │   ├── Reachability.lean        # Reachable sets and reachability criteria
│   │   ├── Controllability.lean     # Controllability matrix & Kalman rank condition
│   │   ├── Cayley.lean              # Cayley–Hamilton theorem for controllability
│   │   └── EdgeTheorem/             # Formalization of the Edge Theorem (Lemma 6.1)
│   │       ├── EdgeTheoremDefs.lean     # Core definitions
│   │       ├── BasicLemmas.lean         # General-purpose helper lemmas
│   │       ├── PreliminaryLemmas.lean   # Dimension & boundary point lemmas
│   │       ├── ExposedFaceLemmas.lean   # Exposed face construction (Hahn–Banach)
│   │       ├── SubfaceConstruction.lean # Proper subface construction
│   │       ├── EdgeDescent.lean         # Recursive dimension descent
│   │       └── Lemma61.lean             # Lemma 6.1 (real case complete)
└── Main.lean                       # Executable entry point
```

## Discrete-Time Linear Systems

The `DiscreteTime/` directory formalizes the standard state-space model

```
x(k+1) = A·x(k) + B·u(k),    x(0) = x₀
```

| Module | Content |
|--------|---------|
| `Basic.lean` | `DiscreteLinearSystemState` structure, system evolution, state equation |
| `zTransform.lean` | Z-transform of discrete signals, linearity, time delay, final value theorem |
| `AsymptoticStability.lean` | Spectral radius < 1 ⇒ asymptotic stability (Gelfand formula) |
| `Reachability.lean` | Reachable sets in k steps, total reachable set |
| `Controllability.lean` | Controllability matrix, Kalman rank condition |
| `Cayley.lean` | Cayley–Hamilton theorem applied to controllability |

## Edge Theorem (`EdgeTheorem/`)

The **Edge Theorem** (from *"Robust Control: The Parametric Approach"* by Bhattacharyya, Chapellat, Keel) characterizes the root locations of a family of polynomials whose coefficients vary within a box.

The main result formalized so far is **Lemma 6.1**:

> **Real case** (complete): If a real `s` belongs to the root space `R(Ω)` of a polytope `Ω`, then there exists an **exposed edge** `E` of `Ω` such that `s ∈ R(E)`.
>
> **Complex case** (deferred): If a complex `s` belongs to `R(Ω)`, then there exists an **exposed face** `F` such that `s ∈ R(F)`.

### Files

| File | Purpose |
|------|---------|
| `EdgeTheoremDefs.lean` | Core definitions: `CoeffBox`, `Polytope`, `RootSpace`, `RootSpaceSet`, `SupportingHyperplane`, `ExposedFace`, `IsExposedEdge`, `evalLinear`, `P_sr` |
| `BasicLemmas.lean` | Simp lemmas, frontier/segment helpers, separating functional via Hahn–Banach |
| `PreliminaryLemmas.lean` | `P_sr_dimension`, `intersection_affine_dim_ge_one`, boundary point existence via connectedness |
| `ExposedFaceLemmas.lean` | Exposed face properties: compactness, convexity, construction from boundary point (`geometric_hahn_banach_open_point`) |
| `SubfaceConstruction.lean` | Construction of a proper exposed subface `G ⊂ F` with strictly smaller affine dimension |
| `EdgeDescent.lean` | Recursive descent to an exposed edge (`descend_to_exposed_edge`) with termination by dimension measure |
| `Lemma61.lean` | `lemma61_real` (the full real case) and `lemma61` (bundling both cases) |

The proof proceeds by **dimension descent**: starting from a root vector `δ ∈ Ω`, it finds a boundary point on the frontier, constructs an exposed face containing it, and iteratively finds a strictly smaller subface until reaching dimension 1 (an exposed edge) or 0 (a vertex, handled via an axiom).

## Build

Requires Lean 4.27.0 and Mathlib v4.27.0.

```bash
lake build
```

## Dependencies

- [Mathlib](https://github.com/leanprover-community/mathlib4) (v4.27.0)
