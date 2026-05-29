# AGENTS.md — ControlSystems

## Project structure

- **Lean 4.27.0** (`lean-toolchain`), mathlib `v4.27.0` pinned via `lake-manifest.json`.
- `lakefile.toml` uses `globs = ["ControlSystems.+"]` — new `.lean` files under `ControlSystems/` are **auto-discovered**. No need to register them.
- `ControlSystems.lean` is library root; `Main.lean` is executable entrypoint (trivial).
- All library code lives under `ControlSystems/DiscreteTime/`.
- `ControlSystems/Init.lean` re-exports `Mathlib.Init` + `Mathlib.Tactic.Common`.

## Build & CI

```
lake build                    # builds everything (default target `ControlSystems`)
```

CI via `.github/workflows/lean_action_ci.yml` (`leanprover/lean-action@v1`) on push/PR.
No test framework. No explicit lint command (weak linters in `lakefile.toml`).

## Import conventions

- Use **specific mathlib imports** (never `import Mathlib`). If found, replace with explicit paths.
  - Current violation: `ControlSystems/DiscreteTime/zTransform.lean:10` has `import Mathlib`.
- Most files: `module` (no name) + `public import` for re-exports.
- Exception: `Controllability.lean` — no `module`, uses plain `import`.
- `ControlSystems.Init` should be imported by every non-trivial file.
- `@[expose] public section` blocks control visibility in several files.

## Gotchas

- `ControlSystems.lean:1` imports `ControlSystems.Basic` but **no `ControlSystems/Basic.lean` exists** — the core definitions are at `ControlSystems/DiscreteTime/Basic.lean`. Harmless: the glob picks up all `ControlSystems.+` files regardless.
- `ControlSystems/DiscreteTime/EdgeTheoremDefs.txt` is a stale artifact with blanket `import Mathlib`. Edit only `EdgeTheoremDefs.lean`.
- `ControlSystems/DiscreteTime/EdgeTheorem.lean` has incomplete proofs (`sorry`) at several points — expect to fill them in.
  - Two axioms introduced to bypass polytope face-lattice theory: `frontier_point_in_proper_face` and `vertex_lies_on_exposed_edge`.
  - Three more axioms added to finish the real branch of `lemma61`: `polytope_Omega_is_exposed_face`, `polytope_direction_dim_pos`, `polytope_dim1_is_exposed_edge`.
  - The only remaining `sorry` in `lemma61` is the complex case (`s.im ≠ 0`).
- `tree/` directory contains auxiliary proof-rendering HTML, not library code.
- `set_option linter.style.emptyLine false` and similar are set locally in several files (`Basic.lean`, `Cayley.lean`, `zTransform.lean`). Avoid adding redundant options in new files.

## Code style notes

- `open scoped ComplexOrder` in `Basic.lean`, `Cayley.lean`, `zTransform.lean`.
- `CoeffBox` namespace in EdgeTheorem files; `Polynomial`, `Affine`, `FiniteDimensional`, `LinearMap` opened there.

## Mathlib v4.27.0 import paths

Mathlib `v4.27.0` uses directory-flat structure. Verify paths against `.lake/packages/mathlib/Mathlib/`:
- Polynomials: `Algebra/Polynomial/` (not `Data/Polynomial/`)
- `ContinuousLinearMap`: `Analysis/Normed/Operator/ContinuousLinearMap`
- `LinearMap`/`Submodule`: `Algebra/Module/` (not `LinearAlgebra/`)
- HahnBanach separation: `Analysis/LocallyConvex/Separation`
- Affine subspace: `LinearAlgebra/AffineSpace/AffineSubspace/`
- Norm lemmas (`norm_smul` etc.): `Analysis/Normed/Group/Basic`
- `finrank`: `LinearAlgebra/Dimension/` and `LinearAlgebra/FiniteDimensional/`
