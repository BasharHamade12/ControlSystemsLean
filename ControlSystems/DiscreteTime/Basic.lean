/-
Copyright (c) 2026 Bashar Hamade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bashar Hamade
-/
module


public import ControlSystems.Init
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Order.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

@[expose] public section

open scoped ComplexOrder


set_option linter.style.emptyLine false
set_option linter.deprecated.module false

universe u v

section DiscreteLinearSystem

/-!
# Basic definitions for Discrete Linear Time Systems

This module defines the state space representation of a discrete-time linear dynamical system.
It includes the definition of the system state, the evolution function,
and the property of satisfying the state equation.

## Main Definitions
* `DiscreteLinearSystemState`: Structure representing the system matrices (A and B),
the current state, input, and initial state.
* `DiscreteLinearSystemState.system_evolution`: Function computing the state at time `k`
given an input sequence.
* `DiscreteLinearSystemState.satisfies_state_equation`: Proposition stating that
the sequence `x` satisfies the linear difference equation `x(k+1) = A x(k) + B u(k)`.
-/

variable {σ : Type u} {ι : Type v}
variable [TopologicalSpace σ] [NormedAddCommGroup σ] [NormedSpace ℂ σ]
variable [TopologicalSpace ι] [NormedAddCommGroup ι] [NormedSpace ℂ ι]
variable [Inhabited ι]

/-- Discrete-time linear dynamical system with state equation x(k+1) = A·x(k) + B·u(k). -/
structure DiscreteLinearSystemState (σ : Type u) (ι : Type v)
    [TopologicalSpace σ] [NormedAddCommGroup σ] [NormedSpace ℂ σ]
    [TopologicalSpace ι] [NormedAddCommGroup ι] [NormedSpace ℂ ι] where
  /-- State transition matrix (A), mapping the current state to the next state component (n×n). -/
  a : σ →L[ℂ] σ
  /-- Input matrix (B), mapping the current input to the next state component (n×p). -/
  B : ι →L[ℂ] σ
  /-- Initial state -/
  x₀ : σ
  /-- State sequence -/
  x : ℕ → σ
  /-- Input sequence -/
  u : ℕ → ι

variable {sys : DiscreteLinearSystemState σ ι}

/-- System evolution function from initial state -/
noncomputable def DiscreteLinearSystemState.system_evolution (u : ℕ → ι) : ℕ → σ
  | 0 => sys.x₀
  | k + 1 => sys.a (system_evolution u k) + sys.B (u k)

/-- Discrete state space representation property -/
def DiscreteLinearSystemState.satisfies_state_equation : Prop :=
  ∀ k : ℕ, sys.x (k + 1) = sys.a (sys.x k) + sys.B (sys.u k)


/-- Evolution from zero initial state with given input -/
noncomputable def DiscreteLinearSystemState.evolve_from_zero
   (u : ℕ → ι) (sys : DiscreteLinearSystemState σ ι) : ℕ → σ
  | 0 => 0
  | k + 1 => sys.a (evolve_from_zero u sys k) + sys.B (u k)




/-- Zero input sequence -/
def zero_input : ℕ → ι := fun _ => 0

end DiscreteLinearSystem

section TransferFunction

/-!
# Transfer functions

A transfer function is a rational function of the complex variable `z` with complex
coefficients, that is, a quotient

    H(z) = num(z) / denom(z)

of two complex polynomials, as it arises for instance as the `z`-transform of a
discrete-time system, e.g. `G(z) = (δ₁z + δ₀) / (z²(z + δ₂))`.

Mathlib already supplies the appropriate type: `RatFunc ℂ` is the field of fractions
`ℂ(X)` of the polynomial ring `ℂ[X]`, so a transfer function is a genuine rational
function rather than a pair of polynomials: two presentations of the same function
(for example `(z + 1) / (2z + 2)` and `1 / 2`) are *equal*, and the field operations,
composition and evaluation are available. We use it directly and expose the
numerator/denominator presentation.

## Main definitions
* `TransferFunction`: a rational function over `ℂ`.
* `TransferFunction.ofPolys`: the transfer function `num z / denom z` of two complex
  polynomials.
* `TransferFunction.num`, `TransferFunction.denom`: numerator and denominator, the
  latter normalized to be monic; `TransferFunction.num_denom` shows that this
  presentation loses no information.
* `TransferFunction.X`: the transfer function of the identity map `z ↦ z`.
* `TransferFunction.eval`: evaluation of a transfer function at a point `z : ℂ`.
-/

/-- A transfer function: a rational function of `z` with complex coefficients, i.e. an
element of the field of fractions `ℂ(X)` of `ℂ[X]`. -/
abbrev TransferFunction := RatFunc ℂ

namespace TransferFunction

/-- The transfer function with numerator `num` and denominator `denom`, that is
`z ↦ num(z) / denom(z)`. It is `0` when `denom = 0`, matching `RatFunc.mk`. -/
noncomputable def ofPolys (num denom : Polynomial ℂ) : TransferFunction :=
  RatFunc.mk num denom

/-- The numerator of a transfer function, normalized so that the denominator is monic. -/
noncomputable def num (H : TransferFunction) : Polynomial ℂ :=
  RatFunc.num H

/-- The denominator of a transfer function; it is monic, and in particular nonzero. -/
noncomputable def denom (H : TransferFunction) : Polynomial ℂ :=
  RatFunc.denom H



/-- The denominator of a transfer function is nonzero. -/
theorem denom_ne_zero (H : TransferFunction) : H.denom ≠ 0 :=
  RatFunc.denom_ne_zero H

/-- Every transfer function is the quotient of its numerator by its denominator: the
`num`/`denom` presentation loses no information. -/
theorem num_denom (H : TransferFunction) : ofPolys H.num H.denom = H := by
  rw [ofPolys, RatFunc.mk_eq_div]
  exact RatFunc.num_div_denom H

/-- A zero denominator gives the zero transfer function. -/
@[simp] theorem ofPolys_zero_denom (num : Polynomial ℂ) : ofPolys num 0 = 0 := by
  rw [ofPolys, RatFunc.mk_zero, RatFunc.ofFractionRing_zero]

/-- The identity transfer function, `z ↦ z`. -/
noncomputable def X : TransferFunction :=
  RatFunc.X

/-- Evaluation of a transfer function at a point `z : ℂ`, returning `num(z) / denom(z)`.
Common factors are cancelled before evaluating, so `eval z ((X ^ 2 - 1) / (X - 1))` is
`eval z (X + 1)`; at a pole of `H`, where the denominator evaluates to `0`, the value is
`0` (see `RatFunc.eval_eq_zero_of_eval₂_denom_eq_zero`). -/
noncomputable def eval (z : ℂ) (H : TransferFunction) : ℂ :=
  RatFunc.eval (RingHom.id ℂ) z H

/-- **Schur stability** of a transfer function: every root of the denominator `H.denom` —
every pole — lies strictly inside the unit circle, i.e. in the open unit disc
`{z : ℂ | ‖z‖ < 1}`. Equivalently, the root space of `H.denom` is contained in the unit
disc. (The strict inequality is the discrete-time condition; roots on the circle
`‖z‖ = 1` are not allowed.) -/
def IsSchurStable (H : TransferFunction) : Prop :=
  ∀ z : ℂ, H.denom.IsRoot z → ‖z‖ < 1

end TransferFunction

end TransferFunction
