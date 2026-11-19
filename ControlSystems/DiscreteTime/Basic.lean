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

/-- The **closed-loop characteristic polynomial** of the negative-feedback loop with
forward gain `K` around `H`: `H.denom + C K * H.num`.

Clearing denominators, `1 + K·H = (denom + K·num) / denom`, so the poles of the closed
loop are the roots of this polynomial.  It is *not* the open-loop denominator `H.denom`,
and it is in general not monic: for the plant of Example 6.1,
`G = (δ₂s² + δ₀)/(s³ + δ₁s)`, unit gain gives `s³ + δ₂s² + δ₁s + δ₀`, monic with leading
coefficient `1`, which is the polynomial the Edge Theorem is applied to. -/
noncomputable def charPoly (K : ℂ) (H : TransferFunction) : Polynomial ℂ :=
  H.denom + Polynomial.C K * H.num

/-- Unit-gain characteristic polynomial: `H.denom + H.num`. -/
theorem charPoly_one (H : TransferFunction) : charPoly 1 H = H.denom + H.num := by
  simp [charPoly]

/-- The characteristic polynomial of the loop `1 + K·(p/q)` written **before** the
rational function normalizes `p/q`: `q + C K * p`.  For a coprime pair `p, q` with `q`
monic this agrees exactly with `(ofPolys p q).charPoly K` (see `charPoly_ofPolys`), and
in general it agrees up to the nonzero constant that cancelling `gcd p q` introduces. -/
noncomputable def charPolyOfPolys (K : ℂ) (num den : Polynomial ℂ) : Polynomial ℂ :=
  den + Polynomial.C K * num


theorem charPoly_ofPolys {p q : Polynomial ℂ} (hq : q.Monic)
    (hgcd : gcd p q = 1) (K : ℂ) :
    (ofPolys p q).charPoly K = q + Polynomial.C K * p := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hqg : q / gcd p q = q := by rw [hgcd, EuclideanDomain.div_one]
  have hpg : p / gcd p q = p := by rw [hgcd, EuclideanDomain.div_one]
  simp only [charPoly, num, denom, ofPolys, RatFunc.mk_eq_div]
  rw [RatFunc.num_div, RatFunc.denom_div p hq0, hqg, hpg, hq.leadingCoeff, inv_one]
  simp

/-- **Schur stability** of a transfer function: every root of the denominator `H.denom` —
every pole — lies strictly inside the unit circle, i.e. in the open unit disc
`{z : ℂ | ‖z‖ < 1}`. Equivalently, the root space of `H.denom` is contained in the unit
disc. (The strict inequality is the discrete-time condition; roots on the circle
`‖z‖ = 1` are not allowed.) -/
def IsSchurStable (H : TransferFunction) : Prop :=
  ∀ z : ℂ, H.denom.IsRoot z → ‖z‖ < 1

/-! ### String rendering

Mathlib's `Polynomial` and `RatFunc` are declared inside `noncomputable` sections: their
API (`coeff`, `natDegree`, the ring operations) is never compiled, so *no* function that
inspects a `TransferFunction = RatFunc ℂ` can be executed by `#eval`.  Two complementary
tools are therefore provided here:

* `display` / `displayWith` / `toString`: a **noncomputable symbolic** rendering of a
  genuine `TransferFunction`, with coefficients printed by name (`c_0, c_1, …` or
  parameter names chosen by the caller).  Suitable for statements and documentation but
  not executable.
* `renderTransfer` (with the helpers `ratAbsStr`, `monoTerm`, `polyTerms`,
  `joinSignedTerms`, `renderPoly`): a **computable** rendering for a transfer function
  supplied by explicit rational coefficient lists (ascending degree order).  This one is
  executed by `#eval`; `ofCoeffLists` bridges such a list pair to a real
  `TransferFunction`.
-/

/-- Absolute value of a rational coefficient as a string: `n` when the denominator
is `1`, otherwise `n/d`.  Only integer operations on `Rat.num`/`Rat.den` are used,
so this is computable. -/
def ratAbsStr (q : ℚ) : String :=
  let n := q.num.natAbs
  if q.den = 1 then toString n else toString n ++ "/" ++ toString q.den

/-- One monomial with its sign factored out: `.1` records whether the term is
negative, `.2` is the unsigned rendering (e.g. `3·X^2`, `X`, `1/2`). -/
def monoTerm (var : String) (n : ℕ) (c : ℚ) : Bool × String :=
  let body : String :=
    match n with
    | 0 => ""
    | 1 => var
    | k => var ++ "^" ++ toString k
  let magn : String :=
    if body = "" then ratAbsStr c
    else if c.num.natAbs = 1 then body
    else ratAbsStr c ++ "·" ++ body
  (c.num < 0, magn)

/-- The sign-tagged monomials of the polynomial with coefficients `cs`
(ascending degree order), zero coefficients dropped. -/
def polyTerms (var : String) : ℕ → List ℚ → List (Bool × String)
  | _, [] => []
  | n, c :: cs =>
      let rest := polyTerms var (n + 1) cs
      if c.num = 0 then rest else monoTerm var n c :: rest

/-- Join sign-tagged terms as `t₁ + t₂ - t₃`; the empty sum is `0`. -/
def joinSignedTerms : List (Bool × String) → String
  | [] => "0"
  | (b, t) :: ts =>
      (if b then "-" else "") ++ t ++
        ts.foldl (fun acc p => acc ++ (if p.1 then " - " else " + ") ++ p.2) ""

/-- Computable rendering of a polynomial from its coefficients in ascending
degree order, highest degree first, zero terms dropped:
`renderPoly "X" [10, 0, 7]` is `"7·X^2 + 10"`. -/
def renderPoly (var : String) (cs : List ℚ) : String :=
  joinSignedTerms (polyTerms var 0 cs).reverse

/-- Computable rendering of a transfer function from numerator and denominator
coefficients (both ascending degree order, i.e. `[c₀, c₁, c₂, …]`):
`renderTransfer "s" [10, 0, 7] [0, 15, 0, 1]` is `"(7·s^2 + 10) / (s^3 + 15·s)"`. -/
def renderTransfer (var : String) (num den : List ℚ) : String :=
  "(" ++ renderPoly var num ++ ") / (" ++ renderPoly var den ++ ")"

/-- One monomial whose coefficient is given *by name* rather than numerically.
`.1` records whether the name is negative (a leading `-`, stripped from `.2`); a
coefficient name `"1"` is omitted entirely, so `("1", 3)` renders `var^3`. -/
def namedTerm (var : String) (n : ℕ) (c : String) : Bool × String :=
  let body : String :=
    match n with
    | 0 => ""
    | 1 => var
    | k => var ++ "^" ++ toString k
  let neg : Bool := c.startsWith "-"
  let c' : String := if neg then (c.drop 1).toString else c
  let magn : String :=
    if body = "" then c'
    else if c' = "1" then body
    else c' ++ "·" ++ body
  (neg, magn)

/-- Computable rendering of a polynomial whose coefficients are *symbolic* — given by
name — with the terms listed in **descending** degree order, zero coefficients written
`""` and dropped:

`symbolicPoly "s" [(2, "δ₂"), (0, "δ₀")]` is `"δ₂·s^2 + δ₀"`.

This is the form the book uses for a family of systems, where the coefficients are
parameters with known ranges rather than numbers. -/
def symbolicPoly (var : String) (cs : List (ℕ × String)) : String :=
  joinSignedTerms ((cs.filter fun p => p.2 ≠ "").map fun p => namedTerm var p.1 p.2)


def symbolicTransfer (var : String) (num den : List (ℕ × String)) : String :=
  "(" ++ symbolicPoly var num ++ ") / (" ++ symbolicPoly var den ++ ")"

/-- Bridge from executable coefficient lists to a genuine `TransferFunction`: the
polynomial `∑ cᵢ·Xⁱ` is built by Horner's rule and read into `ℂ`. -/
noncomputable def coeffListToPoly (cs : List ℚ) : Polynomial ℂ :=
  cs.reverse.foldl (fun p c => p * Polynomial.X + Polynomial.C (((c : ℝ) : ℂ))) 0

/-- The `TransferFunction` with the given rational numerator and denominator
coefficient lists (ascending degree order). -/
noncomputable def ofCoeffLists (num den : List ℚ) : TransferFunction :=
  ofPolys (coeffListToPoly num) (coeffListToPoly den)

-- `#eval` demos: these really print at build time, unlike anything that inspects a
-- `TransferFunction`.
#eval renderTransfer "X" [1, 0, 2] [0, 3]
#eval renderTransfer "s" [10, 0, 7] [0, 15, 0, 1]
#eval renderTransfer "s" [-3, 1] [1, -2]

-- Symbolic (parameter-name) rendering: the book's notation for a family of systems.
#eval symbolicTransfer "s" [(2, "δ₂"), (0, "δ₀")] [(3, "1"), (1, "δ₁")]
#eval symbolicTransfer "z" [(1, "a"), (0, "b")] [(2, "1"), (0, "-1")]


noncomputable def polyDisplay (name : ℕ → String) (var : String)
    (p : Polynomial ℂ) : String := by
  classical
  exact
    if p = 0 then "0"
    else
      let term : ℕ → String := fun n =>
        match n with
        | 0 => name 0
        | 1 => name 1 ++ "·" ++ var
        | k => name k ++ "·" ++ var ++ "^" ++ ToString.toString k
      let ns : List ℕ :=
        ((List.range (p.natDegree + 1)).filter fun n => !decide (p.coeff n = 0)).reverse
      String.intercalate " + " (ns.map term)


noncomputable def displayWith (name : ℕ → String) (var : String)
    (H : TransferFunction) : String :=
  "(" ++ polyDisplay name var H.num ++ ") / (" ++ polyDisplay name var H.denom ++ ")"


noncomputable def display (H : TransferFunction) : String :=
  displayWith (fun n => "c_" ++ ToString.toString n) "X" H


noncomputable def toString (H : TransferFunction) : String :=
  display H


noncomputable instance : ToString TransferFunction :=
  ⟨fun H => toString H⟩


end TransferFunction

end TransferFunction
