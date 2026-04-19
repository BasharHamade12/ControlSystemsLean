module


public import ControlSystems.Init
public import Mathlib

@[expose] public section


-- public import Mathlib.Algebra.Polynomial.Degree.Defs

open Polynomial
/--
A box `B_n` in the space of coefficients for polynomials of degree `n`.
It is defined by lower bounds `l` and upper bounds `u` for each coefficient index `j ∈ {0, ..., n}`.
-/
structure CoeffBox (n : ℕ) where
  l : Fin (n + 1) → ℝ  -- Lower bounds l_j
  u : Fin (n + 1) → ℝ  -- Upper bounds u_j
  interval : ∀ j : Fin (n + 1), l j ≤ u j





namespace CoeffBox

/--
Predicate stating that the polynomial `f` has natural degree `n`
and its coefficients lie within the box `B`.
Note: We explicitly require `f.natDegree = n` to ensure the leading coefficient
is non-zero and corresponds to index `n`.
-/
def InBox (B : CoeffBox n) (f : Polynomial ℝ) : Prop :=
  f.natDegree = n ∧  ∀ j : Fin (n + 1), B.l j ≤ coeff f j.val ∧ coeff f j.val ≤ B.u j

def FOIP (B : CoeffBox n) : Set (Polynomial ℝ) :=
  { f | InBox B f }
/--
The set of extreme coefficient vectors `E_k` for a fixed index `k`.
A coefficient vector `α` (represented here as a function `Fin (n+1) → ℝ`)
is in `E_k B` if:
1. The k-th coefficient `α k` is within its interval `[l k, u k]`.
2. For all other indices `j ≠ k`, the coefficient `α j` is exactly either `l j` or `u j`.
-/
def ExtremeCoeffs (B : CoeffBox n) (k : Fin (n + 1)) : Set (Fin (n + 1) → ℝ) :=
  { α |
    (B.l k ≤ α k ∧ α k ≤ B.u k) ∧
    ∀ j : Fin (n + 1), j ≠ k → (α j = B.l j ∨ α j = B.u j)
  }

/--
The collection of all extreme coefficient vectors `E`.
This is the union of `ExtremeCoeffs B k` for all `k` from `0` to `n`.
Geometrically, this represents the "edges" of the hyperrectangle `B_n`
parallel to the axes.
-/
def ExtremeSet (B : CoeffBox n) : Set (Fin (n + 1) → ℝ) :=
  ⋃ k : Fin (n + 1), ExtremeCoeffs B k

/--
The Family of Extreme Polynomials.
This maps the extreme coefficient vectors back to polynomials.
Note: Not every vector in `ExtremeSet` necessarily forms a polynomial of degree `n`
(i.e., the leading coefficient might be 0 if `l n = 0` and `α n` is chosen as `l n`).
We filter for `natDegree = n` to match the definition of `FOIP`.
-/
def ExtremePolys (B : CoeffBox n) : Set (Polynomial ℝ) :=
  { f | ∃ α ∈ ExtremeSet B,
      (∀ j : Fin (n + 1), coeff f j.val = α j) ∧
      f.natDegree = n
  }

def Schur_Stable (f : Polynomial ℝ) : Prop :=
  ∀ a : ℝ , f.IsRoot a → abs a < 1

theorem Product_of_Schur_Stable (f : Polynomial ℝ) (g : Polynomial ℝ) :
  (Schur_Stable f) → (Schur_Stable g) → (Schur_Stable (f * g)) := by
  intros hf hg
  unfold Schur_Stable
  intro a hfg
  have heval : f.eval a * g.eval a = 0 := by
    rw [← eval_mul]
    exact hfg
  rcases mul_eq_zero.mp heval with hfa | hga
  -- Case 1: a is a root of f → apply Schur stability of f
  · exact hf a hfa
  -- Case 2: a is a root of g → apply Schur stability of g
  · exact hg a hga


abbrev CoeffVec (n : ℕ) := Fin (n + 1) → ℝ

/--
A polytope Ω in coefficient space ℝ^{n+1}.
It is defined as the convex hull of a finite set of vertices V.
This matches the PDF: "the convex hull of a finite number of points".
-/
structure Polytope (n : ℕ) where
  vertices : Finset (CoeffVec n)     -- finite set of vertex polynomials
  nonempty  : vertices.Nonempty       -- at least one vertex

/-- The actual set Ω ⊆ ℝ^{n+1} as a convex hull -/
def Polytope.Ω (P : Polytope n) : Set (CoeffVec n) :=
  convexHull ℝ (P.vertices : Set (CoeffVec n))

open Polynomial

/-- Convert a coefficient vector α : Fin(n+1) → ℝ to a polynomial
    δ(s) = α(0) + α(1)·s + ... + α(n)·sⁿ
-/
noncomputable def polyOfVec {n : ℕ} (α : CoeffVec n) : Polynomial ℝ :=
  ∑ j : Fin (n + 1), Polynomial.monomial j.val (α j)


def RootSpaceSet {n : ℕ}
  (W : Set (CoeffVec n)) : Set ℂ :=
  { s | ∃ δ ∈ W,
      ((polyOfVec δ).map (algebraMap ℝ ℂ)).IsRoot s }

def RootSpace (P : Polytope n) : Set ℂ :=
  RootSpaceSet P.Ω

/--
def HyperPlaneAffineSet (f : Polynomial ℝ) (c : ℝ) : Set ℝ :=
  { x | f.eval x = c }


structure SupportingHyperplane (f : Polynomial ℝ) (c : ℕ ) (P : Polytope n) where
   H : HyperPlaneAffineSet f c
   inclusion : ∀ x ∈ P.Ω , f.eval x ≤ c
   intersection : Ω_1 ∩ H ≠ ∅
-/
def Hyperplane {n : ℕ}
    (f : CoeffVec n →ₗ[ℝ] ℝ)
    (c : ℝ) : Set (CoeffVec n) :=
  { x | f x = c }

structure SupportingHyperplane (P : Polytope n) where
  f : CoeffVec n →ₗ[ℝ] ℝ
  c : ℝ
  nonzero : f ≠ 0
  upper_bound : ∀ x ∈ P.Ω, f x ≤ c
  touches : ∃ x ∈ P.Ω, f x = c
  H : Set (CoeffVec n) := Hyperplane f c

def ExposedFace_ (P : Polytope n) (hp : SupportingHyperplane P) :=
  P.Ω ∩ hp.H

def ExposedFace {n : ℕ} {P : Polytope n} (hp : SupportingHyperplane P) :
    Set (CoeffVec n) :=
  { x | x ∈ P.Ω ∧ hp.f x = hp.c }
  -- equivalently: P.Ω ∩ hp.H

open Affine

/-- `E` is an exposed edge of `P` if it is an exposed face of affine dimension 1. -/
def IsExposedEdge {n : ℕ} (P : Polytope n) (E : Set (CoeffVec n)) : Prop :=
  ∃ hp : SupportingHyperplane P,
    E = ExposedFace hp ∧
    ∃ p q : CoeffVec n, p ≠ q ∧ E = segment ℝ p q
open FiniteDimensional

def ExposedEdge {n : ℕ} {P : Polytope n} (hp : SupportingHyperplane P) : Prop :=
  Module.finrank ℝ (affineSpan ℝ (ExposedFace hp)).direction = 1

lemma lemma61a
  (P : Polytope n)
  {s : ℂ}
  (hs : s ∈ RootSpace P) :
  ∃ hp : SupportingHyperplane P,
    s ∈ RootSpaceSet (ExposedFace hp) := by
  sorry

end CoeffBox
