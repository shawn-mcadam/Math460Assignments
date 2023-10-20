import GlimpseOfLean.Library.Basic


namespace Compute

/- MoP 1.3.11 question 1. You will likely use `rw` and `ring` -/
example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) :
  y = 9 := by {
  sorry
}

/- MoP 1.3.11 question 3. You will likely use `apply?`, `rw`, and `rfl`.
   Any time you are in doubt, use `apply?` -/
example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) :
  x = 14 := by {
  sorry
}


/- 1.4.11 question 6. Make liberal use of apply? for this question.
You will also need the fact that (a-b)^2 ≥ 0 -/
example (a b : ℝ)
    : a ^ 2 + b ^ 2 ≥ 2 * a * b := by {
  sorry
}

end Compute


/- TODO define namespace ACT here so our definitions of Preorder and PartialOrder don't conflict with Mathlib's!! -/


/- A preorder is a reflexive, transitive relation `≤` with `a < b` defined in the obvious way.
   Note that this is _not_ a partial order because it is not necessarily symmetric.
   Everything in a preorder need not be comparable either, because we don't have a property saying ∀ x y, 𝑥 ≤ 𝑦 ∨ 𝑦 ≤ 𝑥 -/
class Preorder (α : Type) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

/- Preorders need not be symmetric, but ACT defines notation for when a≤b and b≤a b/c this situation is still special -/
notation a "≅" b => a ≤ b ∧ b ≤ a

/- A partial order is a reflexive, transitive, antisymmetric relation `≤`. -/
class PartialOrder (α : Type) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

section Ch1

/- A set P is a discrete preorder if ∀ a,b ∈ P, a ≤ b ↔ a = b
 - A discrete preorder is a preorder: -/
def DiscretePreorder (α : Type) : Preorder α where
  le := fun a b => a = b
  le_refl := by sorry
  le_trans := by {
    sorry
  }

/- A set P is a codiscrete preorder if ∀ a,b ∈ A, a ≤ b
 - A codiscrete preorder is a preorder: -/
def CodiscretePreorder (α : Type) : Preorder α where
  le := fun a b => true
  le_refl := by intro a; rfl
  le_trans := by intro a b c hab hbc; rfl

/- Lean 4's Bool is a Preorder (and it comes packaged with a definition for ≤ already) -/
instance : Preorder (Bool) where
  le_refl := by intro a; rfl
  le_trans := by intro a b c hab hbc; apply ge_trans hbc hab


/- Until the end of this section, A,B,C are sets whose elements might be comparable with ≤ and < -/
variable [Preorder X]
variable {A B C : Set X}

/- TODO Fill out the definition of a monotone function -/
def monotone (f : A → B) := ∀ x, x

/- Prove the identity function is monotone -/
example (I : A → A) (hI : ∀ x, I x = x) : monotone I := by {
  sorry
}

/- Prove that a function composition of two monotone functions is a monotone function -/
theorem monotone_composition {g : A → B} {f : B → C} (hf : monotone f) (hg : monotone g) :
  monotone (f ∘ g) := by {
  sorry
}

/- We will continue to build up to meets, joins, and Galois connections -/
def lowerBounds (s : Set X) : Set X := { x | ∀ a, a ∈ s → x ≤ a }
def upperBounds (s : Set X) : Set X := { x | ∀ a, a ∈ s → a ≤ x }

-- a meet is a greatest lower bound is an infimum
def isMeet (s : Set X) (x₀ : X) := ∀ x, x ∈ lowerBounds s ↔ x ≤ x₀

-- a join is a least upper bound is a supremum
def isJoin (s : Set X) (x₀ : X) := ∀ x, x ∈ upperBounds s ↔ x₀ ≤ x

/- Any two meets are isomorphic -/
example {x y : X} (h1 : isMeet A x) (h2 : isMeet A y) : x ≅ y := by {
  constructor
  · apply (h2 x).1
    apply (h1 x).2
    apply Preorder.le_refl
  · apply (h1 y).1
    apply (h2 y).2
    apply Preorder.le_refl
}

end Ch1