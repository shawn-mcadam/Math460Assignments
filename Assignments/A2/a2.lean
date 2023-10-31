import GlimpseOfLean.Library.Basic
open Set Function


/- Getting some extra practice with the \forall quantifier -/
def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

/- The sum of two even functions is even -/
example (f g : ℝ → ℝ) : even_fun f → even_fun g → even_fun (f + g) := by {
  intro hf hg x
  unfold even_fun at *
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g x        := by rw [hf, hg]
}

/- The composition of two even functions is even -/
example (f g : ℝ → ℝ) : even_fun f → even_fun (g ∘ f) := by {
  /- sorry -/
  intro hf x
  calc
    (g ∘ f) (-x) = g (f (-x)) := by rfl
               _ = g (f (x))  := by rw [hf]
               _ = (g ∘ f) x  := by rfl
}


section conjunctions

/-
The conjunction of two statements `P` and `Q` is denoted by `P ∧ Q`, read as "P and Q".

We can use a conjunction similarly to the `↔`:
* If `h : P ∧ Q` then `h.1 : P` and `h.2 : Q`.
* To prove `P ∧ Q` use the `constructor` tactic.

Furthermore, we can decompose conjunction and equivalences.
* If `h : P ∧ Q`, the tactic `rcases h with ⟨hP, hQ⟩`
  gives two new assumptions `hP : P` and `hQ : Q`.
* If `h : P ↔ Q`, the tactic `rcases h with ⟨hPQ, hQP⟩`
  gives two new assumptions `hPQ : P → Q` and `hQP : Q → P`.
-/
example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by {
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  constructor
  · exact h hp
  · exact h' hq
}

/- One can also prove a conjunction without the constructor tactic by gathering both sides
using the `⟨`/`⟩` brackets. The above proof can be rewritten as follows. -/
example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by {
  intro hpq
  exact ⟨h hpq.1, h' hpq.2⟩
}

/- The angle brackets are especially useful for doing formal logic. You probably have to
write ⟨h1, h2⟩ somewhere in this proof -/
example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by {
  sorry
}

/- Lean has the tactic `tauto` which is especially useful for proving logical tautologies.
Prove the result above again using `tauto`. If you used `tauto` above, then redo the proof without
using `tauto`. -/
example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by {
  sorry
}


section qualifiers

/- To prove `∃ x, P x`, we must provide some `x₀` with the tactic
`use x₀` and then prove `P x₀`. In the example below, the property
to check after `use` is true by definition so the proof is over. -/
example : ∃ n : ℕ, 8 = 2*n := by {
  use 4
}

/-
To use a hypothesis of the form `h : ∃ x, P x`, we use the `rcases`
tactic to materialize some `x₀` such that `P x₀`. We'll see many
other uses for `rcases` throughout this file.
-/
example (n : ℕ) (h : ∃ k : ℕ, n = k + 1) : n > 0 := by {
  -- Let's fix k₀ such that n = k₀ + 1.
  rcases h with ⟨k₀, hk₀⟩
  -- It now suffices to prove k₀ + 1 > 0.
  rw [hk₀]
  -- and we have a lemma about this
  exact Nat.succ_pos k₀
}

/-
The next exercises use divisibility in ℤ (beware the ∣ symbol which is not ASCII).
By definition, `a ∣ b ↔ ∃ k, b = a*k`, so you can prove `a ∣ b` using the
`use` tactic. You can mouse over ∣ to see how to type is and what it means.
-/
example (a b c : ℤ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by {
  sorry
}

/-
We can now start combining quantifiers, using the definition
  `Surjective (f : X → Y) := ∀ y, ∃ x, f x = y`

  fun x ↦ x + c is lean's way of defining a function inline.
  The tactic `simp` will expand function applications, and
  automatically perform many other simplifications
-/
example {c : ℝ} : Surjective fun x ↦ x + c := by {
  intro x
  use x - c
  simp
}

/- You must specialize the proposition h for this next proof. Any proposition with
∀ can be specialized by giving it an argument. So, to specialize `h` in the example
below, provide some real number -/
example (f g : ℝ → ℝ) (h : Surjective (g ∘ f)) : Surjective g := by {
  /- Use `unfold` to plug in the definitions of a term in the goal. This is helpful for showing quantifiers
  `unfold Surjective at *` will unfold every occurence of Surjective in the infoview.
  `unfold Surjective at h` will only unfold Surjective at `h`. -/
  unfold Surjective
  sorry
}


section disjunctions

/- The most straightforward way to prove a disjunction "A ∨ B" is to prove A or to prove B.
The `left` tactic says "I will prove A" and the `right` tactic says "I will prove A" -/
example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by {
  left
  linarith [pow_two_nonneg x]
}

/- rcases lets us split and name each piece of a disjunction, separated by those vertical bars.
This syntax will come up frequently. -/
example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by {
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt
}

/- more advanced use of rcases involving divisibility -/
example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, ha⟩ | ⟨b, hb⟩
  · rw [ha]
    rw [mul_assoc]
    apply dvd_mul_right
  . rw [hb]
    rw [mul_comm, mul_assoc]
    apply dvd_mul_right

/- we can skip the `rw`s in the above proof by using `rfl` in `rcase`s angle brackets -/
example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]; apply dvd_mul_right
  . rw [mul_comm, mul_assoc]; apply dvd_mul_right


/- For this next proof, you must use add_nonneg, sq_nonneg, and linarith.
The trickiest part is the first line involving `rcases`. Try to use `rfl` in the
angle brackets of `rcases` to simplify the proof -/
example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by {
  sorry
}

section contradictions

/- Negations Lean are proven by contradiction. When we derive `False` then we
can close the proof with the tactic `contractiction`. We will also experiment with
the definition of a monotone function in this section. -/
example {f : ℝ → ℝ} {a b : ℝ} (h : Monotone f) (h' : f a < f b) : a < b := by {
  apply lt_of_not_ge
  intro h1
  /- to use the `contradiction` tactic, often we must spell out the negation of h1 this
     Remember that you can use `apply?` to search for tactics -/
  have : ¬(f a < f b)
  · apply sorry
  contradiction
}

/- When we try to prove p → q, it's often easier to show the contrapositive: ¬q → ¬p.
   In fact, the proof by contradiction above is equivalent to a proof by contrapositive.
   Derive a much simpler proof of the above example by using the tactic `contrapose!` -/
example {f : ℝ → ℝ} {a b : ℝ} (h : Monotone f) (h' : f a < f b) : a < b := by {
  contrapose! h'
  sorry
}

/- Here we show that the strict inequalities above cannot be weakened.
This requires the following
    1. showing that the zero function is monotone
    2. using h' to arrive upon the contradiction
    3. properly closing the proof with the contradiction tactic -/
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by {
  intro h
  let zerof := fun x : ℝ ↦ (0 : ℝ) /- adds a local definition to the context -/
  have monof : Monotone zerof := sorry
  have h' : zerof 1 ≤ zerof 0 := le_refl _ /- Lean automatically expands zerof 1 and zerof 0 to 0 -/

  /- This proof fails if we do not annotate the type of `1` and `0`. It's a little silly, but
  Lean's 0 or 1 could belong to several different sets -/
  have h1 : ¬((1 : ℝ) ≤ (0 : ℝ)) := by linarith
  have h2 : (1 : ℝ) ≤ (0 : ℝ) := sorry

  contradiction
}

/- The lean infoview was not helpful in the last example because the goal was `False` the whole time.
   That's why we had to use so many `have` statments. This alternate proof starts with `push_neg`
   which pushes the negation through an entire goal/hypothesis. This is helpful because now the
   goal can guide each of our steps -/
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by {
  push_neg
  let f := fun x : ℝ ↦ (0 : ℝ) /- adds a local definition to the context -/
  sorry
}


/- We will finish this part of the assignment with a smidgen of set theory,
   and we'll show some more uses of rcases -/
section SetTheory
variable {α : Type}
variable (s t u : Set α)

/- If α is any type, the type Set α consists of sets of elements of α (its type is the power set of α)
Set α has various operations defined on it such as ⊂, ∩, ∪, etc. The following are proofs of familiar
facts, but uses some new tools -/

/- use `simp` to prove the following -/
example (x : ℝ) (X Y : Set ℝ) (hx : x ∈ X) : x ∈ (X ∩ Y) ∪ (X \ Y) := by {
  sorry
}

/- Here we use rcases to work with set union and intersection -/
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    exact ⟨xs, xt⟩
  . right
    exact ⟨xs, xu⟩

/- here's a shorter proof -/
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  . right; exact ⟨xs, xu⟩

/- one way to prove two sets A,B are equal is by showing A ⊆ B ∧ B ⊆ A. To do this
in Lean we can use the theorem `Subset.antisymm := A ⊆ B ∧ B ⊆ A ↔ A = B` -/
example : s ∩ t = t ∩ s := by {
  apply Subset.antisymm
  sorry
  sorry
}


/- A more direct method of showing two sets are equal is by showing that every
element of one set is an element of the other. `ext` does exact this -/
example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  . rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩


/- use your preferred style for the following proof -/
example : s ∩ (s ∪ t) = s := by {
  sorry
}


section ImagePreimage_Connection
variable {α β : Type}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

/- For every function f: α → β, we can consider f's image and preimage over some Set α.
    1. preimage f p, written f ⁻¹' p. preimage f p = {x | f x ∈ p}.
      The expression x ∈ f ⁻¹' p reduces to f x ∈ p
    2. image f s, written f '' s. image f s = {y | ∃ x, x ∈ s ∧ f x = y}.
      The expression y ∈ f '' s decomposes to a triple ⟨x, xs, xeq⟩ with x : α satisfying
      the hypotheses xs : x ∈ s and xeq : f x = y. The rfl tag in the rintro tactic was
      made for this situation.
-/

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by {
  ext
  rfl
}

/- Working with image f s is much trickier because of the quantifiers -/
example : f '' (s ∪ t) = f '' s ∪ f '' t := by {
  ext y
  constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left;
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt
}

/- Complete the following proof. `simp` is helpful for this example -/
example : s ⊆ f ⁻¹' (f '' s) := by {
  intro x xs
  show f x ∈ f '' s
  unfold image
  sorry
}

/- Show that image, preimage form a galois connection from Set s to Set s.
   image f is the left adjoint and preimage f s is the right adjoint -/
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by {
  sorry
}
