import Mathlib.Init.Core
import Mathlib.Tactic
import Mathlib.Algebra.GroupPower.Order
import Mathlib.Tactic.Positivity


/- MATH 460 -- working through the content of the
 - _Mechanics of Proof_ online book by H.R. MacBeth
 -   (https://hrmacbeth.github.io/math2001/index.html)
 - transliterated into plain Lean4
 -
 - tactics like `addarith' and `numbers' and `extra' do not exist
 - but `linarith' and `simp' and `ring' exist and do more
 -/

/- Example 2.1.1 -/
example {a b : ℝ}
      (h1 : a - 5 * b = 4)
      (h2 : b + 2 = 3)
    : a = 9 := by
  have hb : b = 1 := by linarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring

/- Example 2.1.2 -/
example {m n : ℤ}
      (h1 : m + 3 ≤ 2 * n - 1)
      (h2 : n ≤ 5)
    : m ≤ 6 := by
  have h3 :=
    calc
      m + 3 ≤ 2 * n - 1 := by rel [h1]
      _ ≤ 2 * 5 - 1 := by rel [h2]
      _ = 9 := by simp                /- calc gave h3: m+3 ≤ 9 -/
  linarith [h3]

/- Example 2.1.3 -/
example {r s : ℚ}
      (h1 : s + 3 ≥ r)
      (h2 : s + r ≤ 3)
    : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by linarith
  have h4 : r ≤ 3 - s := by linarith
  calc
    r = (r + r) / 2           := by ring
    _ ≤ (3 - s + (3 + s)) / 2 := by rel[h3,h4] 
    _ = 3                     := by linarith

/- Example 2.1.4 -/

lemma extraℝ { x : ℝ }
    : x ^ 2 ≥ 0 := by
  cases (lt_trichotomy x 0) with
  | inl xn  =>  have h : (0 < -x) := by apply neg_pos_of_neg ; apply xn
                calc
                  x ^ 2 =      x *      x := by ring
                  _     = -1 * x * -1 * x := by ring
                  _     =   -x   *   -x   := by ring
                  _     ≥    0   *    0   := by rel[h]
                  _     =        0        := by simp
  | inr x0p => cases x0p with
              | inl x0 => calc
                            x ^ 2 = x * x := by ring
                            _     = 0 * 0 := by rw[x0]
                            _     ≥ 0     := by simp
              | inr xp => calc
                            x ^ 2 = x * x := by ring
                            _     ≥ 0 * 0 := by rel[xp]
                            _     =   0   := by simp 

example {a b : ℝ}
      (h1 : a ^ 2 = b ^ 2 + 1)
      (h2 : a ≥ 0)
    : a ≥ 1 := by
  have hb : b ^ 2 ≥ 0 := by apply extraℝ
  have h3 :=
    calc
      a ^ 2 = b ^ 2 + 1 := by rw [h1]
      _     ≥ 0     + 1 := by linarith
      _     = 1 * 1     := by ring
  cancel 2 at h3

/- Example 2.1.6 -/
example {x y : ℤ}
      (hx : x + 3 ≤ 2)
      (hy : y + 2 * x ≥ 3)
    : y > 3 := by
  have x ≤ -1 by
    calc
      x = x + 3 - 3 := by ring
      _ ≤   2   - 3 := by linarith
      _ =   -1      := by ring
  calc
    y = y + 2 * x - 2 * x    := by ring
    _ ≥      3    - (2 * -1) := by linarith
    _ =      5               := by ring


/- Example 2.1.7 -/
example {a b : ℝ}
      (h1 : -b ≤ a)
      (h2 : a ≤ b)
    : a ^ 2 ≤ b ^ 2 := by
  have ha : 0 ≤ b + a := by
    calc
      0 = b - b := by ring
      _ ≤ b - a := by linarith
