import Mathlib.Init.Core
import Mathlib.Tactic

/- MATH 460 -- working through the content of the
 - _Mechanics of Proof_ online book by H.R. MacBeth
 -   (https://hrmacbeth.github.io/math2001/index.html)
 - transliterated into plain Lean4
 -
 - tactics like `addarith' and `numbers' and `extra' do not exist
 - but `linarith' and `simp' and `ring' exist and do more
 -/

 /- Example 1.2.1 -/
example {a b : ℚ}
      (h1 : a - b = 4)
      (h2 : a * b = 1)
    : (a + b) ^ 2 = 20 := by 
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by ring

/- Example 1.2.2 -/
example {r s : ℝ}
      (h1 : s = 3)
      (h2 : r + 2 * s = -1)
    : r = -7 :=
  calc
    r = r + 2 * s - 2 * s := by ring
    _ = -1 - 2 * s := by rw[h2]
    _ = -1 - 2 * 3 := by rw[h1]
    _ = -7 := by ring

/- Example 1.2.3 -/
example {a b m n : ℤ}
      (h1 : a * m + b * n = 1)
      (h2 : b ^ 2 = 2 * a ^ 2)
    : (2 * a * n + b * m) ^ 2 = 2 :=
  calc
    (2 * a * n + b * m) ^ 2
      = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by ring
    _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by rw[h1,h2]    
    _ = 2 := by ring

/- Example 1.2.4 -/
example {a b c d e f : ℤ}
      (h1 : a * d = b * c)
      (h2 : c * f = d * e)
    : d * (a * f - b * e) = 0 :=
  calc
    d * (a * f - b * e) = (a * d * f) - (d * b * e) := by ring
    _ = (b * c * f) - (d * b * e) := by rw[h1]
    _ = (b * c * f) - (b * d * e) := by ring 
    _ = (b * c * f) - (d * e * b) := by ring
    _ = (b * c * f) - (c * f * b) := by rw[← h2]
    _ = (b * c * f) - (b * c * f) := by ring
    _ = 0 := by ring

/- Example 1.3.1 -/
example {a b : ℤ}
      (h1 : a = 2 * b + 5)
      (h2 : b = 3)
    : a = 11 :=
  calc
    a = 2 * b + 5 := by rw[h1]
    _ = 2 * 3 + 5 := by rw[h2]
    _ = 11        := by ring


/- Example 1.3.2 -/
example {x : ℤ}
      (h1 : x + 4 = 2)
    : x = -2 :=
  calc
    x = x + 4 - 4 := by ring
    _ =     2 - 4 := by rw[h1]
    _ =        -2 := by ring

/- Example 1.3.3 -/
example {a b : ℝ}
      (h1 : a - 5 * b = 4)
      (h2 : b + 2 = 3)
    : a = 9 :=
  calc
    a = a - 5 * b +  5 *  b                  := by ring
    _ =         4 +  5 *  b                  := by rw[h1]
    _ =         4 + (5 * (b + 2 - 2 ))       := by ring
    _ =         4 + (5 * (b + 2)) + (5 * -2) := by ring
    _ =         4 + (5 *    3   ) + (5 * -2) := by rw[h2]
    _ =         9                            := by ring

/- Example 1.3.4 -/
example {w : ℚ}
      (h1 : 3 * w + 1 = 4)
    : w = 1 :=
  calc
    w = (3 * w + 1) / 3 - 1 / 3 := by ring
    _ =      4      / 3 - 1 / 3 := by rw[h1]
    _ =      1                  := by ring

/- Example 1.3.5 -/
example {x : ℤ}
      (h1 : 2 * x + 3 = x)
    : x = -3 :=
  calc
    x = 2 * x + 3 - x - 3 := by ring
    _ =     x     - x - 3 := by rw[h1]
    _ =                -3 := by ring

/- Example 1.3.6 -/
example {x y : ℤ}
      (h1 : 2 * x - y = 4)
      (h2 : y - x + 1 = 2)
    : x = 5 :=
  calc
    x = (2 * x - y) + (y - x + 1) - 1 := by ring
    _ =      4      + (y - x + 1) - 1 := by rw[h1]
    _ =      4     +       2      - 1 := by rw[h2]
    _ =                             5 := by ring

/- Example 1.3.7 -/
example {u v : ℚ}
      (h1 : u + 2 * v = 4)
      (h2 : u - 2 * v = 6)
    : u = 5 :=
  calc
    u = ((u + 2 * v) + (u - 2 * v)) / 2 := by ring
    _ = (     4      +      6     ) / 2 := by rw[h1,h2]
    _ =              5                  := by ring

/- Example 1.3.8 -/
example {x y : ℝ}
      (h1 : x + y = 4)
      (h2 : 5 * x - 3 * y = 4)
    : x = 2 :=
  calc
    x = 8 * x / 8 := by ring
    _ = (8 * x - 3 * y + 3 * y) / 8 := by ring
    _ = (5 * x - 3 * y + 3 *  x + 3 * y)  / 8 := by ring
    _ = (      4       + 3 *  x + 3 * y)  / 8 := by rw[h2]
    _ = (      4       + 3 * (x +     y)) / 8 := by ring
    _ = (      4       + 3 *    4       ) / 8 := by rw[h1]
    _ = 2                                     := by ring

/- Example 1.3.9 -/
example {a b : ℚ}
      (h1 : a - 3 = 2 * b)
    : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
    a ^ 2 - a + 3 = (a - 3) ^ 2 + 5 * (a - 3) + 9 := by ring
    _             = (2 * b) ^ 2 + 5 * (2 * b) + 9 := by rw[h1]
    _             =  4 *  b ^ 2 + 10 * b      + 9 := by ring

/- Example 1.3.10 -/    
example {z : ℝ}
      (h1 : z ^ 2 - 2 = 0)
    : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 :=
  calc
    z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = (z ^ 2 - 2 - z + 3) * (z ^ 2 - 2) + 3 := by ring
    _                                 = (  0       - z + 3) *     0       + 3 := by rw[h1]
    _                                 =                     0             + 3 := by ring
    _                                 =                                     3 := by ring

/- Exercises 1.3.11 -/

/-1-/
example {x y : ℝ}
      (h1 : x = 3)
      (h2 : y = 4 * x - 3)
    : y = 9 :=
  sorry

/-2-/
example {a b : ℤ}
      (h : a - b = 0)
    : a = b :=
  sorry

/-3-/
example {x y : ℤ}
      (h1 : x - 3 * y = 5)
      (h2 : y = 3)
    : x = 14 :=
  sorry

/-4-/
example {p q : ℚ}
      (h1 : p - 2 * q = 1)
      (h2 : q = -1)
    : p = -1 :=
  sorry

/-5-/
example {x y : ℚ}
      (h1 : y + 1 = 3)
      (h2 : x + 2 * y = 3)
    : x = -1 :=
  sorry

/-6-/
example {p q : ℤ}
      (h1 : p + 4 * q = 1)
      (h2 : q - 1 = 2)
    : p = -11 :=
  sorry

/-7-/
example {a b c : ℝ}
      (h1 : a + 2 * b + 3 * c = 7)
      (h2 : b + 2 * c = 3)
      (h3 : c = 1)
    : a = 2 :=
  sorry

/-8-/
example {u v : ℚ}
      (h1 : 4 * u + v = 3)
      (h2 : v = 2)
    : u = 1 / 4 :=
  sorry

/-9-/
example {c : ℚ}
      (h1 : 4 * c + 1 = 3 * c - 2)
    : c = -3 :=
  sorry

/-10-/
example {p : ℝ}
      (h1 : 5 * p - 3 = 3 * p + 1)
    : p = 2 :=
  sorry

/-11-/
example {x y : ℤ}
      (h1 : 2 * x + y = 4)
      (h2 : x + y = 1)
    : x = 3 :=
  sorry

/-12-/
example {a b : ℝ}
      (h1 : a + 2 * b = 4)
      (h2 : a - b = 1)
    : a = 2 :=
  sorry

/-13-/
example {u v : ℝ}
      (h1 : u + 1 = v)
    : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 :=
  sorry

/-14-/
example {t : ℚ}
      (ht : t ^ 2 - 4 = 0)
    : t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
  sorry

/-15-/
example {x y : ℝ}
      (h1 : x + 3 = 5)
      (h2 : 2 * x - y * x = 0)
    : y = 2 :=
  sorry

/-16-/
example {p q r : ℚ}
      (h1 : p + q + r = 0)
      (h2 : p * q + p * r + q * r = 2)
    : p ^ 2 + q ^ 2 + r ^ 2 = -4 :=
  sorry

/- Example 1.4.1 -/
example {x y : ℤ}
      (hx : x + 3 ≤ 2)
      (hy : y + 2 * x ≥ 3)
    : y > 3 :=
  calc
    y = y + 2 * x - 2 * x         := by ring
    _ ≥     3     - 2 * x         := by rel[hy]
    _ =     3 + 6 - 2 * (x + 3)   := by ring
    _ ≥       9   - 2 *    2      := by rel[hx]
    _ =       3 + 2               := by ring
    _ >       3                   := by simp

/- Example 1.4.2 -/
example {r s : ℚ}
      (h1 : s + 3 ≥ r)
      (h2 : s + r ≤ 3)
    : r ≤ 3 :=
  calc
    r = (s + r +    r    - s) / 2 := by ring
    _ ≤ (  3   + (s + 3) - s) / 2 := by rel[h2, h1]
    _ = 3                         := by ring

/- Example 1.4.3 -/
example {x y : ℝ}
      (h1 : y ≤ x + 5)
      (h2 : x ≤ -2)
    : x + y < 2 :=
calc
  x + y ≤  x +  (x + 5) := by rel[h1]
  _     = 2 * x + 5     := by ring
  _     ≤ 2 * -2 + 5    := by rel[h2]
  _     = 1             := by ring
  _     < 1 + 1         := by simp
  _     = 2             := by ring

/- Example 1.4.4 -/
example {u v x y A B : ℝ}
        (h1 : 0 < A)       /- unused! -/
        (h2 : A ≤ 1)
        (h3 : 1 ≤ B)
        (h4 : x ≤ B)
        (h5 : y ≤ B)
        (h6 : 0 ≤ u)
        (h7 : 0 ≤ v)
        (h8 : u < A)
        (h9 : v < A)
    : u * y + v * x + u * v < 3 * A * B :=
  calc
    u * y + v * x + u * v ≤ u * B + v * B + u * v := by rel[h5,h4]
    _                     ≤ A * B + A * B + A * v := by rel[h8,h9,h7] /- 2 steps and < -/
    _                     ≤ A * B + A * B + 1 * v := by rel[h2]
    _                     ≤ A * B + A * B + B * v := by rel[h3]
    _                     < A * B + A * B + B * A := by rel[h9]
    _                     =  3 *    A * B         := by ring

/- Example 1.4.5 -/
example {t : ℚ}
      (ht : t ≥ 10)
    : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
    t ^ 2 - 3 * t - 17 = t  *  t - 3 * t - 17 := by ring
    _                  ≥ 10 *  t - 3 * t - 17 := by rel[ht]
    _                  =       7 *  t    - 17 := by ring
    _                  ≥       7 * 10    - 17 := by rel[ht]
    _                  =                53    := by ring
    _                  ≥                 5    := by simp

/- Example 1.4.6 -/
example {n : ℤ}
      (hn : n ≥ 5)
    : n ^ 2 > 2 * n + 11 :=
  calc
    n ^ 2 = n * n          := by ring
    _     ≥ 5 * n          := by rel[hn]
    _     = 2 * n +  3 * n := by ring
    _     ≥ 2 * n +  3 * 5 := by rel[hn]
    _     = 2 * n + 11 + 4 := by ring
    _     > 2 * n + 11     := by simp

/- Example 1.4.7 -/
lemma extraℤ  { x : ℤ }
    : x ^ 2 ≥ 0 := by
  cases (lt_trichotomy x 0) with
  | inl xn  =>  have h : (0 < -x) := by apply Int.neg_pos_of_neg ; apply xn
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

/- now we can follow the proof (more or less) like the book -/
example {m n : ℤ}
      (h : m ^ 2 + n ≤ 2)
    : n ≤ 2 :=
  have hm : (m ^ 2 ≥ 0) := by apply extraℤ
  calc
    n = m ^ 2 + n - m ^ 2 := by ring
    _  ≤      2   - m ^ 2 := by rel[h]
    _  ≤      2   - 0     := by rel[hm]
    _  =      2           := by ring

/- Example 1.4.8 -/
/- their `extra' trick doesn't work ...
    but my `extra' lemma does in the same way as above
    except I need a ℝ version of it ... there must be a way to generalize this -/

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

example {x y : ℝ}
      (h : x ^ 2 + y ^ 2 ≤ 1)
    : (x + y) ^ 2 < 3 :=
  have hxy : (x - y) ^ 2 ≥ 0 := by apply extraℝ
  calc
    (x + y) ^ 2 = (x + y) ^ 2 + (x - y) ^ 2 - (x - y) ^ 2 := by ring
    _           ≤ (x + y) ^ 2 + (x - y) ^ 2 - 0           := by rel[hxy]
    _           = 2 * (x ^ 2 + y ^ 2)                     := by ring
    _           ≤ 2 * 1                                   := by rel[h]
    _           = 2                                       := by ring
    _           < 2 + 1                                   := by simp
    _           = 3                                       := by ring

/- Example 1.4.9 -/
lemma extraℚ {a : ℚ} 
    : a ≥ 0 → a ^ 2 ≥ 0 := by
  intros h
  calc
      a ^ 2 = a * a := by ring
      _     ≥ 0 * 0 := by rel[h]
      _     = 0     := by ring

example {a b : ℚ}
      (h1 : a ≥ 0)
      (h2 : b ≥ 0)
      (h3 : a + b ≤ 8)
    : 3 * a * b + a ≤ 7 * b + 72 :=
  have hb : (b ^ 2 ≥ 0) := by apply extraℚ ; exact h2
  have ha : (a ^ 2 ≥ 0) := by apply extraℚ ; exact h1
  calc
    3 * a * b + a = 2 *   0   +   0   + (3 * a * b + a) := by ring
    _             ≤ 2 * b ^ 2 +   0   + (3 * a * b + a) := by rel[hb]
    _             ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by rel[ha]
    _             = 2 * ((a + b) * b) + (a + b) * a + a := by ring
    _             ≤ 2 * (8 * b) + 8 * a + a             := by rel[h3]
    _             = 7 * b + 9 * (a + b)                 := by ring
    _             ≤ 7 * b + 9 * 8                       := by rel[h3]
    _             = 7 * b + 72                          := by ring

/- Example 1.4.10 -/
example {a b c : ℝ}
    : a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 :=
  have h1 : (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 ≥ 0         := by apply extraℝ 
  have h2 : (b ^ 4 - c ^ 4) ^ 2 ≥ 0                   := by apply extraℝ 
  have h3 : (a ^ 2 * b * c - b ^ 2 * c ^ 2) ^ 2 ≥ 0   := by apply extraℝ 
  calc
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3)
      =   2 * 0
        + 0
        + 4 * 0
        + a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3)                    := by ring
    _ ≤   2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2
        + 0
        + 4 * 0
        + a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3)                    := by rel[h1]
    _ ≤   2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2
        + (b ^ 4 - c ^ 4) ^ 2
        + 4 * 0
        + a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3)                    := by rel[h2]
    _ ≤   2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2
        + (b ^ 4 - c ^ 4) ^ 2
        + 4 * (a ^ 2 * b * c - b ^ 2 * c ^ 2) ^ 2
        + a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3)                    := by rel[h3]
    _ =   2 * a ^ 4 * b ^ 4 - 4 * a ^ 4 * b ^ 2 * c ^ 2 + 2 * a ^ 4 * c ^ 4
        + b ^ 8 - 2 * b ^ 4 * c ^ 4 + c ^ 8
        + 4 * a ^ 4 * b ^ 2 * c ^ 2 - 8 * a ^ 2 * b ^ 3 * c ^ 3 + 4 * b ^ 4 * c ^ 4
        + a ^ 8 + 8 * a ^ 2 * b ^ 3 * c ^ 3                      := by ring
    _ = (a ^ 4 + b ^ 4 + c ^ 4) ^ 2                              := by ring

/- Exercises 1.4.11 -/

/-1-/
example {x y : ℤ}
      (h1 : x + 3 ≥ 2 * y)
      (h2 : 1 ≤ y)
    : x ≥ -1 :=
  sorry

/-2-/
example {a b : ℚ}
      (h1 : 3 ≤ a)
      (h2 : a + 2 * b ≥ 4)
    : a + b ≥ 3 :=
  sorry

/-3-/
example {x : ℤ}
      (hx : x ≥ 9)
    : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  sorry

/-4-/
example {n : ℤ}
      (hn : n ≥ 10)
    : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 :=
  sorry

/-5-/
example {n : ℤ}
      (h1 : n ≥ 5)
    : n ^ 2 - 2 * n + 3 > 14 :=
  sorry

/-5 [AGAIN!]-/
example {x : ℚ}
    : x ^ 2 - 2 * x ≥ -1 :=
  sorry

/-6-/
example (a b : ℝ)
    : a ^ 2 + b ^ 2 ≥ 2 * a * b :=
  sorry

/- 1.5 -/
/- the addarith is a simpler version of linarith -/
example {x : ℤ}
      (h1 : x + 4 = 2)
    : x = -2 := by linarith[h1]

example {a b : ℤ}
      (ha : a - 2 * b = 1)
    : a = 2 * b + 1 := by linarith [ha]

example {x y : ℚ}
      (hx : x = 2)
      (hy : y ^ 2 = -7)
    : x + y ^ 2 = -5 :=
  calc
    x + y ^ 2 = x - 7 := by linarith [hy]
    _ = -5            := by linarith [hx]

example {s t : ℝ}
      (h : t = 4 - s * t)
    : t + s * t > 0 := by linarith [h]

example {m n : ℝ}
      (h1 : m ≤ 8 - n)
    : 10 > m + n := by linarith [h1]

/- this one is too hard -/
example {w : ℚ}
      (h1 : 3 * w + 1 = 4)
    : w = 1 := sorry