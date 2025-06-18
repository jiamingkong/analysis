import Mathlib.Tactic
import Analysis.Section_2_2

/-!
# Analysis I, Section 2.3

This file is a translation of Section 2.3 of Analysis I to Lean 4.
All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of multiplication and exponentiation for the "Chapter 2" natural numbers,
  `Chapter2.Nat`

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of
`Chapter2.Nat` "by hand" for pedagogical purposes.
-/

namespace Chapter2

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod + m) 0 n

instance Nat.instMul : Mul Nat where
  mul := mul

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
theorem Nat.zero_mul (m: Nat) : 0 * m = 0 := recurse_zero (fun _ prod ↦ prod+m) _

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
theorem Nat.succ_mul (n m: Nat) : (n++) * m = n * m + m := recurse_succ (fun _ prod ↦ prod+m) _ _

theorem Nat.one_mul' (m: Nat) : 1 * m = 0 + m := by
  rw [←zero_succ, succ_mul, zero_mul]

theorem Nat.one_mul (m: Nat) : 1 * m = m := by
  rw [one_mul', zero_add]

theorem Nat.two_mul (m: Nat) : 2 * m = 0 + m + m := by
  rw [←one_succ, succ_mul, one_mul']

/-- This lemma will be useful to prove Lemma 2.3.2. -/
lemma Nat.mul_zero (n: Nat) : n * 0 = 0 := by
  revert n; apply induction
  . rw [zero_mul]
  . intro n h
    rw [succ_mul, h]
    rw [zero_add]

/-- This lemma will be useful to prove Lemma 2.3.2. -/
lemma Nat.mul_succ (n m:Nat) : n * m++ = n * m + n := by
  revert n; apply induction
  . rw [zero_mul, zero_mul, zero_add]
  . intro n h
    rw [succ_mul, h, succ_mul]
    rw [succ_eq_add_one, succ_eq_add_one, ← add_assoc, ← add_assoc]
    rw [add_comm (n * m + n)]
    rw [add_comm (n * m) m]
    rw [← add_assoc]



/-- Lemma 2.3.2 (Multiplication is commutative) / Exercise 2.3.1 -/
lemma Nat.mul_comm (n m: Nat) : n * m = m * n := by
  revert m; apply induction
  . rw [zero_mul, mul_zero]
  . intro m h
    rw [succ_mul, mul_succ, h]

theorem Nat.mul_one (m: Nat) : m * 1 = m := by
  rw [mul_comm, one_mul]

/-- Lemma 2.3.3 (Positive natural numbers have no zero divisors) / Exercise 2.3.2 -/
lemma Nat.mul_eq_zero_iff (n m: Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  · -- Forward direction: if n * m = 0, then n = 0 or m = 0
    intro h
    -- Use induction on n
    induction n with
    | zero => left; rfl
    | succ k ih =>
      -- For n = k++, we have (k++) * m = k * m + m = 0
      rw [succ_mul] at h
      -- Since k * m + m = 0 and m ≠ 0 would make the sum positive, we must have m = 0
      right
      by_contra hm_ne_zero
      -- If m ≠ 0, then m is positive
      have hm_pos : m.isPos := by rwa [isPos_iff]
      -- But then k * m + m is positive, contradiction
      have h_pos : (k * m + m).isPos := by
        apply add_pos
        exact hm_pos
      rw [isPos_iff] at h_pos
      rw [h] at h_pos
      exact h_pos rfl
  · -- Reverse direction: if n = 0 or m = 0, then n * m = 0
    intro h
    cases' h with hn hm
    · rw [hn, zero_mul]
    · rw [hm, mul_zero]

lemma Nat.pos_mul_pos {n m: Nat} (h₁: n.isPos) (h₂: m.isPos) : (n * m).isPos := by
  -- Use the contrapositive of mul_eq_zero_iff
  rw [isPos_iff]
  intro h
  rw [mul_eq_zero_iff] at h
  cases' h with hn hm
  · rw [isPos_iff] at h₁
    exact h₁ hn
  · rw [isPos_iff] at h₂
    exact h₂ hm

/-- Proposition 2.3.4 (Distributive law)-/
theorem Nat.mul_add (a b c: Nat) : a * (b + c) = a * b + a * c := by
  -- This proof is written to follow the structure of the original text.
  revert c; apply induction
  . rw [add_zero]
    rw [mul_zero, add_zero]
  intro c habc
  rw [add_succ, mul_succ]
  rw [mul_succ, ←add_assoc, ←habc]

/-- Proposition 2.3.4 (Distributive law)-/
theorem Nat.add_mul (a b c: Nat) : (a + b)*c = a*c + b*c := by
  simp only [mul_comm, mul_add]

/-- Proposition 2.3.5 (Multiplication is associative) / Exercise 2.3.3 -/
theorem Nat.mul_assoc (a b c: Nat) : (a * b) * c = a * (b * c) := by
  revert c; apply induction
  . rw [mul_zero, mul_zero, mul_zero]
  . intro c habc
    rw [mul_succ, mul_succ]
    rw [habc]
    -- a * (b * c) + a * b = a * (b * c + b)
    rw [←mul_add]

/-- (Not from textbook)  Nat is a commutative semiring. -/
instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_lt_mul_of_pos_right {a b c: Nat} (h: a < b) (hc: c.isPos) : a * c < b * c := by
  -- This proof is written to follow the structure of the original text.
  rw [lt_iff_add_pos] at h
  obtain ⟨ d, hdpos, hd ⟩ := h
  apply_fun (· * c) at hd
  rw [add_mul] at hd
  have hdcpos : (d * c).isPos := pos_mul_pos hdpos hc
  rw [lt_iff_add_pos]
  use d*c

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_right {a b c: Nat} (h: a > b) (hc: c.isPos) :
    a * c > b * c := mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_lt_mul_of_pos_left {a b c: Nat} (h: a < b) (hc: c.isPos) : c * a < c * b := by
  simp [mul_comm]
  exact mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_left {a b c: Nat} (h: a > b) (hc: c.isPos) :
    c * a > c * b := mul_lt_mul_of_pos_left h hc



/-- Corollary 2.3.7 (Cancellation law) -/
lemma Nat.mul_cancel_right {a b c: Nat} (h: a * c = b * c) (hc: c.isPos) : a = b := by
  -- This proof is written to follow the structure of the original text.
  have := trichotomous a b
  rcases this with hlt | heq | hgt
  . replace hlt := mul_lt_mul_of_pos_right hlt hc
    replace hlt := ne_of_lt _ _ hlt
    contradiction
  . assumption
  replace hgt := mul_gt_mul_of_pos_right hgt hc
  replace hgt := ne_of_gt _ _ hgt
  contradiction

/-- (Not from textbook) Nat is an ordered semiring. -/
instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one := by
    use 1
    rw [Nat.zero_add]
  mul_le_mul_of_nonneg_left := by
    intros a b c hab hc
    by_cases h : c = 0
    · -- Case c = 0
      rw [h, zero_mul, zero_mul]
    · -- Case c ≠ 0, so c.isPos
      have hc_pos : c.isPos := by rwa [isPos_iff]
      rw [le_iff_lt_or_eq] at hab ⊢
      cases hab with
      | inl hab_lt =>
        left
        exact mul_lt_mul_of_pos_left hab_lt hc_pos
      | inr hab_eq =>
        right
        rw [hab_eq]
  mul_le_mul_of_nonneg_right := by
    intros a b c hab hc
    by_cases h : c = 0
    · -- Case c = 0
      rw [h, mul_zero, mul_zero]
    · -- Case c ≠ 0, so c.isPos
      have hc_pos : c.isPos := by rwa [isPos_iff]
      rw [le_iff_lt_or_eq] at hab ⊢
      cases hab with
      | inl hab_lt =>
        left
        exact mul_lt_mul_of_pos_right hab_lt hc_pos
      | inr hab_eq =>
        right
        rw [hab_eq]


/-- Proposition 2.3.9 (Euclid's division lemma) / Exercise 2.3.5 -/
theorem Nat.exists_div_mod (n :Nat) {q: Nat} (hq: q.isPos) :
    ∃ m r: Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  sorry

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
abbrev Nat.pow (m n: Nat) : Nat := Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.instPow : HomogeneousPow Nat where
  pow := Nat.pow

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
theorem Nat.zero_pow_zero : (0:Nat) ^ 0 = 1 := recurse_zero (fun _ prod ↦ prod * 0) _

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
theorem Nat.pow_succ (m n: Nat) : (m:Nat) ^ n++ = m^n * m :=
  recurse_succ (fun _ prod ↦ prod * m) _ _

/-- Exercise 2.3.4-/
theorem Nat.sq_add_eq (a b: Nat) : (a + b) ^ (2 : Nat) = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by
  rw [show (2:Nat) = 1++ from rfl, pow_succ, pow_succ, pow_succ]
  rw [show (1:Nat) = 0++ from rfl, pow_succ, pow_succ, pow_succ]
  -- Now we have m^0 * m * m on each term. Since m^0 = 1 by definition:
  change (1 * (a + b) * (a + b) = 1 * a * a + 0++++ * a * b + 1 * b * b)
  rw [one_mul, one_mul, one_mul]
  rw [add_mul, mul_add, mul_add, mul_comm b a]
  -- Now we have: a * a + a * b + a * b + b * b = a * a + 0++++ * a * b + b * b
  -- We need to show that a * b + a * b = 0++++ * a * b
  -- Since 0++++ = 2, this means a * b + a * b = 2 * a * b
  have h : a * b + a * b = 0++++ * a * b := by
    rw [show 0++++ = 2 from rfl, show (2:Nat) = 1++ from rfl]
    rw [succ_mul, one_mul]
    rw [←add_mul]
  -- Rearrange to group a * b + a * b together
  rw [add_assoc (a * a)]
  -- Now we have a * a + (a * b + (a * b + b * b))
  -- Rearrange the inner part: a * b + (a * b + b * b) = (a * b + a * b) + b * b
  rw [← add_assoc (a * b)]
  rw [h]
  rw [add_assoc]

end Chapter2
