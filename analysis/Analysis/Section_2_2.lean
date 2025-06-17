import Mathlib.Tactic
import Analysis.Section_2_1

/-!
# Analysis I, Section 2.2

This file is a translation of Section 2.2 of Analysis I to Lean 4.  All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.   When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Definition of addition and order for the "Chapter 2" natural numbers, `Chapter2.Nat`
- Establishment of basic properties of addition and order

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of `Chapter2.Nat` "by hand" for pedagogical purposes.
-/

namespace Chapter2

/-- Definition 2.2.1. (Addition of natural numbers). -/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

instance Nat.instAdd : Add Nat where
  add := add

theorem Nat.zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

theorem Nat.succ_add (n m: Nat) : n++ + m = (n+m)++ := by rfl

theorem Nat.one_add (m:Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl, succ_add, zero_add]

theorem Nat.two_add (m:Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl, succ_add, one_add]

example : (2:Nat) + 3 = 5 := by
  rw [Nat.two_add, show 3++=4 from rfl, show 4++=5 from rfl]

-- sum of two natural numbers is again a natural number
#check (fun (n m:Nat) ↦ n + m)

/-- Lemma 2.2.2 (n + 0 = n) -/
lemma Nat.add_zero (n:Nat) : n + 0 = n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . exact zero_add 0
  intro n ih
  calc
    (n++) + 0 = (n + 0)++ := by rfl
    _ = n++ := by rw [ih]

/-- Lemma 2.2.3 (n+(m++) = (n+m)++). -/
lemma Nat.add_succ (n m:Nat) : n + (m++) = (n + m)++ := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, zero_add]
  intro n ih
  rw [succ_add, ih]
  rw [succ_add]


/-- n++ = n + 1 (Why?) -/
theorem Nat.succ_eq_add_one (n:Nat) : n++ = n + 1 := by
  rw [← zero_succ]
  rw [add_succ]
  rw [add_zero]

/-- Proposition 2.2.4 (Addition is commutative) -/
theorem Nat.add_comm (n m:Nat) : n + m = m + n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, add_zero]
  intro n ih
  rw [succ_add]
  rw [add_succ, ih]

/-- Proposition 2.2.5 (Addition is associative) / Exercise 2.2.1-/
theorem Nat.add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
  -- this proof is written to follow the structure of the original text.
  revert a; apply induction
  . rw [zero_add, zero_add]
  . intro a ih
    rw [succ_add, succ_add, succ_add, ih]

/-- Proposition 2.2.6 (Cancellation law) -/
theorem Nat.add_cancel_left (a b c:Nat) (habc: a + b = a + c) : b = c := by
  -- this proof is written to follow the structure of the original text.
  revert a; apply induction
  . intro hbc
    rwa [zero_add, zero_add] at hbc
  intro a ih
  intro hbc
  rw [succ_add, succ_add] at hbc
  replace hbc := succ_cancel hbc
  exact ih hbc


/-- (Not from textbook) Nat can be given the structure of a commutative additive monoid. -/
instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- Definition 2.2.7 (Positive natural numbers).-/
def Nat.isPos (n:Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n:Nat) : n.isPos ↔ n ≠ 0 := by rfl

/-- Proposition 2.2.8 (positive plus natural number is positive).-/
theorem Nat.pos_add {a:Nat} (b:Nat) (ha: a.isPos) : (a + b).isPos := by
  -- this proof is written to follow the structure of the original text.
  revert b; apply induction
  . rwa [add_zero]
  intro b hab
  rw [add_succ]
  have : (a+b)++ ≠ 0 := succ_ne _
  exact this

theorem Nat.add_pos {a:Nat} (b:Nat) (ha: a.isPos) : (b + a).isPos := by
  rw [add_comm]
  exact pos_add _ ha

/-- Corollary 2.2.9 (if sum vanishes, then summands vanish).-/
theorem Nat.add_eq_zero (a b:Nat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  -- this proof is written to follow the structure of the original text.
  by_contra h
  simp only [not_and_or, ←ne_eq] at h
  rcases h with ha | hb
  . rw [← isPos_iff] at ha
    have : (a + b).isPos := pos_add _ ha
    contradiction
  rw [← isPos_iff] at hb
  have : (a + b).isPos := add_pos _ hb
  contradiction

/-- Lemma 2.2.10 (unique predecessor) / Exercise 2.2.2 -/
lemma Nat.uniq_succ_eq (a:Nat) (ha: a.isPos) : ∃! b, b++ = a := by
  -- this proof is written to follow the structure of the original text.
  -- Since a is positive, a ≠ 0, so a must be of the form n++ for some n
  rw [isPos_iff] at ha
  -- Use induction on the structure of a
  induction a with
  | zero =>
    -- This case is impossible since ha : 0 ≠ 0
    contradiction
  | succ n =>
    -- For a = n++, we have b = n is the unique predecessor
    use n
    constructor
    · -- Existence: n++ = n++
      rfl
    · -- Uniqueness: if b++ = n++, then b = n
      intro b hb
      exact succ_cancel hb


/-- Definition 2.2.11 (Ordering of the natural numbers) -/
instance Nat.instLE : LE Nat where
  le n m := ∃ a:Nat, m = n + a

/-- Definition 2.2.11 (Ordering of the natural numbers) -/
instance Nat.instLT : LT Nat where
  lt n m := (∃ a:Nat, m = n + a) ∧ n ≠ m

lemma Nat.le_iff (n m:Nat) : n ≤ m ↔ ∃ a:Nat, m = n + a := by rfl

lemma Nat.lt_iff (n m:Nat) : n < m ↔ (∃ a:Nat, m = n + a) ∧ n ≠ m := by rfl

lemma Nat.ge_iff_le (n m:Nat) : n ≥ m ↔ m ≤ n := by rfl

lemma Nat.gt_iff_lt (n m:Nat) : n > m ↔ m < n := by rfl

lemma Nat.le_of_lt {n m:Nat} (hnm: n < m) : n ≤ m := hnm.1

lemma Nat.le_iff_lt_or_eq (n m:Nat) : n ≤ m ↔ n < m ∨ n = m := by
  rw [Nat.le_iff, Nat.lt_iff]
  by_cases h : n = m
  . simp [h]
    use 0
    rw [add_zero]
  simp [h]

example : (8:Nat) > 5 := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  . have : (8:Nat) = 5 + 3 := by rfl
    rw [this]
    use 3
  decide

theorem Nat.succ_gt (n:Nat) : n++ > n := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  . use 1
    rw [Nat.succ_eq_add_one]
  . intro h
    -- We need to show n ≠ n++, so we assume n = n++ and derive a contradiction
    -- We can prove by induction that no natural number equals its successor
    induction n with
    | zero =>
      -- Case n = 0: we have 0 = 0++, but 0++ ≠ 0 by succ_ne
      have := succ_ne 0
      exact this h.symm
    | succ k ih =>
      -- Case n = k++: we have k++ = (k++)++, so k = k++ by succ_cancel
      have : k = k++ := succ_cancel h
      exact ih this

/-- Proposition 2.2.12 (Basic properties of order for natural numbers) / Exercise 2.2.3

(a) (Order is reflexive). -/
theorem Nat.ge_refl (a:Nat) : a ≥ a := by
  use 0
  rw [add_zero]

/-- (b) (Order is transitive) -/
theorem Nat.ge_trans {a b c:Nat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  rcases hab with ⟨d, rfl⟩
  rcases hbc with ⟨e, rfl⟩
  use e + d
  rw [Nat.add_assoc]

/-- (c) (Order is anti-symmetric)  -/
theorem Nat.ge_antisymm {a b:Nat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  rcases hab with ⟨d, had⟩
  rcases hba with ⟨e, hbe⟩
  -- we now have a = b + d and b = a + e
  -- Substituting the first into the second: b = (b + d) + e = b + (d + e)
  rw [had] at hbe
  rw [Nat.add_assoc] at hbe
  -- So b = b + (d + e). We want to show d + e = 0
  have h_zero : d + e = 0 := by
    -- From b = b + (d + e), we get b + 0 = b + (d + e) since b + 0 = b
    have : b + (d + e) = b + 0 := hbe ▸ (Nat.add_zero b).symm
    exact Nat.add_cancel_left _ _ _ this
  -- Since d + e = 0, both d = 0 and e = 0
  have ⟨hd, he⟩ := Nat.add_eq_zero _ _ h_zero
  -- Therefore a = b + 0 = b
  rw [had, hd, Nat.add_zero]

/-- (d) (Addition preserves order)  -/
theorem Nat.add_ge_add_right (a b c:Nat) : a ≥ b ↔ a + c ≥ b + c := by
  constructor
  · -- Forward direction: a ≥ b → a + c ≥ b + c
    intro hab
    rcases hab with ⟨d, hd⟩
    -- We have a = b + d, so a + c = (b + d) + c = b + (d + c) = b + c + d
    use d
    calc a + c
      = (b + d) + c := by rw [hd]
      _ = b + (d + c) := by rw [Nat.add_assoc]
      _ = b + (c + d) := by rw [Nat.add_comm d c]
      _ = (b + c) + d := by rw [← Nat.add_assoc]
  · -- Reverse direction: a + c ≥ b + c → a ≥ b
    intro habc
    rcases habc with ⟨d, hd⟩
    -- We have a + c = (b + c) + d = b + c + d
    use d
    -- We need to show a = b + d from a + c = b + c + d
    -- Use cancellation: a + c = b + c + d implies a + c = (b + d) + c
    have : a + c = (b + d) + c := calc a + c
      = (b + c) + d := hd
      _ = b + (c + d) := by rw [Nat.add_assoc]
      _ = b + (d + c) := by rw [Nat.add_comm c d]
      _ = (b + d) + c := by rw [← Nat.add_assoc]
    -- Now we have c + a = c + (b + d), so a = b + d by cancellation
    have h_cancel : c + a = c + (b + d) := by rw [Nat.add_comm c a, this, Nat.add_comm (b + d) c]
    exact Nat.add_cancel_left _ _ _ h_cancel

/-- (d) (Addition preserves order)  -/
theorem Nat.add_ge_add_left (a b c:Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

/-- (d) (Addition preserves order)  -/
theorem Nat.add_le_add_right (a b c:Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

/-- (d) (Addition preserves order)  -/
theorem Nat.add_le_add_left (a b c:Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

/-- (e) a < b iff a++ ≤ b. -/
theorem Nat.lt_iff_succ_le (a b:Nat) : a < b ↔ a++ ≤ b := by
  constructor
  · -- Forward direction: a < b → a++ ≤ b
    intro hab
    rcases hab with ⟨⟨d, hd⟩, hne⟩
    -- Since a ≠ b and b = a + d, we must have d > 0
    have hd_pos : d.isPos := by
      rw [isPos_iff]
      intro hd_zero
      rw [hd_zero, Nat.add_zero] at hd
      exact hne hd.symm
    -- Since d > 0, we can write d = e++ for some e
    obtain ⟨e, he_eq, _⟩ := uniq_succ_eq d hd_pos
    use e
    -- Now b = a + d = a + e++ = a++ + e
    calc b
      = a + d := hd
      _ = a + e++ := by rw [← he_eq]
      _ = a + (e + 1) := by rw [Nat.succ_eq_add_one]
      _ = (a + e) + 1 := by rw [Nat.add_assoc]
      _ = 1 + (a + e) := by rw [Nat.add_comm]
      _ = 1 + a + e := by rw [← Nat.add_assoc]
      _ = a + 1 + e := by rw [Nat.add_comm 1 a]
      _ = a++ + e := by rw [← Nat.succ_eq_add_one]
  · -- Reverse direction: a++ ≤ b → a < b
    intro h_succ_le
    rcases h_succ_le with ⟨e, he⟩
    constructor
    · use 1 + e
      rw [he, Nat.succ_eq_add_one, Nat.add_assoc]
    · intro h_eq
      -- If a = b, then b = a++ + e gives us a = a++ + e
      have h_absurd : a = a++ + e := by
        calc a
          = b := h_eq
          _ = a++ + e := he
      -- Since a++ = a + 1, we have a = (a + 1) + e = a + (1 + e)
      rw [Nat.succ_eq_add_one, Nat.add_assoc] at h_absurd
      -- By cancellation: 0 = 1 + e
      have h_zero : 0 = 1 + e := Nat.add_cancel_left _ _ _ (by rw [Nat.add_zero]; exact h_absurd)
      -- But 1 + e ≠ 0, contradiction
      exfalso
      -- Since 1 ≠ 0, we have 1 + e ≠ 0
      have : 1 + e ≠ 0 := by
        intro h_contra
        -- From h_zero: 0 = 1 + e and h_contra: 1 + e = 0
        -- We can show this is impossible by cases on e
        cases e with
        | zero =>
          -- If e = 0, then 1 + e = 1 ≠ 0
          simp at h_contra
        | succ e' =>
          -- If e = e'++, then 1 + e = 1 + e'++ ≠ 0
          simp at h_contra
      exact this h_zero.symm

/-- (f) a < b if and only if b = a + d for positive d. -/
theorem Nat.lt_iff_add_pos (a b:Nat) : a < b ↔ ∃ d:Nat, d.isPos ∧ b = a + d := by
  constructor
  . intro h
    rcases h with ⟨⟨d, hd⟩, hne⟩
    -- Since a < b, we have d > 0
    have hd_pos : d.isPos := by
      rw [isPos_iff]
      intro hd_zero
      rw [hd_zero, Nat.add_zero] at hd
      exact hne hd.symm
    use d, hd_pos, hd
  · intro h
    rcases h with ⟨d, hd_pos, hd_eq⟩
    -- We have b = a + d and d > 0
    constructor
    · -- Show a ≤ b
      use d, hd_eq
    · -- Show a ≠ b
      intro h_eq
      -- If a = b, then a = a + d, so 0 = d by cancellation
      have h_zero : 0 = d := by
        have : a + 0 = a + d := by
          calc a + 0
            = a := Nat.add_zero _
            _ = b := h_eq
            _ = a + d := hd_eq
        exact Nat.add_cancel_left _ _ _ this
      -- But d > 0, contradiction
      rw [isPos_iff] at hd_pos
      exact hd_pos h_zero.symm


/-- If a < b then a ̸= b,-/
theorem Nat.ne_of_lt (a b:Nat) : a < b → a ≠ b := by
  intro h; exact h.2

/-- if a > b then a ̸= b. -/
theorem Nat.ne_of_gt (a b:Nat) : a > b → a ≠ b := by
  intro h; exact h.2.symm

/-- If a > b and a < b then contradiction -/
theorem Nat.not_lt_of_gt (a b:Nat) : a < b ∧ a > b → False := by
  intro h
  have := (ge_antisymm (Nat.le_of_lt h.1) (Nat.le_of_lt h.2)).symm
  have := ne_of_lt _ _ h.1
  contradiction


/-- Proposition 2.2.13 (Trichotomy of order for natural numbers) / Exercise 2.2.4 -/
theorem Nat.trichotomous (a b:Nat) : a < b ∨ a = b ∨ a > b := by
  -- this proof is written to follow the structure of the original text.
  revert a; apply induction
  . have why : 0 ≤ b := by
      use b
      rw [Nat.zero_add]
    replace why := (Nat.le_iff_lt_or_eq _ _).mp why
    tauto
  intro a ih
  rcases ih with case1 | case2 | case3
  . rw [lt_iff_succ_le] at case1
    rw [Nat.le_iff_lt_or_eq] at case1
    tauto
  . have why : a++ > b := by
      rw [← case2]
      exact Nat.succ_gt a
    tauto
  have why : a++ > b := by
    rw [succ_eq_add_one]
    rw [gt_iff_lt, lt_iff_succ_le] at case3
    rcases case3 with ⟨ d, hd_eq ⟩
    rw [hd_eq]
    rw [gt_iff_lt, lt_iff_succ_le]
    use d+1
    rw [add_assoc]
  tauto

/-- (Not from textbook) Establish the decidability of this order computably.  The portion of the proof involving decidability has been provided; the remaining sorries involve claims about the natural numbers.  One could also have established this result by the `classical` tactic followed by `exact Classical.decRel _`, but this would make this definition (as well as some instances below) noncomputable. -/
def Nat.le_dec : (a b : Nat) → Decidable (a ≤ b)
  | 0, b => by
    apply isTrue
    use b
    rw [Nat.zero_add]
  | a++, b => by
    cases le_dec a b with
    | isTrue h =>
      cases decEq a b with
      | isTrue h_eq =>
        apply isFalse
        intro h_succ_le
        -- If a = b, then h_succ_le : a++ ≤ b becomes a++ ≤ a
        -- This contradicts a < a++
        have h_a_lt_succ : a < a++ := succ_gt a
        have h_succ_ge_a : a++ ≥ a := le_of_lt h_a_lt_succ
        -- From h_eq : a = b and h_succ_le : a++ ≤ b, we get a++ ≤ a
        have h_contra : a++ ≤ a := by
          rw [← h_eq] at h_succ_le
          exact h_succ_le
        -- But a < a++ means a ≤ a++, so we have a++ ≤ a ≤ a++
        have h_a_le_succ : a ≤ a++ := le_of_lt h_a_lt_succ
        -- By antisymmetry: a++ = a
        have h_eq_bad : a++ = a := ge_antisymm h_succ_ge_a h_contra
        -- But this contradicts the fact that a++ ≠ a
        have h_ne : a++ ≠ a := by
          -- This follows from the fact that a < a++
          have h_a_lt_succ : a < a++ := succ_gt a
          exact (ne_of_lt _ _ h_a_lt_succ).symm
        exact h_ne h_eq_bad
      | isFalse h_ne =>
        apply isTrue
        -- If a ≤ b and a ≠ b, then a < b, so a++ ≤ b
        have h_lt : a < b := by
          rw [le_iff_lt_or_eq] at h
          exact h.resolve_right h_ne
        exact (lt_iff_succ_le _ _).mp h_lt
    | isFalse h_not_le =>
      apply isFalse
      intro h_succ_le
      -- If ¬(a ≤ b) but a++ ≤ b, then a < a++ ≤ b implies a ≤ b
      have h_a_lt_succ : a < a++ := succ_gt a
      have h_a_le_b : a ≤ b := ge_trans h_succ_le (le_of_lt h_a_lt_succ)
      exact h_not_le h_a_le_b

instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := Nat.le_dec


/-- (Not from textbook) Nat has the structure of a linear ordering. -/
instance Nat.linearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_le := by
    intro a b
    constructor
    · -- Forward: a < b → a ≤ b ∧ ¬ b ≤ a
      intro h
      constructor
      · exact Nat.le_of_lt h
      · intro hba
        -- We have a < b and b ≤ a, which gives a = b by antisymmetry
        have : a = b := ge_antisymm hba (Nat.le_of_lt h)
        -- But a ≠ b from a < b
        exact Nat.ne_of_lt _ _ h this
    · -- Reverse: a ≤ b ∧ ¬ b ≤ a → a < b
      intro ⟨hab, hnba⟩
      -- Use trichotomy: either a < b, a = b, or a > b
      rcases trichotomous a b with h | h | h
      · exact h
      · -- Case a = b: but then b ≤ a, contradicting ¬ b ≤ a
        exfalso
        apply hnba
        rw [h]
        exact ge_refl _
      · -- Case a > b: but then b ≤ a, contradicting ¬ b ≤ a
        exfalso
        apply hnba
        exact Nat.le_of_lt h
  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total := by
    intro a b
    -- Use trichotomy
    rcases trichotomous a b with h | h | h
    · -- Case a < b: then a ≤ b
      left
      exact Nat.le_of_lt h
    · -- Case a = b: then a ≤ b
      left
      rw [h]
      exact ge_refl _
    · -- Case a > b: then b ≤ a
      right
      exact Nat.le_of_lt h
  toDecidableLE := decidableRel

/-- (Not from textbook) Nat has the structure of an ordered monoid. -/
instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left := by
    intro a b hab c
    exact (add_le_add_left a b c).mp hab

/-- Proposition 2.2.14 (Strong principle of induction) / Exercise 2.2.5
-/
theorem Nat.strong_induction {m₀:Nat} {P: Nat → Prop} (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) : ∀ m, m ≥ m₀ → P m := by
  -- We prove by strong induction that for all k ≥ m₀, P k holds
  -- The key idea is to use regular induction with a stronger inductive hypothesis
  have aux : ∀ n, ∀ m, m₀ ≤ m ∧ m ≤ n → P m := by
    apply induction
    · -- Base case: n = 0
      intro m ⟨hm_ge_m0, hm_le_0⟩
      -- Since m ≤ 0 and m is a natural number, we have m = 0
      have hm_eq_0 : m = 0 := by
        have : m ≥ 0 := by use m; rw [zero_add]
        exact ge_antisymm this hm_le_0
      rw [hm_eq_0] at hm_ge_m0
      rw [hm_eq_0]
      -- Apply the induction principle for m = 0
      apply hind 0 hm_ge_m0
      intro m' ⟨hm'_ge_m0, hm'_lt_0⟩
      -- This is impossible since no natural number is < 0
      exfalso
      have : m' ≥ 0 := by use m'; rw [zero_add]
      have : m' = 0 := ge_antisymm this (le_of_lt hm'_lt_0)
      rw [this] at hm'_lt_0
      exact (ne_of_lt 0 0 hm'_lt_0) rfl

    · -- Inductive step: assume property holds for all m ≤ n, prove for all m ≤ n++
      intro n ih_n
      intro m ⟨hm_ge_m0, hm_le_n_succ⟩
      -- Case analysis: either m ≤ n or m = n++
      by_cases h : m ≤ n
      · -- Case m ≤ n: use inductive hypothesis
        exact ih_n m ⟨hm_ge_m0, h⟩
      · -- Case m > n: then m ≥ n++ and m ≤ n++, so m = n++
        have hm_gt_n : m > n := by
          rw [not_le] at h
          exact h
        have hm_eq_n_succ : m = n++ := by
          have : m ≥ n++ := by
            rw [gt_iff_lt] at hm_gt_n
            rw [lt_iff_succ_le] at hm_gt_n
            exact hm_gt_n
          exact le_antisymm hm_le_n_succ this
        rw [hm_eq_n_succ]
        -- Apply the strong induction principle for m = n++
        -- First we need to show n++ ≥ m₀
        have hn_succ_ge_m0 : n++ ≥ m₀ := by
          rw [← hm_eq_n_succ]
          exact hm_ge_m0
        apply hind (n++) hn_succ_ge_m0
        intro m' ⟨hm'_ge_m0, hm'_lt_n_succ⟩
        -- We need to show P m' where m₀ ≤ m' < n++
        -- Since m' < n++, we have m' ≤ n
        have hm'_le_n : m' ≤ n := by
          -- From m' < n++, we either have m' ≤ n or m' = n++, but the latter is impossible
          by_contra h_not
          -- If ¬(m' ≤ n), then m' > n, so m' ≥ n++
          have : m' > n := by
            rw [not_le] at h_not
            exact h_not
          have : m' ≥ n++ := by
            rw [gt_iff_lt] at this
            rw [lt_iff_succ_le] at this
            exact this
          -- But this contradicts m' < n++
          have : m' ≥ n++ := this
          exact (ne_of_lt _ _ hm'_lt_n_succ) (ge_antisymm this (le_of_lt hm'_lt_n_succ))
        -- Apply the inductive hypothesis
        exact ih_n m' ⟨hm'_ge_m0, hm'_le_n⟩

  -- Now use the auxiliary result
  intro m hm_ge_m0
  exact aux m m ⟨hm_ge_m0, le_refl m⟩

/-- Exercise 2.2.6 (backwards induction) -/
theorem Nat.backwards_induction {n:Nat} {P: Nat → Prop}  (hind: ∀ m, P (m++) → P m) (hn: P n) : ∀ m, m ≤ n → P m := by
  intro m hm_le_n
  -- We'll use induction on n to prove that for all m ≤ n, P(m) holds
  revert hn
  revert hm_le_n
  revert m
  revert n
  apply induction
  · -- Base case: n = 0
    intro m hm_le_0 h0
    -- m ≤ 0 means m = 0
    have : m = 0 := by
      have : m ≥ 0 := by use m; rw [zero_add]
      exact ge_antisymm this hm_le_0
    rw [this]
    exact h0

  · -- Inductive step: assume theorem holds for n, prove for n++
    intro n ih
    intro m hm_le_succ hn_succ
    -- We have m ≤ n++ and P(n++)
    -- By trichotomy, either m ≤ n or m = n++
    rw [le_iff_lt_or_eq] at hm_le_succ
    cases hm_le_succ with
    | inl hm_lt_succ =>
      -- Case m < n++, so m ≤ n
      have hm_le_n : m ≤ n := by
        -- From m < n++, we show m ≤ n
        rcases trichotomous m n with h1 | h2 | h3
        · exact le_of_lt h1
        · rw [h2]
        · -- m > n would imply m ≥ n++, contradicting m < n++
          exfalso
          have : m ≥ n++ := by
            rw [gt_iff_lt] at h3
            rw [lt_iff_succ_le] at h3
            exact h3
          exact (ne_of_lt _ _ hm_lt_succ) (ge_antisymm this (le_of_lt hm_lt_succ))
      -- P(n) follows from P(n++) by the hypothesis
      have hn : P n := hind n hn_succ
      -- Apply induction hypothesis
      exact ih m hm_le_n hn
    | inr hm_eq_succ =>
      -- Case m = n++
      rw [hm_eq_succ]
      exact hn_succ

/-- Exercise 2.2.7 (induction from a starting point) -/
theorem Nat.induction_from {n:Nat} {P: Nat → Prop} (hind: ∀ m, P m → P (m++)) : P n → ∀ m, m ≥ n → P m := by
  intro hn m hm_ge_n
  -- We use strong induction on the "excess" k = m - n
  -- Since m ≥ n, we can write m = n + k for some k

  -- We'll prove this by induction on m itself, but only for m ≥ n
  suffices h : ∀ k, P (n + k) by
    obtain ⟨k, hk⟩ := hm_ge_n
    rw [hk]
    exact h k

  -- Prove by induction on k that P(n + k)
  intro k
  induction k with
  | zero =>
    -- Base case: P(n + 0) = P(n)
    show P (n + 0)
    rw [Nat.add_zero]
    exact hn
  | succ k' ih_k' =>
    -- Inductive step: P(n + k') → P(n + k'++)
    -- We have P(n + k') from ih_k'
    -- We want P(n + k'++) = P((n + k')++)
    rw [add_succ]
    exact hind (n + k') ih_k'


end Chapter2
