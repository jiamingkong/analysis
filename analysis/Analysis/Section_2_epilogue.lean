import Mathlib.Tactic
import Analysis.Section_2_3

/-!
# Analysis I, Chapter 2 epilogue

In this (technical) epilogue, we show that the "Chapter 2" natural numbers `Chapter2.Nat` are
isomorphic in various standard senses to the standard natural numbers `ℕ`.

From this point onwards, `Chapter2.Nat` will be deprecated, and we will use the standard natural
numbers `ℕ` instead.  In particular, one should use the full Mathlib API for `ℕ` for all
subsequent chapters, in lieu of the `Chapter2.Nat` API.

Filling the sorries here requires both the Chapter2.Nat API and the Mathlib API for the standard
natural numbers `ℕ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

In second half of this section we also give a fully axiomatic treatment of the natural numbers
via the Peano axioms. The treatment in the preceding three sections was only partially
axiomatic, because we used a specific construction `Chapter2.Nat` of the natural numbers that was
an inductive type, and used that inductive type to construct a recursor.  Here, we give some
exercises to show how one can accomplish the same tasks directly from the Peano axioms, without
knowing the specific implementation of the natural numbers.
-/

abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | zero => 0
  | succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := toNat
  invFun n := (n:Chapter2.Nat)
  left_inv n := by
    induction' n with n hn
    . rfl
    simp [succ_toNat, hn]
    symm
    exact succ_eq_add_one _
  right_inv n := by
    induction' n with n hn
    . rfl
    simp [←succ_eq_add_one]
    exact hn

abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := by
    intro n m
    induction' n with n ih
    · -- zero case: (zero + m).toNat = zero.toNat + m.toNat
      simp [equivNat]
      have zero_add_rfl : (zero + m).toNat = m.toNat := by
        induction' m with m'
        . rfl
        . simp [succ_toNat]
      rw [zero_add_rfl]

    · -- succ case: (succ n + m).toNat = (succ n).toNat + m.toNat
      simp [equivNat]
      simp [equivNat] at ih
      rw [succ_add, succ_toNat, succ_toNat, ih]
      ring
  map_mul' := by
    intro n m
    simp [equivNat]
    induction' n with n ih
    . simp [zero_mul]
    . rw [succ_mul, succ_toNat]
      -- We need: (n * m + m).toNat = (n.toNat + 1) * m.toNat
      -- First show that toNat preserves addition
      have add_toNat : ∀ a b : Chapter2.Nat, (a + b).toNat = a.toNat + b.toNat := by
        intro a b
        induction' a with a' ha'
        . -- zero case: (zero + b).toNat = b.toNat
          have zero_add_rfl : (zero + b).toNat = b.toNat := by
            induction' b with m'
            . rfl
            . simp [succ_toNat]
          simp [toNat, zero_add, zero_add_rfl]
        . rw [succ_add, succ_toNat, succ_toNat, ha']
          ring
      rw [add_toNat, ih]
      ring
  map_le_map_iff' := by
    intro n m
    simp [equivNat]
    -- We need to prove: n.toNat ≤ m.toNat ↔ n ≤ m
    -- Both orders are defined as ∃ d, larger = smaller + d
    -- We use the fact that toNat preserves addition (proven in map_mul')
    have add_toNat : ∀ a b : Chapter2.Nat, (a + b).toNat = a.toNat + b.toNat := by
      intro a b
      induction' a with a' ha'
      . -- zero case: (zero + b).toNat = b.toNat
        have zero_add_rfl : (zero + b).toNat = b.toNat := by
          induction' b with m'
          . rfl
          . simp [succ_toNat]
        simp [toNat, zero_add, zero_add_rfl]
      . rw [succ_add, succ_toNat, succ_toNat, ha']
        ring
    constructor
    · -- Forward: n.toNat ≤ m.toNat → n ≤ m
      intro h
      -- h : n.toNat ≤ m.toNat means ∃ d, m.toNat = n.toNat + d
      rw [Nat.le_iff_exists_add] at h
      obtain ⟨d, hd⟩ := h
      -- Convert d back to Chapter2.Nat and show m = n + (d : Chapter2.Nat)
      use (d : Chapter2.Nat)
      apply equivNat.injective
      simp [equivNat]
      rw [add_toNat, hd]
    · -- Reverse: n ≤ m → n.toNat ≤ m.toNat
      intro h
      -- h : n ≤ m means ∃ e : Chapter2.Nat, m = n + e
      obtain ⟨e, he⟩ := h
      rw [Nat.le_iff_exists_add]
      use e.toNat
      rw [← he, add_toNat]


lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) : n.toNat ^ m.toNat = n^m := by
  induction n
  . simp [toNat, toNat]


/-- The Peano axioms for an abstract type `Nat` -/
@[ext]
class PeanoAxioms where
  Nat : Type
  zero : Nat -- Axiom 2.1
  succ : Nat → Nat -- Axiom 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Axiom 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Axiom 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Axiom 2.5

namespace PeanoAxioms

/-- The Chapter 2 natural numbers obey the Peano axioms. -/
def Chapter2.Nat : PeanoAxioms where
  Nat := _root_.Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

/-- The Mathlib natural numbers obey the Peano axioms. -/
def Mathlib.Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast  := by
  intro n m h
  induction' n with n' ih generalizing m
  · -- Base case: n = 0
    cases' m with m'
    · rfl  -- 0 = 0
    · -- contradiction: natCast 0 = natCast (succ m'), but natCast 0 = zero and natCast (succ m') = succ (natCast m')
      exfalso
      simp [natCast] at h
      exact P.succ_ne (natCast P m') h.symm
  · -- Inductive case: n = succ n'
    cases' m with m'
    · -- contradiction: natCast (succ n') = natCast 0
      exfalso
      simp [natCast] at h
      exact P.succ_ne (natCast P n') h
    · -- natCast (succ n') = natCast (succ m') implies succ n' = succ m'
      simp [natCast] at h
      have : natCast P n' = natCast P m' := P.succ_cancel h
      have : n' = m' := ih this
      rw [this]

theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  intro x
  -- We use induction on x
  apply P.induction (fun x => ∃ n : ℕ, natCast P n = x)
  · -- Base case: x = zero
    use 0
  · -- Inductive case: if there exists n such that natCast P n = y, then there exists m such that natCast P m = succ y
    intro y hy
    obtain ⟨n, hn⟩ := hy
    use n + 1
    simp [natCast, hn]

/-- The notion of an equivalence between two structures obeying the Peano axioms -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

abbrev Equiv.symm (equiv : Equiv P Q) : Equiv Q P where
  equiv := equiv.equiv.symm
  equiv_zero := by
    have h := equiv.equiv_zero
    rw [← h]
    exact Equiv.symm_apply_apply equiv.equiv P.zero
  equiv_succ n := by
    have h := equiv.equiv_succ (equiv.equiv.symm n)
    rw [Equiv.apply_symm_apply] at h
    rw [← h]
    rw [Equiv.symm_apply_apply]

abbrev Equiv.trans (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by
    rw [Equiv.trans_apply]
    rw [equiv1.equiv_zero]
    rw [equiv2.equiv_zero]
  equiv_succ n := by
    simp [Equiv.trans_apply, equiv1.equiv_succ, equiv2.equiv_succ]

/-- Note: I suspect that this construction is non-computable and requires classical logic. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib.Nat P where
  equiv := {
    toFun := P.natCast
    invFun := fun x => by
      -- Since natCast is surjective, we can use choice to pick a preimage
      classical
      exact Classical.choose (natCast_surjective P x)
    left_inv := by
      intro n
      classical
      exact natCast_injective P (Classical.choose_spec (natCast_surjective P (P.natCast n)))
    right_inv := by
      intro x
      classical
      exact Classical.choose_spec (natCast_surjective P x)
  }
  equiv_zero := by rfl
  equiv_succ n := by rfl

noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q :=
  (Equiv.fromNat P).symm.trans (Equiv.fromNat Q)

theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) : equiv1 = equiv2 := by
  -- We need to show that the underlying equivalences are equal
  have h : equiv1.equiv = equiv2.equiv := by
    ext x
    -- We prove by induction on x that equiv1.equiv x = equiv2.equiv x
    apply P.induction (fun x => equiv1.equiv x = equiv2.equiv x)
    · -- Base case: x = zero
      rw [equiv1.equiv_zero, equiv2.equiv_zero]
    · -- Inductive case: x = succ y
      intro y hy
      rw [equiv1.equiv_succ, equiv2.equiv_succ, hy]
  -- injectivity of the equivalence gives us the result
  sorry

/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  -- We prove uniqueness first, then existence follows from the axiom of choice

  -- Uniqueness: any two functions satisfying the conditions are equal
  have uniqueness : ∀ a1 a2 : P.Nat → P.Nat,
    (a1 P.zero = c ∧ ∀ n, a1 (P.succ n) = f n (a1 n)) →
    (a2 P.zero = c ∧ ∀ n, a2 (P.succ n) = f n (a2 n)) →
    a1 = a2 := by
    intro a1 a2 h1 h2
    ext x
    apply P.induction (fun x => a1 x = a2 x)
    · -- Base case: a1 P.zero = a2 P.zero
      rw [h1.1, h2.1]
    · -- Inductive case: if a1 y = a2 y, then a1 (P.succ y) = a2 (P.succ y)
      intro y hy
      rw [h1.2, h2.2, hy]

  -- Existence: we construct a function using the equivalence with ℕ
  classical

  -- Define helper function on natural numbers
  let helper : ℕ → P.Nat :=
    Nat.rec c (fun n acc => f (P.natCast n) acc)

  -- Define our function using the surjectivity of natCast
  let a : P.Nat → P.Nat := fun x =>
    helper (Classical.choose (natCast_surjective P x))

  use a
  constructor
  · -- Prove a satisfies the required properties
    constructor
    · -- a P.zero = c
      unfold a
      have zero_choice : Classical.choose (natCast_surjective P P.zero) = 0 := by
        apply natCast_injective P
        have spec := Classical.choose_spec (natCast_surjective P P.zero)
        rw [spec]
        -- natCast P 0 = P.zero by definition
      rw [zero_choice]
      -- helper 0 = c by definition of Nat.rec
      rfl
    · -- ∀ n, a (P.succ n) = f n (a n)
      intro n
      unfold a
      sorry

  · -- Uniqueness follows from our lemma
    intro a' h'
    have a_props : a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
      constructor
      · -- We proved this above
        unfold a
        have zero_choice : Classical.choose (natCast_surjective P P.zero) = 0 := by
          apply natCast_injective P
          have spec := Classical.choose_spec (natCast_surjective P P.zero)
          rw [spec]
        rw [zero_choice]
        rfl
      · -- This follows from the construction, but we used sorry above
        sorry
    sorry

end PeanoAxioms
