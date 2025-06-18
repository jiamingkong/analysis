import Mathlib.Tactic
import Analysis.Section_3_1

set_option linter.unusedVariables false

/-!
# Analysis I, Section 3.2

In this section we set up a version of Zermelo-Frankel set theory (with atoms) that tries to be
as faithful as possible to the original text of Analysis I, Section 3.1. All numbering refers to
the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

This section is mostly optional, though it does make explicit the axiom of foundation which is
used in a minor role in an exercise in Section 3.5.

Main constructions and results of this section:

- Russell's paradox (ruling out the axiom of universal specification)
- The axiom of regularity (foundation) - an axiom designed to avoid Russell's paradox
--/

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/-- Axiom 3.8 (Universal specification) -/
abbrev axiom_of_universal_specification : Prop :=
  ∀ P : Object → Prop, ∃ A : Set, ∀ x : Object, x ∈ A ↔ P x

theorem Russells_paradox : ¬ axiom_of_universal_specification := by
  -- this proof is written to follow the structure of the original text.
  intro h
  set P : Object → Prop := fun x ↦ ∃ X:Set, x = X ∧ x ∉ X
  obtain ⟨Ω, hΩ⟩ := h P
  by_cases h: (Ω:Object) ∈ Ω
  . have : P (Ω:Object) := (hΩ _).mp h
    obtain ⟨ Ω', ⟨ hΩ1, hΩ2⟩ ⟩ := this
    simp at hΩ1
    rw [←hΩ1] at hΩ2
    contradiction
  have : P (Ω:Object) := by use Ω
  replace this := (hΩ _).mpr this
  contradiction

/-- Axiom 3.9 (Regularity ) -/
theorem SetTheory.Set.axiom_of_regularity {A:Set} (h: A ≠ ∅) :
    ∃ x:A, ∀ S:Set, x.val = S → Disjoint S A := by
  obtain ⟨ x, h, h' ⟩ := SetTheory.regularity_axiom A (nonempty_def h)
  use ⟨x, h⟩
  intro S hS
  specialize h' S hS
  rw [disjoint_iff, eq_empty_iff_forall_notMem]
  contrapose! h'
  simp at h'
  obtain ⟨ y, h1, h2 ⟩ := h'
  exact ⟨ y, h2, h1 ⟩

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the empty set.
-/
theorem SetTheory.Set.emptyset_exists (h: axiom_of_universal_specification):
    ∃ (X:Set), ∀ x, x ∉ X := by
  -- Use the axiom with a property that's never satisfied
  obtain ⟨X, hX⟩ := h (fun x ↦ False)
  use X
  intro x
  intro hx
  have : False := (hX x).mp hx
  exact this

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the singleton set.
-/
theorem SetTheory.Set.singleton_exists (h: axiom_of_universal_specification) (x:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x := by
  -- Use the axiom with the property "y = x"
  obtain ⟨X, hX⟩ := h (fun y ↦ y = x)
  use X

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the pair set.
-/
theorem SetTheory.Set.pair_exists (h: axiom_of_universal_specification) (x₁ x₂:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x₁ ∨ y = x₂ := by
  -- Use the axiom with the property "y = x₁ ∨ y = x₂"
  exact h (fun y ↦ y = x₁ ∨ y = x₂)

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the union operation.
-/
theorem SetTheory.Set.union_exists (h: axiom_of_universal_specification) (A B:Set):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ z ∈ A ∨ z ∈ B := by
  -- Use the axiom with the property "z ∈ A ∨ z ∈ B"
  exact h (fun z ↦ z ∈ A ∨ z ∈ B)

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the specify operation.
-/
theorem SetTheory.Set.specify_exists (h: axiom_of_universal_specification) (A:Set) (P: A → Prop):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ ∃ h : z ∈ A, P ⟨ z, h ⟩ := by
  -- Use the axiom with the property "∃ h : z ∈ A, P ⟨ z, h ⟩"
  exact h (fun z ↦ ∃ h : z ∈ A, P ⟨ z, h ⟩)

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the specify operation.
-/
theorem SetTheory.Set.replace_exists (h: axiom_of_universal_specification) (A:Set)
  (P: A → Object → Prop) (hP: ∀ x y y', P x y ∧ P x y' → y = y') :
    ∃ (Z:Set), ∀ y, y ∈ Z ↔ ∃ a : A, P a y := by
  -- Use the axiom with the property "∃ a : A, P a y"
  exact h (fun y ↦ ∃ a : A, P a y)

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_self (A:Set) : (A:Object) ∉ A := by
  -- Use axiom of regularity directly
  by_contra h
  have h_nonempty : A ≠ ∅ := SetTheory.Set.nonempty_of_inhabited h
  obtain ⟨x, hdisj⟩ := SetTheory.Set.axiom_of_regularity h_nonempty
  -- x is an element of A. If x.val = A, then A should be disjoint from A, which is impossible
  by_cases hx : x.val = (A:Object)
  · -- Case: x.val = A
    specialize hdisj A hx
    rw [SetTheory.Set.disjoint_iff] at hdisj
    -- But A ∈ A ∩ A since we assumed A ∈ A
    have contra : (A:Object) ∈ A ∩ A := by
      rw [SetTheory.Set.mem_inter]
      exact ⟨h, h⟩
    rw [hdisj] at contra
    exact SetTheory.Set.not_mem_empty (A:Object) contra
  · -- Case: x.val ≠ A
    -- We still get a contradiction because x must satisfy the regularity condition
    -- But the key insight is that the regularity axiom applied to any nonempty set
    -- with a self-membership will lead to a contradiction through the chosen element
    -- Since A contains itself, we can construct the contradiction more directly
    have singleton_A_nonempty : ({(A:Object)}:Set) ≠ ∅ := by
      apply SetTheory.Set.nonempty_of_inhabited
      rw [SetTheory.Set.mem_singleton]
    obtain ⟨y, hdisj_sing⟩ := SetTheory.Set.axiom_of_regularity singleton_A_nonempty
    have y_is_A : y.val = (A:Object) := by
      have y_mem : y.val ∈ ({(A:Object)}:Set) := y.property
      rw [SetTheory.Set.mem_singleton] at y_mem
      exact y_mem
    specialize hdisj_sing A y_is_A
    rw [SetTheory.Set.disjoint_iff] at hdisj_sing
    have contra : (A:Object) ∈ A ∩ ({(A:Object)}:Set) := by
      rw [SetTheory.Set.mem_inter]
      constructor
      · exact h
      · rw [SetTheory.Set.mem_singleton]
    rw [hdisj_sing] at contra
    exact SetTheory.Set.not_mem_empty (A:Object) contra

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_mem (A B:Set) : (A:Object) ∉ B ∨ (B:Object) ∉ A := by
  -- Use axiom of regularity applied to the pair {A, B}
  by_contra h
  push_neg at h
  obtain ⟨hAB, hBA⟩ := h
  -- Consider the pair set {A, B} (as objects)
  set P := ({(A:Object), (B:Object)}:Set)
  have hP_nonempty : P ≠ ∅ := by
    apply nonempty_of_inhabited
    rw [mem_pair]
    left; rfl
  -- Apply regularity to get an element x of P such that x is disjoint from P
  obtain ⟨x, hdisj⟩ := axiom_of_regularity hP_nonempty
  -- x.val is either A or B
  have x_mem : x.val ∈ P := x.property
  rw [mem_pair] at x_mem
  cases x_mem with
  | inl hxA =>
    -- Case: x.val = A
    -- Apply disjointness: A and P should be disjoint
    specialize hdisj A hxA
    rw [disjoint_iff] at hdisj
    -- But B ∈ A (from hBA) and B ∈ P, so B ∈ A ∩ P
    have contra : (B:Object) ∈ A ∩ P := by
      rw [mem_inter]
      constructor
      · exact hBA
      · rw [mem_pair]; right; rfl
    rw [hdisj] at contra
    exact not_mem_empty (B:Object) contra
  | inr hxB =>
    -- Case: x.val = B
    -- Apply disjointness: B and P should be disjoint
    specialize hdisj B hxB
    rw [disjoint_iff] at hdisj
    -- But A ∈ B (from hAB) and A ∈ P, so A ∈ B ∩ P
    have contra : (A:Object) ∈ B ∩ P := by
      rw [mem_inter]
      constructor
      · exact hAB
      · rw [mem_pair]; left; rfl
    rw [hdisj] at contra
    exact not_mem_empty (A:Object) contra

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.univ_imp (U: Set) (hU: ∀ x, x ∈ U) :
    axiom_of_universal_specification := by
  -- If a universal set exists, then universal specification holds
  intro P
  use U.specify (fun x ↦ P x.val)
  intro x
  rw [SetTheory.Set.specification_axiom'']
  constructor
  · intro ⟨_, hP⟩
    exact hP
  · intro hP
    exact ⟨hU x, hP⟩

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.no_univ : ¬ ∃ (U:Set), ∀ (x:Object), x ∈ U := by
  -- This follows from Russell's paradox
  intro ⟨U, hU⟩
  have : axiom_of_universal_specification := univ_imp U hU
  exact Russells_paradox this


end Chapter3
