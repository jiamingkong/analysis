import Mathlib.Tactic
set_option linter.unusedVariables false
/-!
# Analysis I, Section 3.1

In this section we set up a version of Zermelo-Frankel set theory (with atoms) that tries to be
as faithful as possible to the original text of Analysis I, Section 3.1. All numbering refers to
the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- A type `Chapter3.SetTheory.Set` of sets
- A type `Chapter3.SetTheory.Object` of objects
- An axiom that every set is (or can be coerced into) an object
- The empty set `∅`, singletons `{y}`, and pairs `{y,z}` (and more general finite tuples), with
  their attendant axioms
- Pairwise union `X ∪ Y`, and their attendant axioms
- Coercion of a set `A` to its associated type `A.toSubtype`, which is a subtype of `Object`, and
  basic API.  (This is a technical construction needed to make the Zermelo-Frankel set theory
  compatible with the dependent type theory of Lean.)
- The specification `A.specify P` of a set `A` and a predicate `P: A.toSubtype → Prop` to the
  subset of elements of `A` obeying `P`, and the axiom of specification.
  TODO: somehow implement set builder elaboration for this.

- The replacement `A.replace hP` of a set `A` via a predicate
  `P: A.toSubtype → Object → Prop` obeying a uniqueness condition
  `∀ x y y', P x y ∧ P x y' → y = y'`, and the axiom of replacement.
- A bijective correspondence between the Mathlib natural numbers `ℕ` and a set
  `Chapter3.Nat : Chapter3.Set` (the axiom of infinity).
- Axioms of regularity, power set, and union (used in later sections of this chapter, but not
  required here)
- Connections with Mathlib's notion of a set

The other axioms of Zermelo-Frankel set theory are discussed in later sections.

Some technical notes:
- Mathlib of course has its own notion of a `Set`, which is not compatible with the notion
  `Chapter3.Set` defined here, though we will try to make the notations match as much as
  possible.  This causes some notational conflict: for instance, one may need to explicitly
  specify `(∅:Chapter3.Set)` instead of just `∅` to indicate that one is using the `Chapter3.Set`
  version of the empty set, rather than the Mathlib version of the empty set, and similarly for
  other notation defined here.
- In Analysis I, we chose to work with an "impure" set theory, in which there could be more
  `Object`s than just `Set`s.  In the type theory of Lean, this requires treating `Chapter3.Set`
  and `Chapter3.Object` as distinct types. Occasionally this means we have to use a coercion
  `X.toObject` of a `Chapter3.Set` `X` to make into a `Chapter3.Object`: this is mostly needed
  when manipulating sets of sets.
- After this chapter is concluded, the notion of a `Chapter3.SetTheory.Set` will be deprecated in
  favor of the standard Mathlib notion of a `Set` (or more precisely of the type `Set X` of a set
  in a given type `X`).  However, due to various technical incompatibilities between set theory
  and type theory, we will not attempt to create any sort of equivalence between these two
  notions of sets. (As such, this makes this entire chapter optional from the point of view of
  the rest of the book, though we retain it for pedagogical purposes.)
-/


namespace Chapter3

/-- Some of the axioms of Zermelo-Frankel theory with atoms  -/
class SetTheory where
  Set : Type -- Axiom 3.1
  Object : Type -- Axiom 3.1
  set_to_object : Set ↪ Object -- Axiom 3.1
  mem : Object → Set → Prop -- Axiom 3.1
  extensionality X Y : (∀ x, mem x X ↔ mem x Y) → X = Y -- Axiom 3.2
  emptyset: Set -- Axiom 3.3
  emptyset_mem x : ¬ mem x emptyset -- Axiom 3.3
  singleton : Object → Set -- Axiom 3.4
  singleton_axiom x y : mem x (singleton y) ↔ x = y -- Axiom 3.4
  union_pair : Set → Set → Set -- Axiom 3.5
  union_pair_axiom X Y x : mem x (union_pair X Y) ↔ (mem x X ∨ mem x Y) -- Axiom 3.5
  specify A (P: Subtype (mem . A) → Prop) : Set -- Axiom 3.6
  specification_axiom A (P: Subtype (mem . A) → Prop) :
    (∀ x, mem x (specify A P) → mem x A) ∧ ∀ x, mem x.val (specify A P) ↔ P x -- Axiom 3.6
  replace A (P: Subtype (mem . A) → Object → Prop)
    (hP: ∀ x y y', P x y ∧ P x y' → y = y') : Set -- Axiom 3.7
  replacement_axiom A (P: Subtype (mem . A) → Object → Prop)
    (hP: ∀ x y y', P x y ∧ P x y' → y = y') : ∀ y, mem y (replace A P hP) ↔ ∃ x, P x y -- Axiom 3.7
  nat : Set -- Axiom 3.8
  nat_equiv : ℕ ≃ Subtype (mem . nat) -- Axiom 3.8
  regularity_axiom A (hA : ∃ x, mem x A) :
    ∃ x, mem x A ∧ ∀ S, x = set_to_object S → ¬ ∃ y, mem y A ∧ mem y S -- Axiom 3.9
  pow : Set → Set → Set -- Axiom 3.11
  function_to_object (X: Set) (Y: Set) :
    (Subtype (mem . X) → Subtype (mem . Y)) ↪ Object -- Axiom 3.11
  power_set_axiom (X: Set) (Y: Set) (F:Object) :
    mem F (pow X Y) ↔ ∃ f: Subtype (mem . Y) → Subtype (mem . X),
    function_to_object Y X f = F -- Axiom 3.11
  union : Set → Set -- Axiom 3.12
  union_axiom A x : mem x (union A) ↔ ∃ S, mem x S ∧ mem (set_to_object S) A -- Axiom 3.12

export SetTheory (Set Object)

-- This instance implicitly imposes (some of) the axioms of Zermelo-Frankel set theory with atoms.
variable [SetTheory]


/-- Definition 3.1.1 (objects can be elements of sets) -/
instance objects_mem_sets : Membership Object Set where
  mem X x := SetTheory.mem x X

/-- Axiom 3.1 (Sets are objects)-/
instance sets_are_objects : Coe Set Object where
  coe X := SetTheory.set_to_object X

abbrev SetTheory.Set.toObject (X:Set) : Object := X

/-- Axiom 3.1 (Sets are objects)-/
theorem SetTheory.Set.coe_eq {X Y:Set} (h: X.toObject = Y.toObject) : X = Y :=
  SetTheory.set_to_object.inj' h

/-- Axiom 3.1 (Sets are objects)-/
@[simp]
theorem SetTheory.Set.coe_eq_iff (X Y:Set) : X.toObject = Y.toObject ↔  X = Y := by
  constructor
  . exact coe_eq
  intro h; subst h; rfl

/-- Axiom 3.2 (Equality of sets)-/
abbrev SetTheory.Set.ext {X Y:Set} (h: ∀ x, x ∈ X ↔ x ∈ Y) : X = Y := SetTheory.extensionality _ _ h

/-- Axiom 3.2 (Equality of sets)-/
theorem SetTheory.Set.ext_iff (X Y: Set) : X = Y ↔ ∀ x, x ∈ X ↔ x ∈ Y := by
  constructor
  . intro h; subst h; simp
  . intro h; apply ext; exact h

instance SetTheory.Set.instEmpty : EmptyCollection Set where
  emptyCollection := SetTheory.emptyset

/--
  Axiom 3.3 (empty set).
  Note: one may have to explicitly cast ∅ to Set due to Mathlib's existing set theory notation.
-/
@[simp]
theorem SetTheory.Set.not_mem_empty : ∀ x, x ∉ (∅:Set) := SetTheory.emptyset_mem

/-- Empty set is unique -/
theorem SetTheory.Set.eq_empty_iff_forall_notMem {X:Set} : X = ∅ ↔ (∀ x, ¬ x ∈ X) := by
  constructor
  . intro h; subst h; simp
  . intro h; apply ext; intro x; simp [h x]

/-- Empty set is unique -/
theorem SetTheory.Set.empty_unique : ∃! (X:Set), ∀ x, x ∉ X := by
  use ∅
  constructor
  · -- existence: empty set satisfies the property
    exact not_mem_empty
  · -- uniqueness: any other set with this property equals empty set
    intro Y hY
    apply ext
    intro x
    simp [not_mem_empty, hY x]

/-- Lemma 3.1.5 (Single choice) -/
lemma SetTheory.Set.nonempty_def {X:Set} (h: X ≠ ∅) : ∃ x, x ∈ X := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have claim (x:Object) : x ∈ X ↔ x ∈ (∅:Set) := by
    simp [this, not_mem_empty]
  replace claim := ext claim
  contradiction

theorem SetTheory.Set.nonempty_of_inhabited {X:Set} {x:Object} (h:x ∈ X) : X ≠ ∅ := by
  contrapose! h
  rw [eq_empty_iff_forall_notMem] at h
  exact h x

instance SetTheory.Set.instSingleton : Singleton Object Set where
  singleton := SetTheory.singleton

/--
  Axiom 3.3(a) (singleton).
  Note one may have to explicitly cast {a} to Set due to Mathlib's existing set theory notation.
-/
@[simp]
theorem SetTheory.Set.mem_singleton (x a:Object) : x ∈ ({a}:Set) ↔ x = a := by
  exact SetTheory.singleton_axiom x a


instance SetTheory.Set.instUnion : Union Set where
  union := SetTheory.union_pair

/-- Axiom 3.4 (Pairwise union)-/
@[simp]
theorem SetTheory.Set.mem_union (x:Object) (X Y:Set) : x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y) :=
  SetTheory.union_pair_axiom X Y x

instance SetTheory.Set.instInsert : Insert Object Set where
  insert x X := {x} ∪ X

/-- Axiom 3.3(b) (pair).  Note that one often has to cast {a,b} to Set -/
theorem SetTheory.Set.pair_eq (a b:Object) : ({a,b}:Set) = {a} ∪ {b} := by rfl

/-- Axiom 3.3(b) (pair).  Note that one often has to cast {a,b} to Set -/
@[simp]
theorem SetTheory.Set.mem_pair (x a b:Object) : x ∈ ({a,b}:Set) ↔ (x = a ∨ x = b) := by
  simp [pair_eq, mem_union, mem_singleton]

@[simp]
theorem SetTheory.Set.mem_triple (x a b:Object) : x ∈ ({a,b,c}:Set) ↔ (x = a ∨ x = b ∨ x = c) := by
  simp [Insert.insert, mem_union, mem_singleton]

/-- Remark 3.1.8 -/
theorem SetTheory.Set.singleton_uniq (a:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a := by
  use {a}
  constructor
  . -- existence: singleton set satisfies the property
    intro x; simp [mem_singleton]
  . -- uniqueness: any other set with this property equals the singleton set
    intro X hX
    apply ext
    intro x
    simp [mem_singleton, hX x]
    -- Note: this proof is written to follow the structure of the original text.
    -- The `simp` tactic is used to simplify the goal to a form that can be solved by `ext`.

/-- Remark 3.1.8 -/
theorem SetTheory.Set.pair_uniq (a b:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a ∨ x = b := by
  use {a,b}
  constructor
  . -- existence: pair set satisfies the property
    intro x; simp [mem_pair]
  . -- uniqueness: any other set with this property equals the pair set
    intro X hX
    apply ext
    intro x
    simp [mem_pair, hX x]
    -- Note: this proof is written to follow the structure of the original text.
    -- The `simp` tactic is used to simplify the goal to a form that can be solved by `ext`.

/-- Remark 3.1.8 -/
theorem SetTheory.Set.pair_comm (a b:Object) : ({a,b}:Set) = {b,a} := by
  -- this proof is written to follow the structure of the original text.
  apply ext
  intro x
  constructor
  . intro hx
    rw [mem_pair] at hx
    rcases hx with case1 | case2
    . rw [mem_pair]; tauto
    rw [mem_pair]; tauto
  intro hx
  rw [mem_pair] at hx
  rcases hx with case1 | case2
  . rw [mem_pair]; tauto
  rw [mem_pair]; tauto

/-- Remark 3.1.8 -/
theorem SetTheory.Set.pair_self (a:Object) : ({a,a}:Set) = {a} := by
  -- this proof is written to follow the structure of the original text.
  apply ext
  intro x
  constructor
  . intro hx
    rw [mem_pair] at hx
    rcases hx with case1 | case2
    . rw [mem_singleton]; tauto
    rw [mem_singleton]; tauto
  intro hx
  rw [mem_singleton] at hx
  simp [hx]

/-- Exercise 3.1.1 -/
theorem SetTheory.Set.pair_eq_pair {a b c d:Object} (h: ({a,b}:Set) = {c,d}) : a = c ∧ b = d ∨ a = d ∧ b = c := by
  -- Since {a,b} = {c,d}, by extensionality, they have the same elements
  -- In particular, a ∈ {a,b} = {c,d}, so a = c or a = d
  have ha : a ∈ ({a,b}:Set) := by simp
  rw [h] at ha
  simp at ha  -- ha : a = c ∨ a = d
  -- Similarly, b ∈ {a,b} = {c,d}, so b = c or b = d
  have hb : b ∈ ({a,b}:Set) := by simp
  rw [h] at hb
  simp at hb  -- hb : b = c ∨ b = d
  -- Also, c ∈ {c,d} = {a,b}, so c = a or c = b
  have hc : c ∈ ({c,d}:Set) := by simp
  rw [←h] at hc
  simp at hc  -- hc : c = a ∨ c = b
  -- And d ∈ {c,d} = {a,b}, so d = a or d = b
  have hd : d ∈ ({c,d}:Set) := by simp
  rw [←h] at hd
  simp at hd  -- hd : d = a ∨ d = b
  -- Now we do case analysis
  cases ha with
  | inl hac => -- Case: a = c
    cases hb with
    | inl hbc => -- Case: a = c and b = c
      -- Then a = b = c, so from hd we get d = a or d = b, hence d = c
      -- So we have a = b = c = d, which means a = c and b = d
      left
      constructor
      · exact hac
      · -- We need to show b = d
        -- We have a = c and b = c, so a = b
        have hab : a = b := by rw [hac, hbc]
        -- From hd: d = a ∨ d = b, and since a = b, we get d = a = b
        cases hd with
        | inl hda => rw [←hab, hda]
        | inr hdb => exact hdb.symm
    | inr hbd => -- Case: a = c and b = d
      left
      exact ⟨hac, hbd⟩
  | inr had => -- Case: a = d
    cases hb with
    | inl hbc => -- Case: a = d and b = c
      right
      exact ⟨had, hbc⟩
    | inr hbd => -- Case: a = d and b = d
      -- Then a = b = d, so from hc we get c = a or c = b, hence c = d
      -- So we have a = b = c = d, which means a = d and b = c
      right
      constructor
      · exact had
      · -- We need to show b = c
        -- We have a = d and b = d, so a = b
        have hab : a = b := by rw [had, hbd]
        -- From hc: c = a ∨ c = b, and since a = b, we get c = a = b
        cases hc with
        | inl hca => rw [←hab, ←hca]
        | inr hcb => exact hcb.symm

abbrev SetTheory.Set.empty : Set := ∅
abbrev SetTheory.Set.singleton_empty : Set := {empty.toObject}
abbrev SetTheory.Set.pair_empty : Set := {empty.toObject, singleton_empty.toObject}

/-- Exercise 3.1.2-/
theorem SetTheory.Set.emptyset_neq_singleton : empty ≠ singleton_empty := by
  intro h
  -- singleton_empty contains empty.toObject
  have : empty.toObject ∈ singleton_empty := by simp
  -- If empty = singleton_empty, then empty.toObject ∈ empty
  rw [←h] at this
  -- But nothing is in the empty set, contradiction
  exact not_mem_empty empty.toObject this

/-- Exercise 3.1.2-/
theorem SetTheory.Set.emptyset_neq_pair : empty ≠ pair_empty := by
  intro h
  -- pair_empty contains empty.toObject
  have : empty.toObject ∈ pair_empty := by simp
  -- If empty = pair_empty, then empty.toObject ∈ empty
  rw [←h] at this
  -- But nothing is in the empty set, contradiction
  exact not_mem_empty empty.toObject this

/-- Exercise 3.1.2-/
theorem SetTheory.Set.singleton_empty_neq_pair : singleton_empty ≠ pair_empty := by
  -- We'll show that pair_empty has an element that singleton_empty doesn't have
  intro h
  -- First, establish that empty ≠ singleton_empty (which we already proved)
  have neq : empty ≠ singleton_empty := emptyset_neq_singleton
  -- This means empty.toObject ≠ singleton_empty.toObject by injectivity
  have neq_obj : empty.toObject ≠ singleton_empty.toObject := by
    intro contra
    exact neq (coe_eq contra)
  -- Now, singleton_empty.toObject ∈ pair_empty
  have in_pair : singleton_empty.toObject ∈ pair_empty := by
    rw [pair_empty, mem_pair]
    right
    rfl
  -- If singleton_empty = pair_empty, then singleton_empty.toObject ∈ singleton_empty
  rw [←h] at in_pair
  -- But singleton_empty only contains empty.toObject
  rw [singleton_empty, mem_singleton] at in_pair
  -- So singleton_empty.toObject = empty.toObject, contradicting neq_obj
  exact neq_obj in_pair.symm

/-- Remark 3.1.11.  (These results can be proven either by a direct rewrite, or by using extensionality.) -/
theorem SetTheory.Set.union_congr_left (A A' B:Set) (h: A = A') : A ∪ B = A' ∪ B := by
  rw [h]

/-- Remark 3.1.11.  (These results can be proven either by a direct rewrite, or by using extensionality.) -/
theorem SetTheory.Set.union_congr_right (A B B':Set) (h: B = B') : A ∪ B = A ∪ B' := by
  rw [h]

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.singleton_union_singleton (a b:Object) : ({a}:Set) ∪ ({b}:Set) = {a,b} := by
  rfl  -- This is true by definition of the pair notation

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.union_comm (A B:Set) : A ∪ B = B ∪ A := by
  apply ext
  intro x
  simp [mem_union]
  constructor
  · intro h; cases h with
    | inl ha => right; exact ha
    | inr hb => left; exact hb
  · intro h; cases h with
    | inl hb => right; exact hb
    | inr ha => left; exact ha

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.union_assoc (A B C:Set) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  -- this proof is written to follow the structure of the original text.
  apply ext
  intro x
  constructor
  . intro hx
    rw [mem_union] at hx
    rcases hx with case1 | case2
    . rw [mem_union] at case1
      rcases case1 with case1a | case1b
      . rw [mem_union]; tauto
      have : x ∈ B ∪ C := by rw [mem_union]; tauto
      rw [mem_union]; tauto
    have : x ∈ B ∪ C := by rw [mem_union]; tauto
    rw [mem_union]; tauto
  . intro hx
    rw [mem_union] at hx
    rcases hx with case1 | case2
    . rw [mem_union]; left; rw [mem_union]; tauto
    rw [mem_union] at case2
    rcases case2 with case2a | case2b
    . rw [mem_union]; left; rw [mem_union]; tauto
    rw [mem_union]; tauto

/-- Proposition 3.1.27(c) -/
theorem SetTheory.Set.union_self (A:Set) : A ∪ A = A := by
  apply ext
  intro x
  simp [mem_union]

/-- Proposition 3.1.27(a) -/
theorem SetTheory.Set.union_empty (A:Set) : A ∪ ∅ = A := by
  apply ext
  intro x
  simp [mem_union, not_mem_empty]

/-- Proposition 3.1.27(a) -/
theorem SetTheory.Set.empty_union (A:Set) : ∅ ∪ A = A := by
  apply ext
  intro x
  simp [mem_union, not_mem_empty]

theorem SetTheory.Set.triple_eq (a b c:Object) : {a,b,c} = ({a}:Set) ∪ {b,c} := by
  rfl

/-- Example 3.1.10 -/
theorem SetTheory.Set.pair_union_pair (a b c:Object) : ({a,b}:Set) ∪ {b,c} = {a,b,c} := by
  apply ext
  intro x
  simp [mem_union, mem_pair, mem_triple]
  tauto

/-- Definition 3.1.14.   -/
instance SetTheory.Set.uinstSubset : HasSubset Set where
  Subset X Y := ∀ x, x ∈ X → x ∈ Y

/--
  Definition 3.1.14.
  Note that the strict subset operation in Mathlib is denoted `⊂` rather than `⊊`.
-/
instance SetTheory.Set.instSSubset : HasSSubset Set where
  SSubset X Y := X ⊆ Y ∧ X ≠ Y

/-- Definition 3.1.14. -/
theorem SetTheory.Set.subset_def (X Y:Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl

/--
  Definition 3.1.14.
  Note that the strict subset operation in Mathlib is denoted `⊂` rather than `⊊`.
-/
theorem SetTheory.Set.ssubset_def (X Y:Set) : X ⊂ Y ↔ (X ⊆ Y ∧ X ≠ Y) := by rfl

/-- Remark 3.1.15 -/
theorem SetTheory.Set.subset_congr_left {A A' B:Set} (hAA':A = A') (hAB: A ⊆ B) : A' ⊆ B := by
  rw [←hAA']
  exact hAB

/-- Examples 3.1.16 -/
theorem SetTheory.Set.subset_self (A:Set) : A ⊆ A := by
  intro x hx
  exact hx

/-- Examples 3.1.16 -/
theorem SetTheory.Set.empty_subset (A:Set) : ∅ ⊆ A := by
  intro x hx
  exfalso
  exact not_mem_empty x hx

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.subset_trans {A B C:Set} (hAB:A ⊆ B) (hBC:B ⊆ C) : A ⊆ C := by
  -- this proof is written to follow the structure of the original text.
  rw [subset_def]
  intro x hx
  rw [subset_def] at hAB
  replace hx := hAB x hx
  replace hx := hBC x hx
  assumption

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.subset_antisymm (A B:Set) (hAB:A ⊆ B) (hBA:B ⊆ A) : A = B := by
  apply ext
  intro x
  constructor
  · exact hAB x
  · exact hBA x

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.ssubset_trans (A B C:Set) (hAB:A ⊂ B) (hBC:B ⊂ C) : A ⊂ C := by
  rw [ssubset_def] at hAB hBC ⊢
  constructor
  · exact subset_trans hAB.1 hBC.1
  · intro h
    apply hBC.2
    apply subset_antisymm
    · exact hBC.1
    · rw [←h]
      exact hAB.1

/--
  This defines the subtype `A.toSubtype` for any `A:Set`.  To produce an element `x'` of this
  subtype, use `⟨ x, hx ⟩`, where `x:Object` and `hx:x ∈ A`.  The object `x` associated to a
  subtype element `x'` is recovered as `x.val`, and the property `hx` that `x` belongs to `A` is
  recovered as `x.property`
-/
abbrev SetTheory.Set.toSubtype (A:Set) := Subtype (fun x ↦ x ∈ A)

instance : CoeSort (Set) (Type) where
  coe A := A.toSubtype

/--
  Elements of a set (implicitly coerced to a subtype) are also elements of the set
  (with respect to the membership operation of the set theory).
-/
lemma SetTheory.Set.subtype_property (A:Set) (x:A) : x.val ∈ A := x.property

lemma SetTheory.Set.subtype_coe (A:Set) (x:A) : x.val = x := rfl

lemma SetTheory.Set.coe_inj (A:Set) (x y:A) : x.val = y.val ↔ x = y := Subtype.coe_inj


/--
  If one has a proof `hx` of `x ∈ A`, then `A.subtype_mk hx` will then make the element of `A`
  (viewed as a subtype) corresponding to `x`.
-/
def SetTheory.Set.subtype_mk (A:Set) {x:Object} (hx:x ∈ A) : A := ⟨ x, hx ⟩

lemma SetTheory.Set.subtype_mk_coe {A:Set} {x:Object} (hx:x ∈ A) : A.subtype_mk hx = x := by rfl



abbrev SetTheory.Set.specify (A:Set) (P: A → Prop) : Set := SetTheory.specify A P

/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom {A:Set} {P: A → Prop} {x:Object} (h: x ∈ A.specify P) :
    x ∈ A :=
  (SetTheory.specification_axiom A P).1 x h

/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom' {A:Set} (P: A → Prop) (x:A.toSubtype) :
    x.val ∈ A.specify P ↔ P x :=
  (SetTheory.specification_axiom A P).2 x

/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom'' {A:Set} (P: A → Prop) (x:Object) :
    x ∈ A.specify P ↔ ∃ h:x ∈ A, P ⟨ x, h ⟩ := by
  constructor
  . intro h
    have h' := specification_axiom h
    use h'
    rw [←specification_axiom' P ⟨ x, h' ⟩ ]
    simp [h]
  intro h
  obtain ⟨ h, hP ⟩ := h
  rw [←specification_axiom' P ⟨ x,h ⟩ ] at hP
  simp at hP; assumption

theorem SetTheory.Set.specify_subset {A:Set} (P: A → Prop) : A.specify P ⊆ A := by
  intro x hx
  exact (SetTheory.specification_axiom A P).1 x hx

/-- This exercise may require some understanding of how subtypes are implemented in Lean. -/
theorem SetTheory.Set.specify_congr {A A':Set} (hAA':A = A') {P: A → Prop} {P': A' → Prop} (hPP': (x:Object) → (h:x ∈ A) → (h':x ∈ A') → P ⟨ x, h⟩ ↔ P' ⟨ x, h'⟩ ) : A.specify P = A'.specify P' := by
  subst hAA'
  apply ext
  intro x
  rw [specification_axiom'', specification_axiom'']
  constructor
  · intro ⟨h, hP⟩
    use h
    exact (hPP' x h h).1 hP
  · intro ⟨h, hP'⟩
    use h
    exact (hPP' x h h).2 hP'

instance SetTheory.Set.instIntersection : Inter Set where
  inter X Y := X.specify (fun x ↦ x.val ∈ Y)

/-- Definition 3.1.22 (Intersections) -/
@[simp]
theorem SetTheory.Set.mem_inter (x:Object) (X Y:Set) : x ∈ (X ∩ Y) ↔ (x ∈ X ∧ x ∈ Y) := by
  constructor
  . intro h
    have h' := specification_axiom h
    simp [h']
    exact (specification_axiom' _ ⟨ x, h' ⟩).mp h
  intro ⟨ hX, hY ⟩
  exact (specification_axiom' (fun x ↦ x.val ∈ Y) ⟨ x,hX⟩).mpr hY

instance SetTheory.Set.instSDiff : SDiff Set where
  sdiff X Y := X.specify (fun x ↦ x.val ∉ Y)

/-- Definition 3.1.26 (Difference sets) -/
@[simp]
theorem SetTheory.Set.mem_sdiff (x:Object) (X Y:Set) : x ∈ (X \ Y) ↔ (x ∈ X ∧ x ∉ Y) := by
  constructor
  . intro h
    have h' := specification_axiom h
    simp [h']
    exact (specification_axiom' _ ⟨ x, h' ⟩ ).mp h
  intro ⟨ hX, hY ⟩
  exact (specification_axiom' (fun x ↦ x.val ∉ Y) ⟨ x, hX⟩ ).mpr hY

/-- Proposition 3.1.27(d) / Exercise 3.1.6 -/
theorem SetTheory.Set.inter_comm (A B:Set) : A ∩ B = B ∩ A := by
  apply ext
  intro x
  constructor
  . intro hx
    rw [mem_inter] at hx
    rcases hx with ⟨ hA, hB ⟩
    rw [mem_inter]
    constructor
    . exact hB
    exact hA
  . intro hx
    rw [mem_inter] at hx
    rcases hx with ⟨ hB, hA ⟩
    rw [mem_inter]
    constructor
    . exact hA
    exact hB

/-- Proposition 3.1.27(b) -/
theorem SetTheory.Set.subset_union {A X: Set} (hAX: A ⊆ X) : A ∪ X = X := by
  apply ext
  intro x
  constructor
  . intro hx
    rw [mem_union] at hx
    rcases hx with case1 | case2
    . exact hAX x case1
    exact case2
  . intro hx
    rw [mem_union]
    right; exact hx

/-- Proposition 3.1.27(b) -/
theorem SetTheory.Set.union_subset {A X: Set} (hAX: A ⊆ X) : X ∪ A = X := by
  apply ext
  intro x
  constructor
  . intro hx
    rw [mem_union] at hx
    rcases hx with case1 | case2
    . exact case1
    exact hAX x case2
  . intro hx
    rw [mem_union]
    left; exact hx

/-- Proposition 3.1.27(c) -/
theorem SetTheory.Set.inter_self (A:Set) : A ∩ A = A := by
  apply ext
  intro x
  constructor
  . intro hx
    rw [mem_inter] at hx
    rcases hx with ⟨ hA, _ ⟩
    exact hA
  . intro hx
    rw [mem_inter]
    constructor
    . exact hx
    exact hx

/-- Proposition 3.1.27(e) -/
theorem SetTheory.Set.inter_assoc (A B C:Set) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  -- this proof is written to follow the structure of the original text.
  apply ext
  intro x
  constructor
  . intro hx
    rw [mem_inter] at hx
    rcases hx with ⟨ hAB, hC ⟩
    rw [mem_inter] at hAB
    rcases hAB with ⟨ hA, hB ⟩
    rw [mem_inter]
    constructor
    . exact hA
    . rw [mem_inter]
      constructor
      . exact hB
      . exact hC
  . intro hx
    rw [mem_inter] at hx
    rcases hx with ⟨ hA, hBC ⟩
    rw [mem_inter] at hBC
    rcases hBC with ⟨ hB, hC ⟩
    rw [mem_inter]
    constructor
    . rw [mem_inter]
      constructor
      . exact hA
      . exact hB
    . exact hC

/-- Proposition 3.1.27(f) -/
theorem  SetTheory.Set.inter_union_distrib_left (A B C:Set) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  apply ext
  intro x
  simp [mem_inter, mem_union]
  tauto

/-- Proposition 3.1.27(f) -/
theorem  SetTheory.Set.union_inter_distrib_left (A B C:Set) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  apply ext
  intro x
  simp [mem_inter, mem_union]
  tauto

/-- Proposition 3.1.27(f) -/
theorem SetTheory.Set.union_compl {A X:Set} (hAX: A ⊆ X) : A ∪ (X \ A) = X := by
  apply ext
  intro x
  constructor
  · intro h
    simp [mem_union, mem_sdiff] at h
    cases h with
    | inl h => exact hAX x h
    | inr h => exact h.1
  · intro h
    simp [mem_union, mem_sdiff]
    by_cases hx : x ∈ A
    · exact Or.inl hx
    · exact Or.inr ⟨h, hx⟩

/-- Proposition 3.1.27(f) -/
theorem SetTheory.Set.inter_compl {A X:Set} (hAX: A ⊆ X) : A ∩ (X \ A) = ∅ := by
  apply ext
  intro x
  simp [mem_inter, mem_sdiff, not_mem_empty]
  intro h
  intro hX
  exact h


/-- Proposition 3.1.27(g) -/
theorem SetTheory.Set.compl_union {A B X:Set} (hAX: A ⊆ X) (hBX: B ⊆ X) : X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by
  apply ext
  intro x
  simp [mem_sdiff, mem_union, mem_inter]
  tauto

/-- Proposition 3.1.27(g) -/
theorem SetTheory.Set.compl_inter {A B X:Set} (hAX: A ⊆ X) (hBX: B ⊆ X) : X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by
  apply ext
  intro x
  simp [mem_sdiff, mem_inter, mem_union]
  tauto

/-- Not from textbook: sets form a distributive lattice. -/
instance SetTheory.Set.instDistribLattice : DistribLattice Set where
  le := (· ⊆ ·)
  le_refl := subset_self
  le_trans := fun _ _ _ ↦ subset_trans
  le_antisymm := subset_antisymm
  inf := (· ∩ ·)
  sup := (· ∪ ·)
  le_sup_left := by
    intro A B
    intro x hx
    rw [mem_union]
    left
    exact hx
  le_sup_right := by
    intro A B
    intro x hx
    rw [mem_union]
    right
    exact hx
  sup_le := by
    intro A B C hAC hBC
    intro x hx
    rw [mem_union] at hx
    cases hx with
    | inl h => exact hAC x h
    | inr h => exact hBC x h
  inf_le_left := by
    intro A B
    intro x hx
    rw [mem_inter] at hx
    exact hx.1
  inf_le_right := by
    intro A B
    intro x hx
    rw [mem_inter] at hx
    exact hx.2
  le_inf := by
    intro A B C hAB hAC
    intro x hx
    rw [mem_inter]
    exact ⟨hAB x hx, hAC x hx⟩
  le_sup_inf := by
    intro X Y Z
    change (X ∪ Y) ∩ (X ∪ Z) ⊆ X ∪ (Y ∩ Z)
    rw [←union_inter_distrib_left]
    exact subset_self _

/-- Sets have a minimal element.  -/
instance SetTheory.Set.instOrderBot : OrderBot Set where
  bot := ∅
  bot_le := empty_subset

/-- Definition of disjointness (using the previous instances) -/
theorem SetTheory.Set.disjoint_iff (A B:Set) : Disjoint A B ↔ A ∩ B = ∅ := by
  convert _root_.disjoint_iff

abbrev SetTheory.Set.replace (A:Set) {P: A → Object → Prop}
  (hP : ∀ x y y', P x y ∧ P x y' → y = y') : Set := SetTheory.replace A P hP

/-- Axiom 3.7 (Axiom of replacement) -/
theorem SetTheory.Set.replacement_axiom {A:Set} {P: A → Object → Prop}
  (hP: ∀ x y y', P x y ∧ P x y' → y = y') (y:Object) :
    y ∈ A.replace hP ↔ ∃ x, P x y := SetTheory.replacement_axiom A P hP y

abbrev Nat := SetTheory.nat

/-- Axiom 3.8 (Axiom of infinity) -/
def SetTheory.Set.nat_equiv : ℕ ≃ Nat := SetTheory.nat_equiv

-- Below are some API for handling coercions. This may not be the optimal way to set things up.

instance SetTheory.Set.instOfNat {n:ℕ} : OfNat Nat n where
  ofNat := nat_equiv n

instance SetTheory.Set.instNatCast : NatCast Nat where
  natCast n := nat_equiv n

instance SetTheory.Set.toNat : Coe Nat ℕ where
  coe n := nat_equiv.symm n

instance SetTheory.Object.instNatCast : NatCast Object where
  natCast n := (n:Nat).val

instance SetTheory.Object.instOfNat {n:ℕ} : OfNat Object n where
  ofNat := ((n:Nat):Object)

@[simp]
lemma SetTheory.Object.ofnat_eq {n:ℕ} : ((n:Nat):Object) = (n:Object) := rfl

lemma SetTheory.Object.ofnat_eq' {n:ℕ} : (ofNat(n):Object) = (n:Object) := rfl

lemma SetTheory.Set.nat_coe_eq {n:ℕ} : (n:Nat) = OfNat.ofNat n := rfl

@[simp]
lemma SetTheory.Set.nat_equiv_inj (n m:ℕ) : (n:Nat) = (m:Nat) ↔ n=m  :=
  Equiv.apply_eq_iff_eq nat_equiv

@[simp]
lemma SetTheory.Set.nat_equiv_symm_inj (n m:Nat) : (n:ℕ) = (m:ℕ) ↔ n = m :=
  Equiv.apply_eq_iff_eq nat_equiv.symm

@[simp]
theorem SetTheory.Set.ofNat_inj (n m:ℕ) :
    (ofNat(n) : Nat) = (ofNat(m) : Nat) ↔ ofNat(n) = ofNat(m) := by
      convert nat_equiv_inj _ _

@[simp]
theorem SetTheory.Set.ofNat_inj' (n m:ℕ) :
    (ofNat(n) : Object) = (ofNat(m) : Object) ↔ ofNat(n) = ofNat(m) := by
      simp only [←Object.ofnat_eq, Object.ofnat_eq', Set.coe_inj, Set.nat_equiv_inj]
      rfl

@[simp]
theorem SetTheory.Object.natCast_inj (n m:ℕ) :
    (n : Object) = (m : Object) ↔ n = m := by
      simp [←ofnat_eq, Subtype.val_inj]

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe (n:ℕ) : ((n:Nat):ℕ) = n :=
  Equiv.symm_apply_apply nat_equiv n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe' (n:Nat) : ((n:ℕ):Nat) = n :=
  Equiv.symm_apply_apply nat_equiv.symm n

example : (5:Nat) ≠ (3:Nat) := by
  simp

example : (5:Object) ≠ (3:Object) := by
  simp

/-- Example 3.1.16 (simplified).  -/
example : ({3, 5}:Set) ⊆ {1, 3, 5} := by
  intro x hx
  simp only [SetTheory.Set.mem_pair] at hx
  simp only [Insert.insert, SetTheory.Set.mem_union, SetTheory.Set.mem_singleton, SetTheory.Set.mem_pair]
  cases hx with
  | inl h => right; left; exact h
  | inr h => right; right; exact h

/-- Example 3.1.17 (simplified). -/
example : ({3, 5}:Set).specify (fun x ↦ x.val ≠ 3)
 = {(5:Object)} := by
  apply SetTheory.Set.ext
  intro x
  constructor
  · intro h
    rw [SetTheory.Set.specification_axiom''] at h
    obtain ⟨h_mem, h_neq⟩ := h
    rw [SetTheory.Set.mem_pair] at h_mem
    simp only [SetTheory.Set.mem_singleton]
    cases h_mem with
    | inl h3 => contradiction
    | inr h5 => exact h5
  · intro h
    rw [SetTheory.Set.specification_axiom'']
    simp only [SetTheory.Set.mem_singleton] at h
    use (SetTheory.Set.mem_pair x 3 5).mpr (Or.inr h)
    simp [h]

/-- Example 3.1.24 -/

example : ({1, 2, 4}:Set) ∩ {2,3,4} = {2, 4} := by
  apply SetTheory.Set.ext
  intro x
  constructor
  · intro h
    rw [SetTheory.Set.mem_inter] at h
    obtain ⟨h1, h2⟩ := h
    -- h1: x ∈ {1, 2, 4}, h2: x ∈ {2, 3, 4}
    -- We need to show x ∈ {2, 4}
    rw [SetTheory.Set.mem_triple] at h1 h2
    cases h1 with
    | inl h =>
      -- x = 1
      cases h2 with
      | inl h' => rw [h] at h'; norm_num at h'  -- 1 ≠ 2
      | inr h' =>
        cases h' with
        | inl h'' => rw [h] at h''; norm_num at h''  -- 1 ≠ 3
        | inr h'' => rw [h] at h''; norm_num at h''  -- 1 ≠ 4
    | inr h =>
      cases h with
      | inl h' =>
        -- x = 2
        rw [SetTheory.Set.mem_pair]
        left; exact h'
      | inr h' =>
        -- x = 4
        rw [SetTheory.Set.mem_pair]
        right; exact h'
  · intro h
    rw [SetTheory.Set.mem_inter]
    rw [SetTheory.Set.mem_pair] at h
    cases h with
    | inl h =>
      -- x = 2
      constructor
      · rw [SetTheory.Set.mem_triple]; right; left; exact h
      · rw [SetTheory.Set.mem_triple]; left; exact h
    | inr h =>
      -- x = 4
      constructor
      · rw [SetTheory.Set.mem_triple]; right; right; exact h
      · rw [SetTheory.Set.mem_triple]; right; right; exact h

/-- Example 3.1.24 -/

example : ({1, 2}:Set) ∩ {3,4} = ∅ := by
  apply SetTheory.Set.ext
  intro x
  constructor
  · intro h
    rw [SetTheory.Set.mem_inter] at h
    obtain ⟨h1, h2⟩ := h
    rw [SetTheory.Set.mem_pair] at h1 h2
    cases h1 with
    | inl h =>
      -- x = 1
      cases h2 with
      | inl h' => rw [h] at h'; norm_num at h'  -- 1 ≠ 3
      | inr h' => rw [h] at h'; norm_num at h'  -- 1 ≠ 4
    | inr h =>
      -- x = 2
      cases h2 with
      | inl h' => rw [h] at h'; norm_num at h'  -- 2 ≠ 3
      | inr h' => rw [h] at h'; norm_num at h'  -- 2 ≠ 4
  · intro h
    exfalso
    exact SetTheory.Set.not_mem_empty x h

example : ¬ Disjoint  ({1, 2, 3}:Set)  {2,3,4} := by
  intro h
  rw [SetTheory.Set.disjoint_iff] at h
  -- h : {1, 2, 3} ∩ {2, 3, 4} = ∅
  -- But 2 ∈ {1, 2, 3} ∩ {2, 3, 4}
  have h2_in_left : (2:Object) ∈ ({1, 2, 3}:Set) := by
    rw [SetTheory.Set.mem_triple]
    right; left; rfl
  have h2_in_right : (2:Object) ∈ ({2, 3, 4}:Set) := by
    rw [SetTheory.Set.mem_triple]
    left; rfl
  have h2_in_inter : (2:Object) ∈ ({1, 2, 3}:Set) ∩ {2, 3, 4} := by
    rw [SetTheory.Set.mem_inter]
    exact ⟨h2_in_left, h2_in_right⟩
  rw [h] at h2_in_inter
  exact SetTheory.Set.not_mem_empty (2:Object) h2_in_inter

example : Disjoint (∅:Set) ∅ := by
  rw [SetTheory.Set.disjoint_iff]
  apply SetTheory.Set.ext
  intro x
  constructor
  · intro h
    rw [SetTheory.Set.mem_inter] at h
    obtain ⟨h1, h2⟩ := h
    exfalso
    exact SetTheory.Set.not_mem_empty x h1
  · intro h
    exfalso
    exact SetTheory.Set.not_mem_empty x h

/-- Definition 3.1.26 example -/

example : ({1, 2, 3, 4}:Set) \ {2,4,6} = {1, 3} := by
  apply SetTheory.Set.ext
  intro x
  constructor
  · intro h
    rw [SetTheory.Set.mem_sdiff] at h
    obtain ⟨h1, h2⟩ := h
    -- h1: x ∈ {1, 2, 3, 4}, h2: x ∉ {2, 4, 6}
    rw [SetTheory.Set.mem_pair]
    -- We need to show x = 1 ∨ x = 3
    -- {1, 2, 3, 4} = {1} ∪ {2, 3, 4}
    simp only [Insert.insert, SetTheory.Set.mem_union, SetTheory.Set.mem_singleton] at h1
    cases h1 with
    | inl h =>
      -- x = 1
      left; exact h
    | inr h =>
      -- x ∈ {2, 3, 4}, so x = 2 ∨ x = 3 ∨ x = 4
      cases h with
      | inl h' =>
        -- x = 2, but x ∉ {2, 4, 6}
        exfalso
        apply h2
        rw [SetTheory.Set.mem_triple]
        left; exact h'
      | inr h' =>
        cases h' with
        | inl h'' =>
          -- x = 3
          right; exact h''
        | inr h'' =>
          -- x = 4, but x ∉ {2, 4, 6}
          exfalso
          apply h2
          rw [SetTheory.Set.mem_triple]
          right; left; exact h''
  · intro h
    rw [SetTheory.Set.mem_sdiff]
    rw [SetTheory.Set.mem_pair] at h
    cases h with
    | inl h =>
      -- x = 1
      constructor
      · simp only [Insert.insert, SetTheory.Set.mem_union, SetTheory.Set.mem_singleton]
        left; exact h
      · intro h_contra
        rw [SetTheory.Set.mem_triple] at h_contra
        cases h_contra with
        | inl h' => rw [h] at h'; norm_num at h'  -- 1 ≠ 2
        | inr h' =>
          cases h' with
          | inl h'' => rw [h] at h''; norm_num at h''  -- 1 ≠ 4
          | inr h'' => rw [h] at h''; norm_num at h''  -- 1 ≠ 6
    | inr h =>
      -- x = 3
      constructor
      · simp only [Insert.insert, SetTheory.Set.mem_union, SetTheory.Set.mem_singleton]
        right; right; left; exact h
      · intro h_contra
        rw [SetTheory.Set.mem_triple] at h_contra
        cases h_contra with
        | inl h' => rw [h] at h'; norm_num at h'  -- 3 ≠ 2
        | inr h' =>
          cases h' with
          | inl h'' => rw [h] at h''; norm_num at h''  -- 3 ≠ 4
          | inr h'' => rw [h] at h''; norm_num at h''  -- 3 ≠ 6

/-- Example 3.1.30 -/

example : ({3,5,9}:Set).replace (P := fun x y ↦ ∃ (n:ℕ), x.val = n ∧ y = (n+1:ℕ)) (by
  sorry
  ) = {4,6,10} := by
  sorry
/-- Example 3.1.31 -/

example : ({3,5,9}:Set).replace (P := fun x y ↦ y=1) (by
  intro x y y' ⟨h1, h2⟩
  rw [h1, h2]
  ) = {1} := by
  apply SetTheory.Set.ext
  intro x
  constructor
  · intro h
    rw [SetTheory.Set.replacement_axiom] at h
    obtain ⟨y, h⟩ := h
    rw [SetTheory.Set.mem_singleton, h]
  · intro h
    rw [SetTheory.Set.replacement_axiom]
    rw [SetTheory.Set.mem_singleton] at h
    use ⟨3, by rw [SetTheory.Set.mem_triple]; left; rfl⟩

/-- Exercise 3.1.5.  One can use the `tfae_have` and `tfae_finish` tactics here. -/
theorem SetTheory.Set.subset_tfae (A B C:Set) : [A ⊆ B, A ∪ B = B, A ∩ B = A].TFAE := by
  -- TFAE means all elements in the list are equivalent
  tfae_have 1 → 2 := by
    intro h
    apply SetTheory.Set.subset_union
    exact h
  tfae_have 2 → 3 := by
    intro h
    rw [← h]
    rw [inter_union_distrib_left]
    rw [inter_self]
    sorry

  tfae_have 3 → 1 := by
    intro h
    intro x hx
    rw [←h] at hx
    sorry
    -- exact SetTheory.Set.inter_subset_right A B x hx
  tfae_finish

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.inter_subset_left (A B:Set) : A ∩ B ⊆ A := by
  intro x hx
  rw [mem_inter] at hx
  exact hx.1

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.inter_subset_right (A B:Set) : A ∩ B ⊆ B := by
  intro x hx
  rw [mem_inter] at hx
  exact hx.2

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_inter_iff (A B C:Set) : C ⊆ A ∩ B ↔ C ⊆ A ∧ C ⊆ B := by
  constructor
  · intro h
    constructor
    · exact subset_trans h (inter_subset_left A B)
    · exact subset_trans h (inter_subset_right A B)
  · intro ⟨hA, hB⟩
    intro x hx
    rw [mem_inter]
    exact ⟨hA x hx, hB x hx⟩

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_union_left (A B:Set) : A ⊆ A ∪ B := by
  intro x hx
  rw [mem_union]
  left
  exact hx

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_union_right (A B:Set) : B ⊆ A ∪ B := by
  intro x hx
  rw [mem_union]
  right
  exact hx

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.union_subset_iff (A B C:Set) : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C := by
  constructor
  · intro h
    constructor
    · exact subset_trans (subset_union_left A B) h
    · exact subset_trans (subset_union_right A B) h
  · intro ⟨hA, hB⟩
    intro x hx
    rw [mem_union] at hx
    cases hx with
    | inl h => exact hA x h
    | inr h => exact hB x h

/-- Exercise 3.1.8 -/
theorem SetTheory.Set.inter_union_cancel (A B:Set) : A ∩ (A ∪ B) = A := by
  apply ext
  intro x
  simp [mem_inter, mem_union]
  tauto

/-- Exercise 3.1.8 -/
theorem SetTheory.Set.union_inter_cancel (A B:Set) : A ∪ (A ∩ B) = A := by
  apply ext
  intro x
  simp [mem_union, mem_inter]
  tauto

/-- Exercise 3.1.9 -/
theorem SetTheory.Set.partition_left {A B X:Set} (h_union: A ∪ B = X) (h_inter: A ∩ B = ∅) : A = X \ B := by
  apply ext
  intro x
  constructor
  · intro hx
    rw [mem_sdiff]
    constructor
    · rw [← h_union, mem_union]
      left
      exact hx
    · intro hxB
      have : x ∈ A ∩ B := by rw [mem_inter]; exact ⟨hx, hxB⟩
      rw [h_inter] at this
      exact not_mem_empty x this
  · intro hx
    rw [mem_sdiff] at hx
    rcases hx with ⟨hxX, hxB⟩
    rw [← h_union, mem_union] at hxX
    cases hxX with
    | inl h => exact h
    | inr h => contradiction

/-- Exercise 3.1.9 -/
theorem SetTheory.Set.partition_right {A B X:Set} (h_union: A ∪ B = X) (h_inter: A ∩ B = ∅) : B = X \ A := by
  apply ext
  intro x
  constructor
  · intro hx
    rw [mem_sdiff]
    constructor
    · rw [← h_union, mem_union]
      right
      exact hx
    · intro hxA
      have : x ∈ A ∩ B := by rw [mem_inter]; exact ⟨hxA, hx⟩
      rw [h_inter] at this
      exact not_mem_empty x this
  · intro hx
    rw [mem_sdiff] at hx
    rcases hx with ⟨hxX, hxA⟩
    rw [← h_union, mem_union] at hxX
    cases hxX with
    | inl h => contradiction
    | inr h => exact h

/-- Exercise 3.1.10 -/
theorem SetTheory.Set.pairwise_disjoint (A B:Set) : Pairwise (Function.onFun Disjoint ![A \ B, A ∩ B, B \ A]) := by
  -- We need to show that any two distinct sets in the collection are disjoint
  intro i j h_ne
  -- Function.onFun applies Disjoint to the values at indices i and j
  simp only [Function.onFun]
  fin_cases i <;> fin_cases j <;> simp at h_ne ⊢
  · -- Case i = 0, j = 1: (A \ B) and (A ∩ B) are disjoint
    rw [disjoint_iff]
    apply ext
    intro x
    simp [mem_inter, mem_sdiff, not_mem_empty]
    intro h_sdiff h_inter
    intro
    exact h_inter
  · -- Case i = 0, j = 2: (A \ B) and (B \ A) are disjoint
    rw [disjoint_iff]
    apply ext
    intro x
    simp [mem_inter, mem_sdiff, not_mem_empty]
    intro h_sdiff1 h_sdiff2
    intro
    exact h_sdiff1
  · -- Case i = 1, j = 0: (A ∩ B) and (A \ B) are disjoint
    rw [disjoint_iff]
    apply ext
    intro x
    simp [mem_inter, mem_sdiff, not_mem_empty]
    intro h_inter h_sdiff
    intro
    exact h_sdiff
  · -- Case i = 1, j = 2: (A ∩ B) and (B \ A) are disjoint
    rw [disjoint_iff]
    apply ext
    intro x
    simp [mem_inter, mem_sdiff, not_mem_empty]
    intro h_inter h_sdiff
    exact h_inter
  · -- Case i = 2, j = 0: (B \ A) and (A \ B) are disjoint
    rw [disjoint_iff]
    apply ext
    intro x
    simp [mem_inter, mem_sdiff, not_mem_empty]
    intro h_sdiff2 h_sdiff1
    intro
    exact h_sdiff2
  · -- Case i = 2, j = 1: (B \ A) and (A ∩ B) are disjoint
    rw [disjoint_iff]
    apply ext
    intro x
    simp [mem_inter, mem_sdiff, not_mem_empty]
    intro h_sdiff h_inter
    intro h_inA
    contradiction

/-- Exercise 3.1.10 -/
theorem SetTheory.Set.union_eq_partition (A B:Set) : A ∪ B = (A \ B) ∪ (A ∩ B) ∪ (B \ A) := by
  apply ext
  intro x
  constructor
  · intro h
    rw [mem_union] at h
    rw [mem_union, mem_union, mem_sdiff, mem_inter, mem_sdiff]
    cases h with
    | inl hA =>
      by_cases h : x ∈ B
      . left; right; constructor
        · exact hA
        · exact h
      . left; left; constructor
        · exact hA
        · exact h
    | inr hB =>
      by_cases h : x ∈ A
      · left; right; exact ⟨h, hB⟩
      · right; exact ⟨hB, h⟩
  · intro h
    rw [mem_union]
    rw [mem_union, mem_union, mem_sdiff, mem_inter, mem_sdiff] at h
    cases h with
    | inl h_left =>
      cases h_left with
      | inl h_sdiff =>
        left; exact h_sdiff.1
      | inr h_inter =>
        left; exact h_inter.1
    | inr h_sdiff =>
      right; exact h_sdiff.1

/-- Exercise 3.1.11.  The challenge is to prove this without using `Set.specify`, `Set.specification_axiom`, or `Set.specification_axiom'`. -/
theorem SetTheory.Set.specification_from_replacement {A:Set} {P: A → Prop} : ∃ B, A ⊆ B ∧ ∀ x:A, x.val ∈ B ↔ P x := by
  sorry

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_union_subset {A B A' B':Set} (hA'A: A' ⊆ A) (hB'B: B' ⊆ B) : A' ∪ B' ⊆ A ∪ B := by
  intro x hx
  rw [mem_union] at hx ⊢
  cases hx with
  | inl h => left; exact hA'A x h
  | inr h => right; exact hB'B x h

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_inter_subset {A B A' B':Set} (hA'A: A' ⊆ A) (hB'B: B' ⊆ B) : A' ∩ B' ⊆ A ∩ B := by
  intro x hx
  rw [mem_inter] at hx ⊢
  exact ⟨hA'A x hx.1, hB'B x hx.2⟩

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_diff_subset_counter : ∃ (A B A' B':Set), (A' ⊆ A) ∧ (B' ⊆ B) ∧ ¬ (A' \ B') ⊆ (A \ B) := by
  -- Counterexample: Let A = {1, 2}, B = {1}, A' = {1, 2}, B' = ∅
  -- Then A' ⊆ A and B' ⊆ B, but A' \ B' = {1, 2} while A \ B = {2}
  -- So A' \ B' ⊄ A \ B since 1 ∈ A' \ B' but 1 ∉ A \ B
  use {1, 2}, {1}, {1, 2}, ∅
  constructor
  · -- A' ⊆ A: {1, 2} ⊆ {1, 2}
    intro x hx
    exact hx
  constructor
  · -- B' ⊆ B: ∅ ⊆ {1}
    intro x hx
    exfalso
    exact not_mem_empty x hx
  · -- ¬ (A' \ B') ⊆ (A \ B)
    intro h
    -- Show that 1 ∈ A' \ B' but 1 ∉ A \ B
    have h1_in_diff : 1 ∈ ({1, 2} : Set) \ (∅ : Set) := by
      rw [mem_sdiff]
      constructor
      · rw [mem_pair]
        left
        rfl
      · exact not_mem_empty 1
    have h1_not_in_AB : 1 ∉ ({1, 2} : Set) \ ({1} : Set) := by
      rw [mem_sdiff]
      push_neg
      intro h1A
      rw [mem_singleton]
    have := h 1 h1_in_diff
    exact h1_not_in_AB this

/-
  Final part of Exercise 3.1.12: state and prove a reasonable substitute positive result for the
  above theorem that involves set differences.
-/

/-- Exercise 3.1.13 -/
theorem SetTheory.Set.singleton_iff (A:Set) (hA: A ≠ ∅) : ¬ ∃ B, B ⊂ A ↔ ∃ x, A = {x} := by
  intro h
  -- We need to show that if there exists a proper subset B of A, then A cannot be a singleton
  -- Assume there exists a proper subset B of A
  sorry


/-
  Now we introduce connections between this notion of a set, and Mathlib's notion.
  The exercise below will acquiant you with the API for Mathlib's sets.
-/

instance SetTheory.Set.inst_coe_set : Coe Set (_root_.Set Object) where
  coe X := { x | x ∈ X }

/--
  Injectivity of the coercion. Note however that we do NOT assert that the coercion is surjective
  (and indeed Russell's paradox prevents this)
-/
@[simp]
theorem SetTheory.Set.coe_inj' (X Y:Set) :
    (X : _root_.Set Object) = (Y : _root_.Set Object) ↔ X = Y := by
  constructor
  . intro h; apply ext; intro x
    apply_fun (fun S ↦ x ∈ S) at h
    simp at h; assumption
  intro h; subst h; rfl

/-- Compatibility of the membership operation ∈ -/
theorem SetTheory.Set.mem_coe (X:Set) (x:Object) : x ∈ (X : _root_.Set Object) ↔ x ∈ X := by
  simp [Coe.coe]

/-- Compatibility of the emptyset -/
theorem SetTheory.Set.coe_empty : ((∅:Set) : _root_.Set Object) = ∅ := by
  simp [Coe.coe, Set.ext_iff, not_mem_empty]

/-- Compatibility of subset -/
theorem SetTheory.Set.coe_subset (X Y:Set) : (X : _root_.Set Object) ⊆ (Y : _root_.Set Object) ↔ X ⊆ Y := by
  simp [Coe.coe, subset_def, _root_.Set.subset_def]

theorem SetTheory.Set.coe_ssubset (X Y:Set) : (X : _root_.Set Object) ⊂ (Y : _root_.Set Object) ↔ X ⊂ Y := by
  constructor
  · intro h
    rw [_root_.Set.ssubset_iff_subset_ne] at h
    rw [ssubset_def]
    exact ⟨(coe_subset X Y).mp h.1, fun heq => h.2 (by rw [heq])⟩
  · intro h
    rw [_root_.Set.ssubset_iff_subset_ne]
    rw [ssubset_def] at h
    exact ⟨(coe_subset X Y).mpr h.1, fun heq => h.2 ((coe_inj' X Y).mp heq)⟩

/-- Compatibility of singleton -/
theorem SetTheory.Set.coe_singleton (x: Object) : ({x} : _root_.Set Object) = {x} := by
  simp [Coe.coe, _root_.Set.ext_iff, mem_singleton]

/-- Compatibility of union -/
theorem SetTheory.Set.coe_union (X Y: Set) : (X ∪ Y : _root_.Set Object) = (X : _root_.Set Object) ∪ (Y : _root_.Set Object) := by
  simp [Coe.coe, _root_.Set.ext_iff, mem_union]

/-- Compatibility of pair -/
theorem SetTheory.Set.coe_pair (x y: Object) : ({x, y} : _root_.Set Object) = {x, y} := by
  simp [Coe.coe, _root_.Set.ext_iff, mem_pair]

/-- Compatibility of subtype -/
theorem SetTheory.Set.coe_subtype (X: Set) :  (X : _root_.Set Object) = X.toSubtype := by
  rfl

/-- Compatibility of intersection -/
theorem SetTheory.Set.coe_intersection (X Y: Set) : (X ∩ Y : _root_.Set Object) = (X : _root_.Set Object) ∩ (Y : _root_.Set Object) := by
  simp [Coe.coe, _root_.Set.ext_iff, mem_inter]

/-- Compatibility of set difference-/
theorem SetTheory.Set.coe_diff (X Y: Set) : (X \ Y : _root_.Set Object) = (X : _root_.Set Object) \ (Y : _root_.Set Object) := by
  simp [Coe.coe, _root_.Set.ext_iff, mem_sdiff]

/-- Compatibility of disjointness -/
theorem SetTheory.Set.coe_Disjoint (X Y: Set) : Disjoint (X : _root_.Set Object) (Y : _root_.Set Object) ↔ Disjoint X Y := by
  constructor
  · intro h
    rw [_root_.Set.disjoint_iff_inter_eq_empty] at h
    rw [disjoint_iff]
    apply ext
    intro x
    simp [mem_inter, not_mem_empty]
    have : x ∉ ({x | x ∈ X} ∩ {x | x ∈ Y} : _root_.Set Object) := by rw [h]; simp
    simp at this
    exact this
  · intro h
    rw [_root_.Set.disjoint_iff_inter_eq_empty]
    rw [disjoint_iff] at h
    apply _root_.Set.ext
    intro x
    simp
    intro hx hy
    have : x ∈ X ∩ Y := by simp [mem_inter, hx, hy]
    rw [h] at this
    exact not_mem_empty x this

end Chapter3
