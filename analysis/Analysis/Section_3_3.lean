import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.3

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- A notion of function `Function X Y` between two sets `X`, `Y` in the set theory of Section 3.1
- Various relations with the Mathlib notion of a function `X → Y` between two types `X`, `Y`.
  (Note from Section 3.1 that every `Set` `X` can also be viewed as a subtype
  `{ x:Object // x ∈ X }` of `Object`.)
- Basic function properties and operations, such as composition, one-to-one and onto functions,
  and inverses.

In the rest of the book we will deprecate the Chapter 3 version of a function, and work with the
Mathlib notion of a function instead.  Even within this section, we will switch to the Mathlib
formalism for some of the examples involving number systems such as `ℤ` or `ℝ` that have not been
implemented in the Chapter 3 framework.
-/

namespace Chapter3

/-
We will work here with the version `nat` of the natural numbers internal to the Chapter 3 set
theory, though usually we will use coercions to then immediately translate to the Mathlib
natural numbers `ℕ`.
-/
export SetTheory (Set Object nat)

variable [SetTheory]

/--
  Definition 3.3.1. `Function X Y` is the structure of functions from `X` to `Y`.
  Analogous to the Mathlib type `X → Y`.
-/
@[ext]
structure Function (X Y: Set) where
  P : X → Y → Prop
  unique : ∀ x: X, ∃! y: Y, P x y

#check Function.mk

/--
  Converting a Chapter 3 function `f: Function X Y` to a Mathlib function `f: X → Y`.
  The Chapter 3 definition of a function was nonconstructive, so we have to use the
  axiom of choice here.
-/
noncomputable instance Function.inst_coefn (X Y: Set)  : CoeFun (Function X Y) (fun _ ↦ X → Y) where
  coe := fun f x ↦ Classical.choose (f.unique x)

noncomputable abbrev Function.to_fn {X Y: Set} (f: Function X Y) (x:X) : Y := f x

theorem Function.to_fn_eval {X Y: Set} (f: Function X Y) (x:X) : f.to_fn x = f x := rfl

/-- Converting a Mathlib function to a Chapter 3 function -/
abbrev Function.mk_fn {X Y: Set} (f: X → Y) : Function X Y :=
  Function.mk (fun x y ↦ y = f x) (by
    intro x
    apply ExistsUnique.intro (f x)
    . rfl
    intro y h
    assumption)


/-- Definition 3.3.1 -/
theorem Function.eval {X Y: Set} (f: Function X Y) (x: X) (y: Y) : y = f x ↔ f.P x y := by
  constructor
  . intro h
    subst h
    exact (Classical.choose_spec (f.unique x)).1
  intro h
  apply (Classical.choose_spec (f.unique x)).2
  assumption

@[simp]
theorem Function.eval_of {X Y: Set} (f: X → Y) (x:X) : (Function.mk_fn f) x = f x := by
  symm; rw [eval]


/-- Example 3.3.2.   -/
abbrev P_3_3_2a : nat → nat → Prop := fun x y ↦ (y:ℕ) = (x:ℕ)+1

theorem SetTheory.Set.P_3_3_2a_existsUnique (x: nat) : ∃! y: nat, P_3_3_2a x y := by
  apply ExistsUnique.intro ((x+1:ℕ):nat)
  . simp [P_3_3_2a]
  intro y h
  simp only [P_3_3_2a, Equiv.symm_apply_eq] at h
  assumption

abbrev SetTheory.Set.f_3_3_2a : Function nat nat := Function.mk P_3_3_2a P_3_3_2a_existsUnique

theorem SetTheory.Set.f_3_3_2a_eval (x y: nat) : y = f_3_3_2a x ↔ (y:ℕ) = (x+1:ℕ) :=
  Function.eval _ _ _


theorem SetTheory.Set.f_3_3_2a_eval' (n: ℕ) : f_3_3_2a (n:nat) = (n+1:ℕ) := by
  symm
  simp only [f_3_3_2a_eval, nat_equiv_coe_of_coe]

theorem SetTheory.Set.f_3_3_2a_eval'' : f_3_3_2a 4 = 5 :=  f_3_3_2a_eval' 4

theorem SetTheory.Set.f_3_3_2a_eval''' (n:ℕ) : f_3_3_2a (2*n+3: ℕ) = (2*n+4:ℕ) := by
  convert f_3_3_2a_eval' _

abbrev SetTheory.Set.P_3_3_2b : nat → nat → Prop := fun x y ↦ (y+1:ℕ) = (x:ℕ)

theorem SetTheory.Set.not_P_3_3_2b_existsUnique : ¬ ∀ x, ∃! y: nat, P_3_3_2b x y := by
  by_contra h
  replace h := ExistsUnique.exists (h (0:nat))
  obtain ⟨ n, hn ⟩ := h
  have : ((0:nat):ℕ) = 0 := by simp [OfNat.ofNat]
  simp [P_3_3_2b, this] at hn

abbrev SetTheory.Set.P_3_3_2c : (nat \ {(0:Object)}: Set) → nat → Prop :=
  fun x y ↦ ((y+1:ℕ):Object) = x

theorem SetTheory.Set.P_3_3_2c_existsUnique (x: (nat \ {(0:Object)}: Set)) :
    ∃! y: nat, P_3_3_2c x y := by
  -- Some technical unpacking here due to the subtle distinctions between the `Object` type,
  -- sets converted to subtypes of `Object`, and subsets of those sets.
  obtain ⟨ x, hx ⟩ := x
  simp at hx
  obtain ⟨ hx1, hx2⟩ := hx
  set n := ((⟨ x, hx1 ⟩:nat):ℕ)
  have : x = (n:nat) := by simp [n]
  simp [P_3_3_2c, this, SetTheory.Object.ofnat_eq'] at hx2 ⊢
  replace hx2 : n = (n-1) + 1 := by omega
  apply ExistsUnique.intro ((n-1:ℕ):nat)
  . simp [←hx2]
  intro y hy
  set m := (y:ℕ)
  simp [←hy, m]

abbrev SetTheory.Set.f_3_3_2c : Function (nat \ {(0:Object)}: Set) nat :=
  Function.mk P_3_3_2c P_3_3_2c_existsUnique

theorem SetTheory.Set.f_3_3_2c_eval (x: (nat \ {(0:Object)}: Set)) (y: nat) :
    y = f_3_3_2c x ↔ ((y+1:ℕ):Object) = x := Function.eval _ _ _

/-- Create a version of a non-zero `n` inside `nat \ {0}` for any natural number n. -/
abbrev SetTheory.Set.coe_nonzero (n:ℕ) (h: n ≠ 0): (nat \ {(0:Object)}: Set) :=
  ⟨((n:ℕ):Object), by
    simp [SetTheory.Object.ofnat_eq',h]
    rw [←SetTheory.Object.ofnat_eq]
    exact Subtype.property _
  ⟩

theorem SetTheory.Set.f_3_3_2c_eval' (n: ℕ) : f_3_3_2c (coe_nonzero (n+1) (by positivity)) = n := by
  symm; rw [f_3_3_2c_eval]; simp

theorem SetTheory.Set.f_3_3_2c_eval'' : f_3_3_2c (coe_nonzero 4 (by positivity)) = 3 := by
  convert f_3_3_2c_eval' 3

theorem SetTheory.Set.f_3_3_2c_eval''' (n:ℕ) :
    f_3_3_2c (coe_nonzero (2*n+3) (by positivity)) = (2*n+2:ℕ) := by convert f_3_3_2c_eval' (2*n+2)

/--
  Example 3.3.3 is a little tricky to replicate with the current formalism as the real numbers
  have not been constructed yet.  Instead, I offer some Mathlib counterparts.  Of course, filling
  in these sorries will require using some Mathlib API, for instance for the nonnegative real
  class `NNReal`, and how this class interacts with `ℝ`.
-/
example : ¬ ∃ f: ℝ → ℝ, ∀ x y, y = f x ↔ y^2 = x := by
  by_contra h
  obtain ⟨ f, hf ⟩ := h
  -- Consider x = 1. Both y = 1 and y = -1 satisfy y^2 = 1
  have h1 : (1:ℝ)^2 = 1 := by norm_num
  have h_neg1 : (-1:ℝ)^2 = 1 := by norm_num
  -- By the function property, both 1 and -1 must equal f(1)
  have f1_eq_1 : 1 = f 1 := (hf 1 1).mpr h1
  have f1_eq_neg1 : -1 = f 1 := (hf 1 (-1)).mpr h_neg1
  -- Therefore 1 = -1, which is false
  have : (1:ℝ) = -1 := by
    calc 1 = f 1 := f1_eq_1
    _ = -1 := f1_eq_neg1.symm
  norm_num at this

example : ¬ ∃ f: NNReal → ℝ, ∀ x y, y = f x ↔ y^2 = x := by
  by_contra h
  obtain ⟨f, hf⟩ := h
  -- Consider x = 1 (as NNReal). Both y = 1 and y = -1 satisfy y^2 = 1
  have h1 : (1:ℝ)^2 = (1:NNReal) := by norm_num
  have h_neg1 : (-1:ℝ)^2 = (1:NNReal) := by norm_num
  -- By the function property, both 1 and -1 must equal f(1)
  have f1_eq_1 : 1 = f 1 := (hf 1 1).mpr h1
  have f1_eq_neg1 : -1 = f 1 := (hf 1 (-1)).mpr h_neg1
  -- Therefore 1 = -1, which is false
  have : (1:ℝ) = -1 := by
    calc 1 = f 1 := f1_eq_1
    _ = -1 := f1_eq_neg1.symm
  norm_num at this

example : ∃ f: NNReal → ℝ, ∀ x y, y = f x ↔ y^2 = x := by sorry
-- note: Nope, this is false.


/-- Example 3.3.4. The unused variable `_x` is underscored to avoid triggering a linter. -/
abbrev SetTheory.Set.P_3_3_4 : nat → nat → Prop := fun _x y ↦ y = 7

theorem SetTheory.Set.P_3_3_4_existsUnique (x: nat) : ∃! y: nat, P_3_3_4 x y := by
  apply ExistsUnique.intro 7
  all_goals simp [P_3_3_4]

abbrev SetTheory.Set.f_3_3_4 : Function nat nat := Function.mk P_3_3_4 P_3_3_4_existsUnique

theorem SetTheory.Set.f_3_3_4_eval (x: nat) : f_3_3_4 x = 7 := by
  symm; rw [Function.eval]

/-- Definition 3.3.7 (Equality of functions) -/
theorem Function.eq_iff {X Y: Set} (f g: Function X Y) : f = g ↔ ∀ x: X, f x = g x := by
  constructor
  . intro h; simp [h]
  intro h
  ext x y
  constructor
  . intro hf
    rwa [←Function.eval _ _ _, ←h x, Function.eval _ _ _]
  intro hg
  rwa [←Function.eval _ _ _, h x, Function.eval _ _ _]

/--
  Example 3.3.8 (simplified).  The second part of the example is tricky to replicate in this
  formalism, so a Mathlib substitute is offered instead.
-/
abbrev SetTheory.Set.f_3_3_8a : Function nat nat := Function.mk_fn (fun x ↦ (x^2 + 2*x + 1:ℕ))

abbrev SetTheory.Set.f_3_3_8b : Function nat nat := Function.mk_fn (fun x ↦ ((x+1)^2:ℕ))

theorem SetTheory.Set.f_3_3_8_eq : f_3_3_8a = f_3_3_8b := by
  rw [Function.eq_iff]
  intro x
  rw [Function.eval_of, Function.eval_of]
  set n := (x:ℕ)
  simp; ring

example : (fun x:NNReal ↦ (x:ℝ)) = (fun x:NNReal ↦ |(x:ℝ)|) := by
  funext x
  simp [abs_of_nonneg, NNReal.coe_nonneg]

example : (fun x:ℝ ↦ (x:ℝ)) ≠ (fun x:ℝ ↦ |(x:ℝ)|) := by
  intro h
  -- Apply the hypothesis to x = -1
  have : (-1:ℝ) = |(-1:ℝ)| := by
    have := congr_fun h (-1)
    exact this
  -- But |-1| = 1, so we get -1 = 1
  simp [abs_neg, abs_one] at this
  norm_num at this

/-- Example 3.3.9 -/
abbrev SetTheory.Set.f_3_3_9 (X:Set) : Function (∅:Set) X :=
  Function.mk (fun _ _ ↦ True) (by intro ⟨ x,hx ⟩; simp at hx)

theorem SetTheory.Set.empty_function_unique {X: Set} (f g: Function (∅:Set) X) : f = g := by
  -- Two functions from the empty set are equal because the empty set has no elements
  -- so there's nothing to distinguish them
  ext x
  -- But x is an element of the empty set, which is impossible
  exfalso
  exact SetTheory.Set.not_mem_empty x.val x.property

/-- Definition 3.3.10 (Composition) -/
noncomputable abbrev Function.comp {X Y Z: Set} (g: Function Y Z) (f: Function X Y) :
    Function X Z :=
  Function.mk_fn (fun x ↦ g (f x))

-- `∘` is already taken in Mathlib for the composition of Mathlib functions,
-- so we use `○` here instead to avoid ambiguity.
infix:90 "○" => Function.comp

theorem Function.comp_eval {X Y Z: Set} (g: Function Y Z) (f: Function X Y) (x: X) :
    (g ○ f) x = g (f x) := Function.eval_of _ _

/--
  Compatibility with Mathlib's composition operation.
  You may find the `ext` and `simp` tactics to be useful.
-/
theorem Function.comp_eq_comp {X Y Z: Set} (g: Function Y Z) (f: Function X Y) :
    (g ○ f).to_fn = g.to_fn ∘ f.to_fn := by
  ext x
  simp [Function.comp, Function.to_fn]
  sorry

/-- Example 3.3.11 -/
abbrev SetTheory.Set.f_3_3_11 : Function nat nat := Function.mk_fn (fun x ↦ (2*x:ℕ))

abbrev SetTheory.Set.g_3_3_11 : Function nat nat := Function.mk_fn (fun x ↦ (x+3:ℕ))

theorem SetTheory.Set.g_circ_f_3_3_11 :
    g_3_3_11 ○ f_3_3_11 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+3:ℕ):nat)) := by
  rw [Function.eq_iff]
  intro x
  rw [Function.comp_eval, Function.eval_of, Function.eval_of, Function.eval_of]
  simp

theorem SetTheory.Set.f_circ_g_3_3_11 :
    f_3_3_11 ○ g_3_3_11 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+6:ℕ):nat)) := by
  rw [Function.eq_iff]
  intro x
  rw [Function.comp_eval, Function.eval_of, Function.eval_of, Function.eval_of]
  simp; ring

/-- Lemma 3.3.12 (Composition is associative) -/
theorem SetTheory.Set.comp_assoc {W X Y Z: Set} (h: Function Y Z) (g: Function X Y)
  (f: Function W X) :
    h ○ (g ○ f) = (h ○ g) ○ f := by
  rw [Function.eq_iff]
  intro x
  simp_rw [Function.comp_eval]

abbrev Function.one_to_one {X Y: Set} (f: Function X Y) : Prop := ∀ x x': X, x ≠ x' → f x ≠ f x'

theorem Function.one_to_one_iff {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ ∀ x x': X, f x = f x' → x = x' := by
  apply forall_congr'; intro x
  apply forall_congr'; intro x'
  tauto

/--
  Compatibility with Mathlib's `Function.Injective`.  You may wish to use the `unfold` tactic to
  understand Mathlib concepts such as `Function.Injective`.
-/
theorem Function.one_to_one_iff' {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ Function.Injective f.to_fn := by
  unfold Function.Injective Function.to_fn
  exact Function.one_to_one_iff f

/--
  Example 3.3.15.  One half of the example requires the integers, and so is expressed using
  Mathlib functions instead of Chapter 3 functions.
-/
theorem SetTheory.Set.f_3_3_15_one_to_one :
    (Function.mk_fn (fun (n:nat) ↦ ((n^2:ℕ):nat))).one_to_one := by
  rw [Function.one_to_one_iff]
  intro x x' hx
  simp [Function.eval_of] at hx
  sorry
  -- We have hx : x^2 = x'^2 in nat type
  -- For natural numbers, this implies x = x'


example : ¬ Function.Injective (fun (n:ℤ) ↦ n^2) := by
  intro h
  -- Use 1 and -1 as counterexample
  have h1 : (1:ℤ)^2 = (-1:ℤ)^2 := by norm_num
  have : (1:ℤ) = (-1:ℤ) := h h1
  norm_num at this

example : Function.Injective (fun (n:ℕ) ↦ n^2) := by
  intro x y h
  simp at h
  exact h

/-- Remark 3.3.16 -/
theorem SetTheory.Set.two_to_one {X Y: Set} {f: Function X Y} (h: ¬ f.one_to_one) :
    ∃ x x': X, x ≠ x' ∧ f x = f x' := by
  -- Since f is not one-to-one, there exist x, x' such that x ≠ x' → f x ≠ f x' is false
  rw [Function.one_to_one] at h
  push_neg at h
  exact h

/-- Definition 3.3.17 (Onto functions) -/
abbrev Function.onto {X Y: Set} (f: Function X Y) : Prop := ∀ y: Y, ∃ x: X, f x = y

/-- Compatibility with Mathlib's Function.Surjective-/
theorem Function.onto_iff {X Y: Set} (f: Function X Y) : f.onto ↔ Function.Surjective f.to_fn := by
  unfold Function.Surjective Function.to_fn
  rfl

/-- Example 3.3.18 (using Mathlib) -/
example : ¬ Function.Surjective (fun (n:ℤ) ↦ n^2) := by
  sorry

abbrev A_3_3_18 := { m:ℤ // ∃ n:ℤ, m = n^2 }

example : Function.Surjective (fun (n:ℤ) ↦ ⟨ n^2, by use n ⟩ : ℤ → A_3_3_18) := by
  intro ⟨m, hm⟩
  -- hm : ∃ n, m = n^2
  obtain ⟨n, hn⟩ := hm
  use n
  simp
  exact hn.symm

/-- Definition 3.3.20 (Bijective functions) -/
abbrev Function.bijective {X Y: Set} (f: Function X Y) : Prop := f.one_to_one ∧ f.onto

/-- Compatibility with Mathlib's Function.Bijective-/
theorem Function.bijective_iff {X Y: Set} (f: Function X Y) :
    f.bijective ↔ Function.Bijective f.to_fn := by
  unfold Function.bijective Function.Bijective
  rw [Function.one_to_one_iff', Function.onto_iff]

/-- Example 3.3.21 (using Mathlib) -/
abbrev f_3_3_21 : Fin 3 → ({3,4}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 3, by norm_num ⟩
| 1 => ⟨ 3, by norm_num ⟩
| 2 => ⟨ 4, by norm_num ⟩

example : ¬ Function.Injective f_3_3_21 := by
  unfold Function.Injective
  intro h
  -- We need to show that there exist x, x' such that f x = f x' and x ≠ x'
  have h_eq : f_3_3_21 0 = f_3_3_21 1 := by
    simp [f_3_3_21]
  have h_ne : (0 : Fin 3) ≠ (1 : Fin 3) := by norm_num
  have : (0 : Fin 3) = (1 : Fin 3) := h h_eq
  exact h_ne this

example : ¬ Function.Bijective f_3_3_21 := by
  intro h
  -- Since f_3_3_21 is not injective, it cannot be bijective
  have h_not_inj : ¬ Function.Injective f_3_3_21 := by
    unfold Function.Injective
    intro h_inj
    have h_eq : f_3_3_21 0 = f_3_3_21 1 := by simp [f_3_3_21]
    have h_ne : (0 : Fin 3) ≠ (1 : Fin 3) := by norm_num
    have : (0 : Fin 3) = (1 : Fin 3) := h_inj h_eq
    exact h_ne this
  have h_inj : Function.Injective f_3_3_21 := h.1
  exact h_not_inj h_inj

abbrev g_3_3_21 : Fin 2 → ({2,3,4}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 2, by norm_num ⟩
| 1 => ⟨ 3, by norm_num ⟩

example : ¬ Function.Surjective g_3_3_21 := by
  intro h
  -- 4 is in the codomain but not in the range
  obtain ⟨x, hx⟩ := h ⟨4, by norm_num⟩
  -- But g only maps to 2 and 3, contradiction follows from fin_cases
  fin_cases x <;> simp [g_3_3_21] at hx


example : ¬ Function.Bijective g_3_3_21 := by
  intro h
  -- Since g_3_3_21 is not surjective, it cannot be bijective
  have h_not_surj : ¬ Function.Surjective g_3_3_21 := by
    intro h_surj
    obtain ⟨x, hx⟩ := h_surj ⟨4, by norm_num⟩
    fin_cases x <;> simp [g_3_3_21] at hx
  have h_surj : Function.Surjective g_3_3_21 := h.2
  exact h_not_surj h_surj

abbrev h_3_3_21 : Fin 3 → ({3,4,5}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 3, by norm_num ⟩
| 1 => ⟨ 4, by norm_num ⟩
| 2 => ⟨ 5, by norm_num ⟩

example : Function.Bijective h_3_3_21 := by
  constructor
  -- Prove injective
  · intro x y h
    fin_cases x <;> fin_cases y <;> simp [h_3_3_21] at h <;> rfl
  -- Prove surjective
  · intro ⟨z, hz⟩
    -- z must be 3, 4, or 5
    simp at hz
    rcases hz with h3 | h4 | h5
    · use 0; simp [h_3_3_21, h3]
    · use 1; simp [h_3_3_21, h4]
    · use 2; simp [h_3_3_21, h5]

/--
  Example 3.3.22 is formulated using Mathlib rather than the set theory framework here to avoid
  some tedious technical issues (cf. Exercise 3.3.2)
-/
example : Function.Bijective (fun n ↦ ⟨ n+1, by omega⟩ : ℕ → { n:ℕ // n ≠ 0 }) := by
  constructor
  -- Prove injective
  · intro x y h
    simp at h
    omega
  -- Prove surjective
  · intro ⟨m, hm⟩
    use m - 1
    ext
    simp
    omega

example : ¬ Function.Bijective (fun n ↦ n+1) := by
  intro h
  -- This function is not surjective because 0 is not in the range
  have h_not_surj : ¬ Function.Surjective (fun n ↦ n+1) := by
    intro h_surj
    obtain ⟨n, hn⟩ := h_surj 0
    simp at hn
  have h_surj : Function.Surjective (fun n ↦ n+1) := h.2
  exact h_not_surj h_surj

/-- Remark 3.3.24 -/
theorem Function.bijective_incorrect_def :
    ∃ X Y: Set, ∃ f: Function X Y, (∀ x: X, ∃! y: Y, y = f x) ∧ ¬ f.bijective := by
  -- Use the natural numbers and a simple non-bijective function
  use nat, nat
  -- Define f(n) = 0 for all n (constant function)
  let f : Function nat nat := Function.mk_fn (fun _ ↦ (0 : ℕ))
  use f
  constructor
  · -- Every function automatically satisfies the existence and uniqueness property
    intro x
    use f x
    constructor
    · rfl
    · intro y hy
      exact hy
  · -- Show f is not bijective (it's not injective)
    intro h
    have h_inj : f.one_to_one := h.1
    -- f is not injective because f(0) = f(1) = 0 but 0 ≠ 1
    rw [Function.one_to_one_iff] at h_inj
    have f_eq : f (0 : ℕ) = f (1 : ℕ) := by
      simp [Function.eval_of]
    have ne_01 : ((0 : ℕ) : nat) ≠ ((1 : ℕ) : nat) := by
      intro h_eq
      -- If (0 : ℕ) : nat = (1 : ℕ) : nat, then by extensionality 0 = 1
      have : (0 : ℕ) = (1 : ℕ) := by
        -- This follows from the fact that the coercion is injective
        have h_coe : ((0 : ℕ) : nat).val = ((1 : ℕ) : nat).val := by
          rw [h_eq]
        simp at h_coe
      norm_num at this
    have eq_01 : ((0 : ℕ) : nat) = ((1 : ℕ) : nat) := h_inj _ _ f_eq
    exact ne_01 eq_01

/--
  We cannot use the notation `f⁻¹` for the inverse because in Mathlib's `Inv` class, the inverse
  of `f` must be exactly of the same type of `f`, and `Function Y X` is a different type from
  `Function X Y`.
-/
abbrev Function.inverse {X Y: Set} (f: Function X Y) (h: f.bijective) :
    Function Y X :=
  Function.mk (fun y x ↦ f x = y) (by
    intro y
    apply existsUnique_of_exists_of_unique
    . obtain ⟨ x, hx ⟩ := h.2 y
      use x
    intro x x' hx hx'
    simp at hx hx'
    rw [←hx'] at hx
    apply f.one_to_one_iff.mp h.1 _ _
    simp [hx]
  )

theorem Function.inverse_eval {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) (x: X) :
    x = (f.inverse h) y ↔ f x = y := Function.eval _ _ _

/-- Compatibility with Mathlib's notion of inverse -/
theorem Function.inverse_eq {X Y: Set} [Nonempty X] {f: Function X Y} (h: f.bijective) :
    (f.inverse h).to_fn = Function.invFun f.to_fn := by
  funext y
  -- This requires showing that our inverse function agrees with Mathlib's invFun
  -- The proof involves showing that both satisfy the same inverse property
  sorry

/-- Exercise 3.3.1 -/
theorem Function.refl {X Y:Set} (f: Function X Y) : f = f := by
  rfl

theorem Function.symm {X Y:Set} (f g: Function X Y) : f = g ↔ g = f := by
  apply Iff.symm
  exact eq_comm

theorem Function.trans {X Y:Set} {f g h: Function X Y} (hfg: f = g) (hgh: g = h) : f = h := by
  exact Eq.trans hfg hgh

theorem Function.comp_congr {X Y Z:Set} {f f': Function X Y} (hff': f = f') {g g': Function Y Z}
  (hgg': g = g') : g ○ f = g' ○ f' := by
  rw [hff', hgg']

/-- Exercise 3.3.2 -/
theorem Function.comp_of_inj {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.one_to_one)
  (hg: g.one_to_one) : (g ○ f).one_to_one := by
  rw [Function.one_to_one_iff]
  intro x x' h
  -- h : (g ○ f) x = (g ○ f) x'
  rw [Function.comp_eval, Function.comp_eval] at h
  -- h : g (f x) = g (f x')
  -- Since g is one-to-one, f x = f x'
  have hf_eq : f x = f x' := by
    apply (Function.one_to_one_iff g).mp hg
    exact h
  -- Since f is one-to-one, x = x'
  exact (Function.one_to_one_iff f).mp hf x x' hf_eq

theorem Function.comp_of_surj {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.onto)
  (hg: g.onto) : (g ○ f).onto := by
  intro z
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  use x
  rw [Function.comp_eval]
  rw [hx, hy]

/--
  Exercise 3.3.3 - fill in the sorrys in the statements in  a reasonable fashion.
-/
example (X: Set) : (SetTheory.Set.f_3_3_9 X).one_to_one ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    -- The empty function is vacuously injective
    rw [Function.one_to_one_iff]
    intro x x' _
    -- But x and x' are elements of the empty set, which is impossible
    exfalso
    exact SetTheory.Set.not_mem_empty x.val x.property

example (X: Set) : (SetTheory.Set.f_3_3_9 X).onto ↔ (X = ∅) := by
  constructor
  · intro h
    -- If f is onto, then for every y in X, there exists x in ∅ such that f(x) = y
    -- But ∅ has no elements, so X must be empty
    by_contra hne
    -- X is nonempty, so there exists some y in X
    have ⟨y, hy⟩ : ∃ y, y ∈ X := SetTheory.Set.nonempty_def hne
    -- By surjectivity, there exists x in ∅ such that f(x) = y
    obtain ⟨x, _⟩ := h ⟨y, hy⟩
    -- But x cannot be in ∅
    exact SetTheory.Set.not_mem_empty x.val x.property
  · intro h
    -- If X = ∅, then f is vacuously onto
    rw [h]
    intro ⟨y, hy⟩
    -- But y cannot be in ∅
    exfalso
    exact SetTheory.Set.not_mem_empty y hy

example (X: Set) : (SetTheory.Set.f_3_3_9 X).bijective ↔ (X = ∅) := by
  rw [Function.bijective]
  constructor
  · intro ⟨_, h_onto⟩
    -- Use the previous result about onto
    have : (SetTheory.Set.f_3_3_9 X).onto ↔ (X = ∅) := by
      constructor
      · intro h
        by_contra hne
        have ⟨y, hy⟩ : ∃ y, y ∈ X := SetTheory.Set.nonempty_def hne
        obtain ⟨x, _⟩ := h ⟨y, hy⟩
        exact SetTheory.Set.not_mem_empty x.val x.property
      · intro h
        rw [h]
        intro ⟨y, hy⟩
        exfalso
        exact SetTheory.Set.not_mem_empty y hy
    exact this.mp h_onto
  · intro h
    constructor
    · -- The empty function is vacuously injective
      rw [Function.one_to_one_iff]
      intro x x' _
      exfalso
      exact SetTheory.Set.not_mem_empty x.val x.property
    · -- Use the previous result about onto
      rw [h]
      intro ⟨y, hy⟩
      exfalso
      exact SetTheory.Set.not_mem_empty y hy

/--
  Exercise 3.3.4.  State and prove theorems or counterexamples in the case that `hg` or `hf` is
  omitted as a hypothesis.
-/
theorem Function.comp_cancel_left {X Y Z:Set} {f f': Function X Y} {g : Function Y Z}
  (heq : g ○ f = g ○ f') (hg: g.one_to_one) : f = f' := by
  rw [Function.eq_iff]
  intro x
  apply (Function.one_to_one_iff g).mp hg
  have h_eq : (g ○ f) x = (g ○ f') x := by
    rw [heq]
  rw [Function.comp_eval, Function.comp_eval] at h_eq
  exact h_eq

theorem Function.comp_cancel_right {X Y Z:Set} {f: Function X Y} {g g': Function Y Z}
  (heq : g ○ f = g' ○ f) (hf: f.onto) : g = g' := by
  rw [Function.eq_iff]
  intro z
  -- Since f is onto, there exists x such that f x = z
  obtain ⟨x, hx⟩ := hf z
  -- We have g z = g (f x) and g' z = g' (f x)
  rw [←hx]
  -- Now we use the fact that g ○ f = g' ○ f
  have h_eq : (g ○ f) x = (g' ○ f) x := by
    rw [heq]
  rw [Function.comp_eval, Function.comp_eval] at h_eq
  exact h_eq

/--
  Exercise 3.3.5.  State or prove theorems or counterexamples in the case that `f` is replaced
  with `g` or vice versa in the conclusion.
-/
theorem Function.comp_injective {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hinj :
    (g ○ f).one_to_one) : f.one_to_one := by
  rw [Function.one_to_one_iff]
  intro x x' hx
  apply (Function.one_to_one_iff (g ○ f)).mp hinj
  rw [Function.comp_eval, Function.comp_eval, hx]

theorem Function.comp_surjective {X Y Z:Set} {f: Function X Y} {g : Function Y Z}
  (hinj : (g ○ f).onto) : g.onto := by
  intro z
  obtain ⟨x, hx⟩ := hinj z
  use f x
  rw [Function.comp_eval] at hx
  exact hx

/-- Exercise 3.3.6 -/
theorem Function.inverse_comp_self {X Y: Set} {f: Function X Y} (h: f.bijective) (x: X) :
    (f.inverse h) (f x) = x := by
  symm
  rw [Function.inverse_eval]

theorem Function.self_comp_inverse {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) :
    f ((f.inverse h) y) = y := by
  have h_inv : (f.inverse h) y = (f.inverse h) y := rfl
  rw [Function.inverse_eval] at h_inv
  exact h_inv

theorem Function.inverse_bijective {X Y: Set} {f: Function X Y} (h: f.bijective) :
    (f.inverse h).bijective := by
  constructor
  · -- Show inverse is injective
    rw [Function.one_to_one_iff]
    intro y y' hc
    -- If (f.inverse h) y = (f.inverse h) y', then applying f to both sides gives f((f.inverse h) y) = f((f.inverse h) y')
    have h1 : f ((f.inverse h) y) = f ((f.inverse h) y') := by
      rw [hc]
    -- But f((f.inverse h) y) = y and f((f.inverse h) y') = y'
    rw [Function.self_comp_inverse, Function.self_comp_inverse] at h1
    exact h1
  · -- Show inverse is surjective
    intro x
    use f x
    exact Function.inverse_comp_self h x

theorem Function.inverse_inverse {X Y: Set} {f: Function X Y} (h: f.bijective) :
    (f.inverse h).inverse (f.inverse_bijective h) = f := by
  rw [Function.eq_iff]
  intro x
  -- We need to show ((f.inverse h).inverse _) x = f x
  -- This follows from the definition of inverse
  symm
  rw [Function.inverse_eval]
  exact Function.inverse_comp_self h x

theorem Function.comp_bijective {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.bijective)
  (hg: g.bijective) : (g ○ f).bijective := by
  constructor
  · exact Function.comp_of_inj hf.1 hg.1
  · exact Function.comp_of_surj hf.2 hg.2

/-- Exercise 3.3.7 -/
theorem Function.inv_of_comp {X Y Z:Set} {f: Function X Y} {g : Function Y Z}
  (hf: f.bijective) (hg: g.bijective) :
    (g ○ f).inverse (Function.comp_bijective hf hg) = (f.inverse hf) ○ (g.inverse hg) := by
  rw [Function.eq_iff]
  intro z
  -- Use uniqueness of inverse: if h ○ (g ○ f) = id, then h = (g ○ f).inverse
  -- We'll show that ((f.inverse hf) ○ (g.inverse hg)) is the inverse of (g ○ f)
  symm
  rw [Function.inverse_eval]
  -- Need to show (g ○ f) (((f.inverse hf) ○ (g.inverse hg)) z) = z
  have h1 : ((f.inverse hf) ○ (g.inverse hg)) z = (f.inverse hf) ((g.inverse hg) z) := Function.comp_eval _ _ _
  rw [h1]
  have h2 : (g ○ f) ((f.inverse hf) ((g.inverse hg) z)) = g (f ((f.inverse hf) ((g.inverse hg) z))) := Function.comp_eval _ _ _
  rw [h2]
  have h3 : f ((f.inverse hf) ((g.inverse hg) z)) = (g.inverse hg) z := Function.self_comp_inverse hf _
  rw [h3]
  exact Function.self_comp_inverse hg z

/-- Exercise 3.3.8 -/
abbrev Function.inclusion {X Y:Set} (h: X ⊆ Y) :
    Function X Y := Function.mk_fn (fun x ↦ ⟨ x.val, h x.val x.property ⟩ )

abbrev Function.id (X:Set) : Function X X := Function.mk_fn (fun x ↦ x)

theorem Function.inclusion_id (X:Set) :
    Function.inclusion (SetTheory.Set.subset_self X) = Function.id X := by
  rfl

theorem Function.inclusion_comp (X Y Z:Set) (hXY: X ⊆ Y) (hYZ: Y ⊆ Z) :
    Function.inclusion hYZ ○ Function.inclusion hXY = Function.inclusion (SetTheory.Set.subset_trans hXY hYZ) := by
  rw [Function.eq_iff]
  intro x
  rw [Function.comp_eval, Function.eval_of, Function.eval_of, Function.eval_of]

theorem Function.comp_id {A B:Set} (f: Function A B) : f ○ Function.id A = f := by
  rw [Function.eq_iff]
  intro x
  rw [Function.comp_eval, Function.eval_of]

theorem Function.id_comp {A B:Set} (f: Function A B) : Function.id B ○ f = f := by
  rw [Function.eq_iff]
  intro x
  rw [Function.comp_eval, Function.eval_of]

theorem Function.comp_inv {A B:Set} (f: Function A B) (hf: f.bijective) :
    f ○ f.inverse hf = Function.id B := by
  rw [Function.eq_iff]
  intro y
  rw [Function.comp_eval, Function.eval_of]
  -- We need to show f ((f.inverse hf) y) = y
  have h : f ((f.inverse hf) y) = y := by
    rw [←Function.inverse_eval]
  exact h

theorem Function.inv_comp {A B:Set} (f: Function A B) (hf: f.bijective) :
    f.inverse hf ○ f = Function.id A := by
  rw [Function.eq_iff]
  intro x
  rw [Function.comp_eval, Function.eval_of]
  -- We need to show (f.inverse hf) (f x) = x
  exact Function.inverse_comp_self hf x

theorem Function.glue {X Y Z:Set} (hXY: Disjoint X Y) (f: Function X Z) (g: Function Y Z) :
    ∃! h: Function (X ∪ Y) Z, (h ○ Function.inclusion (SetTheory.Set.subset_union_left X Y) = f)
    ∧ (h ○ Function.inclusion (SetTheory.Set.subset_union_right X Y) = g) := by
  sorry



end Chapter3
