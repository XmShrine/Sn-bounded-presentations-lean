/-
Formalisation of "Bounded presentations of the symmetric groups on their standard generators
with bit-length O(log n)".

Section 2: power expressions, length, presentations, the presentation criterion
(remark after Definition 2.4), and Lemma 2.5 (elimination of generators).
-/
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Opposite
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SnPres

/-! ## Definition 2.1: power expressions -/

/-- Power expressions over an alphabet `α`.

* `gen a` is the letter `a`;
* `mul E F` is the juxtaposition `E F`; a juxtaposition `E₁ ⋯ E_k` (`k ≥ 2`) of the paper is a
  nested `mul` (its length does not depend on the bracketing);
* `pow E e` is `(E)^e`;
* `one` is the empty product.

The paper only allows `k ≥ 2` and `e ∉ {0, 1}`; `PE.WF` singles out these genuine power
expressions, and `PE.normalize` turns any `PE` into a genuine one (or into the empty product)
with the same value and no larger length. -/
inductive PE (α : Type*) where
  | gen : α → PE α
  | mul : PE α → PE α → PE α
  | one : PE α
  | pow : PE α → ℤ → PE α
  deriving DecidableEq

namespace PE

variable {α β γ : Type*}

/-- The value of a power expression in a group, once the letters are given values. -/
def eval {G : Type*} [Group G] (f : α → G) : PE α → G
  | gen a => f a
  | mul E F => eval f E * eval f F
  | one => 1
  | pow E e => eval f E ^ e

/-- `β(e)`: the number of binary digits of `|e|`, plus `1` if `e < 0`. -/
def beta (e : ℤ) : ℕ := Nat.size e.natAbs + if e < 0 then 1 else 0

/-- The length `ℓ(E)`: letters count `1`, `ℓ((E)^e) = ℓ(E) + 2 + β(e)`. -/
def length : PE α → ℕ
  | gen _ => 1
  | mul E F => length E + length F
  | one => 0
  | pow E e => length E + 2 + beta e

/-- `occ(E)`: number of occurrences of letters. -/
def occ : PE α → ℕ
  | gen _ => 1
  | mul E F => occ E + occ F
  | one => 0
  | pow E _ => occ E

/-- `pw(E)`: number of power operations. -/
def pw : PE α → ℕ
  | gen _ => 0
  | mul E F => pw E + pw F
  | one => 0
  | pow E _ => pw E + 1

/-- `ex(E)`: the largest `|e|` occurring in `E` (and `1` if there is none). -/
def ex : PE α → ℕ
  | gen _ => 1
  | mul E F => max (ex E) (ex F)
  | one => 1
  | pow E e => max (ex E) e.natAbs

/-- Genuine power expressions in the sense of Definition 2.1. -/
def WF : PE α → Prop
  | gen _ => True
  | mul E F => WF E ∧ WF F
  | one => False
  | pow E e => WF E ∧ e ≠ 0 ∧ e ≠ 1

/-- The relator in the free group. -/
def toFreeGroup (E : PE α) : FreeGroup α := eval FreeGroup.of E

/-- Substitution `E[W]`. -/
def subst (W : α → PE β) : PE α → PE β
  | gen a => W a
  | mul E F => mul (subst W E) (subst W F)
  | one => one
  | pow E e => pow (subst W E) e

/-- Renaming of letters. -/
def map (f : α → β) (E : PE α) : PE β := subst (fun a => gen (f a)) E

/-- `E^F := F⁻¹ E F`. -/
def conj (E F : PE α) : PE α := mul (mul (pow F (-1)) E) F

/-- `[E, F] := E⁻¹ F⁻¹ E F`. -/
def comm (E F : PE α) : PE α := mul (mul (mul (pow E (-1)) (pow F (-1))) E) F

/-- `E⁻¹`. -/
def inv (E : PE α) : PE α := pow E (-1)

/-! ### evaluation lemmas -/

section eval
variable {G H : Type*} [Group G] [Group H]

@[simp] lemma eval_gen (f : α → G) (a : α) : (gen a).eval f = f a := rfl
@[simp] lemma eval_mul (f : α → G) (E F : PE α) : (mul E F).eval f = E.eval f * F.eval f := rfl
@[simp] lemma eval_one (f : α → G) : (one : PE α).eval f = 1 := rfl
@[simp] lemma eval_pow (f : α → G) (E : PE α) (e : ℤ) : (pow E e).eval f = E.eval f ^ e := rfl
@[simp] lemma eval_conj (f : α → G) (E F : PE α) :
    (conj E F).eval f = (F.eval f)⁻¹ * E.eval f * F.eval f := by
  simp [conj]
@[simp] lemma eval_comm (f : α → G) (E F : PE α) :
    (comm E F).eval f = (E.eval f)⁻¹ * (F.eval f)⁻¹ * E.eval f * F.eval f := by
  simp [comm]
@[simp] lemma eval_inv (f : α → G) (E : PE α) : (inv E).eval f = (E.eval f)⁻¹ := by
  simp [inv]

lemma eval_hom (φ : G →* H) (f : α → G) (E : PE α) : E.eval (φ ∘ f) = φ (E.eval f) := by
  induction E with
  | gen a => rfl
  | mul E F hE hF => simp [hE, hF]
  | one => simp
  | pow E e hE => simp [hE]

lemma eval_subst (f : β → G) (W : α → PE β) (E : PE α) :
    (E.subst W).eval f = E.eval (fun a => (W a).eval f) := by
  induction E with
  | gen a => rfl
  | mul E F hE hF => simp [subst, hE, hF]
  | one => rfl
  | pow E e hE => simp [subst, hE]

lemma eval_map (f : β → G) (g : α → β) (E : PE α) : (E.map g).eval f = E.eval (f ∘ g) := by
  simp [map, eval_subst]; rfl

lemma lift_toFreeGroup (f : α → G) (E : PE α) : FreeGroup.lift f E.toFreeGroup = E.eval f := by
  rw [toFreeGroup, ← eval_hom]
  congr 1
  funext a
  simp

lemma eval_congr {f g : α → G} {E : PE α} (h : ∀ a, f a = g a) : E.eval f = E.eval g := by
  have : f = g := funext h
  rw [this]

end eval

/-! ### Lemma 2.2 -/

lemma beta_le (e : ℤ) : beta e ≤ Nat.log 2 e.natAbs + 2 := by
  unfold beta
  have h1 : Nat.size e.natAbs ≤ Nat.log 2 e.natAbs + 1 :=
    Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) _)
  split_ifs <;> omega

/-- Lemma 2.2 (with `log₂` replaced by `Nat.log 2`, which is slightly stronger). -/
theorem length_le (E : PE α) : E.length ≤ E.occ + E.pw * (Nat.log 2 E.ex + 4) := by
  induction E with
  | gen a => simp [length, occ, pw]
  | mul E F hE hF =>
    simp only [length, occ, pw, ex]
    have h1 : Nat.log 2 E.ex ≤ Nat.log 2 (max E.ex F.ex) := Nat.log_mono_right (le_max_left _ _)
    have h2 : Nat.log 2 F.ex ≤ Nat.log 2 (max E.ex F.ex) := Nat.log_mono_right (le_max_right _ _)
    have h3 := Nat.mul_le_mul_left E.pw (Nat.add_le_add_right h1 4)
    have h4 := Nat.mul_le_mul_left F.pw (Nat.add_le_add_right h2 4)
    nlinarith
  | one => simp [length]
  | pow E e hE =>
    simp only [length, occ, pw, ex]
    have h1 : Nat.log 2 E.ex ≤ Nat.log 2 (max E.ex e.natAbs) :=
      Nat.log_mono_right (le_max_left _ _)
    have h2 : Nat.log 2 e.natAbs ≤ Nat.log 2 (max E.ex e.natAbs) :=
      Nat.log_mono_right (le_max_right _ _)
    have h3 := Nat.mul_le_mul_left E.pw (Nat.add_le_add_right h1 4)
    have hb := beta_le e
    nlinarith

/-! ### equation (2): substitution bounds -/

/-- The maximum of `occ (W a)` over the letters occurring in `E` is bounded by any `m` with
`occ (W a) ≤ m` for all `a`; we state (2) with such uniform bounds. -/
theorem occ_subst_le (W : α → PE β) (E : PE α) (m : ℕ) (hm : ∀ a, (W a).occ ≤ m) :
    (E.subst W).occ ≤ E.occ * m := by
  induction E with
  | gen a => simpa [subst, occ] using hm a
  | mul E F hE hF => simp only [subst, occ]; rw [Nat.add_mul]; omega
  | one => simp [subst, occ]
  | pow E e hE => simpa [subst, occ] using hE

theorem pw_subst_le (W : α → PE β) (E : PE α) (m : ℕ) (hm : ∀ a, (W a).pw ≤ m) :
    (E.subst W).pw ≤ E.pw + E.occ * m := by
  induction E with
  | gen a => simpa [subst, pw, occ] using hm a
  | mul E F hE hF => simp only [subst, pw, occ]; rw [Nat.add_mul]; omega
  | one => simp [subst, pw, occ]
  | pow E e hE => simp only [subst, pw, occ]; omega

/-- The third line of (2), as an inequality (it is an equality only if every letter occurs). -/
theorem ex_subst_le (W : α → PE β) (E : PE α) (m : ℕ) (hm : ∀ a, (W a).ex ≤ m) :
    (E.subst W).ex ≤ max E.ex m := by
  induction E with
  | gen a => simp only [subst, ex]; exact le_trans (hm a) (le_max_right _ _)
  | mul E F hE hF =>
    simp only [subst, ex]
    exact max_le (le_trans hE (max_le_max (le_max_left _ _) le_rfl))
      (le_trans hF (max_le_max (le_max_right _ _) le_rfl))
  | one => simp [subst, ex]
  | pow E e hE =>
    simp only [subst, ex]
    refine max_le (le_trans hE (max_le_max (le_max_left _ _) le_rfl)) ?_
    exact le_trans (le_max_right _ _) (le_max_left _ _)

lemma one_le_ex (E : PE α) : 1 ≤ E.ex := by
  induction E with
  | gen a => simp [ex]
  | mul E F hE hF => simp only [ex]; omega
  | one => simp [ex]
  | pow E e hE => simp only [ex]; omega

/-! ### Normalisation to genuine power expressions -/

/-- Normalisation: drop empty products and exponents `0`, and remove exponents `1`.
`none` stands for the empty product. -/
def normalize : PE α → Option (PE α)
  | gen a => some (gen a)
  | one => none
  | mul E F =>
    match normalize E, normalize F with
    | none, none => none
    | some E', none => some E'
    | none, some F' => some F'
    | some E', some F' => some (mul E' F')
  | pow E e =>
    if e = 0 then none else
    match normalize E with
    | none => none
    | some E' => if e = 1 then some E' else some (pow E' e)

/-- The free-group value of an optional power expression (`none` is the empty product). -/
def optVal : Option (PE α) → FreeGroup α
  | none => 1
  | some E => E.toFreeGroup

lemma normalize_spec (E : PE α) :
    optVal (normalize E) = E.toFreeGroup ∧
    (∀ E', normalize E = some E' → E'.WF ∧ E'.length ≤ E.length) := by
  induction E with
  | gen a => simp [normalize, optVal, WF]
  | one => simp [normalize, optVal, toFreeGroup, eval]
  | mul E F hE hF =>
    obtain ⟨hE1, hE2⟩ := hE
    obtain ⟨hF1, hF2⟩ := hF
    simp only [normalize]
    rcases hnE : normalize E with _ | E' <;> rcases hnF : normalize F with _ | F' <;>
      simp only [hnE, hnF, optVal] at hE1 hF1 ⊢
    · refine ⟨?_, fun _ h => by cases h⟩
      simp [toFreeGroup, eval, ← hE1, ← hF1]
      simp [toFreeGroup] at hE1 hF1; rw [← hE1, ← hF1]; simp
    · refine ⟨?_, ?_⟩
      · simp only [toFreeGroup, eval] at hE1 hF1 ⊢; rw [← hE1, hF1]; simp
      · rintro _ ⟨⟩
        obtain ⟨h1, h2⟩ := hF2 F' hnF
        exact ⟨h1, by simp only [length]; omega⟩
    · refine ⟨?_, ?_⟩
      · simp only [toFreeGroup, eval] at hE1 hF1 ⊢; rw [hE1, ← hF1]; simp
      · rintro _ ⟨⟩
        obtain ⟨h1, h2⟩ := hE2 E' hnE
        exact ⟨h1, by simp only [length]; omega⟩
    · refine ⟨?_, ?_⟩
      · simp only [toFreeGroup, eval] at hE1 hF1 ⊢; rw [hE1, hF1]
      · rintro _ ⟨⟩
        obtain ⟨h1, h2⟩ := hE2 E' hnE
        obtain ⟨h3, h4⟩ := hF2 F' hnF
        exact ⟨⟨h1, h3⟩, by simp only [length]; omega⟩
  | pow E e hE =>
    obtain ⟨hE1, hE2⟩ := hE
    simp only [normalize]
    by_cases he0 : e = 0
    · subst he0; simp [optVal, toFreeGroup, eval]
    · simp only [he0, if_false]
      rcases hnE : normalize E with _ | E' <;> simp only [hnE, optVal] at hE1 ⊢
      · refine ⟨?_, fun _ h => by cases h⟩
        simp only [toFreeGroup, eval] at hE1 ⊢; rw [← hE1]; simp
      · by_cases he1 : e = 1
        · subst he1
          simp only [if_true, optVal]
          refine ⟨?_, ?_⟩
          · simp only [toFreeGroup, eval] at hE1 ⊢; rw [hE1]; simp
          · rintro _ ⟨⟩
            obtain ⟨h1, h2⟩ := hE2 E' hnE
            exact ⟨h1, by simp only [length]; omega⟩
        · simp only [he1, if_false, optVal]
          refine ⟨?_, ?_⟩
          · simp only [toFreeGroup, eval] at hE1 ⊢; rw [hE1]
          · rintro _ ⟨⟩
            obtain ⟨h1, h2⟩ := hE2 E' hnE
            exact ⟨⟨h1, he0, he1⟩, by simp only [length]; omega⟩

end PE

/-! ## Definition 2.4: presentations -/

open PE

/-- `⟨𝒜 | ℛ⟩` is a presentation of `G` via `φ`: every relator has value `1`, and the induced
homomorphism `F(𝒜)/⟨⟨ℛ⟩⟩ → G` is bijective. -/
def IsPresentation {α G : Type*} [Group G] (φ : α → G) (R : Set (PE α)) : Prop :=
  ∃ h : ∀ r ∈ PE.toFreeGroup '' R, FreeGroup.lift φ r = 1,
    Function.Bijective (PresentedGroup.toGroup h)

/-- The presented group `F(𝒜)/⟨⟨ℛ⟩⟩`. -/
abbrev Pres {α : Type*} (R : Set (PE α)) := PresentedGroup (PE.toFreeGroup '' R)

section presentations

variable {α β : Type*} {G : Type*} [Group G]

lemma rels_hold_iff {φ : α → G} {R : Set (PE α)} :
    (∀ r ∈ PE.toFreeGroup '' R, FreeGroup.lift φ r = 1) ↔ ∀ E ∈ R, E.eval φ = 1 := by
  constructor
  · intro h E hE
    rw [← lift_toFreeGroup]
    exact h _ ⟨E, hE, rfl⟩
  · rintro h _ ⟨E, hE, rfl⟩
    rw [lift_toFreeGroup]
    exact h E hE

/-- The homomorphism `Pres R → G` induced by `φ` when the relators hold. -/
def presLift {φ : α → G} {R : Set (PE α)} (h : ∀ E ∈ R, E.eval φ = 1) : Pres R →* G :=
  PresentedGroup.toGroup (rels_hold_iff.mpr h)

@[simp] lemma presLift_of {φ : α → G} {R : Set (PE α)} (h : ∀ E ∈ R, E.eval φ = 1) (a : α) :
    presLift h (PresentedGroup.of a) = φ a :=
  PresentedGroup.toGroup.of _

lemma eval_of_mk {R : Set (PE α)} (E : PE α) :
    E.eval (fun a => (PresentedGroup.of a : Pres R)) =
      PresentedGroup.mk _ E.toFreeGroup := by
  rw [toFreeGroup, ← eval_hom]
  rfl

/-- In the presented group, every relator has value `1`. -/
lemma eval_of_eq_one {R : Set (PE α)} {E : PE α} (hE : E ∈ R) :
    E.eval (fun a => (PresentedGroup.of a : Pres R)) = 1 := by
  rw [eval_of_mk]
  exact PresentedGroup.one_of_mem ⟨E, hE, rfl⟩

lemma isPresentation_iff {φ : α → G} {R : Set (PE α)} :
    IsPresentation φ R ↔ ∃ h : ∀ E ∈ R, E.eval φ = 1, Function.Bijective (presLift h) := by
  constructor
  · rintro ⟨h, hb⟩
    exact ⟨rels_hold_iff.mp h, hb⟩
  · rintro ⟨h, hb⟩
    exact ⟨rels_hold_iff.mpr h, hb⟩

lemma presLift_surjective {φ : α → G} {R : Set (PE α)} (h : ∀ E ∈ R, E.eval φ = 1)
    (hgen : Subgroup.closure (Set.range φ) = ⊤) : Function.Surjective (presLift h) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  exact ⟨PresentedGroup.of a, presLift_of h a⟩

/-- The remark after Definition 2.4: if the relators hold, `φ(𝒜)` generates `G`, and the presented
group is finite of order at most `|G|`, then we have a presentation. -/
theorem isPresentation_of_card_le [Finite G] {φ : α → G} {R : Set (PE α)}
    (h : ∀ E ∈ R, E.eval φ = 1) (hgen : Subgroup.closure (Set.range φ) = ⊤)
    (hfin : Finite (Pres R)) (hcard : Nat.card (Pres R) ≤ Nat.card G) :
    IsPresentation φ R :=
  isPresentation_iff.mpr ⟨h, (presLift_surjective h hgen).bijective_of_nat_card_le hcard⟩

/-- The isomorphism `Pres R ≃* G` given by a presentation. -/
noncomputable def IsPresentation.equiv {φ : α → G} {R : Set (PE α)} (hP : IsPresentation φ R) :
    Pres R ≃* G :=
  MulEquiv.ofBijective (presLift (isPresentation_iff.mp hP).1) (isPresentation_iff.mp hP).2

@[simp] lemma IsPresentation.equiv_of {φ : α → G} {R : Set (PE α)} (hP : IsPresentation φ R)
    (a : α) : hP.equiv (PresentedGroup.of a) = φ a := by
  simp [IsPresentation.equiv]

lemma IsPresentation.rels {φ : α → G} {R : Set (PE α)} (hP : IsPresentation φ R) :
    ∀ E ∈ R, E.eval φ = 1 := (isPresentation_iff.mp hP).1

/-- Universal property used throughout: if `ψ : 𝒜 → K` satisfies the relators of a presentation of
`G` via `φ`, there is a homomorphism `G →* K` sending `φ a` to `ψ a`. -/
noncomputable def IsPresentation.lift {K : Type*} [Group K] {φ : α → G} {R : Set (PE α)}
    (hP : IsPresentation φ R) {ψ : α → K} (hψ : ∀ E ∈ R, E.eval ψ = 1) : G →* K :=
  (presLift hψ).comp hP.equiv.symm.toMonoidHom

@[simp] lemma IsPresentation.lift_apply {K : Type*} [Group K] {φ : α → G} {R : Set (PE α)}
    (hP : IsPresentation φ R) {ψ : α → K} (hψ : ∀ E ∈ R, E.eval ψ = 1) (a : α) :
    hP.lift hψ (φ a) = ψ a := by
  simp only [IsPresentation.lift, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [← hP.equiv_of a, MulEquiv.symm_apply_apply, presLift_of]

lemma IsPresentation.lift_eval {K : Type*} [Group K] {φ : α → G} {R : Set (PE α)}
    (hP : IsPresentation φ R) {ψ : α → K} (hψ : ∀ E ∈ R, E.eval ψ = 1) (E : PE α) :
    hP.lift hψ (E.eval φ) = E.eval ψ := by
  rw [← eval_hom]
  exact eval_congr (fun a => hP.lift_apply hψ a)

lemma IsPresentation.closure_eq_top {φ : α → G} {R : Set (PE α)} (hP : IsPresentation φ R) :
    Subgroup.closure (Set.range φ) = ⊤ := by
  rw [eq_top_iff]
  have key : ∀ x : Pres R, hP.equiv x ∈ Subgroup.closure (Set.range φ) := by
    intro x
    induction x using PresentedGroup.induction_on with
    | H z =>
      induction z using FreeGroup.induction_on with
      | C1 => simpa using Subgroup.one_mem _
      | of a =>
        have : hP.equiv (PresentedGroup.mk _ (FreeGroup.of a)) = φ a := hP.equiv_of a
        rw [this]; exact Subgroup.subset_closure ⟨a, rfl⟩
      | inv_of a ha =>
        rw [map_inv, map_inv]; exact Subgroup.inv_mem _ ha
      | mul x y hx hy =>
        rw [map_mul, map_mul]; exact Subgroup.mul_mem _ hx hy
  intro g _
  obtain ⟨x, rfl⟩ := hP.equiv.surjective g
  exact key x

lemma IsPresentation.finite [Finite G] {φ : α → G} {R : Set (PE α)} (hP : IsPresentation φ R) :
    Finite (Pres R) := Finite.of_equiv _ hP.equiv.symm.toEquiv

lemma IsPresentation.card_eq {φ : α → G} {R : Set (PE α)} (hP : IsPresentation φ R) :
    Nat.card (Pres R) = Nat.card G := Nat.card_congr hP.equiv.toEquiv

/-- If two relator sets have the same normal closure in the free group, they present the same
groups. -/
theorem isPresentation_congr {φ : α → G} {R R' : Set (PE α)}
    (hN : Subgroup.normalClosure (PE.toFreeGroup '' R) =
      Subgroup.normalClosure (PE.toFreeGroup '' R')) :
    IsPresentation φ R → IsPresentation φ R' := by
  rintro ⟨h, hb⟩
  have hker := PresentedGroup.closure_rels_subset_ker h
  have h' : ∀ r ∈ PE.toFreeGroup '' R', FreeGroup.lift φ r = 1 := by
    intro r hr
    have : r ∈ Subgroup.normalClosure (PE.toFreeGroup '' R) :=
      hN ▸ Subgroup.subset_normalClosure hr
    exact hker this
  refine ⟨h', ?_⟩
  let e : Pres R ≃* Pres R' := QuotientGroup.quotientMulEquivOfEq hN
  have hcomp : (PresentedGroup.toGroup h').comp e.toMonoidHom = PresentedGroup.toGroup h := by
    apply PresentedGroup.ext
    intro a
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, PresentedGroup.toGroup.of]
    have : e (PresentedGroup.of a) = PresentedGroup.of a :=
      QuotientGroup.quotientMulEquivOfEq_mk hN _
    rw [this, PresentedGroup.toGroup.of]
  have : ⇑(PresentedGroup.toGroup h') = ⇑(PresentedGroup.toGroup h) ∘ e.symm := by
    funext x
    have := congrArg (fun f => f (e.symm x)) hcomp
    simpa using this
  rw [this]
  exact hb.comp e.symm.bijective

end presentations

/-! ## Lemma 2.5: elimination of generators -/

section elim

variable {α β : Type*} {G : Type*} [Group G]

lemma toFreeGroup_subst (W : α → PE β) (E : PE α) :
    (E.subst W).toFreeGroup = FreeGroup.lift (fun a => (W a).toFreeGroup) E.toFreeGroup := by
  rw [lift_toFreeGroup, toFreeGroup, eval_subst]
  rfl

/-- Lemma 2.5. -/
theorem elim_generators {φ : α ⊕ β → G} {R : Set (PE (α ⊕ β))} (hP : IsPresentation φ R)
    (W : β → PE α) (hW : ∀ b, (W b).eval (φ ∘ Sum.inl) = φ (Sum.inr b)) :
    IsPresentation (φ ∘ Sum.inl) (PE.subst (Sum.elim PE.gen W) '' R) := by
  set σ : α ⊕ β → PE α := Sum.elim PE.gen W with hσ
  set R' : Set (PE α) := PE.subst σ '' R with hR'
  have hσval : ∀ c, (σ c).eval (φ ∘ Sum.inl) = φ c := by
    rintro (a | b)
    · rfl
    · exact hW b
  have hval : ∀ E : PE (α ⊕ β), (E.subst σ).eval (φ ∘ Sum.inl) = E.eval φ := by
    intro E
    rw [eval_subst]
    exact eval_congr hσval
  have hrel : ∀ E ∈ R', E.eval (φ ∘ Sum.inl) = 1 := by
    rintro _ ⟨E, hE, rfl⟩
    rw [hval]
    exact hP.rels E hE
  -- the homomorphism `Pres R → Pres R'`
  have hψ : ∀ E ∈ R, E.eval (fun c => (σ c).eval (fun a => (PresentedGroup.of a : Pres R'))) = 1 := by
    intro E hE
    rw [← eval_subst]
    exact eval_of_eq_one ⟨E, hE, rfl⟩
  let ψ : Pres R →* Pres R' := presLift hψ
  let iso := presLift hP.rels
  have hiso : Function.Bijective iso := (isPresentation_iff.mp hP).2
  let tg := presLift hrel
  have hcomp : tg.comp ψ = iso := by
    apply PresentedGroup.ext
    intro c
    simp only [MonoidHom.comp_apply, ψ, presLift_of, tg, iso]
    rw [← eval_hom]
    have : (⇑(presLift hrel) ∘ fun a => (PresentedGroup.of a : Pres R')) = φ ∘ Sum.inl := by
      funext a; simp
    rw [this]
    exact hσval c
  have hψsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    rw [← PresentedGroup.closure_range_of, Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    refine ⟨PresentedGroup.of (Sum.inl a), ?_⟩
    simp [ψ, σ]
  refine isPresentation_iff.mpr ⟨hrel, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨x0, rfl⟩ := hψsurj x
    obtain ⟨y0, rfl⟩ := hψsurj y
    have : iso x0 = iso y0 := by
      rw [← hcomp]; simpa using hxy
    rw [hiso.1 this]
  · intro g
    obtain ⟨x, hx⟩ := hiso.2 g
    exact ⟨ψ x, by rw [← hx, ← hcomp]; rfl⟩

end elim

end SnPres
