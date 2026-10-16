/-
The main theorem in Mathlib's conventions.

`Sym n = (Equiv.Perm (Fin n))ᵐᵒᵖ` composes permutations "first the left factor", as in the
paper.  Mathlib's `Equiv.Perm (Fin n)` composes "first the right factor" (`σ * τ = σ ∘ τ`).
Reading a power expression backwards (`PE.rev`) translates presentations between the two
conventions, without changing lengths.  Here `x = Equiv.swap 0 1` and `y = finRotate n`
(`i ↦ i + 1 mod n`).
-/
import SnPres.Main

namespace SnPres

open PE

namespace PE
variable {α : Type*}

/-- reading a power expression backwards -/
def rev : PE α → PE α
  | gen a => gen a
  | mul E F => mul (rev F) (rev E)
  | one => one
  | pow E e => pow (rev E) e

lemma eval_rev_op {G : Type*} [Group G] (f : α → G) (E : PE α) :
    E.eval (fun a => MulOpposite.op (f a)) = MulOpposite.op ((rev E).eval f) := by
  induction E with
  | gen a => rfl
  | mul E F hE hF => simp only [eval, rev, hE, hF, MulOpposite.op_mul]
  | one => simp [eval, rev]
  | pow E e hE => simp only [eval, rev, hE, MulOpposite.op_zpow]

lemma length_rev (E : PE α) : (rev E).length = E.length := by
  induction E with
  | gen a => rfl
  | mul E F hE hF => simp only [rev, length, hE, hF]; omega
  | one => rfl
  | pow E e hE => simp only [rev, length, hE]

lemma wf_rev (E : PE α) (h : E.WF) : (rev E).WF := by
  induction E with
  | gen a => trivial
  | mul E F hE hF => exact ⟨hF h.2, hE h.1⟩
  | one => exact h
  | pow E e hE => exact ⟨hE h.1, h.2⟩

lemma rev_rev (E : PE α) : rev (rev E) = E := by
  induction E with
  | gen a => rfl
  | mul E F hE hF => simp only [rev, hE, hF]
  | one => rfl
  | pow E e hE => simp only [rev, hE]

end PE

/-- A presentation of `Gᵐᵒᵖ` on `op ∘ f` gives a presentation of `G` on `f` with reversed
relators. -/
theorem isPresentation_rev {α G : Type*} [Group G] [Finite G] {f : α → G} {R : Set (PE α)}
    (h : IsPresentation (fun a => MulOpposite.op (f a)) R) : IsPresentation f (PE.rev '' R) := by
  -- the relators hold
  have hrel : ∀ E ∈ PE.rev '' R, E.eval f = 1 := by
    rintro _ ⟨E, hE, rfl⟩
    have := h.rels E hE
    rw [PE.eval_rev_op] at this
    exact MulOpposite.op_injective (this.trans MulOpposite.op_one.symm)
  -- generation
  have hgen : Subgroup.closure (Set.range f) = ⊤ := by
    have h1 := h.closure_eq_top
    rw [← Subgroup.unop_eq_top, Subgroup.unop_closure] at h1
    have e : MulOpposite.op ⁻¹' Set.range (fun a => MulOpposite.op (f a)) = Set.range f := by
      ext g; simp
    rwa [e] at h1
  -- `|⟨𝒜 | rev ℛ⟩| ≤ |⟨𝒜 | ℛ⟩| = |G|`
  set P := Pres (PE.rev '' R)
  have hψ : ∀ E ∈ R, E.eval (fun a => MulOpposite.op (PresentedGroup.of a : P)) = 1 := by
    intro E hE
    rw [PE.eval_rev_op, eval_of_eq_one (show PE.rev E ∈ PE.rev '' R from ⟨E, hE, rfl⟩),
      MulOpposite.op_one]
  let Θ : Pres R →* Pᵐᵒᵖ := presLift hψ
  have hΘ : Function.Surjective Θ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    have : Subgroup.closure (Set.range (fun a => MulOpposite.op (PresentedGroup.of a : P))) = ⊤ := by
      rw [← Subgroup.unop_eq_top, Subgroup.unop_closure]
      have e : MulOpposite.op ⁻¹' Set.range (fun a => MulOpposite.op (PresentedGroup.of a : P)) =
          Set.range (fun a => (PresentedGroup.of a : P)) := by ext g; simp
      rw [e]; exact closure_range_of' _
    rw [← this, Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨PresentedGroup.of a, presLift_of hψ a⟩
  haveI : Finite Gᵐᵒᵖ := Finite.of_equiv _ MulOpposite.opEquiv
  haveI : Finite (Pres R) := h.finite
  have hfin : Finite P := by
    haveI : Finite Pᵐᵒᵖ := Finite.of_surjective Θ hΘ
    exact Finite.of_equiv _ MulOpposite.opEquiv.symm
  have hcard : Nat.card P ≤ Nat.card G := by
    have h1 : Nat.card Pᵐᵒᵖ ≤ Nat.card (Pres R) := Nat.card_le_card_of_surjective Θ hΘ
    rw [h.card_eq, ← Nat.card_congr (MulOpposite.opEquiv : G ≃ Gᵐᵒᵖ),
      ← Nat.card_congr (MulOpposite.opEquiv : P ≃ Pᵐᵒᵖ)] at *
    exact h1
  exact isPresentation_of_card_le hrel hgen hfin hcard

/-- the standard generators `x = (0 1)` and `y = (0 1 … n-1)` in `Equiv.Perm (Fin n)` -/
def stdGen (n : ℕ) (hn : 1 < n) : XY → Equiv.Perm (Fin n)
  | .x => Equiv.swap ⟨0, by omega⟩ ⟨1, hn⟩
  | .y => finRotate n

lemma xyv_eq_op (n : ℕ) (hn : 1 < n) :
    xyv n hn = fun c => MulOpposite.op (stdGen n hn c) := by
  funext c; cases c <;> rfl

/-- **Theorem 1.1 in Mathlib's conventions**: presentations of `Equiv.Perm (Fin n)` on
`Equiv.swap 0 1` and `finRotate n`. -/
theorem main_theorem_mathlib : ∃ r₀ c₀ : ℕ, ∀ n (hn : 2 ≤ n), ∃ R : Finset (PE XY),
    IsPresentation (stdGen n (by omega)) (R : Set (PE XY)) ∧ (∀ E ∈ R, E.WF) ∧
      R.card ≤ r₀ ∧ presLength R ≤ c₀ * Nat.log 2 n := by
  classical
  obtain ⟨r₀, c₀, H⟩ := main_theorem
  refine ⟨r₀, c₀, fun n hn => ?_⟩
  obtain ⟨R, hP, hW, hc, hl⟩ := H n hn
  have hinj : Set.InjOn PE.rev (R : Set (PE XY)) := fun E _ F _ h => by
    rw [← PE.rev_rev E, h, PE.rev_rev]
  refine ⟨R.image PE.rev, ?_, ?_, ?_, ?_⟩
  · rw [Finset.coe_image]
    rw [xyv_eq_op] at hP
    exact isPresentation_rev hP
  · intro E hE
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hE
    exact PE.wf_rev F (hW F hF)
  · exact Finset.card_image_le.trans hc
  · unfold presLength at hl ⊢
    rw [Finset.sum_image hinj]
    simp only [PE.length_rev]
    exact hl

theorem main_theorem_mathlib_62 : ∃ c₀ : ℕ, ∀ n (hn : 245 ≤ n), ∃ R : Finset (PE XY),
    IsPresentation (stdGen n (by omega)) (R : Set (PE XY)) ∧ (∀ E ∈ R, E.WF) ∧
      R.card ≤ 62 ∧ presLength R ≤ c₀ * Nat.log 2 n := by
  classical
  obtain ⟨c₀, H⟩ := main_theorem_62
  refine ⟨c₀, fun n hn => ?_⟩
  obtain ⟨R, hP, hW, hc, hl⟩ := H n hn
  have hinj : Set.InjOn PE.rev (R : Set (PE XY)) := fun E _ F _ h => by
    rw [← PE.rev_rev E, h, PE.rev_rev]
  refine ⟨R.image PE.rev, ?_, ?_, ?_, ?_⟩
  · rw [Finset.coe_image]
    rw [xyv_eq_op] at hP
    exact isPresentation_rev hP
  · intro E hE
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hE
    exact PE.wf_rev F (hW F hF)
  · exact Finset.card_image_le.trans hc
  · unfold presLength at hl ⊢
    rw [Finset.sum_image hinj]
    simp only [PE.length_rev]
    exact hl

end SnPres
