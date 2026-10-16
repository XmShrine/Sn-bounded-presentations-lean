/-
Section 5: presentations of `SL(2,p)` and `ASL(2,p)`.

* Proposition 5.2 (from Sunday's theorem, used as an axiom in its weak form `sunday_bound`);
* Proposition 5.3 (the nine relators A1–A9);
* Corollary 5.4 (ten relators on `L, U, T`);
* Lemma 5.5': the normal closure of `α_{M_L, e₁}` is all of `ASL(2,p)`.  (This replaces the
  paper's Lemma 5.5, which classifies all normal subgroups using the simplicity of `PSL(2,p)`
  [Huppert]; Step 5 of Theorem 6.3 only needs the present weaker statement, which we prove
  directly.)
-/
import SnPres.PE
import SnPres.Affine
import SnPres.Axioms
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Field.ZMod

namespace SnPres

open PE SL2 ASL2

variable {p : ℕ} [Fact p.Prime]

/-! ### Facts about `SL(2,p)` -/

section SLfacts

lemma Lx_eq_pow (x : ZMod p) : Lx x = (ML : SL2 p) ^ x.val := by
  rw [ML_pow, ZMod.natCast_zmod_val]

lemma Uy_eq_pow (y : ZMod p) : Uy y = (MU : SL2 p) ^ y.val := by
  rw [MU_pow, ZMod.natCast_zmod_val]

/-- `M_L` and `M_U` generate `SL(2,p)`. -/
theorem closure_ML_MU : Subgroup.closure ({ML, MU} : Set (SL2 p)) = ⊤ := by
  rw [eq_top_iff]
  intro M _
  set H := Subgroup.closure ({ML, MU} : Set (SL2 p))
  have hL : ∀ x : ZMod p, Lx x ∈ H := fun x => by
    rw [Lx_eq_pow]; exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  have hU : ∀ y : ZMod p, Uy y ∈ H := fun y => by
    rw [Uy_eq_pow]; exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  have key : ∀ N : SL2 p, N.c ≠ 0 → N ∈ H := by
    intro N hc
    have : N = Lx ((N.a - 1) / N.c) * Uy N.c * Lx ((N.d - 1) / N.c) := by
      ext <;> simp [Lx, Uy] <;> field_simp <;>
        first | ring1 | linear_combination N.det | linear_combination (-1 : ZMod p) * N.det
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hL _) (hU _)) (hL _)
  by_cases hc : M.c = 0
  · have hd : M.d ≠ 0 := by
      intro h; have := M.det; rw [hc, h] at this; simp at this
    have h1 : M * Uy 1 ∈ H := key _ (by simp [Uy, hc, hd])
    have : M = (M * Uy 1) * (Uy 1)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hU 1))
  · exact key M hc

/-- equation (3), first two identities -/
lemma MC_eq : (ML : SL2 p)⁻¹ * MU * ML⁻¹ = MC := by ext <;> simp [ML, MU, MC]
lemma MU_eq : (MC : SL2 p)⁻¹ * ML⁻¹ * MC = MU := by ext <;> simp [ML, MU, MC]

lemma closure_ML_MC : Subgroup.closure ({ML, MC} : Set (SL2 p)) = ⊤ := by
  rw [eq_top_iff, ← closure_ML_MU, Subgroup.closure_le]
  intro M hM
  rcases hM with rfl | rfl
  · exact Subgroup.subset_closure (by simp)
  · rw [← MU_eq]
    have h1 : (MC : SL2 p) ∈ Subgroup.closure ({ML, MC} : Set (SL2 p)) :=
      Subgroup.subset_closure (by simp)
    have h2 : (ML : SL2 p) ∈ Subgroup.closure ({ML, MC} : Set (SL2 p)) :=
      Subgroup.subset_closure (by simp)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ h1)
      (Subgroup.inv_mem _ h2)) h1

/-- `e₁ = (1, 0)`, `e₂ = (0, 1)`. -/
abbrev e1 : Vec p := (1, 0)
abbrev e2 : Vec p := (0, 1)

/-- a matrix with first row `v` (for `v ≠ 0`) -/
noncomputable def Mrow (v : Vec p) : SL2 p :=
  if h1 : v.1 ≠ 0 then ⟨v.1, v.2, 0, v.1⁻¹, by field_simp; simp⟩
  else if h2 : v.2 ≠ 0 then ⟨0, v.2, -(v.2)⁻¹, 0, by field_simp; ring⟩
  else 1

lemma vecMul_e1 (M : SL2 p) : vecMul e1 M = (M.a, M.b) := by ext <;> simp
lemma vecMul_e2 (M : SL2 p) : vecMul e2 M = (M.c, M.d) := by ext <;> simp

lemma vecMul_e1_Mrow {v : Vec p} (hv : v ≠ 0) : vecMul e1 (Mrow v) = v := by
  rw [vecMul_e1]
  unfold Mrow
  by_cases h1 : v.1 ≠ 0
  · rw [dif_pos h1]
  · have h2 : v.2 ≠ 0 := by
      intro h2; apply hv; ext
      · simpa using h1
      · simpa using h2
    rw [dif_neg h1, dif_pos h2]
    ext
    · simp only; push_neg at h1; exact h1.symm
    · rfl

/-- `SL(2,p)` is transitive on nonzero vectors. -/
lemma exists_row (v : Vec p) (hv : v ≠ 0) : ∃ M : SL2 p, vecMul e1 M = v :=
  ⟨Mrow v, vecMul_e1_Mrow hv⟩

/-- The matrix with rows `v`, `w` when `det(v, w) = 1`. -/
def rows (v w : Vec p) (h : v.1 * w.2 - v.2 * w.1 = 1) : SL2 p := ⟨v.1, v.2, w.1, w.2, h⟩

lemma vecMul_e1_rows (v w : Vec p) (h) : vecMul e1 (rows v w h) = v := by
  rw [vecMul_e1]; rfl
lemma vecMul_e2_rows (v w : Vec p) (h) : vecMul e2 (rows v w h) = w := by
  rw [vecMul_e2]; rfl

/-- The stabiliser of `e₁` consists of the lower transvections `M_U^k`. -/
lemma stab_e1 {M : SL2 p} (h : vecMul e1 M = e1) : M = Uy M.c := by
  rw [vecMul_e1] at h
  have ha : M.a = 1 := congrArg Prod.fst h
  have hb : M.b = 0 := congrArg Prod.snd h
  have hd : M.d = 1 := by have := M.det; rw [ha, hb] at this; simpa using this
  ext <;> simp [Uy, ha, hb, hd]

lemma vecMul_ne_zero {v : Vec p} (hv : v ≠ 0) (M : SL2 p) : vecMul v M ≠ 0 := by
  intro h
  apply hv
  have := congrArg (fun w => vecMul w M⁻¹) h
  simp only [← vecMul_mul, mul_inv_cancel, vecMul_one, vecMul_zero] at this
  exact this

end SLfacts

/-! ### `|SL(2,p)| = p(p²-1)` -/

section card

instance : DecidableEq (SL2 p) := fun M N =>
  decidable_of_iff (M.a = N.a ∧ M.b = N.b ∧ M.c = N.c ∧ M.d = N.d) (by
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact SL2.ext h1 h2 h3 h4
    · rintro rfl; exact ⟨rfl, rfl, rfl, rfl⟩)

/-- `SL(2,p) ≃ {v ≠ 0} × 𝔽_p` (first row, and one free entry of the second row). -/
noncomputable def slEquiv : SL2 p ≃ {v : Vec p // v ≠ 0} × ZMod p where
  toFun M := (⟨(M.a, M.b), by
      intro h
      have ha : M.a = 0 := congrArg Prod.fst h
      have hb : M.b = 0 := congrArg Prod.snd h
      have := M.det; rw [ha, hb] at this; simp at this⟩,
    if M.a ≠ 0 then M.c else M.d)
  invFun x :=
    if h : x.1.1.1 ≠ 0 then
      ⟨x.1.1.1, x.1.1.2, x.2, (1 + x.1.1.2 * x.2) / x.1.1.1, by field_simp; ring⟩
    else
      ⟨0, x.1.1.2, -(x.1.1.2)⁻¹, x.2, by
        have h2 : x.1.1.2 ≠ 0 := by
          intro h2; apply x.1.2; ext <;> simp_all
        field_simp; ring⟩
  left_inv M := by
    by_cases ha : M.a = 0
    · have hb : M.b ≠ 0 := by
        intro hb; have := M.det; rw [ha, hb] at this; simp at this
      simp only [ha, ne_eq, not_true_eq_false, ite_false, dite_false]
      ext
      · simp [ha]
      · simp
      · simp only
        have := M.det; rw [ha] at this
        field_simp
        first | ring1 | linear_combination this | linear_combination (-1 : ZMod p) * this
      · simp
    · simp only [ha, ne_eq, not_false_eq_true, ite_true, dite_true]
      ext
      · simp
      · simp
      · simp
      · simp only
        have := M.det
        field_simp
        first | ring1 | linear_combination this | linear_combination (-1 : ZMod p) * this
  right_inv x := by
    obtain ⟨⟨⟨a, b⟩, hv⟩, t⟩ := x
    by_cases ha : a = 0
    · subst ha
      simp
    · simp [ha]

noncomputable instance : Fintype (SL2 p) := Fintype.ofEquiv _ slEquiv.symm

lemma card_SL2 : Fintype.card (SL2 p) = p * (p ^ 2 - 1) := by
  rw [Fintype.card_congr slEquiv, Fintype.card_prod, ZMod.card]
  have : Fintype.card {v : Vec p // v ≠ 0} = p ^ 2 - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_prod, ZMod.card, Fintype.card_unique]
    ring_nf
  rw [this, Nat.mul_comm]

lemma natCard_SL2 : Nat.card (SL2 p) = p * (p ^ 2 - 1) := by
  rw [Nat.card_eq_fintype_card, card_SL2]

/-- `ASL(2,p) ≃ SL(2,p) × 𝔽_p²` as sets. -/
def aslEquiv : ASL2 p ≃ SL2 p × Vec p where
  toFun α := (α.M, α.w)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype (ASL2 p) := Fintype.ofEquiv _ aslEquiv.symm

lemma natCard_ASL2 : Nat.card (ASL2 p) = p ^ 2 * Nat.card (SL2 p) := by
  rw [Nat.card_congr aslEquiv, Nat.card_prod, Nat.card_eq_fintype_card (α := Vec p),
    Fintype.card_prod, ZMod.card, Nat.mul_comm]
  ring

end card

end SnPres

namespace SnPres

open PE SL2 ASL2

/-! ### The relators of Propositions 5.2/5.3, generic in the letters -/

section relators
variable {α : Type*}

/-- `h = (p+1)/2` -/
def hh (p : ℕ) : ℕ := (p + 1) / 2

/-- (A1) `a^p` -/
def RA1 (a : PE α) (p : ℕ) : PE α := pow a p
/-- (A2) `a c a c a c⁻¹` -/
def RA2 (a c : PE α) : PE α := mul (mul (mul (mul (mul a c) a) c) a) (inv c)
/-- (A3) `(a^h c a^4 c)^2 c^{-2}` -/
def RA3 (a c : PE α) (p : ℕ) : PE α :=
  mul (pow (mul (mul (mul (pow a (hh p)) c) (pow a 4)) c) 2) (pow c (-2))
/-- (A4) `c^4` -/
def RA4 (c : PE α) : PE α := pow c 4
/-- `u = c⁻¹ a⁻¹ c` -/
def Pu (a c : PE α) : PE α := mul (mul (inv c) (inv a)) c
/-- `ε = c t c⁻¹` -/
def Peps (c t : PE α) : PE α := mul (mul c t) (inv c)
/-- `d = a^λ u^{-μ} a^λ c` -/
def Pd (a u c : PE α) (lam mu : ℕ) : PE α :=
  mul (mul (mul (pow a lam) (pow u (-(mu : ℤ)))) (pow a lam)) c
/-- (A5) `t^p` -/
def RA5 (t : PE α) (p : ℕ) : PE α := pow t p
/-- (A6) `[t, u]` -/
def RA6 (t u : PE α) : PE α := comm t u
/-- (A7) `[t, ε]` -/
def RA7 (t e : PE α) : PE α := comm t e
/-- (A8) `t ε a⁻¹ t⁻¹ a` -/
def RA8 (a t e : PE α) : PE α := mul (mul (mul (mul t e) (inv a)) (inv t)) a
/-- (A9) `d⁻¹ t d t^{-λ}` -/
def RA9 (d t : PE α) (lam : ℕ) : PE α := mul (mul (mul (inv d) t) d) (pow t (-(lam : ℤ)))

variable {G : Type*} [Group G] (f : α → G)

@[simp] lemma eval_RA1 (a : PE α) (p : ℕ) : (RA1 a p).eval f = a.eval f ^ p := by
  simp only [RA1, eval_pow]; exact zpow_natCast _ _
@[simp] lemma eval_RA2 (a c : PE α) : (RA2 a c).eval f =
    a.eval f * c.eval f * a.eval f * c.eval f * a.eval f * (c.eval f)⁻¹ := by simp [RA2]
@[simp] lemma eval_RA3 (a c : PE α) (p : ℕ) : (RA3 a c p).eval f =
    (a.eval f ^ hh p * c.eval f * a.eval f ^ 4 * c.eval f) ^ 2 * (c.eval f ^ 2)⁻¹ := by
  simp only [RA3, eval_mul, eval_pow, zpow_natCast]
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast,
    show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast,
    show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
@[simp] lemma eval_RA4 (c : PE α) : (RA4 c).eval f = c.eval f ^ 4 := by
  simp only [RA4, eval_pow]; exact zpow_ofNat _ 4
@[simp] lemma eval_Pu (a c : PE α) : (Pu a c).eval f = (c.eval f)⁻¹ * (a.eval f)⁻¹ * c.eval f := by
  simp [Pu]
@[simp] lemma eval_Peps (c t : PE α) : (Peps c t).eval f = c.eval f * t.eval f * (c.eval f)⁻¹ := by
  simp [Peps]
@[simp] lemma eval_Pd (a u c : PE α) (lam mu : ℕ) : (Pd a u c lam mu).eval f =
    a.eval f ^ lam * (u.eval f ^ mu)⁻¹ * a.eval f ^ lam * c.eval f := by
  simp only [Pd, eval_mul, eval_pow, zpow_natCast, zpow_neg]
@[simp] lemma eval_RA5 (t : PE α) (p : ℕ) : (RA5 t p).eval f = t.eval f ^ p := by
  simp only [RA5, eval_pow]; exact zpow_natCast _ _
@[simp] lemma eval_RA6 (t u : PE α) : (RA6 t u).eval f =
    (t.eval f)⁻¹ * (u.eval f)⁻¹ * t.eval f * u.eval f := by simp [RA6]
@[simp] lemma eval_RA7 (t e : PE α) : (RA7 t e).eval f =
    (t.eval f)⁻¹ * (e.eval f)⁻¹ * t.eval f * e.eval f := by simp [RA7]
@[simp] lemma eval_RA8 (a t e : PE α) : (RA8 a t e).eval f =
    t.eval f * e.eval f * (a.eval f)⁻¹ * (t.eval f)⁻¹ * a.eval f := by simp [RA8]
@[simp] lemma eval_RA9 (d t : PE α) (lam : ℕ) : (RA9 d t lam).eval f =
    (d.eval f)⁻¹ * t.eval f * d.eval f * (t.eval f ^ lam)⁻¹ := by
  simp only [RA9, eval_mul, eval_inv, eval_pow, zpow_neg, zpow_natCast]

end relators

/-! ### Proposition 5.2 -/

/-- The alphabet `{a, c}`. -/
inductive AC | a | c
  deriving DecidableEq

/-- The relators of Proposition 5.2. -/
def slRels (p : ℕ) : Set (PE AC) :=
  {RA1 (gen .a) p, RA2 (gen .a) (gen .c), RA3 (gen .a) (gen .c) p, RA4 (gen .c)}

variable {p : ℕ} [Fact p.Prime]

/-- `a ↦ M_L`, `c ↦ M_C` -/
def slVal : AC → SL2 p
  | .a => ML
  | .c => MC

lemma p_odd (h5 : 5 ≤ p) : p % 2 = 1 := by
  rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
  · omega
  · exact h

lemma two_mul_hh (h5 : 5 ≤ p) : 2 * hh p = p + 1 := by
  have := p_odd h5; unfold hh; omega

lemma two_hh_cast (h5 : 5 ≤ p) : (2 : ZMod p) * (hh p : ZMod p) = 1 := by
  have := congrArg (Nat.cast : ℕ → ZMod p) (two_mul_hh h5)
  push_cast at this
  rw [this, ZMod.natCast_self, zero_add]

lemma MLp : (ML : SL2 p) ^ p = 1 := by
  rw [ML_pow, ZMod.natCast_self]; ext <;> simp [Lx]

lemma MC_sq : (MC : SL2 p) ^ 2 = negI := by ext <;> simp [MC, negI, pow_two]

lemma sl_rels_hold (h5 : 5 ≤ p) : ∀ E ∈ slRels p, E.eval (slVal (p := p)) = 1 := by
  intro E hE
  simp only [slRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hE
  have h2 := two_hh_cast (p := p) h5
  rcases hE with rfl | rfl | rfl | rfl
  · simp only [eval_RA1, eval_gen, slVal]; exact MLp
  · simp only [eval_RA2, eval_gen, slVal]; ext <;> simp [ML, MC]
  · simp only [eval_RA3, eval_gen, slVal]
    rw [ML_pow, ML_pow, MC_sq]
    have hX : (Lx (hh p : ZMod p) * MC * Lx ((4 : ℕ) : ZMod p) * MC) ^ 2 = (negI : SL2 p) := by
      ext
      · simp [Lx, MC, negI, pow_two]; push_cast; linear_combination (8 * (hh p : ZMod p) - 2) * h2
      · simp [Lx, MC, negI, pow_two]; push_cast; linear_combination (-2 * (hh p : ZMod p)) * h2
      · simp [Lx, MC, negI, pow_two]; push_cast; linear_combination (8 : ZMod p) * h2
      · simp [Lx, MC, negI, pow_two]; push_cast; linear_combination (-2 : ZMod p) * h2
    rw [hX, mul_inv_cancel]
  · simp only [eval_RA4, eval_gen, slVal]
    rw [show 4 = 2 * 2 from rfl, pow_mul, MC_sq]; ext <;> simp [negI, pow_two]

lemma range_slVal : Set.range (slVal (p := p)) = {ML, MC} := by
  ext M; constructor
  · rintro ⟨x, rfl⟩; cases x <;> simp [slVal]
  · rintro (rfl | rfl)
    · exact ⟨.a, rfl⟩
    · exact ⟨.c, rfl⟩

/-! ### Order bounds from presentations -/

/-- If `K` is generated by elements satisfying the relators of a finitely presented finite group
`P`, then `K` is finite and `|K| ≤ |P|`. -/
theorem card_le_of_presented {α K : Type*} [Group K] {rels : Set (FreeGroup α)}
    (f : α → K) (hf : ∀ r ∈ rels, FreeGroup.lift f r = 1)
    (hgen : Subgroup.closure (Set.range f) = ⊤) (hfin : Finite (PresentedGroup rels)) :
    Finite K ∧ Nat.card K ≤ Nat.card (PresentedGroup rels) := by
  have hsurj : Function.Surjective (PresentedGroup.toGroup hf) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨PresentedGroup.of a, PresentedGroup.toGroup.of hf⟩
  exact ⟨Finite.of_surjective _ hsurj, Nat.card_le_card_of_surjective _ hsurj⟩

/-- the images of generators generate a quotient -/
lemma closure_range_quotient {α G : Type*} [Group G] (g : α → G)
    (hg : Subgroup.closure (Set.range g) = ⊤) (N : Subgroup G) [N.Normal] :
    Subgroup.closure (Set.range (fun a => (QuotientGroup.mk (g a) : G ⧸ N))) = ⊤ := by
  have : Set.range (fun a => (QuotientGroup.mk (g a) : G ⧸ N)) =
      (QuotientGroup.mk' N) '' Set.range g := by
    ext x; simp
  rw [this, ← MonoidHom.map_closure, hg, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective N)]

lemma closure_range_of' {α : Type*} (rels : Set (FreeGroup α)) :
    Subgroup.closure (Set.range (fun a => (PresentedGroup.of a : PresentedGroup rels))) = ⊤ :=
  PresentedGroup.closure_range_of rels

/-- `Commute z g` for all `g` once `z` commutes with a generating set. -/
lemma commute_of_gen {G : Type*} [Group G] {S : Set G} (hS : Subgroup.closure S = ⊤) (z : G)
    (h : ∀ s ∈ S, Commute z s) (g : G) : Commute z g := by
  have hg : g ∈ Subgroup.closure S := by rw [hS]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => exact Commute.one_right z
  | mul x y _ _ hx hy => exact hx.mul_right hy
  | inv x _ hx => exact hx.inv_right

/-- the central subgroup `{1, z}` for a central involution `z` -/
def pairSubgroup {G : Type*} [Group G] (z : G) (hz : z ^ 2 = 1) : Subgroup G where
  carrier := {1, z}
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp
    left; rw [← pow_two, hz]
  one_mem' := by simp
  inv_mem' := by
    rintro a (rfl | rfl)
    · simp
    · right
      rw [Set.mem_singleton_iff, inv_eq_iff_mul_eq_one, ← pow_two, hz]

lemma pairSubgroup_normal {G : Type*} [Group G] (z : G) (hz : z ^ 2 = 1)
    (hc : ∀ g, Commute z g) : (pairSubgroup z hz).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rcases hn with rfl | rfl
  · simp [pairSubgroup]
  · show g * n * g⁻¹ ∈ ({1, n} : Set G)
    right
    rw [Set.mem_singleton_iff, ← (hc g).eq, mul_inv_cancel_right]

lemma pairSubgroup_card {G : Type*} [Group G] (z : G) (hz : z ^ 2 = 1) :
    Finite (pairSubgroup z hz) ∧ Nat.card (pairSubgroup z hz) ≤ 2 := by
  let f : Bool → pairSubgroup z hz := fun b =>
    if b then ⟨z, Or.inr rfl⟩ else ⟨1, Or.inl rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rcases hx with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  refine ⟨Finite.of_surjective f hf, ?_⟩
  have := Nat.card_le_card_of_surjective f hf
  simpa using this

/-- **Proposition 5.2.** -/
theorem prop_5_2 (h5 : 5 ≤ p) : IsPresentation (slVal (p := p)) (slRels p) := by
  -- the presented group
  set G := Pres (slRels p) with hG
  have hmem : ∀ E ∈ slRels p, E.eval (fun x => (PresentedGroup.of x : G)) = 1 :=
    fun E hE => eval_of_eq_one hE
  set a : G := PresentedGroup.of AC.a with ha
  set c : G := PresentedGroup.of AC.c with hc
  have r1 : a ^ p = 1 := by
    have := hmem (RA1 (gen .a) p) (by simp [slRels]); simpa using this
  have r2 : a * c * a * c * a * c⁻¹ = 1 := by
    have := hmem (RA2 (gen .a) (gen .c)) (by simp [slRels]); simpa using this
  have r3 : (a ^ hh p * c * a ^ 4 * c) ^ 2 * (c ^ 2)⁻¹ = 1 := by
    have := hmem (RA3 (gen .a) (gen .c) p) (by simp [slRels]); simpa using this
  have r4 : c ^ 4 = 1 := by
    have := hmem (RA4 (gen .c)) (by simp [slRels]); simpa using this
  have hgen : Subgroup.closure (Set.range (fun x : AC => (PresentedGroup.of x : G))) = ⊤ :=
    closure_range_of' _
  set z := c ^ 2 with hz
  have hz2 : z ^ 2 = 1 := by rw [hz, ← pow_mul]; exact r4
  have hac3 : (a * c) ^ 3 = z := by
    have e : (a * c) ^ 3 = (a * c * a * c * a * c⁻¹) * (c * c) := by
      rw [pow_succ, pow_two]; group
    rw [e, r2, one_mul, hz, pow_two]
  have hz_c : Commute z c := (Commute.refl c).pow_left 2
  have hz_ac : Commute z (a * c) := by rw [← hac3]; exact (Commute.refl _).pow_left 3
  have hz_a : Commute z a := by
    have e : a = (a * c) * c⁻¹ := by group
    rw [e]; exact hz_ac.mul_right hz_c.inv_right
  have hcent : ∀ g : G, Commute z g := by
    apply commute_of_gen hgen
    rintro _ ⟨x, rfl⟩
    cases x
    · exact hz_a
    · exact hz_c
  let N := pairSubgroup z hz2
  haveI : N.Normal := pairSubgroup_normal z hz2 hcent
  obtain ⟨hNfin, hNcard⟩ := pairSubgroup_card z hz2
  -- `G/N` is a quotient of Sunday's group
  let f : Fin 2 → G ⧸ N := ![(QuotientGroup.mk a : G ⧸ N), QuotientGroup.mk c]
  have hzN : z ∈ N := Or.inr rfl
  have hf : ∀ r ∈ Classical.sundayRels p, FreeGroup.lift f r = 1 := by
    intro r hr
    simp only [Classical.sundayRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [map_pow, FreeGroup.lift_apply_of, f, Matrix.cons_val_zero]
      rw [← QuotientGroup.mk_pow, r1, QuotientGroup.mk_one]
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, f, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, r2,
        QuotientGroup.mk_one]
    · simp only [map_pow, map_mul, FreeGroup.lift_apply_of, f, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]
      have e : (a ^ hh p * c * a ^ 4 * c) ^ 2 = z := by
        rw [hz]; exact mul_inv_eq_one.mp r3
      rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow]
      show (QuotientGroup.mk ((a ^ ((p + 1) / 2) * c * a ^ 4 * c) ^ 2) : G ⧸ N) = 1
      rw [QuotientGroup.eq_one_iff]
      have : (a ^ ((p + 1) / 2) * c * a ^ 4 * c) ^ 2 = z := e
      rw [this]; exact hzN
  have hfgen : Subgroup.closure (Set.range f) = ⊤ := by
    have e : Set.range f = Set.range (fun x : AC => (QuotientGroup.mk
        ((PresentedGroup.of x : G)) : G ⧸ N)) := by
      ext y; constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact ⟨.a, rfl⟩
        · exact ⟨.c, rfl⟩
      · rintro ⟨x, rfl⟩
        cases x
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [e]
    exact closure_range_quotient _ hgen N
  obtain ⟨hsfin, hscard⟩ := Classical.sunday_bound p Fact.out h5
  obtain ⟨hQfin, hQcard⟩ := card_le_of_presented f hf hfgen hsfin
  have hcardG : Nat.card G = Nat.card (G ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hQpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have heven : p * (p ^ 2 - 1) % 2 = 0 := by
    have := p_odd (p := p) h5
    have h2 : (p ^ 2 - 1) % 2 = 0 := by
      have : p ^ 2 % 2 = 1 := by rw [pow_two, Nat.mul_mod, this]
      omega
    rw [Nat.mul_mod, h2, mul_zero, Nat.zero_mod]
  have hbound : Nat.card G ≤ p * (p ^ 2 - 1) := by
    rw [hcardG]
    calc Nat.card (G ⧸ N) * Nat.card N ≤ (p * (p ^ 2 - 1) / 2) * 2 :=
          Nat.mul_le_mul (hQcard.trans hscard) hNcard
      _ = p * (p ^ 2 - 1) := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero heven)
  have hGfin : Finite G := Nat.finite_of_card_ne_zero (by rw [hcardG]; positivity)
  exact isPresentation_of_card_le (sl_rels_hold h5) (by rw [range_slVal]; exact closure_ML_MC)
    hGfin (by rw [natCard_SL2]; exact hbound)

end SnPres

namespace SnPres

open PE SL2 ASL2

variable {p : ℕ} [Fact p.Prime]

/-! ### Proposition 5.3 -/

/-- The alphabet `{a, c, t}`. -/
inductive ACT | a | c | t
  deriving DecidableEq

/-- The relators (A1)–(A9). -/
def aslRels (p lam mu : ℕ) : Set (PE ACT) :=
  {RA1 (gen .a) p, RA2 (gen .a) (gen .c), RA3 (gen .a) (gen .c) p, RA4 (gen .c), RA5 (gen .t) p,
   RA6 (gen .t) (Pu (gen .a) (gen .c)), RA7 (gen .t) (Peps (gen .c) (gen .t)),
   RA8 (gen .a) (gen .t) (Peps (gen .c) (gen .t)),
   RA9 (Pd (gen .a) (Pu (gen .a) (gen .c)) (gen .c) lam mu) (gen .t) lam}

/-- `a ↦ α_{M_L,0}`, `c ↦ α_{M_C,0}`, `t ↦ t_{e₁}` -/
def aslVal : ACT → ASL2 p
  | .a => lin ML
  | .c => lin MC
  | .t => ASL2.tr e1

/-- `λ` is a primitive root modulo `p` and `λ μ ≡ 1`. -/
structure PrimRoot (p lam mu : ℕ) : Prop where
  gen : ∀ δ : ZMod p, δ ≠ 0 → ∃ k : ℕ, (lam : ZMod p) ^ k = δ
  inv : (lam : ZMod p) * (mu : ZMod p) = 1

/-- `D_λ` -/
noncomputable def Dl (l : ZMod p) : SL2 p :=
  if h : l ≠ 0 then ⟨l, 0, 0, l⁻¹, by rw [mul_inv_cancel₀ h]; ring⟩ else 1

lemma lam_ne_zero {lam mu : ℕ} (h : PrimRoot p lam mu) : (lam : ZMod p) ≠ 0 := by
  intro h0; have := h.inv; rw [h0, zero_mul] at this; exact zero_ne_one this

/-- equation (3), third identity: `M_L^λ M_U^{-μ} M_L^λ M_C = D_λ` -/
lemma D_eq {lam mu : ℕ} (h : PrimRoot p lam mu) :
    (ML : SL2 p) ^ lam * ((MU : SL2 p) ^ mu)⁻¹ * ML ^ lam * MC = Dl (lam : ZMod p) := by
  have hl := lam_ne_zero h
  have hmu : (mu : ZMod p) = (lam : ZMod p)⁻¹ := eq_inv_of_mul_eq_one_right h.inv
  rw [ML_pow, MU_pow, Uy_inv, hmu]
  unfold Dl; rw [dif_pos hl]
  ext <;> simp only [SL2.mul_a, SL2.mul_b, SL2.mul_c, SL2.mul_d, Lx, Uy, MC] <;>
    (try field_simp) <;> (try ring1)

lemma vecMul_e1_Dl {l : ZMod p} (hl : l ≠ 0) : vecMul e1 (Dl l) = (l, 0) := by
  unfold Dl; rw [dif_pos hl]; ext <;> simp

/-- `det(v, w)` -/
def det2 (v w : Vec p) : ZMod p := v.1 * w.2 - v.2 * w.1

lemma dependent_of_det {v w : Vec p} (hv : v ≠ 0) (h : det2 v w = 0) : ∃ δ : ZMod p, w = δ • v := by
  unfold det2 at h
  by_cases h1 : v.1 = 0
  · have h2 : v.2 ≠ 0 := by intro h2; apply hv; ext <;> simp [h1, h2]
    have hw1 : w.1 = 0 := by
      rw [h1, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left h2
    refine ⟨w.2 / v.2, ?_⟩
    ext <;> simp [hw1, h1] <;> field_simp
  · refine ⟨w.1 / v.1, ?_⟩
    ext
    · simp; field_simp
    · simp; field_simp; linear_combination h

lemma rows_det {v w : Vec p} (h : det2 v w ≠ 0) :
    det2 v ((det2 v w)⁻¹ • w) = 1 := by
  unfold det2 at *
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  field_simp

lemma relators_asl {lam mu : ℕ} (h5 : 5 ≤ p) (h : PrimRoot p lam mu) :
    ∀ E ∈ aslRels p lam mu, E.eval (aslVal (p := p)) = 1 := by
  have hsl := sl_rels_hold (p := p) h5
  have hl := lam_ne_zero h
  intro E hE
  simp only [aslRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hE
  -- the linear part, through the homomorphism `lin`
  let linHom : SL2 p →* ASL2 p := ⟨⟨lin, lin_one⟩, fun M N => (lin_mul M N).symm⟩
  have hlinval : ∀ x : AC, linHom (slVal x) = aslVal (match x with | .a => .a | .c => .c) := by
    intro x; cases x <;> rfl
  have hsl' : ∀ F : PE AC, F ∈ slRels p →
      (F.map (fun x => match x with | .a => ACT.a | .c => ACT.c)).eval (aslVal (p := p)) = 1 := by
    intro F hF
    rw [eval_map]
    have : (aslVal (p := p) ∘ fun x => match x with | .a => ACT.a | .c => ACT.c) =
        linHom ∘ slVal := by
      funext x; cases x <;> rfl
    rw [this, eval_hom, hsl F hF, map_one]
  have hu : (Pu (gen ACT.a) (gen .c)).eval (aslVal (p := p)) = lin MU := by
    simp only [eval_Pu, eval_gen, aslVal]
    rw [lin_inv, lin_inv, lin_mul, lin_mul, MU_eq]
  have heps : (Peps (gen ACT.c) (gen .t)).eval (aslVal (p := p)) = ASL2.tr e2 := by
    simp only [eval_Peps, eval_gen, aslVal]
    have := conj_tr (lin (MC : SL2 p))⁻¹ e1
    rw [inv_inv] at this
    rw [this]
    congr 1
    ext <;> simp [lin, MC]
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsl' (RA1 (gen .a) p) (by simp [slRels])
  · exact hsl' (RA2 (gen .a) (gen .c)) (by simp [slRels])
  · exact hsl' (RA3 (gen .a) (gen .c) p) (by simp [slRels])
  · exact hsl' (RA4 (gen .c)) (by simp [slRels])
  · simp only [eval_RA5, eval_gen, aslVal]
    rw [ASL2.tr_pow, ZMod.natCast_self]
    ext1 <;> simp [ASL2.tr]
  · simp only [eval_RA6, eval_gen]
    rw [hu]
    simp only [aslVal]
    have hcomm : (lin (MU : SL2 p))⁻¹ * ASL2.tr e1 * lin MU = ASL2.tr e1 := by
      rw [conj_tr]; congr 1; ext <;> simp [lin, MU]
    calc (ASL2.tr e1)⁻¹ * (lin (MU : SL2 p))⁻¹ * ASL2.tr e1 * lin MU
        = (ASL2.tr e1)⁻¹ * ((lin (MU : SL2 p))⁻¹ * ASL2.tr e1 * lin MU) := by group
      _ = 1 := by rw [hcomm, inv_mul_cancel]
  · simp only [eval_RA7, eval_gen]
    rw [heps]
    simp only [aslVal]
    rw [ASL2.tr_inv, ASL2.tr_inv, ASL2.tr_mul, ASL2.tr_mul, ASL2.tr_mul]
    rw [show -e1 + -e2 + e1 + e2 = (0 : Vec p) by abel, ASL2.tr_zero]
  · simp only [eval_RA8, eval_gen]
    rw [heps]
    simp only [aslVal]
    have := conj_tr (lin (ML : SL2 p)) (-e1)
    rw [ASL2.tr_inv]
    rw [show ASL2.tr e1 * ASL2.tr e2 * (lin ML)⁻¹ * ASL2.tr (-e1) * lin ML =
      ASL2.tr e1 * ASL2.tr e2 * ((lin ML)⁻¹ * ASL2.tr (-e1) * lin ML) by group]
    rw [this, ASL2.tr_mul, ASL2.tr_mul]
    rw [show e1 + e2 + vecMul (-e1) (lin (ML : SL2 p)).M = (0 : Vec p) by
      ext <;> simp [lin, ML]]
    rfl
  · simp only [eval_RA9, eval_gen, eval_Pd]
    rw [hu]
    simp only [aslVal]
    have hp : ∀ (M : SL2 p) (k : ℕ), lin M ^ k = lin (M ^ k) := by
      intro M k; induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ, ih, lin_mul, pow_succ]
    have hd : (lin (ML : SL2 p)) ^ lam * ((lin MU) ^ mu)⁻¹ * (lin ML) ^ lam * lin MC =
        lin (Dl (lam : ZMod p)) := by
      rw [← D_eq h, hp, hp, lin_inv, lin_mul, lin_mul, lin_mul]
    rw [hd]
    have := conj_tr (lin (Dl (lam : ZMod p))) e1
    rw [this, ASL2.tr_pow, mul_inv_eq_one]
    congr 1
    show vecMul e1 (Dl (lam : ZMod p)) = _
    rw [vecMul_e1_Dl hl]
    ext <;> simp

lemma closure_aslVal (h5 : 5 ≤ p) : Subgroup.closure (Set.range (aslVal (p := p))) = ⊤ := by
  set H := Subgroup.closure (Set.range (aslVal (p := p)))
  have hlin : ∀ M : SL2 p, lin M ∈ H := by
    let linHom : SL2 p →* ASL2 p := ⟨⟨lin, lin_one⟩, fun M N => (lin_mul M N).symm⟩
    have h1 : Subgroup.map linHom ⊤ ≤ H := by
      rw [← closure_ML_MC, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨M, hM, rfl⟩
      rcases hM with rfl | rfl
      · exact Subgroup.subset_closure ⟨.a, rfl⟩
      · exact Subgroup.subset_closure ⟨.c, rfl⟩
    intro M
    exact h1 ⟨M, trivial, rfl⟩
  have htr : ∀ v : Vec p, ASL2.tr v ∈ H := by
    intro v
    by_cases hv : v = 0
    · rw [hv, ASL2.tr_zero]; exact Subgroup.one_mem _
    · obtain ⟨M, hM⟩ := exists_row v hv
      have := conj_tr (lin M) e1
      simp only [lin] at this
      rw [show vecMul e1 M = v from hM] at this
      rw [← this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hlin M))
        (Subgroup.subset_closure ⟨.t, rfl⟩)) (hlin M)
  rw [eq_top_iff]
  intro α _
  have e : α = lin α.M * ASL2.tr α.w := by rw [lin_mul_tr]
  rw [e]
  exact Subgroup.mul_mem _ (hlin _) (htr _)

end SnPres
