/-
Proof of the main theorem, part 1: for `n ≥ 245`, eliminating the twelve extra generators of
Theorem 7.3 (Lemma 2.5) gives a presentation of `S_n` on `x, y` with at most `62` relators.
-/
import SnPres.Section7d
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace SnPres

open PE SL2 ASL2

/-! ### The values of `W_L, …, W_Q` (Proposition 4.3) as elements of `Sym([0,N-1]) ≤ S_n` -/

/-- the PEs `W_G` of Definition 4.2 -/
def WG (p : ℕ) : Six → PE XY
  | .L => WL p
  | .U => WU p
  | .T => WT p
  | .X0 => WX0 p
  | .X1 => WX1 p
  | .Q => WQ p

variable {p : ℕ} [Fact p.Prime]

lemma actsAs_embAt_thN {n : ℕ} (hn : NN p ≤ n) (α : ASL2 p) (f : ℕ → ℕ)
    (hf : ∀ i, thetaF α i = f i) : ActsAs (embAt (NN p) n 0 (by omega) (thN α)) f := by
  intro j hj
  rw [nv_embAt]
  unfold embF
  by_cases h : j < NN p
  · rw [if_pos ⟨Nat.zero_le _, by omega⟩, Nat.sub_zero, Nat.add_zero, nv_thN, hf]
  · rw [if_neg (by omega), ← hf, thetaF_ge _ (by have := NN_eq (p := p); omega)]

/-- **Proposition 4.3 ↔ Theorem 6.3**: the value of `W_G` in `S_n` is the permutation `G` of
`S_N`, extended by the identity. -/
theorem eval_WG (h5 : 5 ≤ p) {n : ℕ} (hn : NN p ≤ n) (G : Six) :
    (WG p G).eval (xyv n (by have := NN_eq (p := p); omega)) =
      embAt (NN p) n 0 (by omega) (sixVal G) := by
  have hNNe := NN_eq (p := p)
  have hp : 2 ≤ p := by omega
  have hn' : p * p + p * p + 2 ≤ n := by omega
  cases G
  · exact (acts_L hp hn').eq (actsAs_embAt_thN hn _ _ thetaF_ML)
  · exact (acts_U hp hn').eq (actsAs_embAt_thN hn _ _ thetaF_MU)
  · exact (acts_T hp hn').eq (actsAs_embAt_thN hn _ _ thetaF_te1)
  · refine (acts_X0 hp hn').eq ?_
    intro j hj
    rw [nv_embAt]; unfold embF
    dsimp only
    by_cases h : j < NN p
    · rw [if_pos (show 0 ≤ j ∧ j < 0 + NN p from ⟨Nat.zero_le _, by omega⟩), Nat.sub_zero,
        Nat.add_zero]
      show nv (c3 (NN p) 0 (2 * (p * p)) (2 * (p * p) + 1)) j = _
      have hq : 1 ≤ p * p := by nlinarith
      rw [nv_c3 (n := NN p) (a := 0) (b := 2 * (p * p)) (c := 2 * (p * p) + 1) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)]
    · rw [if_neg (show ¬ (0 ≤ j ∧ j < 0 + NN p) by omega)]; split_ifs <;> omega
  · refine (acts_X1 hp hn').eq ?_
    intro j hj
    rw [nv_embAt]; unfold embF
    have hq : 1 ≤ p * p := by nlinarith
    dsimp only
    by_cases h : j < NN p
    · rw [if_pos (show 0 ≤ j ∧ j < 0 + NN p from ⟨Nat.zero_le _, by omega⟩), Nat.sub_zero,
        Nat.add_zero]
      show nv (c3 (NN p) (p * p) (2 * (p * p)) (2 * (p * p) + 1)) j = _
      rw [nv_c3 (n := NN p) (a := p * p) (b := 2 * (p * p)) (c := 2 * (p * p) + 1) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)]
    · rw [if_neg (show ¬ (0 ≤ j ∧ j < 0 + NN p) by omega)]; split_ifs <;> omega
  · show (WQ p).eval _ = embAt (NN p) n 0 _ (tr (NN p) (2 * (p * p)) (2 * (p * p) + 1))
    rw [eval_Q hp hn', embAt_tr _ (by omega) (by omega)]; rfl

/-! ### Primitive roots -/

/-- a primitive root `λ ∈ [1, p-1]` and `μ ∈ [1, p-1]` with `λ μ ≡ 1` -/
theorem exists_primRoot : ∃ lam mu : ℕ, 1 ≤ lam ∧ lam < p ∧ 1 ≤ mu ∧ mu < p ∧ PrimRoot p lam mu := by
  haveI := ZMod.isCyclic_units_prime (Fact.out : p.Prime)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hval : ∀ u : (ZMod p)ˣ, 1 ≤ (u : ZMod p).val := by
    intro u
    rw [Nat.one_le_iff_ne_zero, Ne, ZMod.val_eq_zero]
    exact u.ne_zero
  refine ⟨(g : ZMod p).val, ((g⁻¹ : (ZMod p)ˣ) : ZMod p).val, hval g, ZMod.val_lt _,
    hval g⁻¹, ZMod.val_lt _, ⟨?_, ?_⟩⟩
  · intro δ hδ
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr (hg (Units.mk0 δ hδ)))
    have hk' : g ^ k = Units.mk0 δ hδ := hk
    refine ⟨k, ?_⟩
    rw [ZMod.natCast_zmod_val, ← Units.val_pow_eq_pow_val, hk', Units.val_mk0]
  · rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]

/-! ### Elimination (Lemma 2.5) and normalisation -/

/-- `W_{G⁽¹⁾} = W_G`, `W_{G⁽²⁾} = (W_G)^{y^s}` -/
def elimW (n p : ℕ) : Six ⊕ Six → PE XY
  | Sum.inl G => WG p G
  | Sum.inr G => conj (WG p G) (Yp (n - NN p))

/-- the substitution `𝒜 → PE {x,y}` -/
def elimSubst (n p : ℕ) : GA → PE XY := Sum.elim gen (elimW n p)

/-- the relators of the main theorem, before normalisation -/
def mainList (n p lam mu : ℕ) : List (PE XY) := (gluList n p lam mu).map (PE.subst (elimSubst n p))

/-- the relators of the main theorem: the genuine power expressions obtained by normalising -/
def mainRels (n p lam mu : ℕ) : List (PE XY) := (mainList n p lam mu).filterMap PE.normalize

/-- Normalisation does not change the presented group. -/
theorem isPresentation_normalize {α G : Type*} [Group G] {φ : α → G} (L : List (PE α))
    (h : IsPresentation φ {E | E ∈ L}) : IsPresentation φ {E | E ∈ L.filterMap PE.normalize} := by
  apply isPresentation_congr _ h
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨E, hE, rfl⟩
    have hs := (normalize_spec E).1
    rcases hn : normalize E with _ | E'
    · rw [hn] at hs
      simp only [optVal] at hs
      rw [← hs]; exact Subgroup.one_mem _
    · rw [hn] at hs
      simp only [optVal] at hs
      rw [← hs]
      apply Subgroup.subset_normalClosure
      exact ⟨E', List.mem_filterMap.mpr ⟨E, hE, hn⟩, rfl⟩
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨E', hE', rfl⟩
    obtain ⟨E, hE, hn⟩ := List.mem_filterMap.mp hE'
    have hs := (normalize_spec E).1
    rw [hn] at hs
    simp only [optVal] at hs
    rw [hs]
    exact Subgroup.subset_normalClosure ⟨E, hE, rfl⟩

lemma gluVal_inl {n : ℕ} (hnN : NN p ≤ n) :
    gluVal (p := p) n hnN ∘ Sum.inl = xyv n (by have := NN_eq (p := p); omega) := by
  funext c; cases c <;> rfl

/-- **The main construction for `n ≥ 245`**: given `p` as in Lemma 7.1 and a primitive root,
`mainRels` is a presentation of `S_n` on `x, y`. -/
theorem isPresentation_main {n lam mu : ℕ} (h5 : 5 ≤ p) (hpr : PrimRoot p lam mu)
    (h1 : n + 3 ≤ 2 * NN p) (h2 : NN p ≤ n - 1) :
    IsPresentation (xyv n (by have := NN_eq (p := p); omega)) {E | E ∈ mainRels n p lam mu} := by
  have hnN : NN p ≤ n := by omega
  have hP := thm_7_3 h5 hpr h1 h2 hnN
  have hW : ∀ b, (elimW n p b).eval (gluVal n hnN ∘ Sum.inl) = gluVal n hnN (Sum.inr b) := by
    rw [gluVal_inl hnN]
    rintro (G | G)
    · exact eval_WG h5 hnN G
    · show (conj (WG p G) (Yp (n - NN p))).eval _ = _
      rw [eval_conj, eval_WG h5 hnN G, eval_Yp (by omega) (show p * p + p * p + 2 ≤ n by
        have := NN_eq (p := p); omega)]
      rfl
  have hE := elim_generators hP (elimW n p) hW
  rw [gluVal_inl hnN] at hE
  apply isPresentation_normalize
  have e : PE.subst (Sum.elim PE.gen (elimW n p)) '' gluRels n p lam mu =
      {E | E ∈ mainList n p lam mu} := by
    ext E
    simp only [gluRels, mainList, Set.mem_image, Set.mem_setOf_eq, List.mem_map, elimSubst]
  rw [← e]
  exact hE

lemma mainRels_length {n lam mu : ℕ} : (mainRels n p lam mu).length ≤ 62 :=
  (List.length_filterMap_le _ _).trans (by
    rw [mainList, List.length_map]; exact gluList_length n p lam mu)

lemma mainRels_wf {n lam mu : ℕ} : ∀ E ∈ mainRels n p lam mu, E.WF := by
  intro E hE
  obtain ⟨F, _, hF⟩ := List.mem_filterMap.mp hE
  exact ((normalize_spec F).2 E hF).1

lemma mainRels_le {n lam mu : ℕ} : ∀ E ∈ mainRels n p lam mu,
    ∃ F ∈ gluList n p lam mu, E.length ≤ (F.subst (elimSubst n p)).length := by
  intro E hE
  obtain ⟨F, hF, hFE⟩ := List.mem_filterMap.mp hE
  obtain ⟨F0, hF0, rfl⟩ := List.mem_map.mp hF
  exact ⟨F0, hF0, ((normalize_spec _).2 E hFE).2⟩

end SnPres
