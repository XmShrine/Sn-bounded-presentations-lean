/-
Section 5 (continued): Proposition 5.3.
-/
import SnPres.Section5

namespace SnPres

open PE SL2 ASL2

variable {p : ℕ} [Fact p.Prime]

lemma pow_eq_pow_mod_of {G : Type*} [Group G] {x : G} {p : ℕ} (hx : x ^ p = 1) (m : ℕ) :
    x ^ m = x ^ (m % p) := by
  conv_lhs => rw [← Nat.div_add_mod m p, pow_add, pow_mul, hx, one_pow, one_mul]

lemma smul_inv_smul' {δ : ZMod p} (hδ : δ ≠ 0) (w : Vec p) : δ • (δ⁻¹ • w) = w := by
  ext <;> simp [← mul_assoc, mul_inv_cancel₀ hδ]

lemma conj_pow' {G : Type*} [Group G] (a b : G) (n : ℕ) : (a⁻¹ * b * a) ^ n = a⁻¹ * b ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

/-- **Proposition 5.3.** -/
theorem prop_5_3 {lam mu : ℕ} (h5 : 5 ≤ p) (h : PrimRoot p lam mu) :
    IsPresentation (aslVal (p := p)) (aslRels p lam mu) := by
  set G := Pres (aslRels p lam mu)
  have hmem : ∀ E ∈ aslRels p lam mu, E.eval (fun x => (PresentedGroup.of x : G)) = 1 :=
    fun E hE => eval_of_eq_one hE
  set a : G := PresentedGroup.of ACT.a with ha
  set c : G := PresentedGroup.of ACT.c with hc
  set t : G := PresentedGroup.of ACT.t with ht
  set u : G := c⁻¹ * a⁻¹ * c with hu
  set ε : G := c * t * c⁻¹ with hε
  set d : G := a ^ lam * (u ^ mu)⁻¹ * a ^ lam * c with hd
  have r5 : t ^ p = 1 := by
    have := hmem (RA5 (gen .t) p) (by simp [aslRels]); simpa using this
  have r6 : Commute t u := by
    have := hmem (RA6 (gen .t) (Pu (gen .a) (gen .c))) (by simp [aslRels])
    simp only [eval_RA6, eval_Pu, eval_gen] at this
    rw [commute_iff_eq]
    have e : t⁻¹ * u⁻¹ * t * u = 1 := this
    calc t * u = u * t * (t⁻¹ * u⁻¹ * t * u) := by group
      _ = u * t := by rw [e, mul_one]
  have r7 : Commute t ε := by
    have := hmem (RA7 (gen .t) (Peps (gen .c) (gen .t))) (by simp [aslRels])
    simp only [eval_RA7, eval_Peps, eval_gen] at this
    rw [commute_iff_eq]
    have e : t⁻¹ * ε⁻¹ * t * ε = 1 := this
    calc t * ε = ε * t * (t⁻¹ * ε⁻¹ * t * ε) := by group
      _ = ε * t := by rw [e, mul_one]
  have r8 : t * ε = a⁻¹ * t * a := by
    have := hmem (RA8 (gen .a) (gen .t) (Peps (gen .c) (gen .t))) (by simp [aslRels])
    simp only [eval_RA8, eval_Peps, eval_gen] at this
    have e : t * ε * a⁻¹ * t⁻¹ * a = 1 := this
    calc t * ε = t * ε * a⁻¹ * t⁻¹ * a * (a⁻¹ * t * a) := by group
      _ = a⁻¹ * t * a := by rw [e, one_mul]
  have r9 : d⁻¹ * t * d = t ^ lam := by
    have := hmem (RA9 (Pd (gen .a) (Pu (gen .a) (gen .c)) (gen .c) lam mu) (gen .t) lam)
      (by simp [aslRels])
    simp only [eval_RA9, eval_Pd, eval_Pu, eval_gen] at this
    exact mul_inv_eq_one.mp this
  -- the homomorphism `π : SL(2,p) → G`
  let ψ : AC → G := fun x => match x with | .a => a | .c => c
  have hψ : ∀ E ∈ slRels p, E.eval ψ = 1 := by
    intro E hE
    simp only [slRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hE
    rcases hE with rfl | rfl | rfl | rfl
    · exact hmem (RA1 (gen .a) p) (by simp [aslRels])
    · exact hmem (RA2 (gen .a) (gen .c)) (by simp [aslRels])
    · exact hmem (RA3 (gen .a) (gen .c) p) (by simp [aslRels])
    · exact hmem (RA4 (gen .c)) (by simp [aslRels])
  have hP52 := prop_5_2 (p := p) h5
  let π : SL2 p →* G := hP52.lift hψ
  have πL : π ML = a := hP52.lift_apply hψ .a
  have πC : π MC = c := hP52.lift_apply hψ .c
  have πU : π MU = u := by
    rw [← MU_eq, map_mul, map_mul, map_inv, map_inv, πL, πC]
  have πD : π (Dl (lam : ZMod p)) = d := by
    rw [← D_eq h]
    simp only [map_mul, map_inv, map_pow]
    rw [πL, πU, πC]
  -- `t^{π(M)}`
  let cj : SL2 p → G := fun M => (π M)⁻¹ * t * π M
  have cj_wd : ∀ M M' : SL2 p, vecMul e1 M = vecMul e1 M' → cj M = cj M' := by
    intro M M' hMM
    have hfix : vecMul e1 (M' * M⁻¹) = e1 := by
      rw [vecMul_mul, ← hMM, ← vecMul_mul, mul_inv_cancel, vecMul_one]
    have hstab := stab_e1 hfix
    have hM' : M' = Uy (M' * M⁻¹).c * M := by
      rw [← hstab]; group
    have hU : π (Uy (M' * M⁻¹).c) = u ^ (M' * M⁻¹).c.val := by
      rw [Uy_eq_pow, map_pow, πU]
    show (π M)⁻¹ * t * π M = (π M')⁻¹ * t * π M'
    rw [hM', map_mul, hU]
    set k := (M' * M⁻¹).c.val
    have hc : Commute t (u ^ k) := r6.pow_right _
    have hc' : (u ^ k)⁻¹ * t * u ^ k = t := by
      rw [mul_assoc, hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]
    calc (π M)⁻¹ * t * π M = (π M)⁻¹ * ((u ^ k)⁻¹ * t * u ^ k) * π M := by rw [hc']
      _ = (u ^ k * π M)⁻¹ * t * (u ^ k * π M) := by group
  -- `t_v`
  let tv : Vec p → G := fun v => if v = 0 then 1 else cj (Mrow v)
  have tv_zero : tv 0 = 1 := by simp [tv]
  have tv_e1M : ∀ M : SL2 p, tv (vecMul e1 M) = cj M := by
    intro M
    have hne : vecMul e1 M ≠ 0 := vecMul_ne_zero (by simp [e1]) M
    simp only [tv, if_neg hne]
    exact cj_wd _ _ (vecMul_e1_Mrow hne)
  have tv_conj : ∀ (v : Vec p) (M : SL2 p), (π M)⁻¹ * tv v * π M = tv (vecMul v M) := by
    intro v M
    by_cases hv : v = 0
    · rw [hv, vecMul_zero, tv_zero]; group
    · have e : v = vecMul e1 (Mrow v) := (vecMul_e1_Mrow hv).symm
      rw [e, tv_e1M, ← vecMul_mul, tv_e1M]
      show (π M)⁻¹ * ((π (Mrow v))⁻¹ * t * π (Mrow v)) * π M =
        (π (Mrow v * M))⁻¹ * t * π (Mrow v * M)
      rw [map_mul]; group
  have tv_e1 : tv e1 = t := by
    have := tv_e1M 1
    rw [vecMul_one] at this
    rw [this]; show (π 1)⁻¹ * t * π 1 = t; rw [map_one]; group
  have tv_e2 : tv e2 = ε := by
    have e : (e2 : Vec p) = vecMul e1 (MC⁻¹) := by ext <;> simp [MC]
    rw [e, tv_e1M]
    show (π MC⁻¹)⁻¹ * t * π MC⁻¹ = ε
    rw [map_inv, πC, inv_inv]
  have tv_11 : tv ((1, 1) : Vec p) = a⁻¹ * t * a := by
    have e : ((1, 1) : Vec p) = vecMul e1 ML := by ext <;> simp [ML]
    rw [e, tv_e1M]
    show (π ML)⁻¹ * t * π ML = _
    rw [πL]
  have tv_eq_cj : ∀ v : Vec p, v ≠ 0 → tv v = (π (Mrow v))⁻¹ * t * π (Mrow v) := by
    intro v hv
    simp only [tv, if_neg hv]
    rfl
  have tv_pow : ∀ v, tv v ^ p = 1 := by
    intro v
    by_cases hv : v = 0
    · rw [hv, tv_zero, one_pow]
    · rw [tv_eq_cj v hv, conj_pow', r5]; group
  -- scalars
  have tv_lam : ∀ v, tv ((lam : ZMod p) • v) = tv v ^ lam := by
    intro v
    by_cases hv : v = 0
    · rw [hv, show (lam : ZMod p) • (0 : Vec p) = 0 by ext <;> simp, tv_zero, one_pow]
    · have e : v = vecMul e1 (Mrow v) := (vecMul_e1_Mrow hv).symm
      have e2 : (lam : ZMod p) • v = vecMul ((lam : ZMod p) • e1) (Mrow v) := by
        rw [vecMul_smul, ← e]
      rw [e2, ← tv_conj, show ((lam : ZMod p) • e1 : Vec p) = vecMul e1 (Dl (lam : ZMod p)) by
        rw [vecMul_e1_Dl (lam_ne_zero h)]; ext <;> simp [e1]]
      rw [tv_e1M]
      show (π (Mrow v))⁻¹ * ((π (Dl (lam : ZMod p)))⁻¹ * t * π (Dl (lam : ZMod p))) * π (Mrow v) =
        tv v ^ lam
      rw [πD, r9, tv_eq_cj v hv, conj_pow']
  have tv_lam_pow : ∀ (k : ℕ) v, tv (((lam : ZMod p) ^ k) • v) = tv v ^ (lam ^ k) := by
    intro k
    induction k with
    | zero => intro v; rw [show ((lam : ZMod p) ^ 0) • v = v by ext <;> simp, pow_zero, pow_one]
    | succ k ih =>
      intro v
      have e : ((lam : ZMod p) ^ (k + 1)) • v = (lam : ZMod p) • (((lam : ZMod p) ^ k) • v) := by
        ext <;> simp <;> ring
      rw [e, tv_lam, ih, ← pow_mul, pow_succ]
  have tv_smul : ∀ (δ : ZMod p) v, tv (δ • v) = tv v ^ δ.val := by
    intro δ v
    by_cases hδ : δ = 0
    · rw [hδ, show (0 : ZMod p) • v = 0 by ext <;> simp, tv_zero, ZMod.val_zero, pow_zero]
    · obtain ⟨k, hk⟩ := h.gen δ hδ
      rw [← hk, tv_lam_pow, pow_eq_pow_mod_of (tv_pow v) (lam ^ k)]
      congr 1
      rw [← Nat.cast_pow, ZMod.val_natCast]
  -- commutation
  have tv_comm : ∀ v w, Commute (tv v) (tv w) := by
    intro v w
    by_cases hv : v = 0
    · rw [hv, tv_zero]; exact Commute.one_left _
    by_cases hdet : det2 v w = 0
    · obtain ⟨δ, rfl⟩ := dependent_of_det hv hdet
      rw [tv_smul]; exact (Commute.refl _).pow_right _
    · obtain ⟨w', hw'⟩ : ∃ w', w' = (det2 v w)⁻¹ • w := ⟨_, rfl⟩
      have hdet1 : det2 v w' = 1 := by rw [hw']; exact rows_det hdet
      have hw : w = (det2 v w) • w' := by
        rw [hw']; exact (smul_inv_smul' hdet w).symm
      let M := rows v w' hdet1
      have h1 : tv v = (π M)⁻¹ * t * π M := by
        have := tv_e1M M; rw [vecMul_e1_rows] at this; exact this
      have h2 : tv w' = (π M)⁻¹ * ε * π M := by
        rw [← tv_e2, tv_conj, vecMul_e2_rows]
      have hc : Commute (tv v) (tv w') := by
        rw [h1, h2]
        rw [commute_iff_eq]
        have := r7.eq
        calc (π M)⁻¹ * t * π M * ((π M)⁻¹ * ε * π M) = (π M)⁻¹ * (t * ε) * π M := by group
          _ = (π M)⁻¹ * (ε * t) * π M := by rw [this]
          _ = _ := by group
      rw [hw, tv_smul]
      exact hc.pow_right _
  -- additivity
  have tv_add_det1 : ∀ v w, det2 v w = 1 → tv (v + w) = tv v * tv w := by
    intro v w hdet
    let M := rows v w hdet
    have h1 : tv v = (π M)⁻¹ * t * π M := by
      have := tv_e1M M; rw [vecMul_e1_rows] at this; exact this
    have h2 : tv w = (π M)⁻¹ * ε * π M := by rw [← tv_e2, tv_conj, vecMul_e2_rows]
    have h3 : v + w = vecMul ((1, 1) : Vec p) M := by
      rw [show ((1, 1) : Vec p) = e1 + e2 by ext <;> simp, vecMul_add, vecMul_e1_rows,
        vecMul_e2_rows]
    rw [h1, h2, h3, ← tv_conj, tv_11, ← r8]
    group
  have tv_add : ∀ v w, tv (v + w) = tv v * tv w := by
    intro v w
    by_cases hv : v = 0
    · rw [hv, zero_add, tv_zero, one_mul]
    by_cases hdet : det2 v w = 0
    · obtain ⟨δ, rfl⟩ := dependent_of_det hv hdet
      have e : v + δ • v = (1 + δ) • v := by ext <;> simp <;> ring
      rw [e, tv_smul, tv_smul, ← pow_succ', pow_eq_pow_mod_of (tv_pow v) (δ.val + 1),
        pow_eq_pow_mod_of (tv_pow v) ((1 + δ).val)]
      congr 1
      rw [ZMod.val_add, ZMod.val_one'' (by have := (Fact.out : p.Prime).two_le; omega),
        Nat.mod_mod, Nat.add_comm]
    · obtain ⟨w', hw'⟩ : ∃ w', w' = (det2 v w)⁻¹ • w := ⟨_, rfl⟩
      have hdet1 : det2 v w' = 1 := by rw [hw']; exact rows_det hdet
      have hw : w = (det2 v w) • w' := by
        rw [hw']; exact (smul_inv_smul' hdet w).symm
      have key : ∀ k : ℕ, tv (v + (k : ZMod p) • w') = tv v * tv w' ^ k := by
        intro k
        induction k with
        | zero => rw [show v + ((0 : ℕ) : ZMod p) • w' = v by ext <;> simp, pow_zero, mul_one]
        | succ k ih =>
          have e : v + ((k + 1 : ℕ) : ZMod p) • w' = (v + (k : ZMod p) • w') + w' := by
            ext <;> simp <;> ring
          have hd1 : det2 (v + (k : ZMod p) • w') w' = 1 := by
            rw [← hdet1]; unfold det2; simp; ring
          rw [e, tv_add_det1 _ _ hd1, ih, pow_succ, mul_assoc]
      have h1 := key (det2 v w).val
      rw [ZMod.natCast_zmod_val] at h1
      have h2 : tv w = tv w' ^ (det2 v w).val := by
        conv_lhs => rw [hw]
        rw [tv_smul]
      rw [← hw] at h1
      rw [h1, h2]
  have tv_neg : ∀ v, tv (-v) = (tv v)⁻¹ := by
    intro v
    rw [eq_inv_iff_mul_eq_one, ← tv_add, neg_add_cancel, tv_zero]
  -- every element is `t_v π(M)`
  have hsurj : Function.Surjective (fun x : Vec p × SL2 p => tv x.1 * π x.2) := by
    have hS : ∀ g : G, ∃ x : Vec p × SL2 p, tv x.1 * π x.2 = g := by
      intro g
      have hg : g ∈ Subgroup.closure (Set.range (fun x : ACT => (PresentedGroup.of x : G))) := by
        rw [closure_range_of']; trivial
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨x, rfl⟩ := hg
        cases x
        · exact ⟨(0, ML), by rw [tv_zero, one_mul, πL]⟩
        · exact ⟨(0, MC), by rw [tv_zero, one_mul, πC]⟩
        · exact ⟨(e1, 1), by rw [tv_e1, map_one, mul_one]⟩
      | one => exact ⟨(0, 1), by rw [tv_zero, map_one, one_mul]⟩
      | mul g g' _ _ hg hg' =>
        obtain ⟨⟨v, M⟩, rfl⟩ := hg
        obtain ⟨⟨w, M'⟩, rfl⟩ := hg'
        refine ⟨(v + vecMul w M⁻¹, M * M'), ?_⟩
        simp only
        rw [tv_add, ← tv_conj, map_inv, inv_inv, map_mul]
        group
      | inv g _ hg =>
        obtain ⟨⟨v, M⟩, rfl⟩ := hg
        refine ⟨(vecMul (-v) M, M⁻¹), ?_⟩
        simp only
        rw [← tv_conj, tv_neg, map_inv]
        group
    intro g
    exact hS g
  have hfin : Finite G := Finite.of_surjective _ hsurj
  have hcard : Nat.card G ≤ Nat.card (ASL2 p) := by
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Vec p), Fintype.card_prod, ZMod.card]
      at this
    rw [natCard_ASL2]
    calc Nat.card G ≤ p * p * Nat.card (SL2 p) := this
      _ = p ^ 2 * Nat.card (SL2 p) := by ring
  exact isPresentation_of_card_le (relators_asl h5 h) (closure_aslVal h5) hfin hcard

end SnPres
