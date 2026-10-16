/-
Section 6, part 4: Theorem 6.3 (the 27 relators present `S_N` on `L, U, T, X₀, X₁, Q`).

The proof follows Steps 1–7 of the paper, with two changes in the routes (the statement is the
paper's):
* Step 5 uses Lemma 5.5' (`normal_eq_top_of_mem`) instead of Lemma 5.5;
* that `ε(Γ) = S_N` (generation) is obtained from Proposition 6.4 (the six permutations produce
  `(0,1)` and `(0,1,…,N-1)`, which generate `S_N`) instead of the 3-cycles argument of Step 6;
  the order bound `|Γ| ≤ 2 |K| ≤ N!` is the paper's (Steps 4, 5 and 7).
-/
import SnPres.Section6c
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Group.Subgroup.MulOppositeLemmas
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Finite.Perm

namespace SnPres

open PE SL2 ASL2

/-! ### Generation -/

lemma eval_mem_closure {α G : Type*} [Group G] (f : α → G) (E : PE α) :
    E.eval f ∈ Subgroup.closure (Set.range f) := by
  induction E with
  | gen a => exact Subgroup.subset_closure ⟨a, rfl⟩
  | mul E F hE hF => exact Subgroup.mul_mem _ hE hF
  | one => exact Subgroup.one_mem _
  | pow E e hE => exact Subgroup.zpow_mem _ hE e

/-- `x = (0,1)` and `y = (0,1,…,n-1)` generate `S_n`. -/
theorem closure_xs_ys {n : ℕ} (hn : 2 ≤ n) :
    Subgroup.closure ({xs n (by omega), ys n} : Set (Sym n)) = ⊤ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [← Subgroup.unop_eq_top, Subgroup.unop_closure]
  have e : (MulOpposite.op ⁻¹' ({xs (m + 2) (by omega), ys (m + 2)} : Set (Sym (m + 2)))) =
      ({finRotate (m + 2), Equiv.swap 0 (finRotate (m + 2) 0)} : Set (Equiv.Perm (Fin (m + 2)))) := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, xs, ys, rp,
      MulOpposite.op_inj, finRotate_succ_apply, zero_add]
    constructor
    · rintro (h | h)
      · right; rw [h]; rfl
      · left; exact h
    · rintro (h | h)
      · right; exact h
      · left; rw [h]; rfl
  rw [e]
  exact Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate_of_le (by omega))
    (support_finRotate_of_le (by omega)) 0

/-- The cardinality of `S_n`. -/
lemma natCard_Sym (n : ℕ) : Nat.card (Sym n) = n.factorial := by
  rw [← Nat.card_congr (MulOpposite.opEquiv : Equiv.Perm (Fin n) ≃ _), Nat.card_perm,
    Nat.card_eq_fintype_card, Fintype.card_fin]

variable {p : ℕ} [Fact p.Prime]

/-- The six permutations generate `S_N` (by Proposition 6.4). -/
lemma closure_sixVal (h5 : 5 ≤ p) : Subgroup.closure (Set.range (sixVal (p := p))) = ⊤ := by
  have hNNe := NN_eq (p := p)
  rw [eq_top_iff, ← closure_xs_ys (n := NN p) (by omega), Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · rw [← (prop_6_4 h5).1]; exact eval_mem_closure _ _
  · rw [← (prop_6_4 h5).2]; exact eval_mem_closure _ _

/-! ### Small group-theoretic helpers -/

lemma commute_of_comm {G : Type*} [Group G] {a b : G} (h : a⁻¹ * b⁻¹ * a * b = 1) :
    Commute a b := by
  rw [commute_iff_eq]
  calc a * b = b * a * (a⁻¹ * b⁻¹ * a * b) := by group
    _ = b * a := by rw [h, mul_one]

lemma sq_swap {G : Type*} [Group G] {a b : G} (h : (a * b) ^ 2 = 1) : (b * a) ^ 2 = 1 := by
  have e : (b * a) ^ 2 = a⁻¹ * (a * b) ^ 2 * a := by rw [pow_two, pow_two]; group
  rw [e, h]; group

lemma conj_sq {G : Type*} [Group G] (g a b : G) (h : (a * b) ^ 2 = 1) :
    ((g⁻¹ * a * g) * (g⁻¹ * b * g)) ^ 2 = 1 := by
  have e : ((g⁻¹ * a * g) * (g⁻¹ * b * g)) ^ 2 = g⁻¹ * (a * b) ^ 2 * g := by
    rw [pow_two, pow_two]; group
  rw [e, h]; group

lemma eval_PEe_lutVal :
    (PEe (gen LUT.L) (gen .U) (gen .T)).eval (lutVal (p := p)) = ASL2.tr e2 := by
  simp only [PEe, eval_Peps, eval_PCe_lutVal]
  simp only [eval_gen, lutVal]
  have := conj_tr (lin (MC : SL2 p))⁻¹ e1
  rw [inv_inv] at this
  rw [this]
  congr 1
  ext <;> simp [lin, MC]

/-! ### Theorem 6.3 -/

instance instFiniteSym (n : ℕ) : Finite (Sym n) :=
  Finite.of_equiv (Equiv.Perm (Fin n)) MulOpposite.opEquiv

set_option maxHeartbeats 4000000 in
/-- **Theorem 6.3.** The 27 relators `sixRels p λ μ` form a presentation of `S_N`, `N = 2p² + 2`,
on the six permutations `L, U, T, X₀, X₁, Q`. -/
theorem thm_6_3 {lam mu : ℕ} (h5 : 5 ≤ p) (h : PrimRoot p lam mu) :
    IsPresentation (sixVal (p := p)) (sixRels p lam mu) := by
  have hNNe := NN_eq (p := p)
  have hq := p_ge (p := p) h5
  set Γ := Pres (sixRels p lam mu)
  set of6 : Six → Γ := fun x => PresentedGroup.of x with hof6
  have hmem : ∀ E ∈ sixRels p lam mu, E.eval of6 = 1 := fun E hE => eval_of_eq_one hE
  have hmem' : ∀ E, E ∈ ({pow (gen .X0) 3, pow (gen .X1) 3,
      comm (gen .X0) (gen .L), comm (gen .X0) (gen .U), comm (gen .X1) (gen .L),
      comm (gen .X1) (gen .U),
      pow (mul (gen .X0) (conj (gen .X0) (gen .T))) 2,
      pow (mul (gen .X1) (conj (gen .X1) (gen .T))) 2,
      pow (mul (gen .X0) (gen .X1)) 2,
      pow (mul (gen .X0) (conj (gen .X1) (gen .T))) 2,
      pow (mul (mul (gen .L) (gen .T)) (sixW p)) ((p * p + 1 : ℕ) : ℤ),
      pow (gen .Q) 2, comm (gen .Q) (gen .L), comm (gen .Q) (gen .U), comm (gen .Q) (gen .T),
      pow (mul (gen .Q) (gen .X0)) 2, pow (mul (gen .Q) (gen .X1)) 2} : Set (PE Six)) →
      E.eval of6 = 1 := fun E hE => hmem E (Or.inr hE)
  set gL := of6 .L with hgL
  set gU := of6 .U with hgU
  set gT := of6 .T with hgT
  set gX0 := of6 .X0 with hgX0
  set gX1 := of6 .X1 with hgX1
  set gQ := of6 .Q with hgQ
  -- the relators (R2)–(R6) in `Γ`
  have z2 : ((2 : ℤ)) = ((2 : ℕ) : ℤ) := by norm_num
  have z3 : ((3 : ℤ)) = ((3 : ℕ) : ℤ) := by norm_num
  have r2a : gX0 ^ 3 = 1 := by
    have := hmem' (pow (gen .X0) 3) (Set.mem_insert _ _)
    simp only [eval_pow, eval_gen] at this; rw [z3, zpow_natCast] at this; exact this
  have r2b : gX1 ^ 3 = 1 := by
    have := hmem' (pow (gen .X1) 3) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    simp only [eval_pow, eval_gen] at this; rw [z3, zpow_natCast] at this; exact this
  have r3a : Commute gX0 gL := by
    have := hmem' (comm (gen .X0) (gen .L)) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    simp only [eval_comm, eval_gen] at this
    exact commute_of_comm this
  have r3b : Commute gX0 gU := by
    have := hmem' (comm (gen .X0) (gen .U)) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
    simp only [eval_comm, eval_gen] at this
    exact commute_of_comm this
  have r3c : Commute gX1 gL := by
    have := hmem' (comm (gen .X1) (gen .L)) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))
    simp only [eval_comm, eval_gen] at this
    exact commute_of_comm this
  have r3d : Commute gX1 gU := by
    have := hmem' (comm (gen .X1) (gen .U)) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))))
    simp only [eval_comm, eval_gen] at this
    exact commute_of_comm this
  have r4a : (gX0 * (gT⁻¹ * gX0 * gT)) ^ 2 = 1 := by
    have := hmem' (pow (mul (gen .X0) (conj (gen .X0) (gen .T))) 2) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))))
    simp only [eval_pow, eval_mul, eval_conj, eval_gen] at this; rw [z2, zpow_natCast] at this; exact this
  have r4b : (gX1 * (gT⁻¹ * gX1 * gT)) ^ 2 = 1 := by
    have := hmem' (pow (mul (gen .X1) (conj (gen .X1) (gen .T))) 2) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))))))
    simp only [eval_pow, eval_mul, eval_conj, eval_gen] at this; rw [z2, zpow_natCast] at this; exact this
  have r4c : (gX0 * gX1) ^ 2 = 1 := by
    have := hmem' (pow (mul (gen .X0) (gen .X1)) 2) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))))))
    simp only [eval_pow, eval_mul, eval_conj, eval_gen] at this; rw [z2, zpow_natCast] at this; exact this
  have r4d : (gX0 * (gT⁻¹ * gX1 * gT)) ^ 2 = 1 := by
    have := hmem' (pow (mul (gen .X0) (conj (gen .X1) (gen .T))) 2) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))))))))
    simp only [eval_pow, eval_mul, eval_conj, eval_gen] at this; rw [z2, zpow_natCast] at this; exact this
  have r5 : (gL * gT * (sixW p).eval of6) ^ (p * p + 1) = 1 := by
    have := hmem' (pow (mul (mul (gen .L) (gen .T)) (sixW p)) ((p * p + 1 : ℕ) : ℤ)) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))))))))
    simp only [eval_pow, eval_mul, eval_gen, zpow_natCast] at this
    exact this
  have r6a : gQ ^ 2 = 1 := by
    have := hmem' (pow (gen .Q) 2) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))))))))))
    simp only [eval_pow, eval_mul, eval_conj, eval_gen] at this; rw [z2, zpow_natCast] at this; exact this
  have r6b : Commute gQ gL := by
    have := hmem' (comm (gen .Q) (gen .L)) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))))))))))
    simp only [eval_comm, eval_gen] at this
    exact commute_of_comm this
  have r6c : Commute gQ gU := by
    have := hmem' (comm (gen .Q) (gen .U)) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))))))))))))
    simp only [eval_comm, eval_gen] at this
    exact commute_of_comm this
  have r6d : Commute gQ gT := by
    have := hmem' (comm (gen .Q) (gen .T)) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))))))))))))
    simp only [eval_comm, eval_gen] at this
    exact commute_of_comm this
  have r6e : (gQ * gX0) ^ 2 = 1 := by
    have := hmem' (pow (mul (gen .Q) (gen .X0)) 2) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))))))))))))))
    simp only [eval_pow, eval_mul, eval_conj, eval_gen] at this; rw [z2, zpow_natCast] at this; exact this
  have r6f : (gQ * gX1) ^ 2 = 1 := by
    have := hmem' (pow (mul (gen .Q) (gen .X1)) 2) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))))))))))))))
    simp only [eval_pow, eval_mul, eval_conj, eval_gen] at this; rw [z2, zpow_natCast] at this; exact this
  /- Step 2: `H = ⟨L, U, T⟩` is a quotient of `ASL(2,p)`: the homomorphism `ϑ`. -/
  have hlut : ∀ E ∈ lutRels p lam mu, E.eval (lutF gL gU gT) = 1 := by
    intro E hE
    have := hmem _ (Or.inl ⟨E, hE, rfl⟩)
    rw [eval_map] at this
    have e : lutF gL gU gT = of6 ∘ lutToSix := by funext x; cases x <;> rfl
    rw [e]; exact this
  set ϑ : ASL2 p →* Γ := lutLift h5 h hlut with hϑ
  have ϑL : ϑ (lin ML) = gL := lutLift_L h5 h hlut
  have ϑU : ϑ (lin MU) = gU := lutLift_U h5 h hlut
  have ϑT : ϑ (ASL2.tr e1) = gT := lutLift_T h5 h hlut
  have hϑlut : lutF gL gU gT = ϑ ∘ lutVal := by
    funext x; cases x
    · exact ϑL.symm
    · exact ϑU.symm
    · exact ϑT.symm
  have ϑE : sixE.eval of6 = ϑ (ASL2.tr e2) := by
    have e : sixE = (PEe (gen LUT.L) (gen .U) (gen .T)).map lutToSix := rfl
    have e' : of6 ∘ lutToSix = lutF gL gU gT := by funext x; cases x <;> rfl
    rw [e, eval_map, e', hϑlut, eval_hom, eval_PEe_lutVal]
  /- Step 3: the elements `x_{j,v}`. -/
  set X : ℕ → Γ := fun j => if j = 0 then gX0 else gX1 with hX
  let linHom : SL2 p →* ASL2 p := ⟨⟨lin, lin_one⟩, fun M N => (lin_mul M N).symm⟩
  have hcomm_lin : ∀ j, ∀ M : SL2 p, Commute (ϑ (lin M)) (X j) := by
    intro j M
    have hL' : Commute gL (X j) := by
      simp only [hX]; split_ifs
      · exact r3a.symm
      · exact r3c.symm
    have hU' : Commute gU (X j) := by
      simp only [hX]; split_ifs
      · exact r3b.symm
      · exact r3d.symm
    have hc : Subgroup.closure ({ML, MU} : Set (SL2 p)) ≤
        Subgroup.comap (ϑ.comp linHom) (Subgroup.centralizer {X j}) := by
      rw [Subgroup.closure_le]
      rintro N (rfl | rfl)
      · show ϑ (lin ML) ∈ Subgroup.centralizer {X j}
        rw [Subgroup.mem_centralizer_iff, ϑL]
        rintro _ rfl; exact hL'.eq.symm
      · show ϑ (lin MU) ∈ Subgroup.centralizer {X j}
        rw [Subgroup.mem_centralizer_iff, ϑU]
        rintro _ rfl; exact hU'.eq.symm
    rw [closure_ML_MU] at hc
    have := hc (Subgroup.mem_top M)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at this
    exact (this (X j) rfl).symm
  set xx : ℕ → Vec p → Γ := fun j v => (ϑ (ASL2.tr v))⁻¹ * X j * ϑ (ASL2.tr v) with hxx
  have xx_conj : ∀ j v (β : ASL2 p), (ϑ β)⁻¹ * xx j v * ϑ β = xx j (ASL2.act v β) := by
    intro j v β
    have e : ASL2.tr v * β = lin β.M * ASL2.tr (ASL2.act v β) := by
      rw [lin_mul_tr]; ext1 <;> simp [ASL2.act, ASL2.tr]
    have hc := (hcomm_lin j β.M).eq
    calc (ϑ β)⁻¹ * ((ϑ (ASL2.tr v))⁻¹ * X j * ϑ (ASL2.tr v)) * ϑ β
        = (ϑ (ASL2.tr v * β))⁻¹ * X j * ϑ (ASL2.tr v * β) := by rw [map_mul]; group
      _ = (ϑ (ASL2.tr (ASL2.act v β)))⁻¹ * ((ϑ (lin β.M))⁻¹ * (X j * ϑ (lin β.M))) *
            ϑ (ASL2.tr (ASL2.act v β)) := by rw [e, map_mul]; group
      _ = (ϑ (ASL2.tr (ASL2.act v β)))⁻¹ * ((ϑ (lin β.M))⁻¹ * (ϑ (lin β.M) * X j)) *
            ϑ (ASL2.tr (ASL2.act v β)) := by rw [← hc]
      _ = (ϑ (ASL2.tr (ASL2.act v β)))⁻¹ * X j * ϑ (ASL2.tr (ASL2.act v β)) := by
            rw [inv_mul_cancel_left]
  have xx_zero : ∀ j, xx j 0 = X j := by
    intro j; simp only [hxx, ASL2.tr_zero, map_one, inv_one, one_mul, mul_one]
  have xx_e1 : ∀ j, xx j e1 = gT⁻¹ * X j * gT := by
    intro j; simp only [hxx, ϑT]
  /- Step 4: Carmichael's relations. -/
  have c1 : ∀ j v, (xx j v) ^ 3 = 1 := by
    intro j v
    simp only [hxx]
    rw [conj_pow']
    have : X j ^ 3 = 1 := by simp only [hX]; split_ifs <;> assumption
    rw [this]; group
  -- pairs of points in one plane / with different points
  have base : ∀ j j', j ≤ 1 → j' ≤ 1 → ¬ (j = 1 ∧ j' = 0) →
      (X j * (gT⁻¹ * X j' * gT)) ^ 2 = 1 := by
    intro j j' hj hj' hne
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;>
      rcases (show j' = 0 ∨ j' = 1 by omega) with rfl | rfl
    · exact r4a
    · exact r4d
    · exact absurd ⟨rfl, rfl⟩ hne
    · exact r4b
  have c2a : ∀ j j' v v', j ≤ 1 → j' ≤ 1 → ¬ (j = 1 ∧ j' = 0) → v ≠ v' →
      (xx j v * xx j' v') ^ 2 = 1 := by
    intro j j' v v' hj hj' hne hvv
    have hd : v' - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hvv)
    set g : ASL2 p := ⟨Mrow (v' - v), v⟩
    have h1 : xx j v = (ϑ g)⁻¹ * X j * ϑ g := by
      rw [← xx_zero j, xx_conj]; congr 1; simp [ASL2.act, g]
    have h2 : xx j' v' = (ϑ g)⁻¹ * (gT⁻¹ * X j' * gT) * ϑ g := by
      rw [← xx_e1 j', xx_conj]; congr 1
      simp only [ASL2.act, g, vecMul_e1_Mrow hd, sub_add_cancel]
    rw [h1, h2]
    exact conj_sq _ _ _ (base j j' hj hj' hne)
  have c2b : ∀ v, (xx 0 v * xx 1 v) ^ 2 = 1 := by
    intro v
    simp only [hxx]
    exact conj_sq _ _ _ (by simpa [hX] using r4c)
  have c2 : ∀ j j' v v', j ≤ 1 → j' ≤ 1 → (j, v) ≠ (j', v') → (xx j v * xx j' v') ^ 2 = 1 := by
    intro j j' v v' hj hj' hne
    by_cases hvv : v = v'
    · subst hvv
      have hjj : j ≠ j' := fun h => hne (by rw [h])
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · obtain rfl : j' = 1 := by omega
        exact c2b v
      · obtain rfl : j' = 0 := by omega
        exact sq_swap (c2b v)
    · by_cases h10 : j = 1 ∧ j' = 0
      · obtain ⟨rfl, rfl⟩ := h10
        exact sq_swap (c2a 0 1 v' v (by omega) (by omega) (by omega) (Ne.symm hvv))
      · exact c2a j j' v v' hj hj' h10 hvv
  -- the subgroup `K` generated by the `2q` elements `x_{j,v}`
  set xf : Fin (2 * (p * p)) → Γ := fun i => xx (i.val / (p * p)) (dec0 (i.val % (p * p))) with hxf
  set K := Subgroup.closure (Set.range xf) with hK
  have hq0 : 0 < p * p := by omega
  have xx_mem : ∀ j v, j ≤ 1 → xx j v ∈ K := by
    intro j v hj
    have hlt : j * (p * p) + iota0 v < 2 * (p * p) := by
      have := iota0_lt v
      have : j * (p * p) ≤ 1 * (p * p) := Nat.mul_le_mul_right _ hj
      omega
    have e : xf ⟨j * (p * p) + iota0 v, hlt⟩ = xx j v := by
      simp only [hxf]
      rw [Nat.mul_comm j, Nat.mul_add_div hq0, Nat.div_eq_of_lt (iota0_lt v), Nat.add_zero,
        Nat.mul_add_mod, Nat.mod_eq_of_lt (iota0_lt v), dec0_iota0]
    rw [← e]; exact Subgroup.subset_closure ⟨_, rfl⟩
  have xf_ind : ∀ i : Fin (2 * (p * p)), i.val / (p * p) ≤ 1 := fun i => by
    have := i.isLt
    have : i.val / (p * p) < 2 := (Nat.div_lt_iff_lt_mul hq0).mpr (by omega)
    omega
  have xf_inj : ∀ i i' : Fin (2 * (p * p)), i ≠ i' →
      (i.val / (p * p), dec0 (p := p) (i.val % (p * p))) ≠
        (i'.val / (p * p), dec0 (p := p) (i'.val % (p * p))) := by
    intro i i' hii h
    apply hii
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun x => iota0 x.2) h
    simp only at h1 h2
    rw [iota0_dec0 (Nat.mod_lt _ hq0), iota0_dec0 (Nat.mod_lt _ hq0)] at h2
    apply Fin.ext
    rw [← Nat.div_add_mod i.val (p * p), ← Nat.div_add_mod i'.val (p * p), h1, h2]
  obtain ⟨hCfin, hCcard⟩ := Classical.carmichael_bound (2 * (p * p)) (by omega)
  let f : Fin (2 * (p * p)) → K := fun i => ⟨xf i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hf : ∀ r ∈ Classical.carmichaelRels (2 * (p * p)), FreeGroup.lift f r = 1 := by
    rintro r (⟨i, rfl⟩ | ⟨i, i', hii, rfl⟩)
    · rw [map_pow, FreeGroup.lift_apply_of]
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one, f, hxf]
      exact c1 _ _
    · rw [map_pow, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one, f]
      exact c2 _ _ _ _ (xf_ind i) (xf_ind i') (xf_inj i i' (ne_of_lt hii))
  have hfgen : Subgroup.closure (Set.range f) = ⊤ := by
    have e : Set.range f = ((↑) : K → Γ) ⁻¹' (Set.range xf) := by
      ext k; constructor
      · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
      · rintro ⟨i, hi⟩; exact ⟨i, Subtype.ext hi⟩
    rw [e]
    exact Subgroup.closure_closure_coe_preimage
  obtain ⟨hKfin, hKcard⟩ := card_le_of_presented f hf hfgen hCfin
  /- Step 5: `Γ_A = K`. -/
  have hKn : ∀ (β : ASL2 p), ∀ k ∈ K, (ϑ β)⁻¹ * k * ϑ β ∈ K := by
    intro β k hk
    induction hk using Subgroup.closure_induction with
    | mem k hk =>
      obtain ⟨i, rfl⟩ := hk
      simp only [hxf]
      rw [xx_conj]
      exact xx_mem _ _ (xf_ind i)
    | one => simp
    | mul a b _ _ ha hb =>
      have e : (ϑ β)⁻¹ * (a * b) * ϑ β = ((ϑ β)⁻¹ * a * ϑ β) * ((ϑ β)⁻¹ * b * ϑ β) := by group
      rw [e]; exact K.mul_mem ha hb
    | inv a _ ha =>
      have e : (ϑ β)⁻¹ * a⁻¹ * ϑ β = ((ϑ β)⁻¹ * a * ϑ β)⁻¹ := by group
      rw [e]; exact K.inv_mem ha
  -- `W ∈ K`
  have hp1 : 1 ≤ p := by omega
  have hW : (sixW p).eval of6 ∈ K := by
    simp only [sixW, eval_mul]
    rw [eval_Tel _ _ _ hp1, eval_Tel _ _ _ hp1, ϑE]
    apply K.mul_mem <;> apply Subgroup.list_prod_mem <;> intro z hz <;>
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hz
    · have := xx_conj 0 0 (ASL2.tr e2 ^ t)
      rw [xx_zero] at this
      rw [← map_pow, show (gen Six.X0).eval of6 = X 0 from rfl, this]
      exact xx_mem _ _ (by omega)
    · have := xx_conj 1 0 (ASL2.tr e2 ^ t)
      rw [xx_zero] at this
      rw [← map_pow, show (gen Six.X1).eval of6 = X 1 from rfl, this]
      exact xx_mem _ _ (by omega)
  -- `g = LT = ϑ(φ)` lies in `K`
  have hg : gL * gT = ϑ phiA := by
    rw [← ϑL, ← ϑT, ← map_mul, lin_mul_tr]; rfl
  have hgp : (gL * gT) ^ p = 1 := by rw [hg, ← map_pow, phiA_pow_p h5, map_one]
  have hgK : gL * gT ∈ K := by
    have hpe := powexp (gL * gT) ((sixW p).eval of6) (p * p + 1)
    rw [r5] at hpe
    have hP : ((List.range (p * p + 1)).reverse.map
        (fun i => ((gL * gT) ^ i)⁻¹ * (sixW p).eval of6 * (gL * gT) ^ i)).prod ∈ K := by
      apply Subgroup.list_prod_mem
      intro z hz
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
      rw [hg, ← map_pow]
      exact hKn _ _ hW
    have e : (gL * gT) ^ (p * p + 1) =
        (((List.range (p * p + 1)).reverse.map
          (fun i => ((gL * gT) ^ i)⁻¹ * (sixW p).eval of6 * (gL * gT) ^ i)).prod)⁻¹ :=
      eq_inv_of_mul_eq_one_left hpe.symm
    have e2 : (gL * gT) ^ (p * p + 1) = gL * gT := by
      rw [pow_succ, pow_mul, hgp, one_pow, one_mul]
    rw [← e2, e]
    exact K.inv_mem hP
  -- the normal subgroup `ϑ⁻¹(K)` of `ASL(2,p)` contains `φ`, hence everything (Lemma 5.5')
  let N' : Subgroup (ASL2 p) := K.comap ϑ
  have hN' : N'.Normal := ⟨fun n hn β => by
    show ϑ (β * n * β⁻¹) ∈ K
    have := hKn β⁻¹ (ϑ n) hn
    rwa [map_inv, inv_inv, ← map_inv, ← map_mul, ← map_mul] at this⟩
  have hφ : phiA ∈ N' := by show ϑ phiA ∈ K; rw [← hg]; exact hgK
  have hN'top := normal_eq_top_of_mem N' hφ
  have hϑK : ∀ α, ϑ α ∈ K := fun α => by
    have : α ∈ N' := by rw [hN'top]; trivial
    exact this
  /- Step 7: `Q` normalises `K`, and `Γ = K ∪ KQ`. -/
  have hQϑ : ∀ α : ASL2 p, Commute gQ (ϑ α) := by
    intro α
    have hc : Subgroup.closure (Set.range (lutVal (p := p))) ≤
        Subgroup.comap ϑ (Subgroup.centralizer {gQ}) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      cases x
      · rw [show lutVal (p := p) LUT.L = lin ML from rfl, ϑL]; exact r6b.eq
      · rw [show lutVal (p := p) LUT.U = lin MU from rfl, ϑU]; exact r6c.eq
      · rw [show lutVal (p := p) LUT.T = ASL2.tr e1 from rfl, ϑT]; exact r6d.eq
    rw [(cor_5_4 h5 h).closure_eq_top] at hc
    have := hc (Subgroup.mem_top α)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at this
    exact (this gQ rfl)
  have hQinv : gQ⁻¹ = gQ := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact r6a)
  have hQX : ∀ j, gQ⁻¹ * X j * gQ = (X j)⁻¹ := by
    intro j
    have hsq : (gQ * X j) ^ 2 = 1 := by simp only [hX]; split_ifs <;> assumption
    rw [hQinv]
    rw [pow_two] at hsq
    apply eq_inv_of_mul_eq_one_left
    rw [← hsq]; group
  have hQxx : ∀ j w, gQ⁻¹ * xx j w * gQ = (xx j w)⁻¹ := by
    intro j w
    simp only [hxx]
    have c1 : Commute gQ⁻¹ (ϑ (ASL2.tr w))⁻¹ := (hQϑ (ASL2.tr w)).inv_inv
    have c2 : Commute (ϑ (ASL2.tr w)) gQ := (hQϑ (ASL2.tr w)).symm
    calc gQ⁻¹ * ((ϑ (ASL2.tr w))⁻¹ * X j * ϑ (ASL2.tr w)) * gQ
        = (gQ⁻¹ * (ϑ (ASL2.tr w))⁻¹) * X j * (ϑ (ASL2.tr w) * gQ) := by group
      _ = ((ϑ (ASL2.tr w))⁻¹ * gQ⁻¹) * X j * (gQ * ϑ (ASL2.tr w)) := by rw [c1.eq, c2.eq]
      _ = (ϑ (ASL2.tr w))⁻¹ * (gQ⁻¹ * X j * gQ) * ϑ (ASL2.tr w) := by group
      _ = (ϑ (ASL2.tr w))⁻¹ * (X j)⁻¹ * ϑ (ASL2.tr w) := by rw [hQX]
      _ = ((ϑ (ASL2.tr w))⁻¹ * X j * ϑ (ASL2.tr w))⁻¹ := by group
  have hQK : ∀ k ∈ K, gQ⁻¹ * k * gQ ∈ K := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem k hk =>
      obtain ⟨i, rfl⟩ := hk
      simp only [hxf]
      rw [hQxx]
      exact K.inv_mem (xx_mem _ _ (xf_ind i))
    | one => simp
    | mul a b _ _ ha hb =>
      have e : gQ⁻¹ * (a * b) * gQ = (gQ⁻¹ * a * gQ) * (gQ⁻¹ * b * gQ) := by group
      rw [e]; exact K.mul_mem ha hb
    | inv a _ ha =>
      have e : gQ⁻¹ * a⁻¹ * gQ = (gQ⁻¹ * a * gQ)⁻¹ := by group
      rw [e]; exact K.inv_mem ha
  have hQK' : ∀ k ∈ K, gQ * k * gQ⁻¹ ∈ K := by
    intro k hk; have := hQK k hk; rwa [hQinv] at this ⊢
  have hcover : ∀ γ : Γ, ∃ k ∈ K, γ = k ∨ γ = k * gQ := by
    intro γ
    have hγ : γ ∈ Subgroup.closure (Set.range of6) := by
      rw [closure_range_of']; trivial
    induction hγ using Subgroup.closure_induction with
    | mem γ hγ =>
      obtain ⟨x, rfl⟩ := hγ
      cases x
      · exact ⟨gL, ϑL ▸ hϑK _, Or.inl rfl⟩
      · exact ⟨gU, ϑU ▸ hϑK _, Or.inl rfl⟩
      · exact ⟨gT, ϑT ▸ hϑK _, Or.inl rfl⟩
      · exact ⟨gX0, by have := xx_mem 0 0 (by omega); rwa [xx_zero] at this, Or.inl rfl⟩
      · exact ⟨gX1, by have := xx_mem 1 0 (by omega); rwa [xx_zero] at this, Or.inl rfl⟩
      · exact ⟨1, K.one_mem, Or.inr (one_mul _).symm⟩
    | one => exact ⟨1, K.one_mem, Or.inl rfl⟩
    | mul a b _ _ ha hb =>
      obtain ⟨k1, hk1, h1⟩ := ha
      obtain ⟨k2, hk2, h2⟩ := hb
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2]
      · exact ⟨k1 * k2, K.mul_mem hk1 hk2, Or.inl rfl⟩
      · exact ⟨k1 * k2, K.mul_mem hk1 hk2, Or.inr (by group)⟩
      · refine ⟨k1 * (gQ * k2 * gQ⁻¹), K.mul_mem hk1 (hQK' k2 hk2), Or.inr (by group)⟩
      · refine ⟨k1 * (gQ * k2 * gQ⁻¹), K.mul_mem hk1 (hQK' k2 hk2), Or.inl ?_⟩
        calc k1 * gQ * (k2 * gQ) = k1 * (gQ * k2 * gQ⁻¹) * (gQ * gQ) := by group
          _ = k1 * (gQ * k2 * gQ⁻¹) := by rw [← pow_two, r6a, mul_one]
    | inv a _ ha =>
      obtain ⟨k, hk, h1 | h1⟩ := ha <;> rw [h1]
      · exact ⟨k⁻¹, K.inv_mem hk, Or.inl rfl⟩
      · refine ⟨gQ⁻¹ * k⁻¹ * gQ, hQK _ (K.inv_mem hk), Or.inr ?_⟩
        rw [mul_inv_rev, mul_assoc, mul_assoc, hQinv]
        rw [show gQ * gQ = 1 by rw [← pow_two, r6a]]
        group
  -- the order bound
  let ψ : K × Bool → Γ := fun x => x.1.1 * (if x.2 then gQ else 1)
  have hψ : Function.Surjective ψ := by
    intro γ
    obtain ⟨k, hk, h1 | h1⟩ := hcover γ
    · exact ⟨(⟨k, hk⟩, false), by simp [ψ, h1]⟩
    · exact ⟨(⟨k, hk⟩, true), by simp [ψ, h1]⟩
  have hΓfin : Finite Γ := by
    haveI := hKfin
    exact Finite.of_surjective ψ hψ
  have hΓcard : Nat.card Γ ≤ Nat.card (Sym (NN p)) := by
    have h1 := Nat.card_le_card_of_surjective ψ hψ
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
    rw [natCard_Sym, hNNe]
    have h2 : (2 * (p * p) + 2).factorial / 2 * 2 = (2 * (p * p) + 2).factorial :=
      Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) (by omega))
    calc Nat.card Γ ≤ Nat.card K * 2 := h1
      _ ≤ (2 * (p * p) + 2).factorial / 2 * 2 := Nat.mul_le_mul_right 2 (hKcard.trans hCcard)
      _ = _ := h2
  exact isPresentation_of_card_le (sixRels_hold h5 h) (closure_sixVal h5) hΓfin hΓcard

end SnPres
