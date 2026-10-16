/-
Section 7, part 4: Theorem 7.3, Steps 2–5 (gluing two copies of `S_N`, Moore's theorem).
-/
import SnPres.Section7c

namespace SnPres

open PE SL2 ASL2

/-! ### Transpositions -/

section adj
variable {n : ℕ}

lemma tr_adj_cube {a : ℕ} (ha : a + 2 < n) :
    (tr n a (a + 1) * tr n (a + 1) (a + 2)) ^ 3 = 1 := by
  have T1 := nv_tr (n := n) (a := a) (b := a + 1) (by omega) (by omega)
  have T2 := nv_tr (n := n) (a := a + 1) (b := a + 2) (by omega) (by omega)
  have e : tr n a (a + 1) * tr n (a + 1) (a + 2) = c3 n a (a + 2) (a + 1) := by
    apply sym_ext; intro j _
    rw [nv_mul, T1, T2, nv_c3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    split_ifs <;> omega
  rw [e]
  exact c3_pow_three (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

lemma tr_disj_sq {a b : ℕ} (hab : a + 2 ≤ b) (hb : b + 1 < n) :
    (tr n a (a + 1) * tr n b (b + 1)) ^ 2 = 1 := by
  have hc : Commute (tr n a (a + 1)) (tr n b (b + 1)) := by
    apply commute_tr _ (by omega) (by omega)
    · rw [nv_tr (by omega) (by omega)]; split_ifs <;> omega
    · rw [nv_tr (by omega) (by omega)]; split_ifs <;> omega
  rw [hc.mul_pow, tr_sq (by omega) (by omega), tr_sq (by omega) (by omega), mul_one]

/-- the adjacent transpositions generate `S_N` -/
lemma closure_adj {N : ℕ} (hN : 2 ≤ N) :
    Subgroup.closure {g : Sym N | ∃ i, i + 1 < N ∧ g = tr N i (i + 1)} = ⊤ := by
  rw [eq_top_iff, ← closure_xs_ys hN, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · rw [xs_eq_tr]; exact Subgroup.subset_closure ⟨0, by omega, rfl⟩
  · rw [← adjProd_inv_eq_ys hN]
    apply Subgroup.inv_mem
    apply Subgroup.list_prod_mem
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    rw [List.mem_range] at hi
    exact Subgroup.subset_closure ⟨i, by omega, rfl⟩

end adj

variable {p : ℕ} [Fact p.Prime]

set_option maxHeartbeats 8000000 in
/-- **Theorem 7.3.** The relators (G1)–(G4) present `S_n` via `φ`. -/
theorem thm_7_3 {n lam mu : ℕ} (h5 : 5 ≤ p) (hpr : PrimRoot p lam mu)
    (h1 : n + 3 ≤ 2 * NN p) (h2 : NN p ≤ n - 1) (hnN : NN p ≤ n) :
    IsPresentation (gluVal n hnN) (gluRels n p lam mu) := by
  have hNNe := NN_eq (p := p)
  have hq := p_ge (p := p) h5
  have hxy : 1 < NN p := by omega
  have hs1 : 1 ≤ sS n p := by simp only [sS]; omega
  have hsN : sS n p + 3 ≤ NN p := by simp only [sS]; omega
  have hk3 : 3 ≤ kK n p := by simp only [kK]; omega
  have hsk : sS n p + kK n p = NN p := by simp only [sS, kK]; omega
  have hsn : sS n p + NN p = n := by simp only [sS]; omega
  set s := sS n p with hs
  set k := kK n p with hk
  set Δ := Pres (gluRels n p lam mu)
  set ofg : GA → Δ := fun a => PresentedGroup.of a with hofg
  have hmem : ∀ E, E ∈ gluList n p lam mu → E.eval ofg = 1 := fun E hE => eval_of_eq_one hE
  have mem_tail : ∀ E, E ∈ [mul (vs1 n p) (inv (vs2)), mul (ga1 n p) (inv (ga2 n p))] ++
      (LamList n p).flatMap (fun l => (RList n p).map (fun r => comm l r)) ++
      [mul (gen (Sum.inl .x)) (inv (XiK gi1)),
       mul (gen (Sum.inl .y)) (inv (mul (rStar n p) (UpsK p gi1)))] → E.eval ofg = 1 := by
    intro E hE
    apply hmem
    unfold gluList
    simp only [List.append_assoc, List.mem_append] at hE ⊢
    right; right; exact hE
  /- Step 2: the homomorphisms `ψ_κ : S_N → Δ_κ ≤ Δ` (from Theorem 6.3). -/
  have hrel1 : ∀ E ∈ sixRels p lam mu, E.eval (ofg ∘ gi1) = 1 := by
    intro E hE
    rw [← eval_map]
    apply hmem
    rw [sixRels_eq] at hE
    unfold gluList
    simp only [List.mem_append, List.mem_map]
    left; left; left; left; exact ⟨E, hE, rfl⟩
  have hrel2 : ∀ E ∈ sixRels p lam mu, E.eval (ofg ∘ gi2) = 1 := by
    intro E hE
    rw [← eval_map]
    apply hmem
    rw [sixRels_eq] at hE
    unfold gluList
    simp only [List.mem_append, List.mem_map]
    left; left; left; right; exact ⟨E, hE, rfl⟩
  set ψ1 : Sym (NN p) →* Δ := (thm_6_3 h5 hpr).lift hrel1 with hψ1
  set ψ2 : Sym (NN p) →* Δ := (thm_6_3 h5 hpr).lift hrel2 with hψ2
  have ψ1v : ∀ F : PE Six, ψ1 (F.eval sixVal) = (F.map gi1).eval ofg := by
    intro F; rw [hψ1, IsPresentation.lift_eval, eval_map]
  have ψ2v : ∀ F : PE Six, ψ2 (F.eval sixVal) = (F.map gi2).eval ofg := by
    intro F; rw [hψ2, IsPresentation.lift_eval, eval_map]
  have ψ1xs : ψ1 (xs (NN p) hxy) = (XiK gi1).eval ofg := by rw [← (prop_6_4 h5).1, ψ1v]; rfl
  have ψ2xs : ψ2 (xs (NN p) hxy) = (XiK gi2).eval ofg := by rw [← (prop_6_4 h5).1, ψ2v]; rfl
  have ψ1ys : ψ1 (ys (NN p)) = (UpsK p gi1).eval ofg := by rw [← (prop_6_4 h5).2, ψ1v]; rfl
  have ψ2ys : ψ2 (ys (NN p)) = (UpsK p gi2).eval ofg := by rw [← (prop_6_4 h5).2, ψ2v]; rfl
  have ψxy : ∀ (ψ : Sym (NN p) →* Δ) (ι : Six → GA), ψ (xs (NN p) hxy) = (XiK ι).eval ofg →
      ψ (ys (NN p)) = (UpsK p ι).eval ofg →
      ∀ F : PE XY, ψ (F.eval (xyv (NN p) hxy)) = (onXY p ι F).eval ofg := by
    intro ψ ι hx hy F
    unfold onXY
    rw [eval_subst, ← eval_hom]
    apply eval_congr
    intro c; cases c
    · exact hx
    · exact hy
  have ψ1xy := ψxy ψ1 gi1 ψ1xs ψ1ys
  have ψ2xy := ψxy ψ2 gi2 ψ2xs ψ2ys
  have ψsh : ∀ (ψ : Sym (NN p) →* Δ) (ι : Six → GA), ψ (ys (NN p)) = (UpsK p ι).eval ofg →
      ∀ (F : PE GA) (g : Sym (NN p)), ψ g = F.eval ofg → ∀ r,
      ψ ((ys (NN p) ^ r)⁻¹ * g * ys (NN p) ^ r) = (shUps p ι F r).eval ofg := by
    intro ψ ι hy F g hg r
    simp only [shUps, eval_conj, eval_pow, zpow_natCast, map_mul, map_inv, map_pow, hy, hg]
  have ψrho : ∀ (ψ : Sym (NN p) →* Δ) (ι : Six → GA),
      (∀ F : PE XY, ψ (F.eval (xyv (NN p) hxy)) = (onXY p ι F).eval ofg) →
      ∀ m (hm : 2 ≤ m) (hmN : m ≤ NN p),
      ψ (embAt m (NN p) 0 (by omega) (ys m)) = (rhoK p ι m).eval ofg := by
    intro ψ ι hF m hm hmN
    rw [← eval_rho_embAt hxy hm hmN, hF]; rfl
  /- the relators (G2)–(G4) in `Δ` -/
  have g2a : (vs1 n p).eval ofg = (vs2).eval ofg := by
    have := mem_tail (mul (vs1 n p) (inv vs2)) (by simp)
    rw [eval_mul, eval_inv, mul_inv_eq_one] at this; exact this
  have g2b : (ga1 n p).eval ofg = (ga2 n p).eval ofg := by
    have := mem_tail (mul (ga1 n p) (inv (ga2 n p))) (by simp)
    rw [eval_mul, eval_inv, mul_inv_eq_one] at this; exact this
  have g3 : ∀ l ∈ LamList n p, ∀ r ∈ RList n p, Commute (l.eval ofg) (r.eval ofg) := by
    intro l hl r hr
    have := mem_tail (comm l r) (by
      simp only [List.mem_append, List.mem_flatMap, List.mem_map]
      left; right; exact ⟨l, hl, r, hr, rfl⟩)
    rw [eval_comm] at this
    exact commute_of_comm this
  have g4a : ofg (Sum.inl .x) = (XiK gi1).eval ofg := by
    have := mem_tail (mul (gen (Sum.inl .x)) (inv (XiK gi1))) (by simp)
    rw [eval_mul, eval_inv, eval_gen, mul_inv_eq_one] at this; exact this
  have g4b : ofg (Sum.inl .y) = (rStar n p).eval ofg * (UpsK p gi1).eval ofg := by
    have := mem_tail (mul (gen (Sum.inl .y)) (inv (mul (rStar n p) (UpsK p gi1)))) (by simp)
    rw [eval_mul, eval_inv, eval_gen, mul_inv_eq_one, eval_mul] at this; exact this
  /- Step 3: `ψ₁` and `ψ₂` agree on `Sym([s, N-1])`. -/
  have hstep3 : ψ1.comp (embAt k (NN p) s (by omega)) = ψ2.comp (embAt k (NN p) 0 (by omega)) := by
    apply MonoidHom.eq_of_eqOn_dense (closure_xs_ys (n := k) (by omega))
    rintro g (rfl | rfl)
    · simp only [MonoidHom.comp_apply]
      rw [← conj_ys_embAt _ s (by omega) (show s + k ≤ NN p by omega),
        ← xs_embAt hxy (show 1 < k by omega) (by omega),
        ψsh ψ1 gi1 ψ1ys _ _ ψ1xs s, ψ2xs]
      exact g2a
    · simp only [MonoidHom.comp_apply]
      rw [← conj_ys_embAt _ s (by omega) (show s + k ≤ NN p by omega),
        ψsh ψ1 gi1 ψ1ys _ _ (ψrho ψ1 gi1 ψ1xy k (by omega) (by omega)) s,
        ψrho ψ2 gi2 ψ2xy k (by omega) (by omega)]
      exact g2b
  /- the elements `τ_i` -/
  set τ : ℕ → Δ := fun i => if i ≤ NN p - 2 then ψ1 (tr (NN p) i (i + 1))
    else ψ2 (tr (NN p) (i - s) (i - s + 1)) with hτ
  have τ1 : ∀ i, i ≤ NN p - 2 → τ i = ψ1 (tr (NN p) i (i + 1)) := by
    intro i hi; simp only [hτ, if_pos hi]
  have τ2 : ∀ i, s ≤ i → i ≤ n - 2 → τ i = ψ2 (tr (NN p) (i - s) (i - s + 1)) := by
    intro i hi1 hi2
    by_cases hi : i ≤ NN p - 2
    · rw [τ1 i hi]
      have e1 : tr (NN p) i (i + 1) =
          embAt k (NN p) s (by omega) (tr k (i - s) (i - s + 1)) := by
        rw [embAt_tr _ (by omega) (by omega)]; congr 1 <;> omega
      have e2 : tr (NN p) (i - s) (i - s + 1) =
          embAt k (NN p) 0 (by omega) (tr k (i - s) (i - s + 1)) := by
        rw [embAt_tr _ (by omega) (by omega)]; rfl
      rw [e1, e2]
      exact DFunLike.congr_fun hstep3 _
    · simp only [hτ, if_neg hi]
  have τsq : ∀ i, i ≤ n - 2 → τ i ^ 2 = 1 := by
    intro i hi
    by_cases h' : i ≤ NN p - 2
    · rw [τ1 i h', ← map_pow, tr_sq (by omega) (by omega), map_one]
    · rw [τ2 i (by omega) hi, ← map_pow, tr_sq (by omega) (by omega), map_one]
  /- Step 4: the cross commutation, from (G3). -/
  set A : Sym (s + 1) →* Δ := ψ1.comp (embAt (s + 1) (NN p) 0 (by omega)) with hA
  set B : Sym (s + 1) →* Δ := ψ2.comp (embAt (s + 1) (NN p) (NN p - 1 - s) (by omega)) with hB
  have Axs : A (xs (s + 1) (by omega)) = (XiK gi1).eval ofg := by
    simp only [hA, MonoidHom.comp_apply]
    rw [← xs_embAt hxy (show 1 < s + 1 by omega) (by omega), ψ1xs]
  have Ays : A (ys (s + 1)) = (rhoK p gi1 (s + 1)).eval ofg := by
    simp only [hA, MonoidHom.comp_apply]
    exact ψrho ψ1 gi1 ψ1xy (s + 1) (by omega) (by omega)
  have Bxs : B (xs (s + 1) (by omega)) = (Rr1 n p).eval ofg := by
    simp only [hB, MonoidHom.comp_apply]
    rw [← conj_ys_embAt _ _ (by omega) (show NN p - 1 - s + (s + 1) ≤ NN p by omega),
      ← xs_embAt hxy (show 1 < s + 1 by omega) (by omega)]
    exact ψsh ψ2 gi2 ψ2ys _ _ ψ2xs _
  have Bys : B (ys (s + 1)) = (Rr2 n p).eval ofg := by
    simp only [hB, MonoidHom.comp_apply]
    rw [← conj_ys_embAt _ _ (by omega) (show NN p - 1 - s + (s + 1) ≤ NN p by omega)]
    exact ψsh ψ2 gi2 ψ2ys _ _ (ψrho ψ2 gi2 ψ2xy (s + 1) (by omega) (by omega)) _
  have hgens : ∀ a ∈ ({xs (s + 1) (by omega), ys (s + 1)} : Set (Sym (s + 1))),
      ∀ b ∈ ({xs (s + 1) (by omega), ys (s + 1)} : Set (Sym (s + 1))), Commute (A a) (B b) := by
    by_cases hs1' : s = 1
    · have hs1'' : sS n p = 1 := hs ▸ hs1'
      have hy : ys (s + 1) = xs (s + 1) (by omega) := ys_eq_xs_of_two (by omega)
      have hc : Commute (A (xs (s + 1) (by omega))) (B (xs (s + 1) (by omega))) := by
        rw [Axs, Bxs]
        apply g3
        · simp [LamList, hs1'']
        · simp [RList, hs1'']
      rintro a (rfl | rfl) b (rfl | rfl) <;> (try rw [hy]) <;> (try rw [hy]) <;> exact hc
    · have hs1'' : ¬ sS n p = 1 := hs ▸ hs1'
      have hL : ∀ l, l = XiK gi1 ∨ l = rhoK p gi1 (s + 1) → l ∈ LamList n p := by
        rintro l (rfl | rfl) <;> simp [LamList, hs1'', hs]
      have hRr : ∀ r, r = Rr1 n p ∨ r = Rr2 n p → r ∈ RList n p := by
        rintro r (rfl | rfl) <;> simp [RList, hs1'']
      rintro a (rfl | rfl) b (rfl | rfl)
      · rw [Axs, Bxs]; exact g3 _ (hL _ (Or.inl rfl)) _ (hRr _ (Or.inl rfl))
      · rw [Axs, Bys]; exact g3 _ (hL _ (Or.inl rfl)) _ (hRr _ (Or.inr rfl))
      · rw [Ays, Bxs]; exact g3 _ (hL _ (Or.inr rfl)) _ (hRr _ (Or.inl rfl))
      · rw [Ays, Bys]; exact g3 _ (hL _ (Or.inr rfl)) _ (hRr _ (Or.inr rfl))
  have hAB : ∀ g g' : Sym (s + 1), Commute (A g) (B g') := by
    have step : ∀ a ∈ ({xs (s + 1) (by omega), ys (s + 1)} : Set (Sym (s + 1))),
        ∀ g' : Sym (s + 1), Commute (A a) (B g') := by
      intro a ha g'
      have hc : Subgroup.closure ({xs (s + 1) (by omega), ys (s + 1)} : Set (Sym (s + 1))) ≤
          (Subgroup.centralizer {A a}).comap B := by
        rw [Subgroup.closure_le]
        intro b hb
        rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact (hgens a ha b hb).eq
      rw [closure_xs_ys (by omega)] at hc
      have := hc (Subgroup.mem_top g')
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at this
      exact (this _ rfl)
    intro g g'
    have hc : Subgroup.closure ({xs (s + 1) (by omega), ys (s + 1)} : Set (Sym (s + 1))) ≤
        (Subgroup.centralizer {B g'}).comap A := by
      rw [Subgroup.closure_le]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact (step a ha g').eq.symm
    rw [closure_xs_ys (by omega)] at hc
    have := hc (Subgroup.mem_top g)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at this
    exact (this _ rfl).symm
  /- Step 4: the Coxeter relations -/
  have cox3 : ∀ i, i + 1 ≤ n - 2 → (τ i * τ (i + 1)) ^ 3 = 1 := by
    intro i hi
    by_cases h' : i + 1 ≤ NN p - 2
    · rw [τ1 i (by omega), τ1 (i + 1) h', ← map_mul, ← map_pow,
        show i + 1 + 1 = i + 2 by omega, tr_adj_cube (by omega), map_one]
    · rw [τ2 i (by omega) (by omega), τ2 (i + 1) (by omega) hi, ← map_mul, ← map_pow,
        show i + 1 - s = i - s + 1 by omega, show i - s + 1 + 1 = i - s + 2 by omega,
        tr_adj_cube (by omega), map_one]
  have cox2 : ∀ i j, i + 2 ≤ j → j ≤ n - 2 → (τ i * τ j) ^ 2 = 1 := by
    intro i j hij hj
    by_cases h' : j ≤ NN p - 2
    · rw [τ1 i (by omega), τ1 j h', ← map_mul, ← map_pow, tr_disj_sq hij (by omega), map_one]
    · by_cases h'' : s ≤ i
      · rw [τ2 i h'' (by omega), τ2 j (by omega) hj, ← map_mul, ← map_pow,
          tr_disj_sq (by omega) (by omega), map_one]
      · -- `i < s` and `j ≥ N - 1`: `τ_i ∈ ⟨Λ⟩`, `τ_j ∈ ⟨ℛ⟩`
        have hi' : τ i = A (tr (s + 1) i (i + 1)) := by
          rw [τ1 i (by omega)]
          simp only [hA, MonoidHom.comp_apply]
          rw [embAt_tr _ (by omega) (by omega)]; rfl
        have hj' : τ j = B (tr (s + 1) (j - (NN p - 1)) (j - (NN p - 1) + 1)) := by
          rw [τ2 j (by omega) hj]
          simp only [hB, MonoidHom.comp_apply]
          rw [embAt_tr _ (by omega) (by omega)]
          congr 2 <;> omega
        rw [hi', hj', (hAB _ _).mul_pow, ← map_pow, ← map_pow, tr_sq (by omega) (by omega),
          tr_sq (by omega) (by omega), map_one, map_one, mul_one]
  /- Step 5: Moore's theorem -/
  obtain ⟨hMfin, hMcard⟩ := Classical.moore_bound n (by omega)
  set T : Subgroup Δ := Subgroup.closure (Set.range (fun i : Fin (n - 1) => τ i.val)) with hT
  let f : Fin (n - 1) → T := fun i => ⟨τ i.val, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hf : ∀ r ∈ Classical.mooreRels n, FreeGroup.lift f r = 1 := by
    rintro r ((⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩) | ⟨i, j, hij, rfl⟩)
    · rw [map_pow, FreeGroup.lift_apply_of]
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one, f]
      exact τsq _ (by omega)
    · rw [map_pow, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one, f]
      rw [hij]
      exact cox3 _ (by have := j.isLt; omega)
    · rw [map_pow, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one, f]
      exact cox2 _ _ hij (by have := j.isLt; omega)
  have hfgen : Subgroup.closure (Set.range f) = ⊤ := by
    have e : Set.range f = ((↑) : T → Δ) ⁻¹' (Set.range (fun i : Fin (n - 1) => τ i.val)) := by
      ext t; constructor
      · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
      · rintro ⟨i, hi⟩; exact ⟨i, Subtype.ext hi⟩
    rw [e]
    exact Subgroup.closure_closure_coe_preimage
  obtain ⟨hTfin, hTcard⟩ := card_le_of_presented f hf hfgen hMfin
  -- `T = Δ`
  have hτT : ∀ i, i ≤ n - 2 → τ i ∈ T := fun i hi =>
    Subgroup.subset_closure ⟨⟨i, by omega⟩, rfl⟩
  have hψ1T : ∀ g, ψ1 g ∈ T := by
    have hc : Subgroup.closure {g : Sym (NN p) | ∃ i, i + 1 < NN p ∧ g = tr (NN p) i (i + 1)} ≤
        T.comap ψ1 := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, ← τ1 i (by omega)]
      exact hτT i (by omega)
    rw [closure_adj (by omega)] at hc
    intro g; exact hc (Subgroup.mem_top g)
  have hψ2T : ∀ g, ψ2 g ∈ T := by
    have hc : Subgroup.closure {g : Sym (NN p) | ∃ i, i + 1 < NN p ∧ g = tr (NN p) i (i + 1)} ≤
        T.comap ψ2 := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have := τ2 (i + s) (by omega) (by omega)
      rw [show i + s - s = i by omega] at this
      rw [← this]
      exact hτT _ (by omega)
    rw [closure_adj (by omega)] at hc
    intro g; exact hc (Subgroup.mem_top g)
  have hTtop : T = ⊤ := by
    rw [eq_top_iff, ← closure_range_of', Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    rcases a with c | G | G
    · cases c
      · show ofg (Sum.inl .x) ∈ T
        rw [g4a, ← ψ1xs]; exact hψ1T _
      · show ofg (Sum.inl .y) ∈ T
        rw [g4b, ← ψ1ys]
        apply T.mul_mem _ (hψ1T _)
        unfold rStar
        split_ifs
        · rw [← Bxs]; exact hψ2T _
        · rw [← Bys]; exact hψ2T _
    · show ofg (gi1 G) ∈ T
      have : ψ1 (sixVal G) = ofg (gi1 G) := (thm_6_3 h5 hpr).lift_apply hrel1 G
      rw [← this]; exact hψ1T _
    · show ofg (gi2 G) ∈ T
      have : ψ2 (sixVal G) = ofg (gi2 G) := (thm_6_3 h5 hpr).lift_apply hrel2 G
      rw [← this]; exact hψ2T _
  have hΔfin : Finite Δ := by
    haveI := hTfin
    rw [hTtop] at hTfin
    exact Finite.of_equiv _ Subgroup.topEquiv.toEquiv
  have hΔcard : Nat.card Δ ≤ Nat.card (Sym n) := by
    rw [natCard_Sym]
    have e : Nat.card T = Nat.card Δ := by
      rw [hTtop]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [← e]
    exact hTcard.trans hMcard
  have hgen : Subgroup.closure (Set.range (gluVal n hnN)) = ⊤ := by
    rw [eq_top_iff, ← closure_xs_ys (n := n) (by omega), Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.subset_closure ⟨Sum.inl .x, rfl⟩
    · exact Subgroup.subset_closure ⟨Sum.inl .y, rfl⟩
  exact isPresentation_of_card_le (glu_rels_hold h5 hpr h1 h2 hnN) hgen hΔfin hΔcard

end SnPres
