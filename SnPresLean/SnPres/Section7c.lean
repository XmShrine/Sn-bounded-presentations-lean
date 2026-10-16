/-
Section 7, part 3: Theorem 7.3, Step 1 (the relators (G1)–(G4) hold in `S_n`).
-/
import SnPres.Section7b

namespace SnPres

open PE SL2 ASL2

/-! ### Permutation facts -/

section perm
variable {n : ℕ}

/-- permutations of disjoint intervals commute -/
lemma embAt_commute {m m' a b : ℕ} (hab : a + m ≤ b) (h1 : a + m ≤ n) (h2 : b + m' ≤ n)
    (g : Sym m) (g' : Sym m') : Commute (embAt m n a h1 g) (embAt m' n b h2 g') := by
  apply commute_of_fixes _ _ (fun j => b ≤ j ∧ j < b + m')
  · intro j hj
    rw [nv_embAt]; unfold embF; rw [if_neg (by omega)]
  · intro j hj
    rw [nv_embAt]; unfold embF; rw [if_neg hj]
  · intro j hj
    rw [nv_embAt]; unfold embF; rw [if_pos hj]
    have := nv_lt g' (show j - b < m' by omega)
    omega

/-- `(N-1, N, …, n-1) · (0, 1, …, N-1) = (0, 1, …, n-1)` -/
lemma glue_ys {N s : ℕ} (hN : 2 ≤ N) (hs : 1 ≤ s) (h : N + s = n) :
    embAt (s + 1) n (N - 1) (by omega) (ys (s + 1)) * embAt N n 0 (by omega) (ys N) = ys n := by
  apply sym_ext
  intro i hi
  rw [nv_mul, nv_embAt, nv_embAt, nv_ys hi]
  have hA : embF (s + 1) (N - 1) (ys (s + 1)) i =
      if i < N - 1 then i else if i + 1 = n then N - 1 else i + 1 := by
    unfold embF
    by_cases h1 : i < N - 1
    · rw [if_neg (by omega), if_pos h1]
    · rw [if_pos ⟨by omega, by omega⟩, nv_ys (show i - (N - 1) < s + 1 by omega), if_neg h1]
      split_ifs <;> omega
  have hB : ∀ j, embF N 0 (ys N) j = if j < N then (if j + 1 = N then 0 else j + 1) else j := by
    intro j; unfold embF
    by_cases hjN : j < N
    · rw [if_pos ⟨Nat.zero_le _, by omega⟩, Nat.sub_zero, Nat.add_zero, nv_ys hjN, if_pos hjN]
    · rw [if_neg (by omega), if_neg hjN]
  rw [hA, hB]
  split_ifs <;> omega

lemma embAt_offset_eq {m a a' : ℕ} (e : a = a') (h1 : a + m ≤ n) (h2 : a' + m ≤ n) (g : Sym m) :
    embAt m n a h1 g = embAt m n a' h2 g := by
  subst e; rfl

end perm

variable {p : ℕ} [Fact p.Prime]

lemma ys_eq_xs_of_two {m : ℕ} (hm : m = 2) : ys m = xs m (by omega) := by
  subst hm; exact ys_two

/-- the value of `F^{(Υ⁽ᵏ⁾)^r}` -/
lemma eval_shUps {n : ℕ} (hn : NN p ≤ n) (ι : Six → GA) (E : Sym (NN p) →* Sym n)
    (hU : (UpsK p ι).eval (gluVal n hn) = E (ys (NN p))) (F : PE GA) (g : Sym (NN p))
    (hF : F.eval (gluVal n hn) = E g) (r : ℕ) :
    (shUps p ι F r).eval (gluVal n hn) = E ((ys (NN p) ^ r)⁻¹ * g * ys (NN p) ^ r) := by
  simp only [shUps, eval_conj, eval_pow, zpow_natCast]
  rw [hU, hF]
  simp only [map_mul, map_inv, map_pow]

/-- **Theorem 7.3, Step 1**: the relators (G1)–(G4) hold. -/
theorem glu_rels_hold {n lam mu : ℕ} (h5 : 5 ≤ p) (hpr : PrimRoot p lam mu)
    (h1 : n + 3 ≤ 2 * NN p) (h2 : NN p ≤ n - 1) (hnN : NN p ≤ n) :
    ∀ E ∈ gluRels n p lam mu, E.eval (gluVal n hnN) = 1 := by
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
  set E1 : Sym (NN p) →* Sym n := embAt (NN p) n 0 (by omega) with hE1
  set E2 : Sym (NN p) →* Sym n := embAt (NN p) n s (by omega) with hE2
  have v1 : ∀ F : PE Six, (F.map gi1).eval (gluVal n hnN) = E1 (F.eval sixVal) := eval_map_gi1 hnN
  have v2 : ∀ F : PE Six, (F.map gi2).eval (gluVal n hnN) = E2 (F.eval sixVal) := eval_map_gi2 hnN
  have w1 : ∀ F : PE XY, (onXY p gi1 F).eval (gluVal n hnN) = E1 (F.eval (xyv (NN p) hxy)) :=
    eval_onXY hnN h5 gi1 E1 v1
  have w2 : ∀ F : PE XY, (onXY p gi2 F).eval (gluVal n hnN) = E2 (F.eval (xyv (NN p) hxy)) :=
    eval_onXY hnN h5 gi2 E2 v2
  have hXi1 : (XiK gi1).eval (gluVal n hnN) = E1 (xs (NN p) hxy) := by
    rw [XiK, v1, (prop_6_4 h5).1]
  have hXi2 : (XiK gi2).eval (gluVal n hnN) = E2 (xs (NN p) hxy) := by
    rw [XiK, v2, (prop_6_4 h5).1]
  have hU1 : (UpsK p gi1).eval (gluVal n hnN) = E1 (ys (NN p)) := by
    rw [UpsK, v1, (prop_6_4 h5).2]
  have hU2 : (UpsK p gi2).eval (gluVal n hnN) = E2 (ys (NN p)) := by
    rw [UpsK, v2, (prop_6_4 h5).2]
  have hrho1 : ∀ m (hm : 2 ≤ m) (hmN : m ≤ NN p),
      (rhoK p gi1 m).eval (gluVal n hnN) = E1 (embAt m (NN p) 0 (by omega) (ys m)) := by
    intro m hm hmN; rw [rhoK, w1, eval_rho_embAt hxy hm hmN]
  have hrho2 : ∀ m (hm : 2 ≤ m) (hmN : m ≤ NN p),
      (rhoK p gi2 m).eval (gluVal n hnN) = E2 (embAt m (NN p) 0 (by omega) (ys m)) := by
    intro m hm hmN; rw [rhoK, w2, eval_rho_embAt hxy hm hmN]
  -- composition of embeddings
  have c1 : ∀ m b (hb : b + m ≤ NN p) (g : Sym m),
      E1 (embAt m (NN p) b hb g) = embAt m n b (by omega) g := by
    intro m b hb g
    rw [hE1, embAt_comp _ hb (by omega)]
    exact embAt_offset_eq (by omega) _ _ _
  have c2 : ∀ m b (hb : b + m ≤ NN p) (g : Sym m),
      E2 (embAt m (NN p) b hb g) = embAt m n (s + b) (by omega) g := by
    intro m b hb g
    rw [hE2, embAt_comp _ hb (by omega)]
  -- (G2) values
  have hvs1 : (vs1 n p).eval (gluVal n hnN) = embAt k n s (by omega) (xs k (by omega)) := by
    unfold vs1
    rw [eval_shUps hnN gi1 E1 hU1 _ _ hXi1, xs_embAt hxy (show 1 < k by omega) (by omega),
      conj_ys_embAt _ _ (by omega) (show s + k ≤ NN p by omega), c1]
  have hvs2 : (vs2).eval (gluVal n hnN) = embAt k n s (by omega) (xs k (by omega)) := by
    unfold vs2
    rw [hXi2, xs_embAt hxy (show 1 < k by omega) (by omega), c2]
    exact embAt_offset_eq (by omega) _ _ _
  have hga1 : (ga1 n p).eval (gluVal n hnN) = embAt k n s (by omega) (ys k) := by
    unfold ga1
    rw [eval_shUps hnN gi1 E1 hU1 _ _ (hrho1 k (by omega) (by omega)),
      conj_ys_embAt _ _ (by omega) (show s + k ≤ NN p by omega), c1]
  have hga2 : (ga2 n p).eval (gluVal n hnN) = embAt k n s (by omega) (ys k) := by
    unfold ga2
    rw [hrho2 k (by omega) (by omega), c2]
    exact embAt_offset_eq (by omega) _ _ _
  -- (G3) values
  have hLam : ∀ l ∈ LamList n p, ∃ g : Sym (s + 1),
      l.eval (gluVal n hnN) = embAt (s + 1) n 0 (by omega) g := by
    intro l hl
    unfold LamList at hl
    have hx : (XiK gi1).eval (gluVal n hnN) = embAt (s + 1) n 0 (by omega) (xs (s + 1) (by omega)) := by
      rw [hXi1, xs_embAt hxy (show 1 < s + 1 by omega) (by omega), c1]
    split_ifs at hl
    · rw [List.mem_singleton] at hl; subst hl; exact ⟨_, hx⟩
    · rcases List.mem_pair.mp hl with rfl | rfl
      · exact ⟨_, hx⟩
      · exact ⟨ys (s + 1), by rw [hrho1 (s + 1) (by omega) (by omega), c1]⟩
  have hr1 : (Rr1 n p).eval (gluVal n hnN) =
      embAt (s + 1) n (NN p - 1) (by omega) (xs (s + 1) (by omega)) := by
    unfold Rr1
    rw [eval_shUps hnN gi2 E2 hU2 _ _ hXi2, xs_embAt hxy (show 1 < s + 1 by omega) (by omega),
      conj_ys_embAt _ _ (by omega) (show NN p - 1 - s + (s + 1) ≤ NN p by omega), c2]
    exact embAt_offset_eq (by omega) _ _ _
  have hr2 : (Rr2 n p).eval (gluVal n hnN) =
      embAt (s + 1) n (NN p - 1) (by omega) (ys (s + 1)) := by
    unfold Rr2
    rw [eval_shUps hnN gi2 E2 hU2 _ _ (hrho2 (s + 1) (by omega) (by omega)),
      conj_ys_embAt _ _ (by omega) (show NN p - 1 - s + (s + 1) ≤ NN p by omega), c2]
    exact embAt_offset_eq (by omega) _ _ _
  have hR : ∀ r ∈ RList n p, ∃ g : Sym (s + 1),
      r.eval (gluVal n hnN) = embAt (s + 1) n (NN p - 1) (by omega) g := by
    intro r hr
    unfold RList at hr
    split_ifs at hr
    · rw [List.mem_singleton] at hr; subst hr; exact ⟨_, hr1⟩
    · rcases List.mem_pair.mp hr with rfl | rfl
      · exact ⟨_, hr1⟩
      · exact ⟨_, hr2⟩
  -- (G4) value of `r*`
  have hrstar : (rStar n p).eval (gluVal n hnN) =
      embAt (s + 1) n (NN p - 1) (by omega) (ys (s + 1)) := by
    unfold rStar
    split_ifs with hs1'
    · rw [hr1, ys_eq_xs_of_two (show s + 1 = 2 by omega)]
    · exact hr2
  -- the relators
  intro E hE
  simp only [gluRels, gluList, Set.mem_setOf_eq, List.mem_append, List.mem_map, List.mem_flatMap,
    List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hE
  rcases hE with ((((⟨F, hF, rfl⟩ | ⟨F, hF, rfl⟩) | (rfl | rfl)) | ⟨l, hl, r, hr, rfl⟩) | (rfl | rfl))
  · -- (G1), first copy
    have hF' : F ∈ sixRels p lam mu := by rw [sixRels_eq]; exact hF
    rw [v1, (thm_6_3 h5 hpr).rels F hF', map_one]
  · -- (G1), second copy
    have hF' : F ∈ sixRels p lam mu := by rw [sixRels_eq]; exact hF
    rw [v2, (thm_6_3 h5 hpr).rels F hF', map_one]
  · -- (G2)
    rw [eval_mul, eval_inv, hvs1, hvs2, mul_inv_cancel]
  · rw [eval_mul, eval_inv, hga1, hga2, mul_inv_cancel]
  · -- (G3)
    obtain ⟨g, hg⟩ := hLam l hl
    obtain ⟨g', hg'⟩ := hR r hr
    rw [eval_comm, hg, hg']
    exact comm_eq_one (embAt_commute (by omega) _ _ g g')
  · -- (G4)
    rw [eval_mul, eval_inv, eval_gen, hXi1, hE1, embAt_xs _ hxy, Nat.zero_add]
    show xs n _ * _ = 1
    rw [xs_eq_tr, mul_inv_cancel]
  · rw [eval_mul, eval_inv, eval_mul, eval_gen, hrstar, hU1, hE1,
      glue_ys (by omega) hs1 (by omega)]
    exact mul_inv_cancel _

end SnPres
