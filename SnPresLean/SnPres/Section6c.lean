/-
Section 6, part 3: Proposition 6.4 — PEs `Ξ_p`, `Υ_p` over the six letters with values
`(0,1)` and `(0,1,…,N-1)`.
-/
import SnPres.Section6b

namespace SnPres

open PE SL2 ASL2

/-! ### Products over ranges -/

lemma prodRange_add {G : Type*} [Monoid G] (f : ℕ → G) (a b : ℕ) :
    ((List.range (a + b)).map f).prod =
      ((List.range a).map f).prod * ((List.range b).map (fun i => f (a + i))).prod := by
  rw [List.range_add, List.map_append, List.prod_append, List.map_map]
  rfl

lemma prodRange_succ {G : Type*} [Monoid G] (f : ℕ → G) (a : ℕ) :
    ((List.range (a + 1)).map f).prod = ((List.range a).map f).prod * f a := by
  rw [List.range_succ, List.map_append, List.prod_append]; simp

lemma prodRange_mul {G : Type*} [Monoid G] (f : ℕ → G) (A k : ℕ) :
    ((List.range (A * k)).map f).prod =
      ((List.range A).map (fun a => ((List.range k).map (fun t => f (a * k + t))).prod)).prod := by
  induction A with
  | zero => simp
  | succ A ih => rw [Nat.succ_mul, prodRange_add, ih, prodRange_succ]

/-! ### Products of transpositions and 3-cycles -/

section perm
variable {n : ℕ}

lemma c3_mul_tr {A s i : ℕ} (hA : A < n) (hs : s < n) (hi : i < n) (hAs : A ≠ s) (hAi : A ≠ i)
    (hsi : s ≠ i) : c3 n A s i * tr n s i = tr n A i := by
  have C := nv_c3 hA hs hi hAs hAi hsi
  have T1 := nv_tr hs hi
  have T2 := nv_tr hA hi
  apply sym_ext; intro j _
  rw [nv_mul]
  by_cases h1 : j = A
  · subst h1; simp [C, T1, T2, hAs, hAi, hsi, Ne.symm hAs, Ne.symm hAi, Ne.symm hsi]
  by_cases h2 : j = s
  · subst h2; simp [C, T1, T2, hAs, hAi, hsi, Ne.symm hAs, Ne.symm hAi, Ne.symm hsi]
  by_cases h3 : j = i
  · subst h3; simp [C, T1, T2, hAs, hAi, hsi, Ne.symm hAs, Ne.symm hAi, Ne.symm hsi]
  simp [C, T1, T2, h1, h2, h3]

lemma tr_mul_c3 {A s i : ℕ} (hA : A < n) (hs : s < n) (hi : i < n) (hAs : A ≠ s) (hAi : A ≠ i)
    (hsi : s ≠ i) : tr n s i * c3 n A s i = tr n A s := by
  have C := nv_c3 hA hs hi hAs hAi hsi
  have T1 := nv_tr hs hi
  have T2 := nv_tr hA hs
  apply sym_ext; intro j _
  rw [nv_mul]
  by_cases h1 : j = A
  · subst h1; simp [C, T1, T2, hAs, hAi, hsi, Ne.symm hAs, Ne.symm hAi, Ne.symm hsi]
  by_cases h2 : j = s
  · subst h2; simp [C, T1, T2, hAs, hAi, hsi, Ne.symm hAs, Ne.symm hAi, Ne.symm hsi]
  by_cases h3 : j = i
  · subst h3; simp [C, T1, T2, hAs, hAi, hsi, Ne.symm hAs, Ne.symm hAi, Ne.symm hsi]
  simp [C, T1, T2, h1, h2, h3]

lemma tr_tr_tr {A B i : ℕ} (hA : A < n) (hB : B < n) (hi : i < n) (hAB : A ≠ B) (hAi : A ≠ i)
    (hBi : B ≠ i) : tr n A i * tr n B i * tr n A i = tr n A B := by
  have T1 := nv_tr hA hi
  have T2 := nv_tr hB hi
  have T3 := nv_tr hA hB
  apply sym_ext; intro j _
  rw [nv_mul, nv_mul]
  by_cases h1 : j = A
  · subst h1; simp [T1, T2, T3, hAB, hAi, hBi, Ne.symm hAB, Ne.symm hAi, Ne.symm hBi]
  by_cases h2 : j = B
  · subst h2; simp [T1, T2, T3, hAB, hAi, hBi, Ne.symm hAB, Ne.symm hAi, Ne.symm hBi]
  by_cases h3 : j = i
  · subst h3; simp [T1, T2, T3, hAB, hAi, hBi, Ne.symm hAB, Ne.symm hAi, Ne.symm hBi]
  simp [T1, T2, T3, h1, h2, h3]

end perm

/-! ### The PEs of Proposition 6.4 -/

/-- `X_j` -/
def gX (j : ℕ) : PE Six := if j = 0 then gen .X0 else gen .X1

/-- `h_v = T^{a} E^{b}` for `v = (a, b)`, `0 ≤ a, b < p` (exponents `0` and `1` are removed by
normalisation, see `PE.normalize`) -/
def hPE (a b : ℕ) : PE Six := mul (pow (gen .T) a) (pow sixE b)
/-- `x_{j,v} = X_j^{h_v}` -/
def xPE (j a b : ℕ) : PE Six := conj (gX j) (hPE a b)
/-- `u_{j,v} = x_{j,v} Q` -/
def uPE (j a b : ℕ) : PE Six := mul (xPE j a b) (gen .Q)
/-- `[j,v | j',v'] = u_{j,v} u_{j',v'} u_{j,v}` -/
def brPE (j a b j' a' b' : ℕ) : PE Six := mul (mul (uPE j a b) (uPE j' a' b')) (uPE j a b)

section defs64
variable (p : ℕ)
/-- `R⁽⁰⁾ = Tel([0,(0,0) | 0,(0,1)], E, p-1)` -/
def R0PE : PE Six := Tel (brPE 0 0 0 0 0 1) sixE (p - 1)
/-- `J⁽⁰⁾ = [0,(0,p-1) | 0,(1,0)]` -/
def J0PE : PE Six := brPE 0 0 (p - 1) 0 1 0
/-- `R⁽¹⁾ = Tel([1,(0,0) | 1,(0,-1)], E⁻¹, p-1)` -/
def R1PE : PE Six := Tel (brPE 1 0 0 1 0 (p - 1)) (inv sixE) (p - 1)
/-- `J⁽¹⁾ = [1,(0,1) | 1,(1,0)]` -/
def J1PE : PE Six := brPE 1 0 1 1 1 0
/-- `Γ_j = Tel(R⁽ʲ⁾ J⁽ʲ⁾, T, p-1) (R⁽ʲ⁾)^{T^{p-1}}` -/
def GamPE (R J : PE Six) : PE Six :=
  mul (Tel (mul R J) (gen .T) (p - 1)) (conj R (pow (gen .T) ((p - 1 : ℕ) : ℤ)))
/-- `K₁ = [0,(p-1,p-1) | 1,(0,0)]` -/
def K1PE : PE Six := brPE 0 (p - 1) (p - 1) 1 0 0
/-- `K₂ = Q x_{1,(p-1,1)}` -/
def K2PE : PE Six := mul (gen .Q) (xPE 1 (p - 1) 1)
/-- `Ξ_p = [0,(0,0) | 0,(0,1)]` -/
def XiPE : PE Six := brPE 0 0 0 0 0 1
/-- `Υ_p = (Γ₀ K₁ Γ₁ K₂ Q)⁻¹` -/
def UpsPE : PE Six :=
  inv (mul (mul (mul (mul (GamPE p (R0PE p) (J0PE p)) (K1PE p)) (GamPE p (R1PE p) J1PE))
    (K2PE p)) (gen .Q))
end defs64

/-! ### Values -/

variable {p : ℕ} [Fact p.Prime]

/-- the point `ι_j(a,b)` -/
def pt (p : ℕ) [NeZero p] (j a b : ℕ) : ℕ :=
  if j = 0 then iota0 ((a : ZMod p), (b : ZMod p)) else iota1 ((a : ZMod p), (b : ZMod p))

lemma pt_lt (j a b : ℕ) : pt p j a b < p * p + p * p := by
  unfold pt; split_ifs
  · have := iota0_lt (p := p) ((a : ZMod p), (b : ZMod p)); omega
  · exact iota1_lt _

lemma eval_hPE (a b : ℕ) :
    (hPE a b).eval (sixVal (p := p)) = thN (ASL2.tr ((a : ZMod p), (b : ZMod p))) := by
  simp only [hPE, eval_mul, eval_pow, eval_gen, zpow_natCast]
  rw [eval_sixE]
  show thN (ASL2.tr e1) ^ a * thN (ASL2.tr e2) ^ b = _
  rw [← map_pow, ← map_pow, ← map_mul, ASL2.tr_pow, ASL2.tr_pow, ASL2.tr_mul]
  congr 2
  ext <;> simp

lemma nv_thN_tr_pt (j a b : ℕ) (hj : j ≤ 1) :
    nv (thN (ASL2.tr ((a : ZMod p), (b : ZMod p)))) (pt p j 0 0) = pt p j a b := by
  unfold pt
  split_ifs
  · rw [nv_thN_iota0]; congr 1; ext <;> simp [ASL2.act, ASL2.tr]
  · rw [nv_thN_iota1]; congr 1; ext <;> simp [ASL2.act, ASL2.tr]

lemma pt_zero_zero_0 : pt p 0 0 0 = 0 := by simp [pt, iota0]
lemma pt_zero_zero_1 : pt p 1 0 0 = p * p := by simp [pt, iota1]

lemma eval_gX (j : ℕ) (hj : j ≤ 1) :
    (gX j).eval (sixVal (p := p)) = c3 (NN p) (pt p j 0 0) (2 * (p * p)) (2 * (p * p) + 1) := by
  unfold gX
  split_ifs with h
  · subst h; rw [pt_zero_zero_0]; rfl
  · obtain rfl : j = 1 := by omega
    rw [pt_zero_zero_1]; rfl

lemma eval_xPE (j a b : ℕ) (hj : j ≤ 1) :
    (xPE j a b).eval (sixVal (p := p)) =
      c3 (NN p) (pt p j a b) (2 * (p * p)) (2 * (p * p) + 1) := by
  have hNNe := NN_eq (p := p)
  have h0 := pt_lt (p := p) j 0 0
  simp only [xPE, eval_conj]
  rw [eval_gX j hj, eval_hPE,
    c3_conj _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    thN_fix_s, thN_fix_i, nv_thN_tr_pt j a b hj]

lemma eval_uPE (j a b : ℕ) (hj : j ≤ 1) :
    (uPE j a b).eval (sixVal (p := p)) = tr (NN p) (pt p j a b) (2 * (p * p) + 1) := by
  have hNNe := NN_eq (p := p)
  have h0 := pt_lt (p := p) j a b
  simp only [uPE, eval_mul, eval_gen]
  rw [eval_xPE j a b hj]
  exact c3_mul_tr (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

lemma eval_brPE (j a b j' a' b' : ℕ) (hj : j ≤ 1) (hj' : j' ≤ 1)
    (hne : pt p j a b ≠ pt p j' a' b') :
    (brPE j a b j' a' b').eval (sixVal (p := p)) = tr (NN p) (pt p j a b) (pt p j' a' b') := by
  have hNNe := NN_eq (p := p)
  have h0 := pt_lt (p := p) j a b
  have h1 := pt_lt (p := p) j' a' b'
  simp only [brPE, eval_mul]
  rw [eval_uPE j a b hj, eval_uPE j' a' b' hj']
  exact tr_tr_tr (by omega) (by omega) (by omega) hne (by omega) (by omega)

/-! ### Moving points by translations -/

lemma val_natCast_lt {k : ℕ} (hk : k < p) : ((k : ZMod p)).val = k := ZMod.val_natCast_of_lt hk

lemma pt0_eq {a b : ℕ} (ha : a < p) (hb : b < p) : pt p 0 a b = a * p + b := by
  simp [pt, iota0, val_natCast_lt ha, val_natCast_lt hb]

lemma pt1_eq {a b : ℕ} (ha : a < p) (hb : b < p) :
    pt p 1 a b = p * p + a * p + (-(b : ZMod p)).val := by
  simp [pt, iota1, val_natCast_lt ha]

/-- `T^a` moves `ι₀(r, c)` to `ι₀(r + a, c)`. -/
lemma nv_T0 {a i : ℕ} (hi : i < p * p) (ha : i / p + a < p) :
    nv (thN (ASL2.tr ((a : ZMod p), (0 : ZMod p)))) i = i + a * p := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  rw [nv_thN, ← iota0_dec0 hi, thetaF_iota0, iota0_dec0 hi]
  unfold iota0 dec0
  simp only [ASL2.act_tr, Prod.fst_add, Prod.snd_add, add_zero]
  rw [← Nat.cast_add, val_natCast_lt ha, val_natCast_lt (Nat.mod_lt _ hp0)]
  have := Nat.div_add_mod' i p
  rw [Nat.add_mul]; omega

/-- `T^a` moves `ι₁(r, c)` to `ι₁(r + a, c)`. -/
lemma nv_T1 {a i : ℕ} (hi1 : p * p ≤ i) (hi2 : i < p * p + p * p) (ha : (i - p * p) / p + a < p) :
    nv (thN (ASL2.tr ((a : ZMod p), (0 : ZMod p)))) i = i + a * p := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  rw [nv_thN, ← iota1_dec1 hi1 hi2, thetaF_iota1, iota1_dec1 hi1 hi2]
  unfold iota1 dec1
  simp only [ASL2.act_tr, Prod.fst_add, Prod.snd_add, add_zero, neg_neg]
  rw [← Nat.cast_add, val_natCast_lt ha, val_natCast_lt (Nat.mod_lt _ hp0)]
  have := Nat.div_add_mod' (i - p * p) p
  rw [Nat.add_mul]; omega

/-- `E^t` moves `ι₀(r, c)` to `ι₀(r, c + t)`. -/
lemma nv_E0 {t i : ℕ} (hi : i < p * p) (ht : i % p + t < p) :
    nv (thN (ASL2.tr ((0 : ZMod p), (t : ZMod p)))) i = i + t := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  rw [nv_thN, ← iota0_dec0 hi, thetaF_iota0, iota0_dec0 hi]
  unfold iota0 dec0
  simp only [ASL2.act_tr, Prod.fst_add, Prod.snd_add, add_zero]
  rw [← Nat.cast_add, val_natCast_lt ht, val_natCast_lt ((Nat.div_lt_iff_lt_mul hp0).mpr hi)]
  have := Nat.div_add_mod' i p
  omega

/-- `E^{-t}` moves `ι₁(r, c)` (at position `\overline{-c}`) forward by `t` positions. -/
lemma nv_E1 {t i : ℕ} (hi1 : p * p ≤ i) (hi2 : i < p * p + p * p) (ht : (i - p * p) % p + t < p) :
    nv (thN (ASL2.tr ((0 : ZMod p), -(t : ZMod p)))) i = i + t := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  rw [nv_thN, ← iota1_dec1 hi1 hi2, thetaF_iota1, iota1_dec1 hi1 hi2]
  unfold iota1 dec1
  simp only [ASL2.act_tr, Prod.fst_add, Prod.snd_add, add_zero, neg_add_rev, neg_neg]
  rw [show (t : ZMod p) + (((i - p * p) % p : ℕ) : ZMod p) = (((i - p * p) % p + t : ℕ) : ZMod p) by
      push_cast; ring,
    val_natCast_lt ht, val_natCast_lt ((Nat.div_lt_iff_lt_mul hp0).mpr (by omega))]
  have := Nat.div_add_mod' (i - p * p) p
  omega

/-! ### The values of `R⁽ʲ⁾, J⁽ʲ⁾, Γ_j, K₁, K₂` -/

/-- `t_i = (i, i+1)` -/
abbrev tA (p i : ℕ) : Sym (NN p) := tr (NN p) i (i + 1)

lemma conj_tA (g : Sym (NN p)) {i : ℕ} (hi : i + 1 < NN p) :
    g⁻¹ * tA p i * g = tr (NN p) (nv g i) (nv g (i + 1)) := tr_conj g (by omega) hi

lemma eval_R0 (h5 : 5 ≤ p) :
    (R0PE p).eval (sixVal (p := p)) = ((List.range (p - 1)).map (fun t => tA p t)).prod := by
  have hNNe := NN_eq (p := p)
  have hpp : p + p ≤ p * p := pp_ge (by omega)
  have hv1 : (1 : ZMod p).val = 1 := ZMod.val_one'' (by omega)
  unfold R0PE
  rw [eval_Tel _ _ _ (by omega)]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  have hb : pt p 0 0 0 ≠ pt p 0 0 1 := by
    rw [pt_zero_zero_0]; simp [pt, iota0, hv1]
  rw [eval_brPE 0 0 0 0 0 1 (by omega) (by omega) hb, eval_sixE, ← map_pow, ASL2.tr_pow,
    tr_conj _ (by have := pt_lt (p := p) 0 0 0; omega) (by have := pt_lt (p := p) 0 0 1; omega)]
  have e : ((t : ZMod p) * (e2 : Vec p).1, (t : ZMod p) * (e2 : Vec p).2) =
      ((0 : ZMod p), (t : ZMod p)) := by ext <;> simp
  rw [e, pt_zero_zero_0, show pt p 0 0 1 = 1 by simp [pt, iota0, hv1],
    nv_E0 (by omega) (by rw [Nat.zero_mod]; omega),
    nv_E0 (by omega) (by rw [Nat.mod_eq_of_lt (by omega)]; omega)]
  simp [tA, Nat.add_comm]

lemma eval_J0 (h5 : 5 ≤ p) : (J0PE p).eval (sixVal (p := p)) = tA p (p - 1) := by
  have hpp : p + p ≤ p * p := pp_ge (by omega)
  unfold J0PE
  rw [eval_brPE 0 0 (p - 1) 0 1 0 (by omega) (by omega)
    (by rw [pt0_eq (by omega) (by omega), pt0_eq (by omega) (by omega)]; omega),
    pt0_eq (by omega) (by omega), pt0_eq (by omega) (by omega)]
  simp only [tA]
  congr 1 <;> omega

lemma eval_R1 (h5 : 5 ≤ p) :
    (R1PE p).eval (sixVal (p := p)) =
      ((List.range (p - 1)).map (fun t => tA p (p * p + t))).prod := by
  have hNNe := NN_eq (p := p)
  have hpp : p + p ≤ p * p := pp_ge (by omega)
  unfold R1PE
  rw [eval_Tel _ _ _ (by omega)]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  have hq1 : pt p 1 0 (p - 1) = p * p + 1 := by
    rw [pt1_eq (by omega) (by omega)]
    have : -(((p - 1 : ℕ) : ZMod p)) = 1 := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
    rw [this, ZMod.val_one'' (by omega)]; ring
  have hb : pt p 1 0 0 ≠ pt p 1 0 (p - 1) := by rw [pt_zero_zero_1, hq1]; omega
  rw [eval_brPE 1 0 0 1 0 (p - 1) (by omega) (by omega) hb, eval_inv, eval_sixE, ← map_inv,
    ASL2.tr_inv, ← map_pow, ASL2.tr_pow,
    tr_conj _ (by have := pt_lt (p := p) 1 0 0; omega) (by have := pt_lt (p := p) 1 0 (p - 1); omega)]
  have e : ((t : ZMod p) * (-(e2 : Vec p)).1, (t : ZMod p) * (-(e2 : Vec p)).2) =
      ((0 : ZMod p), -(t : ZMod p)) := by ext <;> simp
  rw [e, pt_zero_zero_1, hq1,
    nv_E1 (le_refl _) (by omega) (by rw [Nat.sub_self, Nat.zero_mod]; omega),
    nv_E1 (by omega) (by omega) (by rw [show p * p + 1 - p * p = 1 by omega,
      Nat.mod_eq_of_lt (by omega)]; omega)]
  simp only [tA]
  congr 1 <;> omega

lemma eval_J1 (h5 : 5 ≤ p) : J1PE.eval (sixVal (p := p)) = tA p (p * p + (p - 1)) := by
  have hpp : p + p ≤ p * p := pp_ge (by omega)
  have hm1 : (-(1 : ZMod p)).val = p - 1 := by
    rw [ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one'' (by omega)]
  have h1 : pt p 1 0 1 = p * p + (p - 1) := by
    rw [pt1_eq (by omega) (by omega)]; simp [hm1]
  have h2 : pt p 1 1 0 = p * p + p := by
    rw [pt1_eq (by omega) (by omega)]; simp
  unfold J1PE
  rw [eval_brPE 1 0 1 1 1 0 (by omega) (by omega) (by rw [h1, h2]; omega), h1, h2]
  simp only [tA]
  congr 1; omega

lemma eval_K1 (h5 : 5 ≤ p) : (K1PE p).eval (sixVal (p := p)) = tA p (p * p - 1) := by
  have hpp : p + p ≤ p * p := pp_ge (by omega)
  have h1 : pt p 0 (p - 1) (p - 1) = p * p - 1 := by
    rw [pt0_eq (by omega) (by omega)]
    have : (p - 1) * p + p = p * p := by rw [Nat.sub_mul, Nat.one_mul]; omega
    omega
  unfold K1PE
  rw [eval_brPE 0 (p - 1) (p - 1) 1 0 0 (by omega) (by omega)
    (by rw [h1, pt_zero_zero_1]; omega), h1, pt_zero_zero_1]
  simp only [tA]
  congr 1; omega

lemma eval_K2 (h5 : 5 ≤ p) : (K2PE p).eval (sixVal (p := p)) = tA p (2 * (p * p) - 1) := by
  have hNNe := NN_eq (p := p)
  have hpp : p + p ≤ p * p := pp_ge (by omega)
  have hm1 : (-(1 : ZMod p)).val = p - 1 := by
    rw [ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one'' (by omega)]
  have h1 : pt p 1 (p - 1) 1 = 2 * (p * p) - 1 := by
    rw [pt1_eq (by omega) (by omega)]
    simp only [Nat.cast_one, hm1]
    have : (p - 1) * p + p = p * p := by rw [Nat.sub_mul, Nat.one_mul]; omega
    omega
  have hlt := pt_lt (p := p) 1 (p - 1) 1
  unfold K2PE
  simp only [eval_mul, eval_gen]
  rw [eval_xPE 1 (p - 1) 1 (by omega), h1]
  show tr (NN p) (2 * (p * p)) (2 * (p * p) + 1) * c3 (NN p) (2 * (p * p) - 1) (2 * (p * p))
    (2 * (p * p) + 1) = _
  rw [tr_mul_c3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  simp only [tA]
  congr 1; omega


/-- conjugating a segment `t_B ⋯ t_{B+k-1}` (inside `G₀` or `G₁`) by `T^a` shifts it by `a` rows -/
lemma conj_T_seg (h5 : 5 ≤ p) (B : ℕ) (hB : B = 0 ∨ B = p * p) (a k : ℕ) (hk : k ≤ p)
    (hcond : ∀ t < k, (t + 1) / p + a < p) :
    (sixVal (p := p) .T ^ a)⁻¹ * ((List.range k).map (fun t => tA p (B + t))).prod *
      sixVal (p := p) .T ^ a = ((List.range k).map (fun t => tA p (B + a * p + t))).prod := by
  have hNNe := NN_eq (p := p)
  have hpp : p + p ≤ p * p := pp_ge (by omega)
  have hT : sixVal (p := p) .T ^ a = thN (ASL2.tr ((a : ZMod p), (0 : ZMod p))) := by
    show thN (ASL2.tr e1) ^ a = _
    rw [← map_pow, ASL2.tr_pow]
    congr 2
    ext <;> simp
  rw [hT, conj_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  have ht1 := hcond t ht
  have ha : a < p := lt_of_le_of_lt (Nat.le_add_left a ((t + 1) / p)) ht1
  have hdiv : t / p = 0 := Nat.div_eq_of_lt (by omega)
  have hta : t / p + a < p := by rw [hdiv, Nat.zero_add]; exact ha
  simp only [Function.comp]
  rw [conj_tA _ (by omega)]
  rcases hB with rfl | rfl
  · rw [Nat.zero_add, nv_T0 (by omega) hta, nv_T0 (by omega) ht1]
    simp only [tA, Nat.zero_add]
    congr 1 <;> ring
  · rw [nv_T1 (by omega) (by omega) (by rw [Nat.add_sub_cancel_left]; exact hta),
      nv_T1 (by omega) (by omega) (by rw [Nat.add_assoc, Nat.add_sub_cancel_left]; exact ht1)]
    simp only [tA]
    congr 1 <;> ring

/-- the value of `Γ_j` -/
lemma eval_Gam (h5 : 5 ≤ p) (B : ℕ) (hB : B = 0 ∨ B = p * p) (R J : PE Six)
    (hR : R.eval (sixVal (p := p)) = ((List.range (p - 1)).map (fun t => tA p (B + t))).prod)
    (hJ : J.eval (sixVal (p := p)) = tA p (B + (p - 1))) :
    (GamPE p R J).eval (sixVal (p := p)) =
      ((List.range ((p - 1) * p + (p - 1))).map (fun i => tA p (B + i))).prod := by
  have hpp : p + p ≤ p * p := pp_ge (by omega)
  have hRJ : (mul R J).eval (sixVal (p := p)) =
      ((List.range p).map (fun t => tA p (B + t))).prod := by
    have := prodRange_succ (fun t => tA p (B + t)) (p - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p)] at this
    rw [eval_mul, hR, hJ, this]
  unfold GamPE
  rw [eval_mul, eval_Tel _ _ _ (by omega), eval_conj, eval_pow, zpow_natCast, hR, hRJ]
  simp only [eval_gen]
  rw [conj_T_seg h5 B hB (p - 1) (p - 1) (by omega) (fun t ht => by
      rw [Nat.div_eq_of_lt (by omega)]; omega)]
  have hmap : (List.range (p - 1)).map (fun a => (sixVal (p := p) .T ^ a)⁻¹ *
      ((List.range p).map (fun t => tA p (B + t))).prod * sixVal (p := p) .T ^ a) =
      (List.range (p - 1)).map (fun a => ((List.range p).map (fun t => tA p (B + a * p + t))).prod) := by
    apply List.map_congr_left
    intro a ha
    rw [List.mem_range] at ha
    exact conj_T_seg h5 B hB a p le_rfl (fun t ht => by
      have h1 : (t + 1) / p ≤ 1 := by
        rw [Nat.div_le_iff_le_mul_add_pred (by omega)]; omega
      omega)
  rw [hmap, prodRange_add, prodRange_mul]
  simp only [Nat.add_assoc]

/-- splitting `t₀ ⋯ t_{2Q+2}` -/
lemma prod_split5 {G : Type*} [Monoid G] (f : ℕ → G) (Q : ℕ) :
    ((List.range (2 * Q + 3)).map f).prod =
      ((List.range Q).map f).prod * f Q * ((List.range Q).map (fun i => f (Q + 1 + i))).prod *
        f (2 * Q + 1) * f (2 * Q + 2) := by
  rw [show 2 * Q + 3 = (Q + 1) + (Q + 2) by omega, prodRange_add, prodRange_succ,
    show Q + 2 = (Q + 1) + 1 by omega, prodRange_succ, prodRange_succ]
  simp only [mul_assoc]
  rw [show Q + 1 + Q = 2 * Q + 1 by omega, show Q + 1 + (Q + 1) = 2 * Q + 2 by omega]

/-- the inverse of `t₀ t₁ ⋯ t_{n-2}` is the `n`-cycle `y` -/
lemma adjProd_inv_eq_ys {n : ℕ} (hn : 2 ≤ n) : (adjProd n (n - 1))⁻¹ = ys n := by
  apply sym_ext
  intro j hj
  rw [nv_inv_eq_iff, nv_ys hj]
  by_cases h : j + 1 = n
  · rw [if_pos h, nv_adjProd (by omega), if_pos rfl]; omega
  · rw [if_neg h, nv_adjProd (by omega), if_neg (by omega), if_pos (by omega)]; omega

/-- **Proposition 6.4** (values): `Ξ_p ↦ (0,1)` and `Υ_p ↦ (0,1,…,N-1)`. -/
theorem prop_6_4 (h5 : 5 ≤ p) :
    XiPE.eval (sixVal (p := p)) = xs (NN p) (by have := NN_eq (p := p); omega) ∧
    (UpsPE p).eval (sixVal (p := p)) = ys (NN p) := by
  have hNNe := NN_eq (p := p)
  have hpp : p + p ≤ p * p := pp_ge (by omega)
  have hv1 : (1 : ZMod p).val = 1 := ZMod.val_one'' (by omega)
  constructor
  · have h1 : pt p 0 0 1 = 1 := by simp [pt, iota0, hv1]
    unfold XiPE
    rw [eval_brPE 0 0 0 0 0 1 (by omega) (by omega) (by rw [pt_zero_zero_0, h1]; omega),
      pt_zero_zero_0, h1, xs_eq_tr]
  · have hG0 := eval_Gam h5 0 (Or.inl rfl) (R0PE p) (J0PE p)
      (by rw [eval_R0 h5]; simp) (by rw [eval_J0 h5]; simp)
    have hG1 := eval_Gam h5 (p * p) (Or.inr rfl) (R1PE p) J1PE (eval_R1 h5) (eval_J1 h5)
    obtain ⟨Q, hQ⟩ : ∃ Q, p * p = Q + 1 := ⟨p * p - 1, (Nat.sub_add_cancel (by omega)).symm⟩
    have hr : (p - 1) * p + (p - 1) = Q := by
      have : (p - 1) * p + p = p * p := by rw [Nat.sub_mul, Nat.one_mul]; omega
      omega
    rw [hr] at hG0 hG1
    unfold UpsPE
    rw [eval_inv, eval_mul, eval_mul, eval_mul, eval_mul, hG0, hG1, eval_K1 h5, eval_K2 h5,
      ← adjProd_inv_eq_ys (by omega)]
    congr 1
    simp only [eval_gen]
    have hQv : sixVal (p := p) .Q = tA p (2 * (p * p)) := rfl
    rw [hQv, adjProd, show NN p - 1 = 2 * Q + 3 by omega, prod_split5,
      show p * p - 1 = Q by omega, show 2 * (p * p) - 1 = 2 * Q + 1 by omega,
      show 2 * (p * p) = 2 * Q + 2 by omega]
    simp only [tA, Nat.zero_add, hQ]

end SnPres
