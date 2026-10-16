/-
Section 6, part 2: the six permutations `L, U, T, X₀, X₁, Q` of `S_N`, `N = 2p² + 2`, the 27
relators of Theorem 6.3, and Step 1 of its proof (the relators hold).
-/
import SnPres.Section5c
import SnPres.Section6a
import Mathlib.Algebra.BigOperators.Intervals

namespace SnPres

open PE SL2 ASL2

instance instNeZeroOfFactPrime {p : ℕ} [h : Fact p.Prime] : NeZero p := ⟨h.out.ne_zero⟩

/-- `N = 2q + 2` -/
abbrev NN (p : ℕ) : ℕ := 2 * (p * p) + 2

lemma hNN (p : ℕ) : p * p + p * p ≤ NN p := by unfold NN; omega

/-- The six letters `L, U, T, X₀, X₁, Q`. -/
inductive Six | L | U | T | X0 | X1 | Q
  deriving DecidableEq

/-- the letters `L, U, T` among the six letters -/
def lutToSix : LUT → Six
  | .L => .L
  | .U => .U
  | .T => .T

/-- `E = C T C⁻¹` over the six letters -/
def sixE : PE Six := PEe (gen .L) (gen .U) (gen .T)

/-- `W = Tel(X₀, E, p) Tel(X₁, E, p)` -/
def sixW (p : ℕ) : PE Six := mul (Tel (gen .X0) sixE p) (Tel (gen .X1) sixE p)

/-- **The 27 relators of Theorem 6.3**:
(R1) the ten relators of Corollary 5.4 (in the letters `L, U, T`);
(R2) `X₀³, X₁³`; (R3) `[X₀,L], [X₀,U], [X₁,L], [X₁,U]`;
(R4) `(X₀ X₀^T)², (X₁ X₁^T)², (X₀ X₁)², (X₀ X₁^T)²`; (R5) `(L T W)^{q+1}`;
(R6) `Q², [Q,L], [Q,U], [Q,T], (Q X₀)², (Q X₁)²`. -/
def sixRels (p lam mu : ℕ) : Set (PE Six) :=
  (PE.map lutToSix '' lutRels p lam mu) ∪
  {pow (gen .X0) 3, pow (gen .X1) 3,
   comm (gen .X0) (gen .L), comm (gen .X0) (gen .U), comm (gen .X1) (gen .L),
   comm (gen .X1) (gen .U),
   pow (mul (gen .X0) (conj (gen .X0) (gen .T))) 2,
   pow (mul (gen .X1) (conj (gen .X1) (gen .T))) 2,
   pow (mul (gen .X0) (gen .X1)) 2,
   pow (mul (gen .X0) (conj (gen .X1) (gen .T))) 2,
   pow (mul (mul (gen .L) (gen .T)) (sixW p)) ((p * p + 1 : ℕ) : ℤ),
   pow (gen .Q) 2, comm (gen .Q) (gen .L), comm (gen .Q) (gen .U), comm (gen .Q) (gen .T),
   pow (mul (gen .Q) (gen .X0)) 2, pow (mul (gen .Q) (gen .X1)) 2}

variable {p : ℕ} [Fact p.Prime]

/-- `θ : ASL(2,p) → S_N` -/
def thN : ASL2 p →* Sym (NN p) := theta (NN p) (hNN p)

/-- The six permutations: `L = θ(α_{M_L,0})`, `U = θ(α_{M_U,0})`, `T = θ(t_{e₁})`,
`X₀ = (0,⋆,∞)`, `X₁ = (q,⋆,∞)`, `Q = (⋆,∞)`, where `⋆ = 2q`, `∞ = 2q+1`. -/
def sixVal : Six → Sym (NN p)
  | .L => thN (lin ML)
  | .U => thN (lin MU)
  | .T => thN (ASL2.tr e1)
  | .X0 => c3 (NN p) 0 (2 * (p * p)) (2 * (p * p) + 1)
  | .X1 => c3 (NN p) (p * p) (2 * (p * p)) (2 * (p * p) + 1)
  | .Q => tr (NN p) (2 * (p * p)) (2 * (p * p) + 1)

/-! ### Basic facts -/

lemma nv_thN (α : ASL2 p) (i : ℕ) : nv (thN α) i = thetaF α i := nv_theta' (hNN p) α i

lemma thN_fix_s (α : ASL2 p) : nv (thN α) (2 * (p * p)) = 2 * (p * p) := by
  rw [nv_thN, thetaF_ge _ (by omega)]
lemma thN_fix_i (α : ASL2 p) : nv (thN α) (2 * (p * p) + 1) = 2 * (p * p) + 1 := by
  rw [nv_thN, thetaF_ge _ (by omega)]

lemma iota0_zero : iota0 ((0, 0) : Vec p) = 0 := by simp [iota0]
lemma iota1_zero : iota1 ((0, 0) : Vec p) = p * p := by simp [iota1]

lemma nv_thN_iota0 (α : ASL2 p) (v : Vec p) : nv (thN α) (iota0 v) = iota0 (ASL2.act v α) := by
  rw [nv_thN, thetaF_iota0]
lemma nv_thN_iota1 (α : ASL2 p) (v : Vec p) : nv (thN α) (iota1 v) = iota1 (ASL2.act v α) := by
  rw [nv_thN, thetaF_iota1]

lemma thN_lin_fix0 (M : SL2 p) : nv (thN (lin M)) 0 = 0 := by
  rw [← iota0_zero (p := p), nv_thN_iota0]; congr 1; ext <;> simp [ASL2.act, lin]
lemma thN_lin_fixq (M : SL2 p) : nv (thN (lin M)) (p * p) = p * p := by
  rw [← iota1_zero (p := p), nv_thN_iota1]; congr 1; ext <;> simp [ASL2.act, lin]

lemma NN_eq : NN p = 2 * (p * p) + 2 := rfl

lemma p_ge (h5 : 5 ≤ p) : 25 ≤ p * p := Nat.mul_le_mul h5 h5

lemma sixVal_lut : (sixVal (p := p)) ∘ lutToSix = thN ∘ (lutVal (p := p)) := by
  funext x; cases x <;> rfl

lemma eval_sixE : sixE.eval (sixVal (p := p)) = thN (ASL2.tr e2) := by
  have e : sixE = (PEe (gen LUT.L) (gen .U) (gen .T)).map lutToSix := rfl
  rw [e, eval_map, sixVal_lut, eval_hom]
  congr 1
  simp only [PEe, eval_Peps, eval_PCe_lutVal]
  simp only [eval_gen, lutVal]
  have := conj_tr (lin (MC : SL2 p))⁻¹ e1
  rw [inv_inv] at this
  rw [this]
  congr 1
  ext <;> simp [lin, MC]

lemma comm_eq_one {G : Type*} [Group G] {a b : G} (h : Commute a b) : a⁻¹ * b⁻¹ * a * b = 1 := by
  calc a⁻¹ * b⁻¹ * a * b = a⁻¹ * b⁻¹ * (a * b) := by group
    _ = a⁻¹ * b⁻¹ * (b * a) := by rw [h.eq]
    _ = 1 := by group

/-! ### The element `φ = α_{M_L,e₁}` -/

/-- `φ = α_{M_L,0} t_{e₁} = α_{M_L,e₁}` -/
def phiA : ASL2 p := ⟨ML, e1⟩

/-- `0 + 1 + ⋯ + (k-1)` -/
def tri (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, i

lemma tri_succ (k : ℕ) : tri (k + 1) = tri k + k := Finset.sum_range_succ _ _

lemma phiA_pow (k : ℕ) :
    (phiA : ASL2 p) ^ k = ⟨Lx (k : ZMod p), ((k : ZMod p), (tri k : ZMod p))⟩ := by
  induction k with
  | zero =>
    apply ASL2.ext
    · ext <;> simp [Lx]
    · simp [tri]; rfl
  | succ k ih =>
    rw [pow_succ, ih]
    apply ASL2.ext
    · ext <;> simp [Lx, phiA, ML] <;> ring
    · rw [tri_succ]
      ext <;> simp [phiA, ML] <;> ring

lemma act_phiA_pow (v : Vec p) (k : ℕ) :
    ASL2.act v ((phiA : ASL2 p) ^ k) =
      (v.1 + (k : ZMod p), v.2 + (k : ZMod p) * v.1 + (tri k : ZMod p)) := by
  rw [phiA_pow]
  ext <;> simp [ASL2.act, Lx] <;> ring

lemma phiA_pow_p (h5 : 5 ≤ p) : (phiA : ASL2 p) ^ p = 1 := by
  have hodd := p_odd (p := p) h5
  have h2 : 2 ∣ p - 1 := by omega
  have htri : tri p = p * ((p - 1) / 2) := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
    rw [tri, Finset.sum_range_id_mul_two, Nat.mul_assoc, Nat.div_mul_cancel h2]
  rw [phiA_pow, htri]
  apply ASL2.ext
  · ext <;> simp [Lx]
  · ext <;> simp

lemma thN_phiA : sixVal (p := p) .L * sixVal .T = thN phiA := by
  show thN (lin ML) * thN (ASL2.tr e1) = thN phiA
  rw [← map_mul, lin_mul_tr]
  rfl

/-! ### `W` -/

/-- the points `ω_k`: `ι₀(0,k)` for `k < p`, `ι₁(0,k-p)` for `p ≤ k < 2p` -/
def omW (p : ℕ) [NeZero p] (k : ℕ) : ℕ :=
  if k < p then iota0 ((0 : ZMod p), (k : ZMod p))
  else iota1 ((0 : ZMod p), ((k - p : ℕ) : ZMod p))

lemma omW_lt (k : ℕ) : omW p k < p * p + p * p := by
  unfold omW
  split_ifs
  · have := iota0_lt (p := p) (0, (k : ZMod p)); omega
  · exact iota1_lt _

lemma conj_E_pow_X (t : ℕ) {o : ℕ} (v : Vec p) (ho : o = iota0 v ∨ o = iota1 v) :
    ((sixE.eval (sixVal (p := p))) ^ t)⁻¹ * c3 (NN p) o (2 * (p * p)) (2 * (p * p) + 1) *
      (sixE.eval (sixVal (p := p))) ^ t =
    c3 (NN p) (nv (thN (ASL2.tr ((0 : ZMod p), (t : ZMod p)))) o) (2 * (p * p))
      (2 * (p * p) + 1) := by
  have hpp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hq : p * p ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne p))
  have hNNe := NN_eq (p := p)
  have hol : o < 2 * (p * p) := by
    rcases ho with rfl | rfl
    · have := iota0_lt v; omega
    · have := iota1_lt v; omega
  have e : ((t : ZMod p) * (e2 : Vec p).1, (t : ZMod p) * (e2 : Vec p).2) =
      ((0 : ZMod p), (t : ZMod p)) := by ext <;> simp
  rw [eval_sixE, ← map_pow, ASL2.tr_pow, e,
    c3_conj _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    thN_fix_s, thN_fix_i]

/-- The value of `W`: the product `∏_{k<2p} (ω_k, ⋆, ∞)` (proof of Theorem 6.3, (R5)). -/
lemma eval_sixW (h5 : 5 ≤ p) :
    (sixW p).eval (sixVal (p := p)) =
      cprod (NN p) (omW p) (2 * (p * p)) (2 * (p * p) + 1) (2 * p) := by
  have hp1 : 1 ≤ p := by omega
  unfold sixW
  rw [eval_mul, eval_Tel _ _ _ hp1, eval_Tel _ _ _ hp1, cprod, show 2 * p = p + p by omega,
    List.range_add, List.map_append, List.prod_append, List.map_map]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro t ht
    rw [List.mem_range] at ht
    simp only [eval_gen, sixVal]
    rw [conj_E_pow_X t ((0, 0) : Vec p) (Or.inl (iota0_zero (p := p)).symm),
      ← iota0_zero (p := p), nv_thN_iota0]
    unfold omW
    rw [if_pos ht]
    congr 1
    simp [ASL2.act, ASL2.tr]
  · congr 1
    apply List.map_congr_left
    intro t ht
    rw [List.mem_range] at ht
    simp only [eval_gen, sixVal, Function.comp]
    rw [conj_E_pow_X t ((0, 0) : Vec p) (Or.inr (iota1_zero (p := p)).symm),
      ← iota1_zero (p := p), nv_thN_iota1]
    unfold omW
    rw [if_neg (by omega), show p + t - p = t by omega]
    congr 1
    simp [ASL2.act, ASL2.tr]

/-- the points `ω_k` satisfy the hypotheses of Lemma 6.2 -/
lemma pts_omW (h5 : 5 ≤ p) :
    Pts (NN p) (omW p) (2 * (p * p)) (2 * (p * p) + 1) (2 * p) := by
  have hNNe := NN_eq (p := p)
  refine ⟨fun k _ => by have := omW_lt (p := p) k; omega, by omega, by omega, by omega,
    fun k _ => by have := omW_lt (p := p) k; omega, fun k _ => by have := omW_lt (p := p) k; omega,
    ?_⟩
  intro k hk k' hk' h
  unfold omW at h
  split_ifs at h with h1 h2 h2
  · have := congrArg (dec0 (p := p)) h
    rw [dec0_iota0, dec0_iota0] at this
    have e := congrArg Prod.snd this
    simp only at e
    have := congrArg ZMod.val e
    rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at this
  · have := iota0_lt (p := p) (0, (k : ZMod p))
    have := iota1_ge (p := p) (0, ((k' - p : ℕ) : ZMod p))
    omega
  · have := iota1_ge (p := p) (0, ((k - p : ℕ) : ZMod p))
    have := iota0_lt (p := p) (0, (k' : ZMod p))
    omega
  · have := congrArg (dec1 (p := p)) h
    rw [dec1_iota1, dec1_iota1] at this
    have e := congrArg Prod.snd this
    simp only at e
    have := congrArg ZMod.val e
    rw [ZMod.val_natCast_of_lt (show k - p < p by omega),
      ZMod.val_natCast_of_lt (show k' - p < p by omega)] at this
    omega

lemma natCast_ne_zero_of_lt {m : ℕ} (h0 : 0 < m) (hm : m < p) : (m : ZMod p) ≠ 0 := by
  intro h
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hm, ZMod.val_zero] at this
  omega

/-- **(R5)**: `(L T W)^{q+1} = 1`, by Lemma 6.2(b). -/
lemma R5_holds (h5 : 5 ≤ p) :
    (pow (mul (mul (gen Six.L) (gen .T)) (sixW p)) ((p * p + 1 : ℕ) : ℤ)).eval
      (sixVal (p := p)) = 1 := by
  simp only [eval_pow, eval_mul, zpow_natCast]
  rw [eval_sixW h5]
  simp only [eval_gen]
  rw [thN_phiA]
  have hp0 : 0 < p := by omega
  have key := lemma_6_2b (thN (phiA : ASL2 p)) (ω := omW p) (s := 2 * (p * p))
    (i := 2 * (p * p) + 1) (r := 2 * p) (ℓ := p) (by omega) (by omega) (by omega) (pts_omW h5)
    (thN_fix_s _) (thN_fix_i _) ?_ ?_ ?_
  · rw [show 1 + p * (2 * p / 2) = p * p + 1 by
      rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]; ring] at key
    exact key.2.2
  · -- `φ^p = 1`
    intro k _
    rw [← map_pow, phiA_pow_p h5, map_one, nv_one]
  · -- the `φ`-orbit of `(0,b)` meets `{0} × 𝔽_p` only in `(0,b)`
    intro k hk m hm0 hm k' hk' h
    rw [← map_pow] at h
    have hm' : (m : ZMod p) ≠ 0 := natCast_ne_zero_of_lt hm0 hm
    unfold omW at h
    split_ifs at h with h1 h2 h2
    · rw [nv_thN_iota0, act_phiA_pow] at h
      have := congrArg (fun i => (dec0 (p := p) i).1) h
      simp only [dec0_iota0, zero_add] at this
      exact hm' this
    · rw [nv_thN_iota0] at h
      have := iota0_lt (p := p) (ASL2.act (0, (k : ZMod p)) (phiA ^ m))
      have := iota1_ge (p := p) (0, ((k' - p : ℕ) : ZMod p))
      omega
    · rw [nv_thN_iota1] at h
      have := iota1_ge (p := p) (ASL2.act (0, ((k - p : ℕ) : ZMod p)) (phiA ^ m))
      have := iota0_lt (p := p) (0, (k' : ZMod p))
      omega
    · rw [nv_thN_iota1, act_phiA_pow] at h
      have := congrArg (fun i => (dec1 (p := p) i).1) h
      simp only [dec1_iota1, zero_add] at this
      exact hm' this
  · -- every point of `Ω` is on the orbit of some `(0,b)`
    intro j hj hjs hji
    have hNNe := NN_eq (p := p)
    have hj2 : j < p * p + p * p := by omega
    rcases cases_point hj2 with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · refine ⟨(v.2 - (tri v.1.val : ZMod p)).val, by
        have := ZMod.val_lt (v.2 - (tri v.1.val : ZMod p)); omega, v.1.val, ZMod.val_lt _, ?_⟩
      rw [← map_pow, nv_thN]
      unfold omW
      rw [if_pos (ZMod.val_lt _), thetaF_iota0, act_phiA_pow]
      congr 1
      ext <;> simp
    · refine ⟨p + (v.2 - (tri v.1.val : ZMod p)).val, by
        have := ZMod.val_lt (v.2 - (tri v.1.val : ZMod p)); omega, v.1.val, ZMod.val_lt _, ?_⟩
      rw [← map_pow, nv_thN]
      unfold omW
      rw [if_neg (by omega), Nat.add_sub_cancel_left, thetaF_iota1, act_phiA_pow]
      congr 1
      ext <;> simp

/-! ### Step 1: all 27 relators hold -/

theorem sixRels_hold {lam mu : ℕ} (h5 : 5 ≤ p) (h : PrimRoot p lam mu) :
    ∀ E ∈ sixRels p lam mu, E.eval (sixVal (p := p)) = 1 := by
  have hq := p_ge (p := p) h5
  have hpp : p + p ≤ p * p := pp_ge (by omega)
  have hNNe := NN_eq (p := p)
  have hv1 : (1 : ZMod p).val = 1 := ZMod.val_one'' (by have := (Fact.out : p.Prime).two_le; omega)
  have hX0 : sixVal (p := p) .X0 = c3 (NN p) 0 (2 * (p * p)) (2 * (p * p) + 1) := rfl
  have hX1 : sixVal (p := p) .X1 = c3 (NN p) (p * p) (2 * (p * p)) (2 * (p * p) + 1) := rfl
  have hQ : sixVal (p := p) .Q = tr (NN p) (2 * (p * p)) (2 * (p * p) + 1) := rfl
  have hL : sixVal (p := p) .L = thN (lin ML) := rfl
  have hU : sixVal (p := p) .U = thN (lin MU) := rfl
  have hT : sixVal (p := p) .T = thN (ASL2.tr e1) := rfl
  -- `X₀^T = (p,⋆,∞)`, `X₁^T = (q+p,⋆,∞)`
  have hT0 : nv (thN (ASL2.tr (e1 : Vec p))) 0 = p := by
    rw [← iota0_zero (p := p), nv_thN_iota0]; simp [iota0, ASL2.act, ASL2.tr, hv1]
  have hTq : nv (thN (ASL2.tr (e1 : Vec p))) (p * p) = p * p + p := by
    rw [← iota1_zero (p := p), nv_thN_iota1]; simp [iota1, ASL2.act, ASL2.tr, hv1]
  have hX0T : (sixVal (p := p) .T)⁻¹ * sixVal .X0 * sixVal .T =
      c3 (NN p) p (2 * (p * p)) (2 * (p * p) + 1) := by
    rw [hX0, hT, c3_conj _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      hT0, thN_fix_s, thN_fix_i]
  have hX1T : (sixVal (p := p) .T)⁻¹ * sixVal .X1 * sixVal .T =
      c3 (NN p) (p * p + p) (2 * (p * p)) (2 * (p * p) + 1) := by
    rw [hX1, hT, c3_conj _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      hTq, thN_fix_s, thN_fix_i]
  -- commutation facts
  have cX : ∀ (M : SL2 p) (o : ℕ), (o = 0 ∨ o = p * p) →
      Commute (thN (lin M)) (c3 (NN p) o (2 * (p * p)) (2 * (p * p) + 1)) := by
    intro M o ho
    apply commute_c3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · rcases ho with rfl | rfl
      · exact thN_lin_fix0 M
      · exact thN_lin_fixq M
    · exact thN_fix_s _
    · exact thN_fix_i _
  have cQ : ∀ α : ASL2 p, Commute (thN α) (tr (NN p) (2 * (p * p)) (2 * (p * p) + 1)) :=
    fun α => commute_tr _ (by omega) (by omega) (thN_fix_s α) (thN_fix_i α)
  intro E hE
  rcases hE with ⟨E', hE', rfl⟩ | hE
  · -- (R1)
    rw [eval_map, sixVal_lut, eval_hom, (cor_5_4 h5 h).rels E' hE', map_one]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  -- (R2)
  · simp only [eval_pow, eval_gen]
    rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hX0]
    exact c3_pow_three (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · simp only [eval_pow, eval_gen]
    rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hX1]
    exact c3_pow_three (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  -- (R3)
  · simp only [eval_comm, eval_gen]; rw [hX0, hL]; exact comm_eq_one (cX _ _ (Or.inl rfl)).symm
  · simp only [eval_comm, eval_gen]; rw [hX0, hU]; exact comm_eq_one (cX _ _ (Or.inl rfl)).symm
  · simp only [eval_comm, eval_gen]; rw [hX1, hL]; exact comm_eq_one (cX _ _ (Or.inr rfl)).symm
  · simp only [eval_comm, eval_gen]; rw [hX1, hU]; exact comm_eq_one (cX _ _ (Or.inr rfl)).symm
  -- (R4)
  · simp only [eval_pow, eval_mul, eval_conj, eval_gen]
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hX0T, hX0]
    exact c3_mul_c3_sq (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  · simp only [eval_pow, eval_mul, eval_conj, eval_gen]
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hX1T, hX1]
    exact c3_mul_c3_sq (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  · simp only [eval_pow, eval_mul, eval_gen]
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hX0, hX1]
    exact c3_mul_c3_sq (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  · simp only [eval_pow, eval_mul, eval_conj, eval_gen]
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hX1T, hX0]
    exact c3_mul_c3_sq (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  -- (R5)
  · exact R5_holds h5
  -- (R6)
  · simp only [eval_pow, eval_gen]
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hQ]
    exact tr_sq (by omega) (by omega)
  · simp only [eval_comm, eval_gen]; rw [hQ, hL]; exact comm_eq_one (cQ _).symm
  · simp only [eval_comm, eval_gen]; rw [hQ, hU]; exact comm_eq_one (cQ _).symm
  · simp only [eval_comm, eval_gen]; rw [hQ, hT]; exact comm_eq_one (cQ _).symm
  · simp only [eval_pow, eval_mul, eval_gen]
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hQ, hX0]
    exact tr_mul_c3_sq (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · simp only [eval_pow, eval_mul, eval_gen]
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hQ, hX1]
    exact tr_mul_c3_sq (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

end SnPres
