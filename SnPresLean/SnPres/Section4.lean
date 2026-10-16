/-
Section 4: the six power expressions `W_L, …, W_Q` over `{x, y}` (Definition 4.2) and their values
(Proposition 4.3), and Lemma 4.4.
-/
import SnPres.Theta

namespace SnPres

open PE SL2 ASL2

/-! ### Describing permutations by functions on `ℕ` -/

section ActsAs
variable {n : ℕ}

/-- `g` acts on `[0, n)` as the function `f`. -/
def ActsAs (g : Sym n) (f : ℕ → ℕ) : Prop := ∀ j < n, nv g j = f j

lemma ActsAs.lt {g : Sym n} {f : ℕ → ℕ} (h : ActsAs g f) {j : ℕ} (hj : j < n) : f j < n := by
  rw [← h j hj]; exact nv_lt g hj

lemma ActsAs.mul {g h : Sym n} {f f' : ℕ → ℕ} (hg : ActsAs g f) (hh : ActsAs h f') :
    ActsAs (g * h) (fun j => f' (f j)) := by
  intro j hj
  rw [nv_mul, hg j hj, hh _ (hg.lt hj)]

lemma ActsAs.congr {g : Sym n} {f f' : ℕ → ℕ} (hg : ActsAs g f) (e : ∀ j < n, f j = f' j) :
    ActsAs g f' := fun j hj => (hg j hj).trans (e j hj)

lemma ActsAs.inv {g : Sym n} {f f' : ℕ → ℕ} (hg : ActsAs g f)
    (h1 : ∀ j < n, f' j < n) (h2 : ∀ j < n, f (f' j) = j) : ActsAs g⁻¹ f' := by
  intro j hj
  rw [nv_inv_eq_iff, hg _ (h1 j hj), h2 j hj]

lemma ActsAs.eq {g h : Sym n} {f : ℕ → ℕ} (hg : ActsAs g f) (hh : ActsAs h f) : g = h :=
  sym_ext fun j hj => (hg j hj).trans (hh j hj).symm

lemma actsAs_nv (g : Sym n) : ActsAs g (nv g) := fun _ _ => rfl

/-- Lemma 3.4(e) in the `ActsAs` language. -/
lemma ActsAs.shift {g : Sym n} {f : ℕ → ℕ} (hg : ActsAs g f) (s : ℕ) (hs : s < n)
    (hfix : ∀ j, n - s ≤ j → j < n → f j = j) :
    ActsAs ((ys n ^ s)⁻¹ * g * ys n ^ s) (shF s f) := by
  intro j hj
  rw [nv_shift g s hs (fun k h1 h2 => (hg k h2).trans (hfix k h1 h2)) j hj]
  unfold shF
  split_ifs with h
  · rfl
  · rw [hg _ (by omega)]

/-- Products of rotations. -/
lemma actsAs_prod_rotF {p : ℕ} (hp : 0 < p) (hn : p * p + p * p ≤ n) (k : ℕ) (g : ℕ → Sym n)
    (m : ℕ → ℕ → ℕ) (hg : ∀ t < k, ActsAs (g t) (rotF p (m t))) :
    ActsAs ((List.range k).map g).prod (rotF p (fun r => sumTo (fun t => m t r) k)) := by
  induction k with
  | zero =>
    intro j hj
    simp only [List.range_zero, List.map_nil, List.prod_nil, nv_one, sumTo_zero]
    exact (rotF_zero hp j).symm
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have := (ih (fun t ht => hg t (by omega))).mul (hg k (by omega))
    refine this.congr ?_
    intro j hj
    rw [rotF_comp hp]
    rfl

lemma actsAs_prod_crotF {p : ℕ} (hp : 0 < p) (hn : p * p + p * p ≤ n) (k : ℕ) (g : ℕ → Sym n)
    (m : ℕ → ℕ → ℕ) (hg : ∀ t < k, ActsAs (g t) (crotF p (m t))) :
    ActsAs ((List.range k).map g).prod (crotF p (fun c => sumTo (fun t => m t c) k)) := by
  induction k with
  | zero =>
    intro j hj
    simp only [List.range_zero, List.map_nil, List.prod_nil, nv_one, sumTo_zero]
    by_cases h : j < p * p + p * p
    · obtain ⟨h1, h2, h3⟩ := dpt_colOf_rowOf hp h
      rw [← h3, crotF_dpt _ h1 h2, Nat.add_zero, Nat.mod_eq_of_lt h2]
    · rw [crotF_ge _ (by omega)]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have := (ih (fun t ht => hg t (by omega))).mul (hg k (by omega))
    refine this.congr ?_
    intro j hj
    rw [crotF_comp hp]
    rfl

/-- Products of row factors of `Σ`. -/
lemma actsAs_prod_phiRow {p : ℕ} (k : ℕ) (g : ℕ → Sym n)
    (hg : ∀ t < k, ActsAs (g t) (phiRow p t)) :
    ActsAs ((List.range k).map g).prod (sigPart p k) := by
  induction k with
  | zero =>
    intro j hj
    simp [sigPart]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact (ih (fun t ht => hg t (by omega))).mul (hg k (by omega))

end ActsAs

/-- `(y^p)^t = y^{tp}` -/
lemma ys_pow_pow (n p t : ℕ) : (ys n ^ p) ^ t = ys n ^ (t * p) := by
  rw [← pow_mul, Nat.mul_comm]

/-! ### Definition 4.2 -/

/-- `y^k` as a power expression. -/
def Yp (k : ℕ) : PE XY := pow PY k

section defs
variable (p : ℕ)

/-- `B = Tel(ρ_p, y^p, p)` -/
def PB : PE XY := Tel (rhoPE p) (Yp p) p
/-- `Z = Tel(B, y^p, p)` -/
def PZ : PE XY := Tel (PB p) (Yp p) p
/-- `B' = B^{y^q}` -/
def PB' : PE XY := conj (PB p) (Yp (p * p))
/-- `L = Z B⁻¹ B'` -/
def WL : PE XY := mul (mul (PZ p) (inv (PB p))) (PB' p)
/-- `V = Tel(σ_p, y^p, p-1)⁻¹` -/
def PV : PE XY := inv (Tel (sigPE p) (Yp p) (p - 1))
/-- `B_c = Tel(V, y, p)` -/
def PBc : PE XY := Tel (PV p) PY p
/-- `Φ = ρ_p ρ_p^{y^q} σ_q` -/
def PPhi : PE XY := mul (mul (rhoPE p) (conj (rhoPE p) (Yp (p * p)))) (sigPE (p * p))
/-- `Σ = Tel(Φ, y^p, p)` -/
def PSigma : PE XY := Tel (PPhi p) (Yp p) p
/-- `Z_c = Tel(B_c, Σ, p)` -/
def PZc : PE XY := Tel (PBc p) (PSigma p) p
/-- `B_c' = B_c^{y^q}` -/
def PBc' : PE XY := conj (PBc p) (Yp (p * p))
/-- `U = Z_c B_c⁻¹ B_c'` -/
def WU : PE XY := mul (mul (PZc p) (inv (PBc p))) (PBc' p)
/-- `T = ρ_q^p (ρ_q^p)^{y^q}` -/
def WT : PE XY := mul (pow (rhoPE (p * p)) p) (conj (pow (rhoPE (p * p)) p) (Yp (p * p)))
/-- `X_0 = σ_{2q} σ_{2q+1}` -/
def WX0 : PE XY := mul (sigPE (2 * (p * p))) (sigPE (2 * (p * p) + 1))
/-- `X_1 = (σ_q σ_{q+1})^{y^q}` -/
def WX1 : PE XY := conj (mul (sigPE (p * p)) (sigPE (p * p + 1))) (Yp (p * p))
/-- `Q = x^{y^{2q}}` -/
def WQ : PE XY := conj PX (Yp (2 * (p * p)))

end defs

/-! ### Proposition 4.3 -/

lemma p_pos' {p : ℕ} (hp : 2 ≤ p) : 0 < p := by omega
lemma pp_ge {p : ℕ} (hp : 2 ≤ p) : p + p ≤ p * p := by
  have := Nat.mul_le_mul_right p hp; omega
lemma hn1 {p n : ℕ} (hp : 2 ≤ p) (hn : p * p + p * p + 2 ≤ n) : 1 < n := by
  have := pp_ge hp; omega

/-- conjugation of a list product -/
lemma conj_list_prod {G : Type*} [Group G] (g : G) (l : List G) :
    g⁻¹ * l.prod * g = (l.map (fun x => g⁻¹ * x * g)).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.prod_cons, List.map_cons]
    rw [← ih]; group

/-- the 3-cycle `(a, b, c)` -/
def c3 (n a b c : ℕ) : Sym n := tr n a b * tr n a c

lemma nv_c3 {n a b c : ℕ} (ha : a < n) (hb : b < n) (hc : c < n) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (j : ℕ) :
    nv (c3 n a b c) j = if j = a then b else if j = b then c else if j = c then a else j := by
  unfold c3
  rw [nv_mul, nv_tr ha hb, nv_tr ha hc]
  split_ifs <;> omega

section values

variable {p n : ℕ} (hp : 2 ≤ p) (hn : p * p + p * p + 2 ≤ n)
include hp hn

lemma eval_Yp (k : ℕ) : (Yp k).eval (xyv n (hn1 hp hn)) = ys n ^ k := by
  simp [Yp, PY, xyv, zpow_natCast]

/-- `ρ_L` acts as the cycle `(0, …, L-1)` -/
lemma acts_rhoL (L : ℕ) (hL : 2 ≤ L) (hLn : L ≤ n) :
    ActsAs ((rhoPE L).eval (xyv n (hn1 hp hn))) (cycF L) := by
  intro j _
  rw [nv_rho (hn1 hp hn) L hL hLn j]; rfl

/-- `σ_k` acts as the transposition `(0, k)` -/
lemma acts_sig (k : ℕ) (hk1 : 1 ≤ k) (hk : k < n) :
    ActsAs ((sigPE k).eval (xyv n (hn1 hp hn))) (trF 0 k) := by
  intro j _
  rw [nv_sig (hn1 hp hn) k hk1 hk j]; rfl

lemma acts_tr {a b : ℕ} (ha : a < n) (hb : b < n) : ActsAs (tr n a b) (trF a b) := by
  intro j _; rw [nv_tr ha hb]; rfl

/-- `ρ_p = rot(𝟙_{0})` -/
lemma acts_rho : ActsAs ((rhoPE p).eval (xyv n (hn1 hp hn))) (rotF p (ind1 0)) := by
  have := pp_ge hp
  exact (acts_rhoL hp hn p hp (by omega)).congr (fun j _ => cycF_eq_rotF (p_pos' hp) j)

/-- (a) `B = rot(𝟙_{[0,p-1]})` -/
lemma acts_B : ActsAs ((PB p).eval (xyv n (hn1 hp hn))) (rotF p (indLow p)) := by
  have hp0 := p_pos' hp
  have hpp := pp_ge hp
  rw [PB, eval_Tel _ _ _ (by omega), eval_Yp hp hn]
  have := actsAs_prod_rotF (n := n) hp0 (by omega) p
    (fun t => ((ys n ^ p) ^ t)⁻¹ * ((rhoPE p).eval (xyv n (hn1 hp hn))) * (ys n ^ p) ^ t)
    (fun t r => ind1 t r) ?_
  · refine this.congr ?_
    intro j _
    apply rotF_congr hp0
    intro r _
    rw [sumTo_ind1]
    rfl
  · intro t ht
    simp only
    rw [ys_pow_pow]
    have htp : t * p + p ≤ p * p := by rw [← succ_mul']; exact rc_le ht
    have h1 := (acts_rho hp hn).shift (t * p) (by omega) (by
      intro j h1 h2
      exact rotF_fix_high hp0 _ 1 (fun r hr => by unfold ind1; rw [if_neg (by omega),
        Nat.zero_mod]) (by omega))
    refine h1.congr ?_
    intro j _
    rw [rotF_shift hp0 _ 1 t (fun r hr => by unfold ind1; rw [if_neg (by omega), Nat.zero_mod])
      (by omega)]
    apply rotF_congr hp0
    intro r _
    congr 1
    unfold ind1
    split_ifs <;> omega

/-- (a) `Z = rot(τ)` -/
lemma acts_Z : ActsAs ((PZ p).eval (xyv n (hn1 hp hn))) (rotF p (tau p)) := by
  have hp0 := p_pos' hp
  have hpp := pp_ge hp
  rw [PZ, eval_Tel _ _ _ (by omega), eval_Yp hp hn]
  have := actsAs_prod_rotF (n := n) hp0 (by omega) p
    (fun t => ((ys n ^ p) ^ t)⁻¹ * ((PB p).eval (xyv n (hn1 hp hn))) * (ys n ^ p) ^ t)
    (fun t r => win p t r) ?_
  · refine this.congr ?_
    intro j _
    apply rotF_congr hp0
    intro r hr
    rw [sumTo_win_eq_tau p r hr]
  · intro t ht
    simp only
    rw [ys_pow_pow]
    have htp : t * p + p ≤ p * p := by rw [← succ_mul']; exact rc_le ht
    have hlow : ∀ r, p ≤ r → indLow p r % p = 0 := fun r hr => by
      unfold indLow; rw [if_neg (by omega), Nat.zero_mod]
    have h1 := (acts_B hp hn).shift (t * p) (by omega) (by
      intro j h1 h2
      exact rotF_fix_high hp0 _ p hlow (by omega))
    refine h1.congr ?_
    intro j _
    rw [rotF_shift hp0 _ p t hlow (by omega)]
    apply rotF_congr hp0
    intro r _
    congr 1
    unfold indLow win
    split_ifs <;> omega

/-- (a) `B' = rot(𝟙_{[p,2p-1]})` -/
lemma acts_B' : ActsAs ((PB' p).eval (xyv n (hn1 hp hn))) (rotF p (indHigh p)) := by
  have hp0 := p_pos' hp
  have hpp := pp_ge hp
  have hlow : ∀ r, p ≤ r → indLow p r % p = 0 := fun r hr => by
    unfold indLow; rw [if_neg (by omega), Nat.zero_mod]
  simp only [PB', eval_conj]
  rw [eval_Yp hp hn]
  have h1 := (acts_B hp hn).shift (p * p) (by omega) (by
    intro j h1 h2
    exact rotF_fix_high hp0 _ p hlow (by omega))
  refine h1.congr ?_
  intro j _
  rw [rotF_shift hp0 _ p p hlow (by omega)]
  apply rotF_congr hp0
  intro r _
  congr 1
  unfold indLow indHigh
  split_ifs <;> omega

/-- the inverse of `rot(𝟙_{[0,p-1]})` -/
lemma acts_B_inv : ActsAs ((PB p).eval (xyv n (hn1 hp hn)))⁻¹
    (rotF p (fun r => if r < p then p - 1 else 0)) := by
  have hp0 := p_pos' hp
  have hpp := pp_ge hp
  refine (acts_B hp hn).inv (fun j hj => ?_) (fun j hj => ?_)
  · by_cases h : j < p * p + p * p
    · have := rotF_lt hp0 (fun r => if r < p then p - 1 else 0) h; omega
    · rw [rotF_ge _ (by omega)]; exact hj
  · rw [rotF_comp hp0]
    rw [rotF_congr hp0 (m' := fun _ => 0) (fun r _ => by
      show ((if r < p then p - 1 else 0) + indLow p r) % p = 0 % p
      unfold indLow
      split_ifs with h
      · rw [show p - 1 + 1 = p by omega, Nat.mod_self, Nat.zero_mod]
      · rfl) j]
    exact rotF_zero hp0 j

/-- (c) `L = rot(ν)` -/
lemma acts_L : ActsAs ((WL p).eval (xyv n (hn1 hp hn))) (rotF p (nuF p)) := by
  have hp0 := p_pos' hp
  simp only [WL, eval_mul, eval_inv]
  refine (((acts_Z hp hn).mul (acts_B_inv hp hn)).mul (acts_B' hp hn)).congr ?_
  intro j _
  rw [rotF_comp hp0, rotF_comp hp0]
  apply rotF_congr hp0
  intro r hr
  rw [← Nat.add_assoc]
  exact L_amounts hp0 hr

/-- the column product `(c, p+c)(p+c, 2p+c)⋯((p-2)p+c, (p-1)p+c)` -/
def colProd (n p c : ℕ) : Sym n :=
  ((List.range (p - 1)).map (fun t => tr n (t * p + c) ((t + 1) * p + c))).prod

lemma colProd_lt {c t : ℕ} (hc : c < p) (ht : t ≤ p - 1) : t * p + c < n := by
  have hpp := pp_ge hp
  have : t * p + c < p * p := rc_lt (by omega) hc
  omega

/-- `V^{y^c} = (c, p+c, …, (p-1)p+c) = crot(𝟙_{c})` -/
lemma acts_colProd_inv (c : ℕ) (hc : c < p) : ActsAs (colProd n p c)⁻¹ (crotF p (ind1 c)) := by
  have hp0 := p_pos' hp
  have hpp := pp_ge hp
  have hz : ∀ i ≤ p - 1, (fun t => t * p + c) i < n := fun i hi => colProd_lt hp hn hc hi
  have hinj : ∀ i j, i ≤ p - 1 → j ≤ p - 1 →
      (fun t => t * p + c) i = (fun t => t * p + c) j → i = j := by
    intro i j _ _ h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_right hp0 (by omega)
  obtain ⟨h0, h1, h2⟩ := path_lemma (n := n) (fun t => t * p + c) (p - 1) hz hinj
  refine ActsAs.inv (actsAs_nv _) (fun j hj => ?_) (fun j hj => ?_)
  · by_cases h : j < p * p + p * p
    · have := crotF_lt hp0 (ind1 c) h; omega
    · rw [crotF_ge _ (by omega)]; exact hj
  · rw [col_char hp0 hc j]
    unfold colProd
    by_cases hA : j < p * p ∧ j % p = c
    · rw [if_pos hA]
      have hi : j / p < p := (Nat.div_lt_iff_lt_mul hp0).mpr hA.1
      have hj' : j = j / p * p + c := by have := Nat.div_add_mod' j p; omega
      by_cases hA1 : j + p < p * p
      · rw [if_pos hA1]
        have e : j + p = (j / p + 1) * p + c := by rw [succ_mul']; omega
        have hle : j / p + 1 ≤ p - 1 := by
          refine Decidable.byContradiction fun h => ?_
          have h4 : j / p = p - 1 := by omega
          have h3 : (j / p + 1) * p = p * p := by rw [h4, show p - 1 + 1 = p by omega]
          rw [succ_mul'] at h3
          omega
        have h5 := h1 (j / p + 1) (Nat.le_add_left 1 (j / p)) hle
        rw [e, h5]
        simp only [Nat.add_sub_cancel]
        omega
      · rw [if_neg hA1]
        have hi' : j / p = p - 1 := by
          refine Decidable.byContradiction fun h => ?_
          have : (j / p + 1) * p + c < p * p := rc_lt (by omega) hc
          rw [succ_mul'] at this
          omega
        have := h0
        simp only [Nat.zero_mul, Nat.zero_add] at this
        rw [this]
        rw [hi'] at hj'
        omega
    · rw [if_neg hA]
      apply h2
      intro i hi heq
      apply hA
      have : i * p + c < p * p := rc_lt (by omega) hc
      refine ⟨by omega, ?_⟩
      rw [heq, rc_mod hc]

/-- `σ_p^{y^{tp}} = (tp, tp + p)` -/
lemma sig_shift (t : ℕ) (ht : t ≤ p - 2) :
    (ys n ^ (t * p))⁻¹ * ((sigPE p).eval (xyv n (hn1 hp hn))) * ys n ^ (t * p) =
      tr n (t * p + 0) ((t + 1) * p + 0) := by
  have hp0 := p_pos' hp
  have hpp := pp_ge hp
  have htp : (t + 1) * p + p ≤ p * p := by
    rw [← succ_mul']; exact rc_le (by omega)
  rw [succ_mul'] at htp
  refine ActsAs.eq ?_ (acts_tr hp hn (by omega) (by rw [succ_mul']; omega))
  refine ((acts_sig hp hn p (by omega) (by omega)).shift (t * p) (by omega) (by
    intro j h1 h2; unfold trF; rw [if_neg (by omega), if_neg (by omega)])).congr ?_
  intro j _
  rw [trF_shift', succ_mul']
  congr 1 <;> omega

/-- `(y^c)⁻¹ (a, b) y^c = (a + c, b + c)` for `a, b < n - c` -/
lemma tr_shift {a b c : ℕ} (ha : a + c < n) (hb : b + c < n) :
    (ys n ^ c)⁻¹ * tr n a b * ys n ^ c = tr n (a + c) (b + c) := by
  refine ActsAs.eq ?_ (acts_tr hp hn ha hb)
  refine ((acts_tr hp hn (by omega) (by omega)).shift c (by omega) (by
    intro j h1 h2; unfold trF; rw [if_neg (by omega), if_neg (by omega)])).congr ?_
  intro j _
  rw [trF_shift']

/-- `V = colProd(0)⁻¹` -/
lemma eval_V : (PV p).eval (xyv n (hn1 hp hn)) = (colProd n p 0)⁻¹ := by
  have hp0 := p_pos' hp
  simp only [PV, eval_inv]
  rw [eval_Tel _ _ _ (by omega), eval_Yp hp hn]
  congr 1
  unfold colProd
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  rw [ys_pow_pow]
  exact sig_shift hp hn t (by omega)

/-- `V^{y^c} = colProd(c)⁻¹` -/
lemma V_conj (c : ℕ) (hc : c < p) :
    (ys n ^ c)⁻¹ * ((PV p).eval (xyv n (hn1 hp hn))) * ys n ^ c = (colProd n p c)⁻¹ := by
  have hpp := pp_ge hp
  rw [eval_V hp hn, ← inv_inj, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, ← mul_assoc]
  unfold colProd
  rw [conj_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  simp only [Function.comp]
  have h1 : (t + 1) * p + c < n := colProd_lt hp hn hc (by omega)
  have h2 : t * p + c < n := colProd_lt hp hn hc (by omega)
  rw [tr_shift hp hn (by omega) (by omega)]
  simp

/-- (b) `B_c = crot(𝟙_{[0,p-1]})` -/
lemma acts_Bc : ActsAs ((PBc p).eval (xyv n (hn1 hp hn))) (crotF p (indLow p)) := by
  have hp0 := p_pos' hp
  have hpp := pp_ge hp
  rw [PBc, eval_Tel _ _ _ (by omega)]
  have := actsAs_prod_crotF (n := n) hp0 (by omega) p
    (fun c => (PY.eval (xyv n (hn1 hp hn)) ^ c)⁻¹ * ((PV p).eval (xyv n (hn1 hp hn))) *
      PY.eval (xyv n (hn1 hp hn)) ^ c) (fun c r => ind1 c r) ?_
  · refine this.congr ?_
    intro j _
    apply crotF_congr hp0
    intro r _
    rw [sumTo_ind1]; rfl
  · intro c hc
    have e : PY.eval (xyv n (hn1 hp hn)) = ys n := rfl
    simp only [e]
    rw [V_conj hp hn c hc]
    exact acts_colProd_inv hp hn c hc

/-- (b) `Φ` acts on row `0` -/
lemma acts_Phi : ActsAs ((PPhi p).eval (xyv n (hn1 hp hn))) (phiRow p 0) := by
  have hpp := pp_ge hp
  simp only [PPhi, eval_mul, eval_conj]
  rw [eval_Yp hp hn]
  have hr := acts_rhoL hp hn p hp (by omega)
  have hrs := hr.shift (p * p) (by omega) (by
    intro j h1 h2; unfold cycF; rw [if_neg (by omega), if_neg (by omega)])
  have hs := acts_sig hp hn (p * p) (by omega) (by omega)
  refine ((hr.mul hrs).mul hs).congr ?_
  intro j _
  exact phi_formula hp j

/-- (b) `Σ`: `d(c, i) ↦ d(c+1 mod 2p, i)` -/
lemma acts_Sigma : ActsAs ((PSigma p).eval (xyv n (hn1 hp hn))) (sigma p) := by
  have hp0 := p_pos' hp
  have hpp := pp_ge hp
  rw [PSigma, eval_Tel _ _ _ (by omega), eval_Yp hp hn]
  refine actsAs_prod_phiRow p _ ?_
  intro i hi
  rw [ys_pow_pow]
  have hip : i * p + p ≤ p * p := by rw [← succ_mul']; exact rc_le hi
  refine ((acts_Phi hp hn).shift (i * p) (by omega) (by
    intro j h1 h2; unfold phiRow; split_ifs <;> omega)).congr ?_
  intro j _
  exact phiRow_shift hip j

/-- conjugating `crot(m)` by `Σ` -/
lemma acts_conj_Sigma {g S : Sym n} (m : ℕ → ℕ) (hg : ActsAs g (crotF p m))
    (hS : ActsAs S (sigma p)) :
    ActsAs (S⁻¹ * g * S) (crotF p (fun c => m ((c + (2 * p - 1)) % (2 * p)))) := by
  have hp0 := p_pos' hp
  have hpp := pp_ge hp
  intro j hj
  rw [nv_mul, nv_mul]
  set k := nv S⁻¹ j with hk
  have hk' : nv S k = j := by rw [hk, nv_nv_inv]
  have hkn : k < n := (nv_lt_iff S⁻¹ j).mpr hj
  rw [hS k hkn] at hk'
  by_cases hk2 : k < p * p + p * p
  · obtain ⟨h1, h2, h3⟩ := dpt_colOf_rowOf hp0 hk2
    generalize colOf p k = c at h1 h3
    generalize rowOf p k = i at h2 h3
    rw [← h3] at hk' ⊢
    rw [sigma_dpt hp0 h1 h2] at hk'
    rw [hg _ (by rw [h3]; exact hkn), crotF_dpt _ h1 h2,
      hS _ (by have := dpt_lt (p := p) h1 (Nat.mod_lt (i + m c) hp0); omega),
      sigma_dpt hp0 h1 (Nat.mod_lt _ hp0), ← hk', crotF_dpt _ (Nat.mod_lt _ (by omega)) h2,
      prev_succ hp0 h1]
  · rw [sigma_ge (show p * p + p * p ≤ k by omega)] at hk'
    rw [hg _ hkn, crotF_ge _ (show p * p + p * p ≤ k by omega), hS _ hkn,
      sigma_ge (show p * p + p * p ≤ k by omega), hk',
      crotF_ge _ (show p * p + p * p ≤ j by omega)]

/-- `B_c^{Σ^t} = crot(𝟙_{[t, t+p-1]})` -/
lemma acts_Bc_conj (t : ℕ) (ht : t < p) :
    ActsAs (((PSigma p).eval (xyv n (hn1 hp hn)) ^ t)⁻¹ * ((PBc p).eval (xyv n (hn1 hp hn))) *
      (PSigma p).eval (xyv n (hn1 hp hn)) ^ t) (crotF p (win p t)) := by
  have hp0 := p_pos' hp
  set S := (PSigma p).eval (xyv n (hn1 hp hn))
  set B := (PBc p).eval (xyv n (hn1 hp hn))
  have key : ∀ t, t < p → ActsAs ((S ^ t)⁻¹ * B * S ^ t) (crotF p (win p t)) := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [pow_zero, inv_one, one_mul, mul_one]
      refine (acts_Bc hp hn).congr ?_
      intro j _
      apply crotF_congr hp0
      intro c _
      unfold indLow win
      split_ifs <;> omega
    | succ t ih =>
      intro ht
      have e : (S ^ (t + 1))⁻¹ * B * S ^ (t + 1) = S⁻¹ * ((S ^ t)⁻¹ * B * S ^ t) * S := by
        rw [pow_succ]; group
      rw [e]
      refine (acts_conj_Sigma hp hn _ (ih (by omega)) (acts_Sigma hp hn)).congr ?_
      intro j _
      apply crotF_congr hp0
      intro c hc
      rw [win_prev hp0 (by omega) hc]
  exact key t ht

/-- (b) `Z_c = crot(τ)` -/
lemma acts_Zc : ActsAs ((PZc p).eval (xyv n (hn1 hp hn))) (crotF p (tau p)) := by
  have hp0 := p_pos' hp
  have hpp := pp_ge hp
  rw [PZc, eval_Tel _ _ _ (by omega)]
  refine (actsAs_prod_crotF (n := n) hp0 (by omega) p _ (fun t c => win p t c)
    (fun t ht => acts_Bc_conj hp hn t ht)).congr ?_
  intro j _
  apply crotF_congr hp0
  intro c hc
  rw [sumTo_win_eq_tau p c hc]

/-- (b) `B_c' = crot(𝟙_{[p,2p-1]})` -/
lemma acts_Bc' : ActsAs ((PBc' p).eval (xyv n (hn1 hp hn))) (crotF p (indHigh p)) := by
  have hp0 := p_pos' hp
  have hpp := pp_ge hp
  simp only [PBc', eval_conj]
  rw [eval_Yp hp hn]
  refine ((acts_Bc hp hn).shift (p * p) (by omega) (by
    intro j h1 h2
    exact crotF_fix_G1 hp0 _ (fun c hc => by unfold indLow; rw [if_neg (by omega),
      Nat.zero_mod]) (by omega))).congr ?_
  intro j _
  exact crotF_shift_q hp0 j

lemma acts_Bc_inv : ActsAs ((PBc p).eval (xyv n (hn1 hp hn)))⁻¹
    (crotF p (fun c => if c < p then p - 1 else 0)) := by
  have hp0 := p_pos' hp
  have hpp := pp_ge hp
  refine (acts_Bc hp hn).inv (fun j hj => ?_) (fun j hj => ?_)
  · by_cases h : j < p * p + p * p
    · have := crotF_lt hp0 (fun c => if c < p then p - 1 else 0) h; omega
    · rw [crotF_ge _ (by omega)]; exact hj
  · rw [crotF_comp hp0]
    rw [crotF_congr hp0 (m' := fun _ => 0) (fun c _ => by
      show ((if c < p then p - 1 else 0) + indLow p c) % p = 0 % p
      unfold indLow
      split_ifs with h
      · rw [show p - 1 + 1 = p by omega, Nat.mod_self, Nat.zero_mod]
      · rfl) j]
    by_cases h : j < p * p + p * p
    · obtain ⟨h1, h2, h3⟩ := dpt_colOf_rowOf hp0 h
      rw [← h3, crotF_dpt _ h1 h2, Nat.add_zero, Nat.mod_eq_of_lt h2]
    · rw [crotF_ge _ (by omega)]

/-- (c) `U = crot(ν)` -/
lemma acts_U : ActsAs ((WU p).eval (xyv n (hn1 hp hn))) (crotF p (nuF p)) := by
  have hp0 := p_pos' hp
  simp only [WU, eval_mul, eval_inv]
  refine (((acts_Zc hp hn).mul (acts_Bc_inv hp hn)).mul (acts_Bc' hp hn)).congr ?_
  intro j _
  rw [crotF_comp hp0, crotF_comp hp0]
  apply crotF_congr hp0
  intro c hc
  rw [← Nat.add_assoc]
  exact L_amounts hp0 hc

/-- `ρ_q^k` -/
lemma acts_rhoq_pow (k : ℕ) :
    ActsAs (((rhoPE (p * p)).eval (xyv n (hn1 hp hn))) ^ k) (cycPowF (p * p) k) := by
  have hpp := pp_ge hp
  have hq : 0 < p * p := by omega
  induction k with
  | zero => intro j _; rw [pow_zero, nv_one, cycPowF_zero]
  | succ k ih =>
    intro j hj
    rw [nv_pow_succ, ih j hj, acts_rhoL hp hn (p * p) (by omega) (by omega) _
      (by unfold cycPowF; split_ifs with h
          · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hq) (by omega)
          · exact hj), cycPowF_succ hq]

/-- (c) `T = crot(𝟙)` -/
lemma acts_T : ActsAs ((WT p).eval (xyv n (hn1 hp hn))) (crotF p (fun _ => 1)) := by
  have hp0 := p_pos' hp
  have hpp := pp_ge hp
  simp only [WT, eval_mul, eval_conj, eval_pow, zpow_natCast]
  rw [eval_Yp hp hn]
  have h1 := acts_rhoq_pow hp hn p
  have h2 := h1.shift (p * p) (by omega) (by
    intro j h1 h2; unfold cycPowF; rw [if_neg (by omega)])
  refine (h1.mul h2).congr ?_
  intro j _
  exact T_formula hp0 j

/-- (d) `X_0 = (0, ⋆, ∞)` -/
lemma acts_X0 : ActsAs ((WX0 p).eval (xyv n (hn1 hp hn)))
    (fun j => if j = 0 then 2 * (p * p) else if j = 2 * (p * p) then 2 * (p * p) + 1
      else if j = 2 * (p * p) + 1 then 0 else j) := by
  have hpp := pp_ge hp
  simp only [WX0, eval_mul]
  refine ((acts_sig hp hn (2 * (p * p)) (by omega) (by omega)).mul
    (acts_sig hp hn (2 * (p * p) + 1) (by omega) (by omega))).congr ?_
  intro j _
  unfold trF
  split_ifs <;> omega

/-- (d) `X_1 = (q, ⋆, ∞)` -/
lemma acts_X1 : ActsAs ((WX1 p).eval (xyv n (hn1 hp hn)))
    (fun j => if j = p * p then 2 * (p * p) else if j = 2 * (p * p) then 2 * (p * p) + 1
      else if j = 2 * (p * p) + 1 then p * p else j) := by
  have hpp := pp_ge hp
  simp only [WX1, eval_mul, eval_conj]
  rw [eval_Yp hp hn]
  have h := (acts_sig hp hn (p * p) (by omega) (by omega)).mul
    (acts_sig hp hn (p * p + 1) (by omega) (by omega))
  refine (h.shift (p * p) (by omega) (by
    intro j h1 h2; simp only [trF]; split_ifs <;> omega)).congr ?_
  intro j _
  simp only [shF, trF]
  split_ifs <;> omega

/-- (d) `Q = (⋆, ∞)` -/
lemma eval_Q : (WQ p).eval (xyv n (hn1 hp hn)) = tr n (2 * (p * p)) (2 * (p * p) + 1) := by
  have hpp := pp_ge hp
  simp only [WQ, eval_conj]
  rw [eval_Yp hp hn]
  exact xconj (hn1 hp hn) (2 * (p * p)) (by omega)

end values

end SnPres
