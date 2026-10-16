/-
Setup 4.1: the two `p × p` grids `G_0 = [0, q-1]`, `G_1 = [q, 2q-1]`, the bijections
`ι₀ : 𝔽_p² → G_0`, `ι₁ : 𝔽_p² → G_1`, and the injective homomorphism `θ : ASL(2,p) → S_n`.
We also identify `θ` of the elementary transvections and translations with the explicit
rotations `rot`, `crot` of `NatArith`.
-/
import SnPres.Section3
import SnPres.Affine
import SnPres.NatArith

namespace SnPres

open SL2 ASL2

variable {p : ℕ} [NeZero p]

/-- `ι₀(a, b) = ā p + b̄`. -/
def iota0 (v : Vec p) : ℕ := v.1.val * p + v.2.val
/-- `ι₁(a, b) = q + ā p + \overline{-b}`. -/
def iota1 (v : Vec p) : ℕ := p * p + v.1.val * p + (-v.2).val

/-- decoding a point of `G_0` -/
def dec0 (i : ℕ) : Vec p := (((i / p : ℕ) : ZMod p), ((i % p : ℕ) : ZMod p))
/-- decoding a point of `G_1` -/
def dec1 (i : ℕ) : Vec p :=
  ((((i - p * p) / p : ℕ) : ZMod p), -(((i - p * p) % p : ℕ) : ZMod p))

lemma p_pos : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)

lemma iota0_lt (v : Vec p) : iota0 v < p * p := rc_lt (ZMod.val_lt _) (ZMod.val_lt _)

lemma iota1_ge (v : Vec p) : p * p ≤ iota1 v := by unfold iota1; omega

lemma iota1_lt (v : Vec p) : iota1 v < p * p + p * p := by
  have := rc_lt (p := p) (ZMod.val_lt v.1) (ZMod.val_lt (-v.2))
  unfold iota1; omega

lemma dec0_iota0 (v : Vec p) : dec0 (iota0 v) = v := by
  unfold dec0 iota0
  rw [rc_div (ZMod.val_lt _), rc_mod (ZMod.val_lt _), ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val]

lemma iota0_dec0 {i : ℕ} (hi : i < p * p) : iota0 (dec0 (p := p) i) = i := by
  unfold dec0 iota0
  have h1 : i / p < p := (Nat.div_lt_iff_lt_mul p_pos).mpr hi
  have h2 : i % p < p := Nat.mod_lt _ p_pos
  simp only
  rw [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2, Nat.div_add_mod']

lemma dec1_iota1 (v : Vec p) : dec1 (iota1 v) = v := by
  unfold dec1 iota1
  rw [show p * p + v.1.val * p + (-v.2).val - p * p = v.1.val * p + (-v.2).val by omega,
    rc_div (ZMod.val_lt _), rc_mod (ZMod.val_lt _), ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    neg_neg]

lemma iota1_dec1 {i : ℕ} (hi1 : p * p ≤ i) (hi2 : i < p * p + p * p) :
    iota1 (dec1 (p := p) i) = i := by
  unfold dec1 iota1
  have h1 : (i - p * p) / p < p := (Nat.div_lt_iff_lt_mul p_pos).mpr (by omega)
  have h2 : (i - p * p) % p < p := Nat.mod_lt _ p_pos
  simp only
  rw [neg_neg, ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2]
  have := Nat.div_add_mod' (i - p * p) p
  omega

/-- `θ(α)` on natural numbers: `ι_j(v) ↦ ι_j(v^α)`, the identity on `[2q, ∞)`. -/
def thetaF (α : ASL2 p) (i : ℕ) : ℕ :=
  if i < p * p then iota0 (ASL2.act (dec0 i) α)
  else if i < p * p + p * p then iota1 (ASL2.act (dec1 i) α)
  else i

lemma thetaF_iota0 (α : ASL2 p) (v : Vec p) : thetaF α (iota0 v) = iota0 (ASL2.act v α) := by
  unfold thetaF; rw [if_pos (iota0_lt v), dec0_iota0]

lemma thetaF_iota1 (α : ASL2 p) (v : Vec p) : thetaF α (iota1 v) = iota1 (ASL2.act v α) := by
  unfold thetaF; rw [if_neg (by have := iota1_ge v; omega), if_pos (iota1_lt v), dec1_iota1]

lemma thetaF_ge (α : ASL2 p) {i : ℕ} (hi : p * p + p * p ≤ i) : thetaF α i = i := by
  unfold thetaF; rw [if_neg (by omega), if_neg (by omega)]

/-- every point of `[0, 2q)` is `ι₀(v)` or `ι₁(v)` -/
lemma cases_point {i : ℕ} (hi : i < p * p + p * p) :
    (∃ v : Vec p, i = iota0 v) ∨ (∃ v : Vec p, i = iota1 v) := by
  by_cases h : i < p * p
  · exact Or.inl ⟨dec0 i, (iota0_dec0 h).symm⟩
  · exact Or.inr ⟨dec1 i, (iota1_dec1 (by omega) hi).symm⟩

lemma thetaF_mul (α β : ASL2 p) (i : ℕ) : thetaF (α * β) i = thetaF β (thetaF α i) := by
  by_cases hi : i < p * p + p * p
  · rcases cases_point hi with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · rw [thetaF_iota0, thetaF_iota0, thetaF_iota0, ASL2.act_mul]
    · rw [thetaF_iota1, thetaF_iota1, thetaF_iota1, ASL2.act_mul]
  · rw [thetaF_ge α (show p * p + p * p ≤ i by omega), thetaF_ge β (show p * p + p * p ≤ i by omega),
      thetaF_ge (α * β) (show p * p + p * p ≤ i by omega)]

lemma thetaF_one (i : ℕ) : thetaF (1 : ASL2 p) i = i := by
  by_cases hi : i < p * p + p * p
  · rcases cases_point hi with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · rw [thetaF_iota0, ASL2.act_one]
    · rw [thetaF_iota1, ASL2.act_one]
  · rw [thetaF_ge _ (by omega)]

lemma thetaF_lt (α : ASL2 p) {n i : ℕ} (hn : p * p + p * p ≤ n) (hi : i < n) :
    thetaF α i < n := by
  by_cases h : i < p * p + p * p
  · rcases cases_point h with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · rw [thetaF_iota0]; have := iota0_lt (ASL2.act v α); omega
    · rw [thetaF_iota1]; have := iota1_lt (ASL2.act v α); omega
  · rw [thetaF_ge α (show p * p + p * p ≤ i by omega)]; exact hi

lemma thetaF_inv_thetaF (α : ASL2 p) (i : ℕ) : thetaF α⁻¹ (thetaF α i) = i := by
  rw [← thetaF_mul, mul_inv_cancel, thetaF_one]

/-- `θ : ASL(2,p) → S_n` (Setup 4.1), for `n ≥ 2q`. -/
def theta (n : ℕ) (hn : p * p + p * p ≤ n) : ASL2 p →* Sym n where
  toFun α := ofFun n (thetaF α) (thetaF α⁻¹) (fun i hi => thetaF_lt α hn hi)
    (fun i hi => thetaF_lt α⁻¹ hn hi) (fun i _ => thetaF_inv_thetaF α i)
    (fun i _ => by rw [← thetaF_mul, inv_mul_cancel, thetaF_one])
  map_one' := by
    apply sym_ext; intro i hi
    rw [nv_ofFun hi, thetaF_one, nv_one]
  map_mul' α β := by
    apply sym_ext; intro i hi
    rw [nv_ofFun hi, nv_mul, nv_ofFun hi, nv_ofFun (thetaF_lt α hn hi), thetaF_mul]

lemma nv_theta {n : ℕ} (hn : p * p + p * p ≤ n) (α : ASL2 p) {i : ℕ} (hi : i < n) :
    nv (theta n hn α) i = thetaF α i := by
  unfold theta
  dsimp only [MonoidHom.coe_mk, OneHom.coe_mk]
  exact nv_ofFun hi

lemma nv_theta' {n : ℕ} (hn : p * p + p * p ≤ n) (α : ASL2 p) (i : ℕ) :
    nv (theta n hn α) i = thetaF α i := by
  by_cases hi : i < n
  · exact nv_theta hn α hi
  · rw [nv_of_ge _ (show n ≤ i by omega), thetaF_ge α (show p * p + p * p ≤ i by omega)]

lemma theta_injective {n : ℕ} (hn : p * p + p * p ≤ n) : Function.Injective (theta n hn) := by
  intro α β h
  have key : ∀ v : Vec p, ASL2.act v α = ASL2.act v β := by
    intro v
    have h1 := congrArg (fun g => nv g (iota0 v)) h
    simp only at h1
    rw [nv_theta hn _ (by have := iota0_lt v; omega), nv_theta hn _ (by have := iota0_lt v; omega),
      thetaF_iota0, thetaF_iota0] at h1
    have := congrArg (dec0 (p := p)) h1
    rwa [dec0_iota0, dec0_iota0] at this
  have hw : α.w = β.w := by
    have := key 0
    simpa [ASL2.act] using this
  have hM : α.M = β.M := by
    have h1 := key (1, 0)
    have h2 := key (0, 1)
    simp only [ASL2.act, hw] at h1 h2
    have e1 := congrArg Prod.fst h1
    have e2 := congrArg Prod.snd h1
    have e3 := congrArg Prod.fst h2
    have e4 := congrArg Prod.snd h2
    simp at e1 e2 e3 e4
    ext <;> assumption
  exact ASL2.ext hM hw

/-! ### `θ` of the special elements, as explicit rotations -/

/-- casting `ℕ`-subtraction modulo `p` -/
lemma val_sub_cast {c a : ℕ} (hc : c < p) (ha : a < p) :
    ((c : ZMod p) - (a : ZMod p)).val = (c + (p - a)) % p := by
  have : ((c : ZMod p) - (a : ZMod p)) = ((c + (p - a) : ℕ) : ZMod p) := by
    rw [Nat.cast_add, Nat.cast_sub (by omega), ZMod.natCast_self]; ring
  rw [this, ZMod.val_natCast]

/-- `θ(α_{M_L,0}) = rot(ν)`. -/
lemma thetaF_ML (i : ℕ) : thetaF (ASL2.lin (SL2.ML : SL2 p)) i = rotF p (nuF p) i := by
  by_cases hi : i < p * p + p * p
  · obtain ⟨r, c, hr, hc, rfl⟩ := below2q p i p_pos hi
    by_cases hrp : r < p
    · have e : r * p + c = iota0 ((r : ZMod p), (c : ZMod p)) := by
        unfold iota0; simp only; rw [ZMod.val_natCast_of_lt hrp, ZMod.val_natCast_of_lt hc]
      rw [rotF_rc _ hr hc, e, thetaF_iota0]
      unfold iota0 nuF
      simp only [ASL2.act_lin, SL2.vecMul, SL2.ML, mul_one, mul_zero, add_zero, zero_add]
      rw [if_pos hrp, ZMod.val_natCast_of_lt hrp, ZMod.val_add, ZMod.val_natCast_of_lt hrp,
        ZMod.val_natCast_of_lt hc, Nat.add_comm r c]
    · obtain ⟨a, rfl⟩ : ∃ a, r = p + a := ⟨r - p, by omega⟩
      have ha : a < p := by omega
      have e : (p + a) * p + c = iota1 ((a : ZMod p), -(c : ZMod p)) := by
        unfold iota1; simp only; rw [neg_neg, ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hc,
          Nat.add_mul]
      rw [rotF_rc _ hr hc, e, thetaF_iota1]
      unfold iota1 nuF
      simp only [ASL2.act_lin, SL2.vecMul, SL2.ML, mul_one, mul_zero, add_zero, zero_add]
      rw [if_neg (by omega), ZMod.val_natCast_of_lt ha,
        show -((a : ZMod p) + -(c : ZMod p)) = (c : ZMod p) - (a : ZMod p) by ring,
        val_sub_cast hc ha, show 2 * p - (p + a) = p - a by omega, Nat.add_mul]
  · rw [thetaF_ge _ (by omega), rotF_ge _ (by omega)]

/-- `θ(α_{M_U,0}) = crot(ν)`. -/
lemma thetaF_MU (i : ℕ) : thetaF (ASL2.lin (SL2.MU : SL2 p)) i = crotF p (nuF p) i := by
  by_cases hi : i < p * p + p * p
  · obtain ⟨h1, h2, h3⟩ := dpt_colOf_rowOf p_pos hi
    generalize colOf p i = c at h1 h3
    generalize rowOf p i = r at h2 h3
    subst h3
    rw [crotF_dpt _ h1 h2]
    by_cases hcp : c < p
    · have hd : ∀ k, k < p → dpt p c k = iota0 ((k : ZMod p), (c : ZMod p)) := by
        intro k hk
        unfold dpt iota0; rw [if_pos hcp]; simp only
        rw [ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hcp]
      rw [hd r h2, thetaF_iota0, hd _ (Nat.mod_lt _ p_pos)]
      congr 1
      simp only [ASL2.act_lin, SL2.vecMul, SL2.MU, mul_one, mul_zero, add_zero, zero_add]
      unfold nuF; rw [if_pos hcp]
      ext
      · simp only; rw [ZMod.natCast_mod]; push_cast; ring
      · rfl
    · obtain ⟨c', rfl⟩ : ∃ c', c = p + c' := ⟨c - p, by omega⟩
      have hc' : c' < p := by omega
      have hd : ∀ k, k < p → dpt p (p + c') k = iota1 ((k : ZMod p), -(c' : ZMod p)) := by
        intro k hk
        unfold dpt iota1; rw [if_neg (by omega)]; simp only
        rw [neg_neg, ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hc']; omega
      rw [hd r h2, thetaF_iota1, hd _ (Nat.mod_lt _ p_pos)]
      congr 1
      simp only [ASL2.act_lin, SL2.vecMul, SL2.MU, mul_one, mul_zero, add_zero, zero_add]
      unfold nuF; rw [if_neg (by omega)]
      ext
      · simp only
        rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (by omega)]
        push_cast
        linear_combination (-1 : ZMod p) * ZMod.natCast_self p
      · rfl
  · rw [thetaF_ge _ (by omega), crotF_ge _ (by omega)]

/-- `θ(t_{e₁}) = crot(𝟙)`. -/
lemma thetaF_te1 (i : ℕ) : thetaF (ASL2.tr ((1, 0) : Vec p)) i = crotF p (fun _ => 1) i := by
  by_cases hi : i < p * p + p * p
  · obtain ⟨h1, h2, h3⟩ := dpt_colOf_rowOf p_pos hi
    generalize colOf p i = c at h1 h3
    generalize rowOf p i = r at h2 h3
    subst h3
    rw [crotF_dpt _ h1 h2]
    have hk : (r + 1) % p < p := Nat.mod_lt _ p_pos
    by_cases hcp : c < p
    · have hd : ∀ k, k < p → dpt p c k = iota0 ((k : ZMod p), (c : ZMod p)) := by
        intro k hk
        unfold dpt iota0; rw [if_pos hcp]; simp only
        rw [ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hcp]
      rw [hd r h2, thetaF_iota0, hd _ hk]
      congr 1
      simp only [ASL2.act_tr]
      ext
      · simp only [Prod.fst_add]; rw [ZMod.natCast_mod]; push_cast; ring
      · simp
    · obtain ⟨c', rfl⟩ : ∃ c', c = p + c' := ⟨c - p, by omega⟩
      have hc' : c' < p := by omega
      have hd : ∀ k, k < p → dpt p (p + c') k = iota1 ((k : ZMod p), -(c' : ZMod p)) := by
        intro k hk
        unfold dpt iota1; rw [if_neg (by omega)]; simp only
        rw [neg_neg, ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hc']; omega
      rw [hd r h2, thetaF_iota1, hd _ hk]
      congr 1
      simp only [ASL2.act_tr]
      ext
      · simp only [Prod.fst_add]; rw [ZMod.natCast_mod]; push_cast; ring
      · simp
  · rw [thetaF_ge _ (by omega), crotF_ge _ (by omega)]

/-- the rotation amounts of `E = θ(t_{e₂})` -/
def epsF (p r : ℕ) : ℕ := if r < p then 1 else p - 1

/-- `θ(t_{e₂}) = rot(ε)`: positions in the rows of `G_0` move by `+1`, in `G_1` by `-1`. -/
lemma thetaF_te2 (i : ℕ) : thetaF (ASL2.tr ((0, 1) : Vec p)) i = rotF p (epsF p) i := by
  by_cases hi : i < p * p + p * p
  · obtain ⟨r, c, hr, hc, rfl⟩ := below2q p i p_pos hi
    rw [rotF_rc _ hr hc]
    by_cases hrp : r < p
    · have e : ∀ c', c' < p → r * p + c' = iota0 ((r : ZMod p), (c' : ZMod p)) := by
        intro c' hc'
        unfold iota0; simp only; rw [ZMod.val_natCast_of_lt hrp, ZMod.val_natCast_of_lt hc']
      rw [e c hc, thetaF_iota0, e _ (Nat.mod_lt _ p_pos)]
      congr 1
      simp only [ASL2.act_tr]
      unfold epsF; rw [if_pos hrp]
      ext
      · simp
      · simp only [Prod.snd_add]; rw [ZMod.natCast_mod]; push_cast; ring
    · obtain ⟨a, rfl⟩ : ∃ a, r = p + a := ⟨r - p, by omega⟩
      have ha : a < p := by omega
      have e : ∀ c', c' < p → (p + a) * p + c' = iota1 ((a : ZMod p), -(c' : ZMod p)) := by
        intro c' hc'
        unfold iota1; simp only; rw [neg_neg, ZMod.val_natCast_of_lt ha,
          ZMod.val_natCast_of_lt hc', Nat.add_mul]
      rw [e c hc, thetaF_iota1, e _ (Nat.mod_lt _ p_pos)]
      congr 1
      simp only [ASL2.act_tr]
      unfold epsF; rw [if_neg hrp]
      ext
      · simp
      · simp only [Prod.snd_add]
        rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (by omega),
          ZMod.natCast_self]
        push_cast; ring
  · rw [thetaF_ge _ (by omega), rotF_ge _ (by omega)]

end SnPres
