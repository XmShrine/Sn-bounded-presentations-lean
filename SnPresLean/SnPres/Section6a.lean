/-
Section 6, part 1: facts about transpositions and 3-cycles in `Sym n`, and Lemma 6.2.

Lemma 6.2(b) is proved in the form in which it is used: all the cycles `C_k` of `g` on `Ω` have
the same length `ℓ`; then `gπ` is the product of two cycles of length `1 + ℓ r/2`
(through `∞`, resp. `⋆`), and in particular `(gπ)^{1 + ℓ r/2} = 1`.
-/
import SnPres.Section4

namespace SnPres

open PE

section cycles
variable {n : ℕ}

/-- `g` commutes with `h` if `g` fixes every point of an `h`-invariant set `S` outside of which
`h` is the identity. -/
lemma commute_of_fixes (g h : Sym n) (S : ℕ → Prop) (hg : ∀ j, S j → nv g j = j)
    (hh : ∀ j, ¬ S j → nv h j = j) (hhS : ∀ j, S j → S (nv h j)) : Commute g h := by
  rw [commute_iff_eq]
  apply sym_ext
  intro j _
  rw [nv_mul, nv_mul]
  by_cases hj : S j
  · rw [hg j hj, hg _ (hhS j hj)]
  · have h1 : ¬ S (nv g j) := by
      intro hS
      have e : nv g j = j := nv_injective g (hg _ hS)
      exact hj (e ▸ hS)
    rw [hh j hj, hh _ h1]

lemma nv_pow_fixed (g : Sym n) {j : ℕ} (h : nv g j = j) (m : ℕ) : nv (g ^ m) j = j := by
  induction m with
  | zero => rw [pow_zero, nv_one]
  | succ m ih => rw [nv_pow_succ, ih, h]

lemma nv_pow_zero (g : Sym n) (j : ℕ) : nv (g ^ 0) j = j := by rw [pow_zero, nv_one]

lemma nv_pow_add (g : Sym n) (a b j : ℕ) : nv (g ^ (a + b)) j = nv (g ^ b) (nv (g ^ a) j) := by
  rw [pow_add, nv_mul]

lemma c3_pow_three {a b c : ℕ} (ha : a < n) (hb : b < n) (hc : c < n) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : (c3 n a b c) ^ 3 = 1 := by
  have C := nv_c3 ha hb hc hab hac hbc
  apply sym_ext; intro j _
  rw [show (3 : ℕ) = 0 + 1 + 1 + 1 from rfl, nv_pow_succ, nv_pow_succ, nv_pow_succ, nv_pow_zero,
    nv_one]
  by_cases h1 : j = a
  · subst h1; simp [C, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
  by_cases h2 : j = b
  · subst h2; simp [C, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
  by_cases h3 : j = c
  · subst h3; simp [C, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
  simp [C, h1, h2, h3]

lemma tr_sq {a b : ℕ} (ha : a < n) (hb : b < n) : (tr n a b) ^ 2 = 1 := by
  have C := nv_tr ha hb
  apply sym_ext; intro j _
  rw [pow_two, nv_mul, nv_one]
  by_cases h1 : j = a
  · subst h1; by_cases hab : j = b
    · subst hab; simp [C]
    · simp [C, hab, Ne.symm hab]
  by_cases h2 : j = b
  · subst h2; simp [C, h1, Ne.symm h1]
  simp [C, h1, h2]

/-- conjugating a 3-cycle -/
lemma c3_conj (g : Sym n) {a b c : ℕ} (ha : a < n) (hb : b < n) (hc : c < n) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    g⁻¹ * c3 n a b c * g = c3 n (nv g a) (nv g b) (nv g c) := by
  have hinj := nv_injective g
  apply sym_ext; intro j hj
  rw [nv_mul, nv_mul, nv_c3 (nv_lt g ha) (nv_lt g hb) (nv_lt g hc)
    (fun h => hab (hinj h)) (fun h => hac (hinj h)) (fun h => hbc (hinj h)),
    nv_c3 ha hb hc hab hac hbc]
  obtain ⟨k, rfl⟩ : ∃ k, j = nv g k := ⟨nv g⁻¹ j, (nv_nv_inv g j).symm⟩
  rw [nv_inv_nv]
  simp only [hinj.eq_iff]
  split_ifs <;> rfl

/-- conjugating a transposition -/
lemma tr_conj (g : Sym n) {a b : ℕ} (ha : a < n) (hb : b < n) :
    g⁻¹ * tr n a b * g = tr n (nv g a) (nv g b) := by
  have hinj := nv_injective g
  apply sym_ext; intro j hj
  rw [nv_mul, nv_mul, nv_tr (nv_lt g ha) (nv_lt g hb), nv_tr ha hb]
  obtain ⟨k, rfl⟩ : ∃ k, j = nv g k := ⟨nv g⁻¹ j, (nv_nv_inv g j).symm⟩
  rw [nv_inv_nv]
  simp only [hinj.eq_iff]
  split_ifs <;> rfl

/-- `(α,⋆,∞)(β,⋆,∞) = (α,∞)(β,⋆)` is an involution. -/
lemma c3_mul_c3_sq {a b s i : ℕ} (ha : a < n) (hb : b < n) (hs : s < n) (hi : i < n)
    (hab : a ≠ b) (has : a ≠ s) (hai : a ≠ i) (hbs : b ≠ s) (hbi : b ≠ i) (hsi : s ≠ i) :
    (c3 n a s i * c3 n b s i) ^ 2 = 1 := by
  have C1 := nv_c3 ha hs hi has hai hsi
  have C2 := nv_c3 hb hs hi hbs hbi hsi
  have T1 := nv_tr ha hi
  have T2 := nv_tr hb hs
  have e : c3 n a s i * c3 n b s i = tr n a i * tr n b s := by
    apply sym_ext; intro j _
    rw [nv_mul, nv_mul]
    by_cases h1 : j = a
    · subst h1; simp [C1, C2, T1, T2, *, Ne.symm hab, Ne.symm has, Ne.symm hai, Ne.symm hbs,
        Ne.symm hbi, Ne.symm hsi]
    by_cases h2 : j = b
    · subst h2; simp [C1, C2, T1, T2, *, Ne.symm hab, Ne.symm has, Ne.symm hai, Ne.symm hbs,
        Ne.symm hbi, Ne.symm hsi]
    by_cases h3 : j = s
    · subst h3; simp [C1, C2, T1, T2, *, Ne.symm hab, Ne.symm has, Ne.symm hai, Ne.symm hbs,
        Ne.symm hbi, Ne.symm hsi]
    by_cases h4 : j = i
    · subst h4; simp [C1, C2, T1, T2, *, Ne.symm hab, Ne.symm has, Ne.symm hai, Ne.symm hbs,
        Ne.symm hbi, Ne.symm hsi]
    simp [C1, C2, T1, T2, h1, h2, h3, h4]
  rw [e]
  apply sym_ext; intro j _
  rw [pow_two, nv_mul, nv_mul, nv_mul, nv_one]
  by_cases h1 : j = a
  · subst h1; simp [T1, T2, *, Ne.symm hab, Ne.symm has, Ne.symm hai, Ne.symm hbs,
      Ne.symm hbi, Ne.symm hsi]
  by_cases h2 : j = b
  · subst h2; simp [T1, T2, *, Ne.symm hab, Ne.symm has, Ne.symm hai, Ne.symm hbs,
      Ne.symm hbi, Ne.symm hsi]
  by_cases h3 : j = s
  · subst h3; simp [T1, T2, *, Ne.symm hab, Ne.symm has, Ne.symm hai, Ne.symm hbs,
      Ne.symm hbi, Ne.symm hsi]
  by_cases h4 : j = i
  · subst h4; simp [T1, T2, *, Ne.symm hab, Ne.symm has, Ne.symm hai, Ne.symm hbs,
      Ne.symm hbi, Ne.symm hsi]
  simp [T1, T2, h1, h2, h3, h4]

/-- `(⋆,∞)(o,⋆,∞) = (o,⋆)` is an involution. -/
lemma tr_mul_c3_sq {o s i : ℕ} (ho : o < n) (hs : s < n) (hi : i < n) (hos : o ≠ s)
    (hoi : o ≠ i) (hsi : s ≠ i) : (tr n s i * c3 n o s i) ^ 2 = 1 := by
  have C := nv_c3 ho hs hi hos hoi hsi
  have T := nv_tr hs hi
  apply sym_ext; intro j _
  rw [pow_two, nv_mul, nv_mul, nv_mul, nv_one]
  by_cases h1 : j = o
  · subst h1; simp [C, T, *, Ne.symm hos, Ne.symm hoi, Ne.symm hsi]
  by_cases h2 : j = s
  · subst h2; simp [C, T, *, Ne.symm hos, Ne.symm hoi, Ne.symm hsi]
  by_cases h3 : j = i
  · subst h3; simp [C, T, *, Ne.symm hos, Ne.symm hoi, Ne.symm hsi]
  simp [C, T, h1, h2, h3]

/-- a 3-cycle commutes with a permutation fixing its three points -/
lemma commute_c3 (g : Sym n) {a b c : ℕ} (ha : a < n) (hb : b < n) (hc : c < n) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hga : nv g a = a) (hgb : nv g b = b) (hgc : nv g c = c) :
    Commute g (c3 n a b c) := by
  apply commute_of_fixes g _ (fun j => j = a ∨ j = b ∨ j = c)
  · rintro j (rfl | rfl | rfl) <;> assumption
  · intro j hj
    rw [nv_c3 ha hb hc hab hac hbc]
    simp only [not_or] at hj
    rw [if_neg hj.1, if_neg hj.2.1, if_neg hj.2.2]
  · intro j hj
    rw [nv_c3 ha hb hc hab hac hbc]
    rcases hj with rfl | rfl | rfl
    · simp
    · simp [hab.symm]
    · simp [hac.symm, hbc.symm]

/-- a transposition commutes with a permutation fixing its two points -/
lemma commute_tr (g : Sym n) {a b : ℕ} (ha : a < n) (hb : b < n)
    (hga : nv g a = a) (hgb : nv g b = b) : Commute g (tr n a b) := by
  apply commute_of_fixes g _ (fun j => j = a ∨ j = b)
  · rintro j (rfl | rfl) <;> assumption
  · intro j hj
    rw [nv_tr ha hb]
    simp only [not_or] at hj
    rw [if_neg hj.1, if_neg hj.2]
  · intro j hj
    rw [nv_tr ha hb]
    rcases hj with rfl | rfl
    · simp
    · by_cases h : j = a
      · subst h; simp
      · simp [h]

end cycles

/-! ### Lemma 6.2 -/

section lemma62
variable {n : ℕ}

/-- `π = (ω₀,⋆,∞)(ω₁,⋆,∞)⋯(ω_{r-1},⋆,∞)` (indices from `0`). -/
def cprod (n : ℕ) (ω : ℕ → ℕ) (s i r : ℕ) : Sym n :=
  ((List.range r).map (fun k => c3 n (ω k) s i)).prod

lemma cprod_succ (ω : ℕ → ℕ) (s i r : ℕ) :
    cprod n ω s i (r + 1) = cprod n ω s i r * c3 n (ω r) s i := by
  simp [cprod, List.range_succ, List.prod_append]

lemma cprod_zero (ω : ℕ → ℕ) (s i : ℕ) : cprod n ω s i 0 = 1 := by simp [cprod]

/-- The hypotheses of Lemma 6.2: distinct points `ω₀, …, ω_{r-1}, ⋆, ∞` of `[0, n)`. -/
structure Pts (n : ℕ) (ω : ℕ → ℕ) (s i r : ℕ) : Prop where
  hω : ∀ k < r, ω k < n
  hs : s < n
  hi : i < n
  hsi : s ≠ i
  hωs : ∀ k < r, ω k ≠ s
  hωi : ∀ k < r, ω k ≠ i
  hinj : ∀ k < r, ∀ k' < r, ω k = ω k' → k = k'

lemma Pts.mono {ω : ℕ → ℕ} {s i r r' : ℕ} (P : Pts n ω s i r) (h : r' ≤ r) : Pts n ω s i r' :=
  ⟨fun k hk => P.hω k (by omega), P.hs, P.hi, P.hsi, fun k hk => P.hωs k (by omega),
    fun k hk => P.hωi k (by omega), fun k hk k' hk' => P.hinj k (by omega) k' (by omega)⟩

/-- **Lemma 6.2(a)** (indices shifted by one: the paper's `ω_i` is our `ω (i-1)`). -/
theorem lemma_6_2a {ω : ℕ → ℕ} {s i : ℕ} (r : ℕ) (hr : 2 ≤ r) (P : Pts n ω s i r) :
    (∀ k, k + 2 < r → nv (cprod n ω s i r) (ω k) = ω (k + 2)) ∧
    nv (cprod n ω s i r) (ω (r - 2)) = i ∧
    nv (cprod n ω s i r) (ω (r - 1)) = s ∧
    nv (cprod n ω s i r) s = ω 1 ∧
    nv (cprod n ω s i r) i = ω 0 ∧
    (∀ j, (∀ k < r, j ≠ ω k) → j ≠ s → j ≠ i → nv (cprod n ω s i r) j = j) := by
  induction r, hr using Nat.le_induction with
  | base =>
    have h0 := P.hω 0 (by omega)
    have h1 := P.hω 1 (by omega)
    have d01 : ω 0 ≠ ω 1 := fun h => by have := P.hinj 0 (by omega) 1 (by omega) h; omega
    have d0s := P.hωs 0 (by omega)
    have d1s := P.hωs 1 (by omega)
    have d0i := P.hωi 0 (by omega)
    have d1i := P.hωi 1 (by omega)
    have hs := P.hs
    have hi := P.hi
    have hsi := P.hsi
    have e : cprod n ω s i 2 = c3 n (ω 0) s i * c3 n (ω 1) s i := by
      rw [cprod_succ, cprod_succ, cprod_zero, one_mul]
    rw [e]
    simp only [nv_mul, nv_c3 h0 hs hi d0s d0i hsi, nv_c3 h1 hs hi d1s d1i hsi]
    refine ⟨fun k hk => by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [show (2 : ℕ) - 2 = 0 from rfl]; split_ifs <;> omega
    · simp only [show (2 : ℕ) - 1 = 1 from rfl]; split_ifs <;> omega
    · split_ifs <;> omega
    · split_ifs <;> omega
    · intro j hj hjs hji
      have hj0 := hj 0 (by omega)
      have hj1 := hj 1 (by omega)
      split_ifs <;> omega
  | succ r hr ih =>
    obtain ⟨A1, A2, A3, A4, A5, A6⟩ := ih (P.mono (by omega))
    have hr' := P.hω r (by omega)
    have drs := P.hωs r (by omega)
    have dri := P.hωi r (by omega)
    have hs := P.hs
    have hi := P.hi
    have hsi := P.hsi
    have dr : ∀ k < r, ω k ≠ ω r := fun k hk h => by
      have := P.hinj k (by omega) r (by omega) h; omega
    have C := nv_c3 hr' hs hi drs dri hsi
    rw [cprod_succ]
    simp only [nv_mul]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      by_cases hk' : k + 2 < r
      · rw [A1 k hk', C, if_neg (dr _ hk'), if_neg (P.hωs _ (by omega)),
          if_neg (P.hωi _ (by omega))]
      · have e : k = r - 2 := by omega
        rw [e, A2, C, if_neg (Ne.symm dri), if_neg (Ne.symm hsi), if_pos rfl,
          show r - 2 + 2 = r by omega]
    · rw [show r + 1 - 2 = r - 1 by omega, A3, C, if_neg (Ne.symm drs), if_pos rfl]
    · rw [show r + 1 - 1 = r by omega,
        A6 (ω r) (fun k hk => (dr k hk).symm) drs dri, C, if_pos rfl]
    · rw [A4, C, if_neg (dr 1 (by omega)), if_neg (P.hωs 1 (by omega)),
        if_neg (P.hωi 1 (by omega))]
    · rw [A5, C, if_neg (dr 0 (by omega)), if_neg (P.hωs 0 (by omega)),
        if_neg (P.hωi 0 (by omega))]
    · intro j hj hjs hji
      rw [A6 j (fun k hk => hj k (by omega)) hjs hji, C, if_neg (hj r (by omega)), if_neg hjs,
        if_neg hji]

/-- the points of the two cycles of `gπ`: `zz 0 0 = ∞`, `zz 1 0 = ⋆`, and
`zz par (1 + ℓ q + m) = g^m(ω_{2q + par})`. -/
def zz (g : Sym n) (ω : ℕ → ℕ) (s i ℓ par t : ℕ) : ℕ :=
  if t = 0 then (if par = 0 then i else s)
  else nv (g ^ ((t - 1) % ℓ)) (ω (2 * ((t - 1) / ℓ) + par))

lemma zz_zero_zero (g : Sym n) (ω : ℕ → ℕ) (s i ℓ : ℕ) : zz g ω s i ℓ 0 0 = i := by simp [zz]
lemma zz_one_zero (g : Sym n) (ω : ℕ → ℕ) (s i ℓ : ℕ) : zz g ω s i ℓ 1 0 = s := by simp [zz]
lemma zz_succ (g : Sym n) (ω : ℕ → ℕ) (s i ℓ par u : ℕ) :
    zz g ω s i ℓ par (u + 1) = nv (g ^ (u % ℓ)) (ω (2 * (u / ℓ) + par)) := by simp [zz]

lemma divmod_aux {ℓ q m : ℕ} (hm : m < ℓ) : (ℓ * q + m) / ℓ = q ∧ (ℓ * q + m) % ℓ = m :=
  (Nat.div_mod_unique (by omega)).mpr ⟨by ring, hm⟩

/-- **Lemma 6.2(b)**, for cycles of equal length `ℓ`: `gπ` maps each `zz par t` to the next
point `zz par (t+1)` of its cycle (of length `1 + ℓ r/2`), every point is on one of the two cycles,
and hence `(gπ)^{1 + ℓ r/2} = 1`. -/
theorem lemma_6_2b (g : Sym n) {ω : ℕ → ℕ} {s i r ℓ : ℕ} (hr : 2 ≤ r) (heven : r % 2 = 0)
    (hℓ : 1 ≤ ℓ) (P : Pts n ω s i r) (hgs : nv g s = s) (hgi : nv g i = i)
    (hper : ∀ k < r, nv (g ^ ℓ) (ω k) = ω k)
    (hnot : ∀ k < r, ∀ m, 0 < m → m < ℓ → ∀ k' < r, nv (g ^ m) (ω k) ≠ ω k')
    (hcover : ∀ j < n, j ≠ s → j ≠ i → ∃ k < r, ∃ m < ℓ, j = nv (g ^ m) (ω k)) :
    (∀ par, par ≤ 1 → ∀ t < 1 + ℓ * (r / 2),
      nv (g * cprod n ω s i r) (zz g ω s i ℓ par t) =
        zz g ω s i ℓ par ((t + 1) % (1 + ℓ * (r / 2)))) ∧
    (∀ j < n, ∃ par, par ≤ 1 ∧ ∃ t < 1 + ℓ * (r / 2), j = zz g ω s i ℓ par t) ∧
    (g * cprod n ω s i r) ^ (1 + ℓ * (r / 2)) = 1 := by
  obtain ⟨A1, A2, A3, A4, A5, A6⟩ := lemma_6_2a r hr P
  set h := r / 2 with hh
  have hr2 : r = 2 * h := by omega
  have h1 : 1 ≤ h := by omega
  set M := 1 + ℓ * h with hM
  have hM2 : 2 ≤ M := by
    have : ℓ * 1 ≤ ℓ * h := Nat.mul_le_mul_left ℓ h1
    omega
  set f := g * cprod n ω s i r with hf
  -- `g^m` fixes `⋆, ∞` and maps the `ω_k` away from them
  have gs : ∀ m, nv (g ^ m) s = s := nv_pow_fixed g hgs
  have gi : ∀ m, nv (g ^ m) i = i := nv_pow_fixed g hgi
  have gωs : ∀ k < r, ∀ m, nv (g ^ m) (ω k) ≠ s := fun k hk m h => by
    have := nv_injective _ (h.trans (gs m).symm); exact P.hωs k hk this
  have gωi : ∀ k < r, ∀ m, nv (g ^ m) (ω k) ≠ i := fun k hk m h => by
    have := nv_injective _ (h.trans (gi m).symm); exact P.hωi k hk this
  -- the step
  have step : ∀ par, par ≤ 1 → ∀ t < M,
      nv f (zz g ω s i ℓ par t) = zz g ω s i ℓ par ((t + 1) % M) := by
    intro par hpar t ht
    rw [hf, nv_mul]
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · rw [Nat.zero_add, Nat.mod_eq_of_lt (show 1 < M by omega),
        show zz g ω s i ℓ par 1 = nv (g ^ (0 % ℓ)) (ω (2 * (0 / ℓ) + par)) from
          zz_succ g ω s i ℓ par 0, Nat.zero_mod, Nat.zero_div, nv_pow_zero]
      rcases (show par = 0 ∨ par = 1 by omega) with rfl | rfl
      · rw [zz_zero_zero, hgi, A5]
      · rw [zz_one_zero, hgs, A4]
    · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      have hmℓ : u % ℓ < ℓ := Nat.mod_lt _ (by omega)
      have hu : u = ℓ * (u / ℓ) + u % ℓ := (Nat.div_add_mod u ℓ).symm
      obtain ⟨q, hq⟩ : ∃ q, q = u / ℓ := ⟨_, rfl⟩
      obtain ⟨m, hm⟩ : ∃ m, m = u % ℓ := ⟨_, rfl⟩
      rw [← hq, ← hm] at hu
      rw [← hm] at hmℓ
      have hqh : q < h := by
        by_contra hcon
        have : ℓ * h ≤ ℓ * q := Nat.mul_le_mul_left ℓ (by omega)
        omega
      have hk : 2 * q + par < r := by omega
      rw [zz_succ, ← hq, ← hm, ← nv_pow_succ]
      by_cases hm1 : m + 1 < ℓ
      · -- inside a cycle `C_k`
        have hfix : nv (cprod n ω s i r) (nv (g ^ (m + 1)) (ω (2 * q + par))) =
            nv (g ^ (m + 1)) (ω (2 * q + par)) :=
          A6 (nv (g ^ (m + 1)) (ω (2 * q + par)))
            (fun k' hk' => hnot _ hk (m + 1) (by omega) hm1 k' hk') (gωs _ hk _) (gωi _ hk _)
        rw [hfix]
        have hlt : u + 1 + 1 < M := by
          have : ℓ * q + ℓ ≤ ℓ * h := by
            rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left ℓ hqh
          omega
        rw [Nat.mod_eq_of_lt hlt, zz_succ, show u + 1 = ℓ * q + (m + 1) by omega,
          (divmod_aux hm1).1, (divmod_aux hm1).2]
      · -- the end of the cycle `C_k`: jump to `ω_{k+2}` (or to `∞`, `⋆`)
        have hm1' : m + 1 = ℓ := by omega
        rw [hm1', hper _ hk]
        by_cases hq1 : q + 1 < h
        · rw [A1 _ (by omega : 2 * q + par + 2 < r)]
          have hlt : u + 1 + 1 < M := by
            have : ℓ * (q + 1) < ℓ * h := Nat.mul_lt_mul_of_pos_left hq1 (by omega)
            rw [Nat.mul_succ] at this
            omega
          rw [Nat.mod_eq_of_lt hlt, zz_succ,
            show u + 1 = ℓ * (q + 1) + 0 by rw [Nat.mul_succ]; omega,
            (divmod_aux (show 0 < ℓ by omega)).1, (divmod_aux (show 0 < ℓ by omega)).2,
            nv_pow_zero]
          congr 1; ring
        · have hqe : q + 1 = h := by omega
          have hMe : u + 1 + 1 = M := by
            rw [hM, ← hqe, Nat.mul_succ]; omega
          rw [hMe, Nat.mod_self]
          rcases (show par = 0 ∨ par = 1 by omega) with rfl | rfl
          · rw [zz_zero_zero, show 2 * q + 0 = r - 2 by omega, A2]
          · rw [zz_one_zero, show 2 * q + 1 = r - 1 by omega, A3]
  -- iterating the step
  have orbit : ∀ par, par ≤ 1 → ∀ t < M, ∀ k,
      nv (f ^ k) (zz g ω s i ℓ par t) = zz g ω s i ℓ par ((t + k) % M) := by
    intro par hpar t ht k
    induction k with
    | zero => rw [nv_pow_zero, Nat.add_zero, Nat.mod_eq_of_lt ht]
    | succ k ih =>
      rw [nv_pow_succ, ih, step par hpar _ (Nat.mod_lt _ (by omega)), Nat.mod_add_mod,
        Nat.add_assoc]
  -- covering
  have cover : ∀ j < n, ∃ par, par ≤ 1 ∧ ∃ t < M, j = zz g ω s i ℓ par t := by
    intro j hj
    by_cases hji : j = i
    · exact ⟨0, by omega, 0, by omega, by rw [zz_zero_zero, hji]⟩
    by_cases hjs : j = s
    · exact ⟨1, le_rfl, 0, by omega, by rw [zz_one_zero, hjs]⟩
    obtain ⟨k, hk, m, hm, rfl⟩ := hcover j hj hjs hji
    refine ⟨k % 2, by omega, ℓ * (k / 2) + m + 1, ?_, ?_⟩
    · have : ℓ * (k / 2) + ℓ ≤ ℓ * h := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left ℓ (by omega)
      omega
    · rw [zz_succ, (divmod_aux hm).1, (divmod_aux hm).2, show 2 * (k / 2) + k % 2 = k by omega]
  refine ⟨step, cover, ?_⟩
  apply sym_ext
  intro j hj
  obtain ⟨par, hpar, t, ht, rfl⟩ := cover j hj
  rw [orbit par hpar t ht M, Nat.add_mod_right, Nat.mod_eq_of_lt ht, nv_one]

end lemma62

end SnPres
