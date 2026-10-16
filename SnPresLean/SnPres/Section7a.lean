/-
Section 7, part 1: Lemma 7.1, and the embeddings `S_m → S_n` onto `Sym([a, a+m-1])`.
-/
import SnPres.Section6d
import Mathlib.Tactic.IntervalCases

namespace SnPres

open PE

/-! ### Lemma 7.1 -/

/-- **Lemma 7.1.** For every `n ≥ 245` there is a prime `p ≥ 11` with `(n+3)/2 ≤ N ≤ n - 1`,
`N = 2p² + 2`. -/
theorem lemma_7_1 (n : ℕ) (hn : 245 ≤ n) :
    ∃ p, p.Prime ∧ 11 ≤ p ∧ n + 3 ≤ 2 * (2 * (p * p) + 2) ∧ 2 * (p * p) + 2 ≤ n - 1 := by
  classical
  let P : ℕ → Prop := fun p => p.Prime ∧ 2 * (p * p) + 3 ≤ n
  have h11 : P 11 := ⟨by decide, by omega⟩
  obtain ⟨p, hpdef⟩ : ∃ p, p = Nat.findGreatest P n := ⟨_, rfl⟩
  have hp : P p := hpdef ▸ Nat.findGreatest_spec (by omega : 11 ≤ n) h11
  have hp11 : 11 ≤ p := hpdef ▸ Nat.le_findGreatest (by omega : 11 ≤ n) h11
  have hmax : ∀ q, p < q → q ≤ n → ¬ P q := fun q h1 h2 => by
    rw [hpdef] at h1; exact Nat.findGreatest_is_greatest h1 h2
  obtain ⟨hpp, hpn⟩ := hp
  -- a prime `q > p` with `q² ≤ 2p² - 1`
  obtain ⟨q, hq, hpq, hq2⟩ : ∃ q, q.Prime ∧ p < q ∧ q * q + 1 ≤ 2 * (p * p) := by
    by_cases h25 : 25 ≤ p
    · -- Nagura: a prime in `(p, 6p/5)`
      obtain ⟨q, hq, h1, h2⟩ := Classical.nagura p h25
      refine ⟨q, hq, h1, ?_⟩
      have h2' : 5 * q + 1 ≤ 6 * p := h2
      have h3 : (5 * q + 1) * (5 * q + 1) ≤ (6 * p) * (6 * p) := Nat.mul_le_mul h2' h2'
      nlinarith
    · -- `p ∈ {11, 13, 17, 19, 23}`: checked directly
      have hp24 : p ≤ 24 := by omega
      rcases (show p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 by
        interval_cases p <;> first | omega | exact absurd hpp (by decide)) with
        rfl | rfl | rfl | rfl | rfl
      · exact ⟨13, by decide, by norm_num, by norm_num⟩
      · exact ⟨17, by decide, by norm_num, by norm_num⟩
      · exact ⟨19, by decide, by norm_num, by norm_num⟩
      · exact ⟨23, by decide, by norm_num, by norm_num⟩
      · exact ⟨29, by decide, by norm_num, by norm_num⟩
  have hqn : q ≤ n := by nlinarith
  have hlt : n < 2 * (q * q) + 3 := by
    by_contra hc
    exact hmax q hpq hqn ⟨hq, by omega⟩
  exact ⟨p, hpp, hp11, by omega, by omega⟩

/-! ### Embeddings `S_m → S_n` -/

section emb
variable {m n a : ℕ}

/-- `g ∈ S_m` acting on `[a, a+m)` -/
def embF (m a : ℕ) (g : Sym m) (i : ℕ) : ℕ := if a ≤ i ∧ i < a + m then nv g (i - a) + a else i

lemma embF_lt (g : Sym m) (h : a + m ≤ n) {i : ℕ} (hi : i < n) : embF m a g i < n := by
  unfold embF
  split_ifs with h1
  · have := nv_lt g (show i - a < m by omega); omega
  · exact hi

lemma embF_inv (g : Sym m) (i : ℕ) : embF m a g⁻¹ (embF m a g i) = i := by
  unfold embF
  by_cases h1 : a ≤ i ∧ i < a + m
  · have := nv_lt g (show i - a < m by omega)
    rw [if_pos h1, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel, nv_inv_nv]; omega
  · rw [if_neg h1, if_neg h1]

/-- the underlying permutation of the embedding -/
def embRaw (m n a : ℕ) (h : a + m ≤ n) (g : Sym m) : Sym n :=
  ofFun n (embF m a g) (embF m a g⁻¹) (fun _ hi => embF_lt g h hi)
    (fun _ hi => embF_lt g⁻¹ h hi) (fun i _ => embF_inv (a := a) g i)
    (fun i _ => by have := embF_inv (a := a) g⁻¹ i; rwa [inv_inv] at this)

lemma nv_embRaw (h : a + m ≤ n) (g : Sym m) {i : ℕ} (hi : i < n) :
    nv (embRaw m n a h g) i = embF m a g i := nv_ofFun hi

/-- The embedding `S_m → S_n` onto `Sym([a, a+m-1])` (for `a + m ≤ n`). -/
def embAt (m n a : ℕ) (h : a + m ≤ n) : Sym m →* Sym n where
  toFun := embRaw m n a h
  map_one' := by
    apply sym_ext; intro i hi
    rw [nv_embRaw h _ hi, nv_one]
    unfold embF; split_ifs <;> simp; omega
  map_mul' g g' := by
    apply sym_ext; intro i hi
    rw [nv_embRaw h _ hi, nv_mul, nv_embRaw h _ hi, nv_embRaw h _ (embF_lt g h hi)]
    unfold embF
    by_cases h1 : a ≤ i ∧ i < a + m
    · have := nv_lt g (show i - a < m by omega)
      rw [if_pos h1, if_pos h1, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel, nv_mul]
    · rw [if_neg h1, if_neg h1, if_neg h1]

lemma nv_embAt (h : a + m ≤ n) (g : Sym m) (i : ℕ) : nv (embAt m n a h g) i = embF m a g i := by
  by_cases hi : i < n
  · exact nv_embRaw h g hi
  · rw [nv_of_ge _ (by omega)]
    unfold embF; rw [if_neg (by omega)]

lemma embAt_injective (h : a + m ≤ n) : Function.Injective (embAt m n a h) := by
  intro g g' hgg
  apply sym_ext
  intro i hi
  have := congrArg (fun x => nv x (i + a)) hgg
  simp only [nv_embAt] at this
  unfold embF at this
  rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel] at this
  omega

lemma embAt_tr (h : a + m ≤ n) {i j : ℕ} (hi : i < m) (hj : j < m) :
    embAt m n a h (tr m i j) = tr n (i + a) (j + a) := by
  apply sym_ext; intro k hk
  rw [nv_embAt, nv_tr (by omega) (by omega)]
  unfold embF
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;>
    (try rw [nv_tr hi hj] at *) <;> (try rw [nv_tr hi hj]) <;> (try split_ifs) <;> omega

lemma embAt_xs (h : a + m ≤ n) (hm : 1 < m) :
    embAt m n a h (xs m hm) = tr n a (a + 1) := by
  rw [xs_eq_tr, embAt_tr h (by omega) hm, Nat.zero_add, Nat.add_comm 1 a]

/-- conjugating by `y^r` moves `Sym([0, m-1])` to `Sym([r, r+m-1])` -/
lemma conj_ys_embAt (g : Sym m) (r : ℕ) (hm : 1 ≤ m) (h : r + m ≤ n) :
    (ys n ^ r)⁻¹ * embAt m n 0 (by omega) g * ys n ^ r = embAt m n r h g := by
  apply sym_ext; intro i hi
  rw [nv_shift _ r (by omega) (fun j h1 h2 => by
      rw [nv_embAt]; unfold embF; rw [if_neg (by omega)]) i hi, nv_embAt, nv_embAt]
  unfold embF
  by_cases h1 : i < r
  · rw [if_pos h1, if_neg (by omega)]
  · rw [if_neg h1]
    by_cases h2 : i - r < m
    · rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩, Nat.sub_zero,
        Nat.add_zero]
    · rw [if_neg (by omega), if_neg (by omega)]; omega

/-- composing embeddings -/
lemma embAt_comp {k N b : ℕ} (h1 : a + N ≤ n) (h2 : b + k ≤ N) (h3 : (a + b) + k ≤ n)
    (g : Sym k) : embAt N n a h1 (embAt k N b h2 g) = embAt k n (a + b) h3 g := by
  apply sym_ext; intro i hi
  rw [nv_embAt, nv_embAt]
  unfold embF
  by_cases hA : a ≤ i ∧ i < a + N
  · rw [if_pos hA, nv_embAt]
    unfold embF
    by_cases hB : b ≤ i - a ∧ i - a < b + k
    · rw [if_pos hB, if_pos ⟨by omega, by omega⟩, show i - a - b = i - (a + b) by omega]
      omega
    · rw [if_neg hB, if_neg (by omega)]; omega
  · rw [if_neg hA, if_neg (by omega)]

/-- `(0, 1, …, m-1)` -/
lemma ys_two : ys 2 = xs 2 (by norm_num) := by
  apply sym_ext; intro i hi
  rw [nv_ys hi, nv_xs]
  interval_cases i <;> simp

end emb

/-! ### Values of `ρ_m` and of conjugates by powers of `y` -/

section values
variable {N : ℕ}

/-- `ρ_m = (0, 1, …, m-1)` is `y` of `S_m`, embedded -/
lemma eval_rho_embAt (hN : 1 < N) {m : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N) :
    (rhoPE m).eval (xyv N hN) = embAt m N 0 (by omega) (ys m) := by
  apply sym_ext; intro j hj
  rw [nv_rho hN m hm hmN, nv_embAt]
  unfold embF
  by_cases h1 : j < m
  · rw [if_pos (show 0 ≤ j ∧ j < 0 + m from ⟨by omega, by omega⟩), Nat.sub_zero, Nat.add_zero,
      nv_ys h1]
    split_ifs <;> omega
  · rw [if_neg (show ¬ (0 ≤ j ∧ j < 0 + m) by omega), if_neg (show ¬ (j + 1 < m) by omega),
      if_neg (show ¬ (j + 1 = m) by omega)]

/-- `x = (0,1)` is `x` of `S_m`, embedded -/
lemma xs_embAt (hN : 1 < N) {m : ℕ} (hm : 1 < m) (hmN : m ≤ N) :
    xs N hN = embAt m N 0 (by omega) (xs m hm) := by
  rw [embAt_xs _ hm, Nat.zero_add, xs_eq_tr]

end values

end SnPres
