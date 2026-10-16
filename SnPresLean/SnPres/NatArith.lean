/-
Pure arithmetic on natural numbers used to describe the permutations of Section 4
(blocks `R_r = [rp, rp+p-1]`, virtual columns `D_c`, rotations `rot`, `crot`).
This file depends only on Lean core.
-/

namespace SnPres

/-- split all `if`s in the goal -/
macro "split_all" : tactic => `(tactic| repeat' split)

/-! ### Decomposition `i = r p + c` -/

theorem rc_div {p r c : Nat} (hc : c < p) : (r * p + c) / p = r := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]

theorem rc_mod {p r c : Nat} (hc : c < p) : (r * p + c) % p = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem rc_lt {p r c R : Nat} (hr : r < R) (hc : c < p) : r * p + c < R * p := by
  have h : (r + 1) * p ≤ R * p := Nat.mul_le_mul_right _ hr
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

theorem rc_le {p r R : Nat} (hr : r ≤ R) : r * p ≤ R * p := Nat.mul_le_mul_right _ hr

theorem rc_decomp (p i : Nat) (hp : 0 < p) : ∃ r c, c < p ∧ i = r * p + c :=
  ⟨i / p, i % p, Nat.mod_lt _ hp, (Nat.div_add_mod' i p).symm⟩

/-- `2q = 2p²`, written so that `omega` sees the atom `p * p`. -/
theorem two_p_mul (p : Nat) : 2 * p * p = p * p + p * p := by
  rw [Nat.mul_assoc, Nat.two_mul]

theorem rc_lt2 {p r c : Nat} (hr : r < 2 * p) (hc : c < p) : r * p + c < p * p + p * p := by
  have := rc_lt (p := p) hr hc
  rw [two_p_mul] at this
  exact this

theorem rc_ge {p r c : Nat} (hr : R ≤ r) : R * p ≤ r * p + c := by
  have := rc_le (p := p) hr; omega

/-- The row of a point `i = r p + c` is `< R` iff `i < R p`. -/
theorem rc_lt_iff {p r c R : Nat} (hc : c < p) : r * p + c < R * p ↔ r < R := by
  constructor
  · intro h
    refine Decidable.byContradiction fun hr => ?_
    have := rc_ge (p := p) (c := c) (Nat.le_of_not_lt hr)
    omega
  · intro h; exact rc_lt h hc

/-! ### Sums `∑_{t<k} f t` -/

/-- `sumTo f k = f 0 + ⋯ + f (k-1)`. -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => sumTo f k + f k

@[simp] theorem sumTo_zero (f : Nat → Nat) : sumTo f 0 = 0 := rfl
@[simp] theorem sumTo_succ (f : Nat → Nat) (k : Nat) : sumTo f (k + 1) = sumTo f k + f k := rfl

theorem sumTo_congr {f g : Nat → Nat} {k : Nat} (h : ∀ t < k, f t = g t) :
    sumTo f k = sumTo g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sumTo_succ, sumTo_succ, ih (fun t ht => h t (by omega)), h k (by omega)]

theorem sumTo_zero_fun {f : Nat → Nat} {k : Nat} (h : ∀ t < k, f t = 0) : sumTo f k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sumTo_succ, ih (fun t ht => h t (by omega)), h k (by omega)]

/-- The window indicator `𝟙_{[t, t+p-1]}`. -/
def win (p t r : Nat) : Nat := if t ≤ r ∧ r < t + p then 1 else 0

/-- The "tent" function `τ`. -/
def tau (p r : Nat) : Nat := if r < p then r + 1 else 2 * p - 1 - r

/-- Counting the windows containing `r`. -/
theorem sumTo_win (p r k : Nat) (hk : k ≤ p) :
    sumTo (fun t => win p t r) k = if r < p then (if k ≤ r then k else r + 1) else k + p - 1 - r := by
  induction k with
  | zero => simp only [sumTo_zero]; split_all <;> omega
  | succ k ih =>
    rw [sumTo_succ, ih (by omega)]
    unfold win
    split_all <;> omega

theorem sumTo_win_eq_tau (p r : Nat) (hr : r < 2 * p) :
    sumTo (fun t => win p t r) p = tau p r := by
  rw [sumTo_win p r p (Nat.le_refl _)]
  unfold tau
  split_all <;> omega

/-! ### Rotations of the blocks -/

/-- `rot(m)`: rotate each block `R_r = [rp, rp+p-1]` (`r < 2p`) by `m r` places. -/
def rotF (p : Nat) (m : Nat → Nat) (i : Nat) : Nat :=
  if i < p * p + p * p then i / p * p + (i % p + m (i / p)) % p else i

theorem rotF_rc {p : Nat} (m : Nat → Nat) {r c : Nat} (hr : r < 2 * p) (hc : c < p) :
    rotF p m (r * p + c) = r * p + (c + m r) % p := by
  unfold rotF
  rw [if_pos (rc_lt2 hr hc), rc_div hc, rc_mod hc]

theorem rotF_ge {p : Nat} (m : Nat → Nat) {i : Nat} (h : p * p + p * p ≤ i) : rotF p m i = i := by
  unfold rotF; rw [if_neg (by omega)]

/-- every point below `2q` is `r p + c` with `r < 2p`, `c < p` -/
theorem below2q (p i : Nat) (hp : 0 < p) (hi : i < p * p + p * p) :
    ∃ r c, r < 2 * p ∧ c < p ∧ i = r * p + c := by
  obtain ⟨r, c, hc, rfl⟩ := rc_decomp p i hp
  refine ⟨r, c, ?_, hc, rfl⟩
  rw [← two_p_mul] at hi
  exact (rc_lt_iff hc).mp hi

theorem rotF_lt {p : Nat} (hp : 0 < p) (m : Nat → Nat) {i : Nat} (hi : i < p * p + p * p) :
    rotF p m i < p * p + p * p := by
  obtain ⟨r, c, hr, hc, rfl⟩ := below2q p i hp hi
  rw [rotF_rc m hr hc]
  exact rc_lt2 hr (Nat.mod_lt _ hp)

theorem rotF_comp {p : Nat} (hp : 0 < p) (m m' : Nat → Nat) (i : Nat) :
    rotF p m' (rotF p m i) = rotF p (fun r => m r + m' r) i := by
  by_cases hi : i < p * p + p * p
  · obtain ⟨r, c, hr, hc, rfl⟩ := below2q p i hp hi
    rw [rotF_rc m hr hc, rotF_rc m' hr (Nat.mod_lt _ hp), rotF_rc _ hr hc]
    congr 1
    rw [Nat.mod_add_mod, Nat.add_assoc]
  · rw [rotF_ge m (by omega), rotF_ge m' (by omega), rotF_ge _ (by omega)]

theorem rotF_congr {p : Nat} {m m' : Nat → Nat} (hp : 0 < p) (h : ∀ r < 2 * p, m r % p = m' r % p)
    (i : Nat) : rotF p m i = rotF p m' i := by
  by_cases hi : i < p * p + p * p
  · obtain ⟨r, c, hr, hc, rfl⟩ := below2q p i hp hi
    rw [rotF_rc m hr hc, rotF_rc m' hr hc, Nat.add_mod, h r hr, ← Nat.add_mod]
  · rw [rotF_ge m (by omega), rotF_ge m' (by omega)]

theorem rotF_zero {p : Nat} (hp : 0 < p) (i : Nat) : rotF p (fun _ => 0) i = i := by
  by_cases hi : i < p * p + p * p
  · obtain ⟨r, c, hr, hc, rfl⟩ := below2q p i hp hi
    rw [rotF_rc _ hr hc, Nat.add_zero, Nat.mod_eq_of_lt hc]
  · rw [rotF_ge _ (by omega)]

/-- `rot(m)` fixes every point of a block `R_r` with `m r ≡ 0`. -/
theorem rotF_fix {p : Nat} (hp : 0 < p) (m : Nat → Nat) {r c : Nat} (hr : r < 2 * p) (hc : c < p)
    (hm : m r % p = 0) : rotF p m (r * p + c) = r * p + c := by
  rw [rotF_rc m hr hc, Nat.add_mod, hm, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hc]

/-! ### Virtual columns -/

/-- `d(c, i)`: the `i`-th point of the `c`-th virtual column. -/
def dpt (p c i : Nat) : Nat := if c < p then i * p + c else p * p + i * p + (c - p)

/-- the virtual column of a point of `[0, 2q)` -/
def colOf (p j : Nat) : Nat := if j < p * p then j % p else p + (j - p * p) % p
/-- the row of a point of `[0, 2q)` -/
def rowOf (p j : Nat) : Nat := if j < p * p then j / p else (j - p * p) / p

theorem dpt_lt {p c i : Nat} (hc : c < 2 * p) (hi : i < p) : dpt p c i < p * p + p * p := by
  unfold dpt
  by_cases h : c < p
  · rw [if_pos h]; have := rc_lt (p := p) hi h; omega
  · rw [if_neg h]; have := rc_lt (p := p) hi (show c - p < p by omega); omega

theorem dpt_lt_q {p c i : Nat} (hc : c < p) (hi : i < p) : dpt p c i < p * p := by
  unfold dpt; rw [if_pos hc]; exact rc_lt hi hc

theorem dpt_ge_q {p c i : Nat} (hc : p ≤ c) : p * p ≤ dpt p c i := by
  unfold dpt; rw [if_neg (by omega)]; omega

theorem colOf_dpt {p c i : Nat} (hc : c < 2 * p) (hi : i < p) : colOf p (dpt p c i) = c := by
  unfold colOf dpt
  by_cases h1 : c < p
  · rw [if_pos h1, if_pos (rc_lt (p := p) hi h1)]
    exact rc_mod h1
  · rw [if_neg h1, if_neg (by omega)]
    rw [show p * p + i * p + (c - p) - p * p = i * p + (c - p) by omega, rc_mod (by omega)]
    omega

theorem rowOf_dpt {p c i : Nat} (hc : c < 2 * p) (hi : i < p) : rowOf p (dpt p c i) = i := by
  unfold rowOf dpt
  by_cases h1 : c < p
  · rw [if_pos h1, if_pos (rc_lt (p := p) hi h1)]
    exact rc_div h1
  · rw [if_neg h1, if_neg (by omega)]
    rw [show p * p + i * p + (c - p) - p * p = i * p + (c - p) by omega, rc_div (by omega)]

theorem dpt_colOf_rowOf {p j : Nat} (hp : 0 < p) (hj : j < p * p + p * p) :
    colOf p j < 2 * p ∧ rowOf p j < p ∧ dpt p (colOf p j) (rowOf p j) = j := by
  unfold colOf rowOf
  by_cases h : j < p * p
  · simp only [if_pos h]
    have h1 : j % p < p := Nat.mod_lt _ hp
    have h2 : j / p < p := (Nat.div_lt_iff_lt_mul hp).mpr h
    refine ⟨by omega, h2, ?_⟩
    unfold dpt; rw [if_pos h1]; exact Nat.div_add_mod' j p
  · simp only [if_neg h]
    have h1 : (j - p * p) % p < p := Nat.mod_lt _ hp
    have h2 : (j - p * p) / p < p := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
    refine ⟨by omega, h2, ?_⟩
    unfold dpt; rw [if_neg (by omega)]
    have := Nat.div_add_mod' (j - p * p) p
    omega

theorem dpt_inj {p c i c' i' : Nat} (hc : c < 2 * p) (hi : i < p) (hc' : c' < 2 * p)
    (hi' : i' < p) (h : dpt p c i = dpt p c' i') : c = c' ∧ i = i' := by
  constructor
  · rw [← colOf_dpt hc hi, h, colOf_dpt hc' hi']
  · rw [← rowOf_dpt hc hi, h, rowOf_dpt hc' hi']

/-- `crot(m)`: rotate each virtual column `D_c` downwards by `m c` places. -/
def crotF (p : Nat) (m : Nat → Nat) (j : Nat) : Nat :=
  if j < p * p + p * p then dpt p (colOf p j) ((rowOf p j + m (colOf p j)) % p) else j

theorem crotF_dpt {p : Nat} (m : Nat → Nat) {c i : Nat} (hc : c < 2 * p) (hi : i < p) :
    crotF p m (dpt p c i) = dpt p c ((i + m c) % p) := by
  unfold crotF
  rw [if_pos (dpt_lt hc hi), colOf_dpt hc hi, rowOf_dpt hc hi]

theorem crotF_ge {p : Nat} (m : Nat → Nat) {j : Nat} (h : p * p + p * p ≤ j) :
    crotF p m j = j := by
  unfold crotF; rw [if_neg (by omega)]

theorem crotF_comp {p : Nat} (hp : 0 < p) (m m' : Nat → Nat) (j : Nat) :
    crotF p m' (crotF p m j) = crotF p (fun c => m c + m' c) j := by
  by_cases hj : j < p * p + p * p
  · obtain ⟨h1, h2, h3⟩ := dpt_colOf_rowOf hp hj
    rw [← h3, crotF_dpt m h1 h2, crotF_dpt m' h1 (Nat.mod_lt _ hp), crotF_dpt _ h1 h2]
    congr 1
    rw [Nat.mod_add_mod, Nat.add_assoc]
  · rw [crotF_ge m (by omega), crotF_ge m' (by omega), crotF_ge _ (by omega)]

theorem crotF_congr {p : Nat} {m m' : Nat → Nat} (hp : 0 < p)
    (h : ∀ c < 2 * p, m c % p = m' c % p) (j : Nat) : crotF p m j = crotF p m' j := by
  by_cases hj : j < p * p + p * p
  · obtain ⟨h1, h2, h3⟩ := dpt_colOf_rowOf hp hj
    rw [← h3, crotF_dpt m h1 h2, crotF_dpt m' h1 h2, Nat.add_mod, h _ h1, ← Nat.add_mod]
  · rw [crotF_ge m (by omega), crotF_ge m' (by omega)]

theorem crotF_lt {p : Nat} (hp : 0 < p) (m : Nat → Nat) {j : Nat} (hj : j < p * p + p * p) :
    crotF p m j < p * p + p * p := by
  obtain ⟨h1, h2, h3⟩ := dpt_colOf_rowOf hp hj
  rw [← h3, crotF_dpt m h1 h2]
  exact dpt_lt h1 (Nat.mod_lt _ hp)

/-- The permutation `Σ`: `d(c, i) ↦ d(c+1 mod 2p, i)`. -/
def sigF (p : Nat) (j : Nat) : Nat :=
  if j < p * p + p * p then dpt p ((colOf p j + 1) % (2 * p)) (rowOf p j) else j

theorem sigF_dpt {p c i : Nat} (hc : c < 2 * p) (hi : i < p) :
    sigF p (dpt p c i) = dpt p ((c + 1) % (2 * p)) i := by
  unfold sigF
  rw [if_pos (dpt_lt hc hi), colOf_dpt hc hi, rowOf_dpt hc hi]

theorem sigF_ge {p j : Nat} (h : p * p + p * p ≤ j) : sigF p j = j := by
  unfold sigF; rw [if_neg (by omega)]

/-! ### Explicit formulas for the permutations of Section 4 -/

/-- the cycle `(0, 1, …, L-1)` on `ℕ` -/
def cycF (L j : Nat) : Nat := if j + 1 < L then j + 1 else if j + 1 = L then 0 else j

/-- the transposition `(a, b)` on `ℕ` -/
def trF (a b j : Nat) : Nat := if j = a then b else if j = b then a else j

/-- `g` shifted by `s` -/
def shF (s : Nat) (f : Nat → Nat) (j : Nat) : Nat := if j < s then j else f (j - s) + s

/-- indicator of a single row/column -/
def ind1 (t r : Nat) : Nat := if r = t then 1 else 0
/-- indicator of `[0, p-1]` -/
def indLow (p r : Nat) : Nat := if r < p then 1 else 0
/-- indicator of `[p, 2p-1]` -/
def indHigh (p r : Nat) : Nat := if p ≤ r then 1 else 0

/-- `ρ_p = (0, …, p-1) = rot(𝟙_{0})`. -/
theorem cycF_eq_rotF {p : Nat} (hp : 0 < p) (j : Nat) : cycF p j = rotF p (ind1 0) j := by
  by_cases hj : j < p * p + p * p
  · obtain ⟨r, c, hr, hc, rfl⟩ := below2q p j hp hj
    rw [rotF_rc _ hr hc]
    by_cases hr0 : r = 0
    · subst hr0
      have e : ind1 0 0 = 1 := rfl
      rw [e]
      simp only [Nat.zero_mul, Nat.zero_add]
      unfold cycF
      by_cases h1 : c + 1 < p
      · rw [if_pos h1, Nat.mod_eq_of_lt h1]
      · rw [if_neg h1, if_pos (by omega), show c + 1 = p by omega, Nat.mod_self]
    · have e : ind1 0 r = 0 := by unfold ind1; rw [if_neg hr0]
      rw [e, Nat.add_zero, Nat.mod_eq_of_lt hc]
      have : p ≤ r * p := by
        have := Nat.mul_le_mul_right p (show 1 ≤ r by omega); omega
      unfold cycF
      rw [if_neg (by omega), if_neg (by omega)]
  · rw [rotF_ge _ (by omega)]
    unfold cycF
    have : p ≤ p * p := Nat.le_mul_self p
    rw [if_neg (by omega), if_neg (by omega)]

/-- Shifting `rot(m)` (with `m ≡ 0` on rows `≥ R`) by `t` rows. -/
theorem rotF_shift {p : Nat} (hp : 0 < p) (m : Nat → Nat) (R t : Nat)
    (hR : ∀ r, R ≤ r → m r % p = 0) (hRt : R + t ≤ 2 * p) (i : Nat) :
    shF (t * p) (rotF p m) i = rotF p (fun r => if t ≤ r then m (r - t) else 0) i := by
  unfold shF
  by_cases hi : i < p * p + p * p
  · obtain ⟨r, c, hr, hc, rfl⟩ := below2q p i hp hi
    rw [rotF_rc _ hr hc]
    by_cases htr : t ≤ r
    · obtain ⟨u, rfl⟩ : ∃ u, r = t + u := ⟨r - t, by omega⟩
      have e1 : (t + u) * p + c = u * p + c + t * p := by rw [Nat.add_mul]; omega
      rw [if_neg (by rw [e1]; omega), if_pos htr, e1, Nat.add_sub_cancel,
        rotF_rc _ (by omega) hc, show t + u - t = u by omega]
      rw [Nat.add_mul]; omega
    · rw [if_pos (by have := rc_lt (p := p) (Nat.lt_of_not_le htr) hc; omega), if_neg htr,
        Nat.add_zero, Nat.mod_eq_of_lt hc]
  · rw [rotF_ge (fun r => if t ≤ r then m (r - t) else 0) (show p * p + p * p ≤ i by omega)]
    have h2 : R * p + t * p ≤ p * p + p * p := by
      rw [← Nat.add_mul, ← two_p_mul]; exact Nat.mul_le_mul_right _ hRt
    rw [if_neg (by omega)]
    have hfix : rotF p m (i - t * p) = i - t * p := by
      by_cases h3 : i - t * p < p * p + p * p
      · obtain ⟨r, c, hr, hc, hrc⟩ := below2q p (i - t * p) hp h3
        rw [hrc]
        have hRr : R ≤ r := by
          refine Decidable.byContradiction fun h => ?_
          have := rc_lt (p := p) (Nat.lt_of_not_le h) hc
          omega
        exact rotF_fix hp m hr hc (hR r hRr)
      · exact rotF_ge _ (by omega)
    rw [hfix]; omega

/-- `rot(m)` fixes the points of rows `≥ R` when `m ≡ 0` there. -/
theorem rotF_fix_high {p : Nat} (hp : 0 < p) (m : Nat → Nat) (R : Nat)
    (hR : ∀ r, R ≤ r → m r % p = 0) {j : Nat} (hj : R * p ≤ j) : rotF p m j = j := by
  by_cases h3 : j < p * p + p * p
  · obtain ⟨r, c, hr, hc, rfl⟩ := below2q p j hp h3
    have hRr : R ≤ r := by
      refine Decidable.byContradiction fun h => ?_
      have := rc_lt (p := p) (Nat.lt_of_not_le h) hc
      omega
    exact rotF_fix hp m hr hc (hR r hRr)
  · exact rotF_ge _ (by omega)

/-- the transposition `(0, p)` shifted by `t p` is `(t p, (t+1) p)` -/
theorem trF_shift (p t j : Nat) :
    shF (t * p) (trF 0 p) j = trF (t * p) (t * p + p) j := by
  unfold shF trF
  by_cases h1 : j < t * p
  · rw [if_pos h1, if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h1]
    split_all <;> omega

/-- `V = (0, p, 2p, …, (p-1)p) = crot(𝟙_{0})`. -/
theorem V_char {p : Nat} (hp : 0 < p) (j : Nat) :
    crotF p (ind1 0) j =
      (if j < p * p ∧ j % p = 0 then (if j + p < p * p then j + p else 0) else j) := by
  by_cases hj : j < p * p + p * p
  · obtain ⟨h1, h2, h3⟩ := dpt_colOf_rowOf hp hj
    generalize colOf p j = c at h1 h3
    generalize rowOf p j = i at h2 h3
    subst h3
    rw [crotF_dpt _ h1 h2]
    by_cases hcp : c < p
    · have hd : ∀ k, dpt p c k = k * p + c := fun k => by unfold dpt; rw [if_pos hcp]
      rw [hd, hd, rc_mod hcp]
      have hlt : i * p + c < p * p := rc_lt h2 hcp
      by_cases hc0 : c = 0
      · subst hc0
        have e : ind1 0 0 = 1 := rfl
        rw [e, if_pos ⟨hlt, rfl⟩, Nat.add_zero, Nat.add_zero]
        have hip : (i + 1) * p = i * p + p := by rw [Nat.add_mul, Nat.one_mul]
        by_cases hi1 : i + 1 < p
        · rw [Nat.mod_eq_of_lt hi1, hip]
          have : (i + 1) * p + 0 < p * p := rc_lt hi1 hp
          rw [if_pos (by omega)]
          omega
        · have hi' : i + 1 = p := by omega
          rw [hi', Nat.mod_self, Nat.zero_mul]
          have : (i + 1) * p = p * p := by rw [hi']
          rw [if_neg (by omega)]
      · have e : ind1 0 c = 0 := by unfold ind1; rw [if_neg hc0]
        rw [e, Nat.add_zero, Nat.mod_eq_of_lt h2]
        rw [if_neg (fun h => hc0 h.2)]
    · have e : ind1 0 c = 0 := by unfold ind1; rw [if_neg (by omega)]
      rw [e, Nat.add_zero, Nat.mod_eq_of_lt h2]
      have : p * p ≤ dpt p c i := dpt_ge_q (by omega)
      rw [if_neg (fun h => by omega)]
  · rw [crotF_ge _ (by omega), if_neg (by omega)]

/-- `Φ^{y^{ip}}` acts on row `i` of both grids: `d(c, i) ↦ d(c+1 mod 2p, i)`. -/
def phiRow (p i j : Nat) : Nat :=
  if i * p ≤ j ∧ j < i * p + p then (if j + 1 < i * p + p then j + 1 else p * p + i * p)
  else if p * p + i * p ≤ j ∧ j < p * p + i * p + p then
    (if j + 1 < p * p + i * p + p then j + 1 else i * p)
  else j

/-- `Σ`, defined as the composite of the row factors `Φ^{y^{ip}}`, `i < p`. -/
def sigPart (p : Nat) : Nat → Nat → Nat
  | 0, j => j
  | k + 1, j => phiRow p k (sigPart p k j)

/-- `Σ`: `d(c, i) ↦ d(c+1 mod 2p, i)`. -/
def sigma (p j : Nat) : Nat := sigPart p p j

/-- `Φ = ρ_p ρ_p^{y^q} σ_q` (as a composite of explicit functions). -/
theorem phi_formula {p : Nat} (hp : 2 ≤ p) (j : Nat) :
    trF 0 (p * p) (shF (p * p) (cycF p) (cycF p j)) = phiRow p 0 j := by
  have hpq : p + p ≤ p * p := by
    have := Nat.mul_le_mul_right p hp; omega
  unfold trF shF cycF phiRow
  simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero]
  split_all <;> omega

/-- `Φ` shifted by `i p` acts on row `i`. -/
theorem phiRow_shift {p : Nat} {i : Nat} (hi : i * p + p ≤ p * p) (j : Nat) :
    shF (i * p) (phiRow p 0) j = phiRow p i j := by
  unfold shF phiRow
  simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero]
  split_all <;> omega

/-- `(a+1) p = a p + p` -/
theorem succ_mul' (a p : Nat) : (a + 1) * p = a * p + p := by rw [Nat.add_mul, Nat.one_mul]

/-- `phiRow` on structured points. -/
theorem phiRow_dpt {p c i k : Nat} (hp : 0 < p) (hc : c < 2 * p) (hi : i < p) (hk : k < p) :
    phiRow p k (dpt p c i) = if i = k then dpt p ((c + 1) % (2 * p)) i else dpt p c i := by
  have hkq : k * p + p ≤ p * p := by rw [← succ_mul']; exact rc_le (by omega)
  have hiq : i * p + p ≤ p * p := by rw [← succ_mul']; exact rc_le (by omega)
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl]
    have hmod : c + 1 < 2 * p ∨ c + 1 = 2 * p := by omega
    rcases hmod with hm | hm
    · rw [Nat.mod_eq_of_lt hm]
      unfold dpt phiRow
      split_all <;> omega
    · rw [hm, Nat.mod_self]
      unfold dpt phiRow
      split_all <;> omega
  · rw [if_neg hik]
    have h' : i * p + p ≤ k * p ∨ k * p + p ≤ i * p := by
      rcases Nat.lt_or_gt_of_ne hik with h | h
      · exact Or.inl (by rw [← succ_mul']; exact rc_le (by omega))
      · exact Or.inr (by rw [← succ_mul']; exact rc_le (by omega))
    unfold dpt phiRow
    rcases h' with h | h <;> split_all <;> omega

theorem sigPart_dpt {p c i : Nat} (hp : 0 < p) (hc : c < 2 * p) (hi : i < p) (k : Nat)
    (hk : k ≤ p) :
    sigPart p k (dpt p c i) = if i < k then dpt p ((c + 1) % (2 * p)) i else dpt p c i := by
  induction k with
  | zero => simp [sigPart]
  | succ k ih =>
    simp only [sigPart]
    rw [ih (by omega)]
    by_cases hik : i < k
    · rw [if_pos hik, phiRow_dpt hp (Nat.mod_lt _ (by omega)) hi (by omega), if_neg (by omega),
        if_pos (by omega)]
    · rw [if_neg hik, phiRow_dpt hp hc hi (by omega)]
      by_cases h : i = k
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]

theorem sigma_dpt {p c i : Nat} (hp : 0 < p) (hc : c < 2 * p) (hi : i < p) :
    sigma p (dpt p c i) = dpt p ((c + 1) % (2 * p)) i := by
  unfold sigma
  rw [sigPart_dpt hp hc hi p (Nat.le_refl _), if_pos hi]

theorem phiRow_ge {p i j : Nat} (hi : i * p + p ≤ p * p) (hj : p * p + p * p ≤ j) :
    phiRow p i j = j := by
  unfold phiRow; split_all <;> omega

theorem sigPart_ge {p j : Nat} (hj : p * p + p * p ≤ j) (k : Nat) (hk : k ≤ p) :
    sigPart p k j = j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [sigPart]
    rw [ih (by omega)]
    exact phiRow_ge (by have := rc_le (p := p) (show k + 1 ≤ p by omega); rw [Nat.add_mul,
      Nat.one_mul] at this; omega) hj

theorem sigma_ge {p j : Nat} (hj : p * p + p * p ≤ j) : sigma p j = j :=
  sigPart_ge hj p (Nat.le_refl _)

/-- The window shift needed for `B_c^{Σ^t}`. -/
theorem win_prev {p t c : Nat} (hp : 0 < p) (ht : t + 1 < p) (hc : c < 2 * p) :
    win p t ((c + (2 * p - 1)) % (2 * p)) = win p (t + 1) c := by
  unfold win
  by_cases hc0 : c = 0
  · subst hc0
    rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    split_all <;> omega
  · rw [show c + (2 * p - 1) = (c - 1) + 2 * p by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    split_all <;> omega

/-- the predecessor of a virtual column -/
theorem prev_succ {p c : Nat} (hp : 0 < p) (hc : c < 2 * p) :
    ((c + 1) % (2 * p) + (2 * p - 1)) % (2 * p) = c := by
  by_cases h : c + 1 < 2 * p
  · rw [Nat.mod_eq_of_lt h, show c + 1 + (2 * p - 1) = c + 2 * p by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hc]
  · rw [show c + 1 = 2 * p by omega, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    omega

/-- the transposition `(a, b)` shifted by `s` -/
theorem trF_shift' (a b s j : Nat) : shF s (trF a b) j = trF (a + s) (b + s) j := by
  unfold shF trF
  split_all <;> omega

/-- the cycle `(0, …, L-1)` shifted by `s` -/
def cycShF (s L j : Nat) : Nat := if s ≤ j ∧ j + 1 < s + L then j + 1 else if j + 1 = s + L then s else j

theorem cycF_shift (s L j : Nat) (hL : 1 ≤ L) : shF s (cycF L) j = cycShF s L j := by
  unfold shF cycF cycShF
  split_all <;> omega

/-- `crot(m)` fixes `G_1` and everything above when `m ≡ 0` on the columns `≥ p`. -/
theorem crotF_fix_G1 {p : Nat} (hp : 0 < p) (m : Nat → Nat) (hm : ∀ c, p ≤ c → m c % p = 0)
    {j : Nat} (hj : p * p ≤ j) : crotF p m j = j := by
  by_cases h2 : j < p * p + p * p
  · obtain ⟨h1, h2', h3⟩ := dpt_colOf_rowOf hp h2
    generalize colOf p j = c at h1 h3
    generalize rowOf p j = i at h2' h3
    subst h3
    have hcp : p ≤ c := by
      refine Decidable.byContradiction fun h => ?_
      have := dpt_lt_q (p := p) (c := c) (i := i) (by omega) h2'
      omega
    rw [crotF_dpt _ h1 h2', Nat.add_mod, hm c hcp, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt h2']
  · exact crotF_ge _ (by omega)

/-- `crot(m)` fixes `G_0` when `m ≡ 0` on the columns `< p`. -/
theorem crotF_fix_G0 {p : Nat} (hp : 0 < p) (m : Nat → Nat) (hm : ∀ c, c < p → m c % p = 0)
    {j : Nat} (hj : j < p * p) : crotF p m j = j := by
  obtain ⟨h1, h2', h3⟩ := dpt_colOf_rowOf hp (show j < p * p + p * p by omega)
  generalize colOf p j = c at h1 h3
  generalize rowOf p j = i at h2' h3
  subst h3
  have hcp : c < p := by
    refine Decidable.byContradiction fun h => ?_
    have := dpt_ge_q (p := p) (c := c) (i := i) (by omega)
    omega
  rw [crotF_dpt _ h1 h2', Nat.add_mod, hm c hcp, Nat.add_zero, Nat.mod_mod,
    Nat.mod_eq_of_lt h2']

/-- `B_c' = B_c^{y^q}`: shifting `crot(𝟙_{[0,p-1]})` by `q` gives `crot(𝟙_{[p,2p-1]})`. -/
theorem crotF_shift_q {p : Nat} (hp : 0 < p) (j : Nat) :
    shF (p * p) (crotF p (indLow p)) j = crotF p (indHigh p) j := by
  unfold shF
  by_cases hj : j < p * p
  · rw [if_pos hj, crotF_fix_G0 hp _ (fun c hc => by unfold indHigh; rw [if_neg (by omega), Nat.zero_mod]) hj]
  · rw [if_neg hj]
    by_cases h2 : j < p * p + p * p
    · obtain ⟨h1, h2', h3⟩ := dpt_colOf_rowOf hp h2
      generalize colOf p j = c at h1 h3
      generalize rowOf p j = i at h2' h3
      subst h3
      have hcp : p ≤ c := by
        refine Decidable.byContradiction fun h => ?_
        have := dpt_lt_q (p := p) (c := c) (i := i) (by omega) h2'
        omega
      have e : dpt p c i - p * p = dpt p (c - p) i := by
        unfold dpt; rw [if_neg (by omega), if_pos (by omega)]; omega
      rw [e, crotF_dpt _ (by omega) h2', crotF_dpt _ h1 h2']
      have e1 : indLow p (c - p) = 1 := by unfold indLow; rw [if_pos (by omega)]
      have e2 : indHigh p c = 1 := by unfold indHigh; rw [if_pos hcp]
      rw [e1, e2]
      unfold dpt; rw [if_pos (by omega), if_neg (by omega)]; omega
    · rw [crotF_fix_G1 hp _ (fun c hc => by unfold indLow; rw [if_neg (by omega), Nat.zero_mod]) (by omega),
        crotF_ge _ (by omega)]
      omega

/-- The cycle `(c, p + c, …, (p-1)p + c)` of the `c`-th column of `G_0` is `crot(𝟙_{c})`. -/
theorem col_char {p c : Nat} (hp : 0 < p) (hc : c < p) (j : Nat) :
    crotF p (ind1 c) j =
      (if j < p * p ∧ j % p = c then (if j + p < p * p then j + p else c) else j) := by
  by_cases hj : j < p * p + p * p
  · obtain ⟨h1, h2, h3⟩ := dpt_colOf_rowOf hp hj
    generalize colOf p j = c' at h1 h3
    generalize rowOf p j = i at h2 h3
    subst h3
    rw [crotF_dpt _ h1 h2]
    by_cases hcp : c' < p
    · have hd : ∀ k, dpt p c' k = k * p + c' := fun k => by unfold dpt; rw [if_pos hcp]
      rw [hd, hd, rc_mod hcp]
      have hlt : i * p + c' < p * p := rc_lt h2 hcp
      by_cases hcc : c' = c
      · subst hcc
        have e : ind1 c' c' = 1 := by unfold ind1; rw [if_pos rfl]
        rw [e, if_pos ⟨hlt, rfl⟩]
        by_cases hi1 : i + 1 < p
        · rw [Nat.mod_eq_of_lt hi1, succ_mul']
          have : (i + 1) * p + c' < p * p := rc_lt hi1 hcp
          rw [succ_mul'] at this
          rw [if_pos (by omega)]
          omega
        · have hi' : i + 1 = p := by omega
          rw [hi', Nat.mod_self, Nat.zero_mul, Nat.zero_add]
          have : (i + 1) * p = p * p := by rw [hi']
          rw [succ_mul'] at this
          rw [if_neg (by omega)]
      · have e : ind1 c c' = 0 := by unfold ind1; rw [if_neg hcc]
        rw [e, Nat.add_zero, Nat.mod_eq_of_lt h2]
        rw [if_neg (fun h => hcc h.2)]
    · have e : ind1 c c' = 0 := by unfold ind1; rw [if_neg (by omega)]
      rw [e, Nat.add_zero, Nat.mod_eq_of_lt h2]
      have : p * p ≤ dpt p c' i := dpt_ge_q (by omega)
      rw [if_neg (fun h => by omega)]
  · rw [crotF_ge _ (by omega), if_neg (by omega)]

/-- powers of the cycle `(0, …, L-1)` -/
def cycPowF (L k j : Nat) : Nat := if j < L then (j + k) % L else j

theorem cycPowF_succ {L : Nat} (hL : 0 < L) (k j : Nat) :
    cycF L (cycPowF L k j) = cycPowF L (k + 1) j := by
  unfold cycPowF
  by_cases hj : j < L
  · rw [if_pos hj, if_pos hj]
    have hlt : (j + k) % L < L := Nat.mod_lt _ hL
    have e : (j + (k + 1)) % L = ((j + k) % L + 1) % L := by
      rw [Nat.mod_add_mod, Nat.add_assoc]
    rw [e]
    unfold cycF
    by_cases h1 : (j + k) % L + 1 < L
    · rw [if_pos h1, Nat.mod_eq_of_lt h1]
    · rw [if_neg h1, if_pos (by omega), show (j + k) % L + 1 = L by omega, Nat.mod_self]
  · rw [if_neg hj, if_neg hj]; unfold cycF; rw [if_neg (by omega), if_neg (by omega)]

theorem cycPowF_zero {L j : Nat} : cycPowF L 0 j = j := by
  unfold cycPowF; split_all
  · rw [Nat.add_zero]; exact Nat.mod_eq_of_lt (by assumption)
  · rfl

/-- `ρ_q^p` (`q = p²`) rotates every column of `G_0` down by one. -/
theorem rhoq_pow {p : Nat} (hp : 0 < p) (j : Nat) :
    cycPowF (p * p) p j = (if j < p * p then crotF p (fun _ => 1) j else j) := by
  unfold cycPowF
  by_cases hj : j < p * p
  · rw [if_pos hj, if_pos hj]
    obtain ⟨h1, h2, h3⟩ := dpt_colOf_rowOf hp (show j < p * p + p * p by omega)
    generalize colOf p j = c at h1 h3
    generalize rowOf p j = i at h2 h3
    subst h3
    have hcp : c < p := by
      refine Decidable.byContradiction fun h => ?_
      have := dpt_ge_q (p := p) (c := c) (i := i) (by omega)
      omega
    rw [crotF_dpt _ h1 h2]
    have hd : ∀ k, dpt p c k = k * p + c := fun k => by unfold dpt; rw [if_pos hcp]
    rw [hd, hd]
    by_cases hi1 : i + 1 < p
    · rw [Nat.mod_eq_of_lt hi1]
      have : (i + 1) * p + c < p * p := rc_lt hi1 hcp
      rw [succ_mul'] at this ⊢
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · have hi' : i + 1 = p := by omega
      rw [hi', Nat.mod_self, Nat.zero_mul, Nat.zero_add]
      have : (i + 1) * p = p * p := by rw [hi']
      rw [succ_mul'] at this
      rw [show i * p + c + p = c + p * p by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by
        have : p ≤ p * p := Nat.le_mul_self p; omega)]
  · rw [if_neg hj, if_neg hj]

/-- `T = ρ_q^p (ρ_q^p)^{y^q} = crot(𝟙)`. -/
theorem T_formula {p : Nat} (hp : 0 < p) (j : Nat) :
    shF (p * p) (cycPowF (p * p) p) (cycPowF (p * p) p j) = crotF p (fun _ => 1) j := by
  unfold shF
  by_cases hj : j < p * p
  · have e1 := rhoq_pow hp j
    rw [if_pos hj] at e1
    have hlt : crotF p (fun _ => 1) j < p * p := by
      obtain ⟨h1, h2, h3⟩ := dpt_colOf_rowOf hp (show j < p * p + p * p by omega)
      generalize colOf p j = c at h1 h3
      generalize rowOf p j = i at h2 h3
      subst h3
      have hcp : c < p := by
        refine Decidable.byContradiction fun h => ?_
        have := dpt_ge_q (p := p) (c := c) (i := i) (by omega)
        omega
      rw [crotF_dpt _ h1 h2]
      exact dpt_lt_q hcp (Nat.mod_lt _ hp)
    rw [e1, if_pos hlt]
  · have e1 : cycPowF (p * p) p j = j := by unfold cycPowF; rw [if_neg hj]
    rw [e1, if_neg hj]
    by_cases h2 : j < p * p + p * p
    · obtain ⟨h1, h2', h3⟩ := dpt_colOf_rowOf hp h2
      generalize colOf p j = c at h1 h3
      generalize rowOf p j = i at h2' h3
      subst h3
      have hcp : p ≤ c := by
        refine Decidable.byContradiction fun h => ?_
        have := dpt_lt_q (p := p) (c := c) (i := i) (by omega) h2'
        omega
      have e : dpt p c i - p * p = dpt p (c - p) i := by
        unfold dpt; rw [if_neg (by omega), if_pos (by omega)]; omega
      have e2 := rhoq_pow hp (dpt p (c - p) i)
      rw [if_pos (dpt_lt_q (by omega) h2')] at e2
      rw [e, e2, crotF_dpt _ (by omega) h2', crotF_dpt _ h1 h2']
      unfold dpt; rw [if_pos (by omega), if_neg (by omega)]; omega
    · rw [crotF_ge _ (by omega)]
      have e2 : cycPowF (p * p) p (j - p * p) = j - p * p := by
        unfold cycPowF
        have : p * p ≤ j - p * p := by omega
        rw [if_neg (by omega)]
      rw [e2]; omega

/-- `ν`: the rotation amounts of `L` and `U`. -/
def nuF (p r : Nat) : Nat := if r < p then r else 2 * p - r

theorem L_amounts {p r : Nat} (hp : 0 < p) (hr : r < 2 * p) :
    (tau p r + (if r < p then p - 1 else 0) + indHigh p r) % p = nuF p r % p := by
  unfold tau indHigh nuF
  by_cases h : r < p
  · rw [if_pos h, if_pos h, if_neg (by omega), if_pos h,
      show r + 1 + (p - 1) + 0 = r + p by omega, Nat.add_mod_right]
  · rw [if_neg h, if_neg h, if_pos (by omega), if_neg h]
    congr 1; omega

theorem sumTo_ind1 (r k : Nat) : sumTo (fun t => ind1 t r) k = if r < k then 1 else 0 := by
  induction k with
  | zero => simp only [sumTo_zero]; rw [if_neg (by omega)]
  | succ k ih => rw [sumTo_succ, ih]; unfold ind1; split_all <;> omega

end SnPres
