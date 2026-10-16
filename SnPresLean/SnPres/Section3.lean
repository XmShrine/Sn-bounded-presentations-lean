/-
Section 3: short power words in `S_n`.

We model the paper's `S_n` (permutations acting on the right, `gh` = first `g` then `h`) as the
opposite group of Mathlib's `Equiv.Perm (Fin n)`.
-/
import SnPres.PE
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Basic

namespace SnPres

open PE

/-- The symmetric group on `X` with the conventions of the paper: permutations act on the right
(`ω ↦ ω^g`), and `g h` means "first `g`, then `h`".  It is the opposite of Mathlib's
`Equiv.Perm X` (where `f * g` means "first `g`, then `f`"). -/
abbrev RPerm (X : Type*) := (Equiv.Perm X)ᵐᵒᵖ

/-- `S_n = Sym([0, n-1])` with the conventions of the paper. -/
abbrev Sym (n : ℕ) := RPerm (Fin n)

/-- The right action `ω^g`. -/
def act {X : Type*} (ω : X) (g : RPerm X) : X := (MulOpposite.unop g) ω

section RPermBasic
variable {X : Type*}

@[simp] lemma act_mul (ω : X) (g h : RPerm X) : act ω (g * h) = act (act ω g) h := rfl
@[simp] lemma act_one (ω : X) : act ω (1 : RPerm X) = ω := rfl
@[simp] lemma act_inv_act (ω : X) (g : RPerm X) : act (act ω g) g⁻¹ = ω := by
  simp only [act, MulOpposite.unop_inv]; exact Equiv.Perm.inv_apply_self _ _
@[simp] lemma act_act_inv (ω : X) (g : RPerm X) : act (act ω g⁻¹) g = ω := by
  simp only [act, MulOpposite.unop_inv]; exact Equiv.Perm.apply_inv_self _ _

lemma rperm_ext {g h : RPerm X} (H : ∀ ω, act ω g = act ω h) : g = h := by
  apply MulOpposite.unop_injective
  exact Equiv.ext H

/-- A permutation (as a function), viewed in `RPerm`. -/
def rp (f : Equiv.Perm X) : RPerm X := MulOpposite.op f
@[simp] lemma act_rp (f : Equiv.Perm X) (ω : X) : act ω (rp f) = f ω := rfl
lemma rp_mul (f g : Equiv.Perm X) : rp f * rp g = rp (g * f) := rfl
lemma rp_inv (f : Equiv.Perm X) : (rp f)⁻¹ = rp f⁻¹ := rfl

end RPermBasic

/-! ### The action on natural numbers -/

section NatAction
variable {n : ℕ}

/-- `i ↦ i^g` on `ℕ`: the action on `[0, n-1]`, extended by the identity. -/
def nv (g : Sym n) (i : ℕ) : ℕ := if h : i < n then (act (⟨i, h⟩ : Fin n) g).val else i

lemma nv_of_lt (g : Sym n) {i : ℕ} (h : i < n) : nv g i = (act (⟨i, h⟩ : Fin n) g).val :=
  dif_pos h
lemma nv_of_ge (g : Sym n) {i : ℕ} (h : n ≤ i) : nv g i = i := dif_neg (by omega)
lemma nv_lt (g : Sym n) {i : ℕ} (h : i < n) : nv g i < n := by
  rw [nv_of_lt g h]; exact Fin.isLt _
lemma nv_fin (g : Sym n) (ω : Fin n) : nv g ω.val = (act ω g).val := by
  rw [nv_of_lt g ω.isLt]

@[simp] lemma nv_mul (g h : Sym n) (i : ℕ) : nv (g * h) i = nv h (nv g i) := by
  by_cases hi : i < n
  · have h1 : nv g i = (act (⟨i, hi⟩ : Fin n) g).val := nv_of_lt g hi
    rw [nv_of_lt _ hi, h1, nv_fin, act_mul]
  · rw [nv_of_ge (g * h) (show n ≤ i by omega), nv_of_ge g (show n ≤ i by omega),
      nv_of_ge h (show n ≤ i by omega)]

@[simp] lemma nv_one (i : ℕ) : nv (1 : Sym n) i = i := by
  by_cases hi : i < n
  · rw [nv_of_lt _ hi]; rfl
  · rw [nv_of_ge _ (by omega)]

lemma nv_inv_nv (g : Sym n) (i : ℕ) : nv g⁻¹ (nv g i) = i := by
  rw [← nv_mul, mul_inv_cancel, nv_one]
lemma nv_nv_inv (g : Sym n) (i : ℕ) : nv g (nv g⁻¹ i) = i := by
  rw [← nv_mul, inv_mul_cancel, nv_one]
lemma nv_injective (g : Sym n) : Function.Injective (nv g) := fun i j h => by
  rw [← nv_inv_nv g i, h, nv_inv_nv]
lemma nv_inv_eq_iff (g : Sym n) (i j : ℕ) : nv g⁻¹ i = j ↔ nv g j = i := by
  constructor
  · rintro rfl; exact nv_nv_inv g i
  · rintro rfl; exact nv_inv_nv g j

lemma sym_ext {g h : Sym n} (H : ∀ i < n, nv g i = nv h i) : g = h := by
  apply rperm_ext
  intro ω
  apply Fin.ext
  rw [← nv_fin, ← nv_fin]
  exact H _ ω.isLt

lemma nv_pow_succ (g : Sym n) (k i : ℕ) : nv (g ^ (k + 1)) i = nv g (nv (g ^ k) i) := by
  rw [pow_succ, nv_mul]

lemma nv_lt_iff (g : Sym n) (i : ℕ) : nv g i < n ↔ i < n := by
  constructor
  · intro h
    by_contra h'
    rw [nv_of_ge _ (by omega)] at h
    omega
  · exact nv_lt g

/-- If `g` fixes every point of a set `A ⊆ [0,n)`, it maps `[0,n) \ A` into itself. -/
lemma nv_ne_of_fixed (g : Sym n) {j k : ℕ} (hk : nv g k = k) (hjk : j ≠ k) : nv g j ≠ k := by
  intro h
  exact hjk (nv_injective g (h.trans hk.symm))

/-- A permutation of `[0, n-1]` given by a function on `ℕ` together with its inverse. -/
def ofFun (n : ℕ) (f g : ℕ → ℕ) (hf : ∀ i < n, f i < n) (hg : ∀ i < n, g i < n)
    (hgf : ∀ i < n, g (f i) = i) (hfg : ∀ i < n, f (g i) = i) : Sym n :=
  rp { toFun := fun ω => ⟨f ω.val, hf _ ω.isLt⟩
       invFun := fun ω => ⟨g ω.val, hg _ ω.isLt⟩
       left_inv := fun ω => Fin.ext (hgf _ ω.isLt)
       right_inv := fun ω => Fin.ext (hfg _ ω.isLt) }

lemma nv_ofFun {f g : ℕ → ℕ} {hf : ∀ i < n, f i < n} {hg : ∀ i < n, g i < n}
    {hgf : ∀ i < n, g (f i) = i} {hfg : ∀ i < n, f (g i) = i} {i : ℕ} (hi : i < n) :
    nv (ofFun n f g hf hg hgf hfg) i = f i := by
  rw [nv_of_lt _ hi]; rfl

/-- The transposition `(a, b)` (the identity if `a` or `b` is out of range). -/
def tr (n a b : ℕ) : Sym n :=
  if h : a < n ∧ b < n then rp (Equiv.swap ⟨a, h.1⟩ ⟨b, h.2⟩) else 1

lemma nv_tr {a b : ℕ} (ha : a < n) (hb : b < n) (i : ℕ) :
    nv (tr n a b) i = if i = a then b else if i = b then a else i := by
  unfold tr
  rw [dif_pos ⟨ha, hb⟩]
  by_cases hi : i < n
  · rw [nv_of_lt _ hi]
    simp only [act_rp, Equiv.swap_apply_def, Fin.ext_iff]
    split_ifs <;> simp
  · rw [nv_of_ge _ (by omega)]
    split_ifs <;> omega

lemma tr_inv {a b : ℕ} (ha : a < n) (hb : b < n) : (tr n a b)⁻¹ = tr n a b := by
  apply sym_ext; intro i _
  rw [nv_inv_eq_iff, nv_tr ha hb, nv_tr ha hb]
  split_ifs <;> omega

end NatAction

/-! ### The standard generators -/

/-- `x = (0, 1)`. -/
def xs (n : ℕ) (hn : 1 < n) : Sym n := rp (Equiv.swap ⟨0, by omega⟩ ⟨1, hn⟩)

/-- `y = (0, 1, …, n-1)`, i.e. `i ↦ i + 1` (mod `n`). -/
def ys (n : ℕ) : Sym n := rp (finRotate n)

lemma xs_eq_tr (n : ℕ) (hn : 1 < n) : xs n hn = tr n 0 1 := by
  unfold tr; rw [dif_pos ⟨by omega, hn⟩]; rfl

lemma nv_xs {n : ℕ} (hn : 1 < n) (i : ℕ) :
    nv (xs n hn) i = if i = 0 then 1 else if i = 1 then 0 else i := by
  rw [xs_eq_tr, nv_tr (by omega) hn]

lemma nv_ys {n : ℕ} {i : ℕ} (hi : i < n) : nv (ys n) i = if i + 1 = n then 0 else i + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [nv_of_lt _ hi]
  simp only [ys, act_rp]
  rw [coe_finRotate]
  simp only [Fin.ext_iff, Fin.val_last]
  split_ifs <;> omega

lemma nv_ys_pow {n : ℕ} (k : ℕ) {i : ℕ} (hi : i < n) : nv (ys n ^ k) i = (i + k) % n := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt hi]
  | succ k ih =>
    rw [nv_pow_succ, ih]
    have hlt : (i + k) % n < n := Nat.mod_lt _ (by omega)
    rw [nv_ys hlt]
    have e : (i + (k + 1)) % n = ((i + k) % n + 1) % n := by
      rw [Nat.mod_add_mod, Nat.add_assoc]
    rw [e]
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact (Nat.mod_eq_of_lt (show (i + k) % n + 1 < n by omega)).symm

/-- Lemma 3.4(e): conjugating by `y^s` shifts a permutation supported in `[0, n-1-s]` by `s`. -/
theorem nv_shift {n : ℕ} (g : Sym n) (s : ℕ) (hs : s < n)
    (hg : ∀ j, n - s ≤ j → j < n → nv g j = j) (i : ℕ) (hi : i < n) :
    nv ((ys n ^ s)⁻¹ * g * ys n ^ s) i = if i < s then i else nv g (i - s) + s := by
  simp only [nv_mul]
  by_cases his : i < s
  · have h1 : nv (ys n ^ s)⁻¹ i = i + n - s := by
      rw [nv_inv_eq_iff, nv_ys_pow _ (by omega)]
      rw [show i + n - s + s = i + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    rw [h1, hg _ (by omega) (by omega), nv_ys_pow _ (by omega), if_pos his,
      show i + n - s + s = i + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have h1 : nv (ys n ^ s)⁻¹ i = i - s := by
      rw [nv_inv_eq_iff, nv_ys_pow _ (by omega), show i - s + s = i by omega,
        Nat.mod_eq_of_lt hi]
    rw [h1, if_neg his]
    have hlt : nv g (i - s) < n - s := by
      by_contra hcon
      have hlt' : nv g (i - s) < n := nv_lt g (by omega)
      have hfix := hg (nv g (i - s)) (by omega) hlt'
      have := nv_injective g hfix
      omega
    rw [nv_ys_pow _ (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The fixed points form the complement: if `g` fixes `[n-s, n-1]`, so does `g⁻¹`. -/
lemma nv_inv_fixed {n : ℕ} (g : Sym n) {j : ℕ} (h : nv g j = j) : nv g⁻¹ j = j := by
  rw [nv_inv_eq_iff]; exact h

/-! ### Lemma 3.1 (telescoping) and Lemma 3.2 -/

/-- Lemma 3.1. -/
theorem telescoping {G : Type*} [Group G] (B S : G) (K : ℕ) :
    ((List.range K).map (fun t => (S ^ t)⁻¹ * B * S ^ t)).prod = (B * S⁻¹) ^ K * S ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [pow_succ (B * S⁻¹) K, pow_succ S K]
    group

/-- Lemma 3.2. -/
theorem powexp {G : Type*} [Group G] (g W : G) (e : ℕ) :
    (g * W) ^ e = g ^ e * ((List.range e).reverse.map (fun i => (g ^ i)⁻¹ * W * g ^ i)).prod := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', ih, List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.map_cons, List.prod_cons]
    rw [pow_succ']
    group

/-- `Tel(B, S, K)`: `(B S⁻¹)^K S^K` for `K ≥ 2` and `B` for `K = 1`. -/
def Tel {α : Type*} (B S : PE α) (K : ℕ) : PE α :=
  if K = 1 then B else mul (pow (mul B (inv S)) K) (pow S K)

lemma eval_Tel {α G : Type*} [Group G] (f : α → G) (B S : PE α) {K : ℕ} (hK : 1 ≤ K) :
    (Tel B S K).eval f =
      ((List.range K).map (fun t => (S.eval f ^ t)⁻¹ * B.eval f * S.eval f ^ t)).prod := by
  rw [telescoping]
  unfold Tel
  split_ifs with h
  · subst h; simp
  · simp [zpow_natCast]

/-! ### Lemma 3.3 (path lemma), in the `ℕ`-model -/

/-- Lemma 3.3: for distinct points `z₀, …, z_k`, `(z₀,z₁)(z₁,z₂)⋯(z_{k-1},z_k) = (z₀,z_k,…,z₁)`. -/
theorem path_lemma {n : ℕ} (z : ℕ → ℕ) (k : ℕ) (hzn : ∀ i ≤ k, z i < n)
    (hz : ∀ i j, i ≤ k → j ≤ k → z i = z j → i = j) :
    nv (((List.range k).map (fun i => tr n (z i) (z (i + 1)))).prod) (z 0) = z k ∧
    (∀ i, 1 ≤ i → i ≤ k →
      nv (((List.range k).map (fun i => tr n (z i) (z (i + 1)))).prod) (z i) = z (i - 1)) ∧
    (∀ j, (∀ i ≤ k, j ≠ z i) →
      nv (((List.range k).map (fun i => tr n (z i) (z (i + 1)))).prod) j = j) := by
  induction k with
  | zero =>
    refine ⟨by simp, fun i h1 h2 => by omega, fun j _ => by simp⟩
  | succ k ih =>
    have hzn' : ∀ i ≤ k, z i < n := fun i hi => hzn i (by omega)
    have hz' : ∀ i j, i ≤ k → j ≤ k → z i = z j → i = j :=
      fun i j hi hj => hz i j (by omega) (by omega)
    obtain ⟨h0, h1, h2⟩ := ih hzn' hz'
    rw [List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, nv_mul]
    have hne : ∀ i ≤ k, z (k + 1) ≠ z i := fun i hi h => by
      have := hz (k+1) i le_rfl (by omega) h; omega
    have htr := nv_tr (n := n) (hzn k (by omega)) (hzn (k + 1) le_rfl)
    refine ⟨?_, ?_, ?_⟩
    · rw [h0, htr]; simp
    · intro i hi1 hi2
      rcases Nat.lt_or_ge i (k + 1) with hik | hik
      · rw [h1 i hi1 (by omega), htr]
        have a1 : z (i - 1) ≠ z k := fun h => by have := hz _ _ (by omega) (by omega) h; omega
        have a2 : z (i - 1) ≠ z (k + 1) := fun h => by
          have := hz _ _ (by omega) le_rfl h; omega
        rw [if_neg a1, if_neg a2]
      · have hik' : i = k + 1 := by omega
        subst hik'
        rw [h2 _ hne, htr]
        rw [if_neg (hne k le_rfl), if_pos rfl]
        simp
    · intro j hj
      rw [h2 j (fun i hi => hj i (by omega)), htr,
        if_neg (hj k (by omega)), if_neg (hj (k+1) le_rfl)]

/-- The product of the transpositions `(i, i+1)`, `0 ≤ i < k`, in the paper's order. -/
def adjProd (n k : ℕ) : Sym n := ((List.range k).map (fun i => tr n i (i + 1))).prod

lemma nv_adjProd {n k : ℕ} (hk : k < n) (j : ℕ) :
    nv (adjProd n k) j = if j = 0 then k else if j ≤ k then j - 1 else j := by
  obtain ⟨h0, h1, h2⟩ := path_lemma (n := n) (fun i => i) k (fun i hi => by simp only; omega)
    (fun i j _ _ h => h)
  unfold adjProd
  split_ifs with hj0 hjk
  · subst hj0; exact h0
  · exact h1 j (by omega) hjk
  · exact h2 j (fun i hi => by omega)

/-! ### Lemma 3.4 -/

/-- The alphabet `{x, y}`. -/
inductive XY | x | y
  deriving DecidableEq

instance : Fintype XY where
  elems := {.x, .y}
  complete := by intro a; cases a <;> simp

/-- The values of `x` and `y` in `S_n`. -/
def xyv (n : ℕ) (hn : 1 < n) : XY → Sym n
  | .x => xs n hn
  | .y => ys n

/-- The letters `x`, `y` as power expressions. -/
def PX : PE XY := gen .x
def PY : PE XY := gen .y

/-- `P_k = (x y⁻¹)^k y^k` (`k ≥ 2`), `P_1 = x`. -/
def Pk (k : ℕ) : PE XY := Tel PX PY k
/-- `ρ_L = P_{L-1}⁻¹`. -/
def rhoPE (L : ℕ) : PE XY := inv (Pk (L - 1))
/-- `σ_k = P_k P_{k-1}⁻¹` (`k ≥ 2`), `σ_1 = x`. -/
def sigPE (k : ℕ) : PE XY := if k = 1 then PX else mul (Pk k) (inv (Pk (k - 1)))

section lemma34
variable {n : ℕ} (hn : 1 < n)

/-- Lemma 3.4(a). -/
theorem xconj (i : ℕ) (hi : i + 1 < n) :
    (ys n ^ i)⁻¹ * xs n hn * ys n ^ i = tr n i (i + 1) := by
  apply sym_ext
  intro j hj
  rw [nv_shift _ i (by omega) _ j hj, nv_tr (by omega) hi, nv_xs]
  · split_ifs <;> omega
  · intro k hk1 hk2
    rw [nv_xs]
    split_ifs <;> omega

/-- Lemma 3.4(b). -/
theorem eval_Pk (k : ℕ) (hk1 : 1 ≤ k) (hk : k < n) :
    (Pk k).eval (xyv n hn) = adjProd n k := by
  rw [Pk, eval_Tel _ _ _ hk1, adjProd]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact xconj hn i (by omega)

lemma nv_Pk (k : ℕ) (hk1 : 1 ≤ k) (hk : k < n) (j : ℕ) :
    nv ((Pk k).eval (xyv n hn)) j = if j = 0 then k else if j ≤ k then j - 1 else j := by
  rw [eval_Pk hn k hk1 hk, nv_adjProd hk]

/-- Lemma 3.4(c): `ρ_L = (0, 1, …, L-1)`. -/
theorem nv_rho (L : ℕ) (hL : 2 ≤ L) (hLn : L ≤ n) (j : ℕ) :
    nv ((rhoPE L).eval (xyv n hn)) j = if j + 1 < L then j + 1 else if j + 1 = L then 0 else j := by
  simp only [rhoPE, eval_inv]
  rw [nv_inv_eq_iff, nv_Pk hn (L - 1) (by omega) (by omega)]
  by_cases h1 : j + 1 < L
  · rw [if_pos h1, if_neg (by omega), if_pos (by omega)]; omega
  · by_cases h2 : j + 1 = L
    · rw [if_neg h1, if_pos h2, if_pos rfl]; omega
    · rw [if_neg h1, if_neg h2]
      by_cases h3 : j = 0
      · omega
      · rw [if_neg h3, if_neg (by omega)]

/-- Lemma 3.4(d): `σ_k = (0, k)`. -/
theorem nv_sig (k : ℕ) (hk1 : 1 ≤ k) (hk : k < n) (j : ℕ) :
    nv ((sigPE k).eval (xyv n hn)) j = if j = 0 then k else if j = k then 0 else j := by
  by_cases h1 : k = 1
  · subst h1
    have e : (sigPE 1).eval (xyv n hn) = xs n hn := by simp [sigPE, PX, xyv]
    rw [e, nv_xs]
  · have e : (sigPE k).eval (xyv n hn) =
        (Pk k).eval (xyv n hn) * ((Pk (k - 1)).eval (xyv n hn))⁻¹ := by
      simp [sigPE, h1]
    rw [e, nv_mul, nv_Pk hn k hk1 hk]
    have key : ∀ m, nv ((Pk (k - 1)).eval (xyv n hn))⁻¹ m =
        if m = k - 1 then 0 else if m < k - 1 then m + 1 else m := by
      intro m
      rw [nv_inv_eq_iff, nv_Pk hn (k - 1) (by omega) (by omega)]
      by_cases hm1 : m = k - 1
      · rw [if_pos hm1, if_pos rfl]; omega
      · rw [if_neg hm1]
        by_cases hm2 : m < k - 1
        · rw [if_pos hm2, if_neg (by omega), if_pos (by omega)]; omega
        · rw [if_neg hm2]
          by_cases hm3 : m = 0
          · omega
          · rw [if_neg hm3, if_neg (by omega)]
    rw [key]
    split_ifs <;> omega

end lemma34

end SnPres
