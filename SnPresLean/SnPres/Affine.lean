/-
The groups `SL(2,p)` and `ASL(2,p)` (concrete models), with the conventions of the paper:
vectors of `𝔽_p²` are row vectors, matrices act on the right (`v ↦ v M`), and affine maps are
composed like permutations (first the left factor): `α_{M,w} α_{M',w'} = α_{MM', wM'+w'}`.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.SetTheory.Cardinal.Finite

namespace SnPres

variable (p : ℕ)

/-- Row vectors `𝔽_p²`. -/
abbrev Vec := ZMod p × ZMod p

/-- `SL(2,p)`: the matrix `[[a, b], [c, d]]` with `a d - b c = 1`. -/
@[ext] structure SL2 where
  a : ZMod p
  b : ZMod p
  c : ZMod p
  d : ZMod p
  det : a * d - b * c = 1

namespace SL2
variable {p}

instance : Mul (SL2 p) :=
  ⟨fun M N => ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d, M.c * N.a + M.d * N.c,
    M.c * N.b + M.d * N.d, by linear_combination (N.a * N.d - N.b * N.c) * M.det + N.det⟩⟩

instance : One (SL2 p) := ⟨⟨1, 0, 0, 1, by ring⟩⟩

instance : Inv (SL2 p) := ⟨fun M => ⟨M.d, -M.b, -M.c, M.a, by linear_combination M.det⟩⟩

@[simp] lemma mul_a (M N : SL2 p) : (M * N).a = M.a * N.a + M.b * N.c := rfl
@[simp] lemma mul_b (M N : SL2 p) : (M * N).b = M.a * N.b + M.b * N.d := rfl
@[simp] lemma mul_c (M N : SL2 p) : (M * N).c = M.c * N.a + M.d * N.c := rfl
@[simp] lemma mul_d (M N : SL2 p) : (M * N).d = M.c * N.b + M.d * N.d := rfl
@[simp] lemma one_a : (1 : SL2 p).a = 1 := rfl
@[simp] lemma one_b : (1 : SL2 p).b = 0 := rfl
@[simp] lemma one_c : (1 : SL2 p).c = 0 := rfl
@[simp] lemma one_d : (1 : SL2 p).d = 1 := rfl
@[simp] lemma inv_a (M : SL2 p) : M⁻¹.a = M.d := rfl
@[simp] lemma inv_b (M : SL2 p) : M⁻¹.b = -M.b := rfl
@[simp] lemma inv_c (M : SL2 p) : M⁻¹.c = -M.c := rfl
@[simp] lemma inv_d (M : SL2 p) : M⁻¹.d = M.a := rfl

instance : Group (SL2 p) where
  mul_assoc M N P := by ext <;> simp <;> ring
  one_mul M := by ext <;> simp
  mul_one M := by ext <;> simp
  inv_mul_cancel M := by
    ext <;> simp
    · linear_combination M.det
    · ring
    · ring
    · linear_combination M.det

/-- `v M` for a row vector `v`. -/
def vecMul (v : Vec p) (M : SL2 p) : Vec p := (v.1 * M.a + v.2 * M.c, v.1 * M.b + v.2 * M.d)

@[simp] lemma vecMul_fst (v : Vec p) (M : SL2 p) : (vecMul v M).1 = v.1 * M.a + v.2 * M.c := rfl
@[simp] lemma vecMul_snd (v : Vec p) (M : SL2 p) : (vecMul v M).2 = v.1 * M.b + v.2 * M.d := rfl

lemma vecMul_mul (v : Vec p) (M N : SL2 p) : vecMul v (M * N) = vecMul (vecMul v M) N := by
  ext <;> simp <;> ring
@[simp] lemma vecMul_one (v : Vec p) : vecMul v 1 = v := by ext <;> simp
lemma vecMul_add (v w : Vec p) (M : SL2 p) : vecMul (v + w) M = vecMul v M + vecMul w M := by
  ext <;> simp <;> ring
lemma vecMul_neg (v : Vec p) (M : SL2 p) : vecMul (-v) M = -vecMul v M := by
  ext <;> simp <;> ring
@[simp] lemma vecMul_zero (M : SL2 p) : vecMul 0 M = 0 := by ext <;> simp
lemma vecMul_smul (k : ZMod p) (v : Vec p) (M : SL2 p) : vecMul (k • v) M = k • vecMul v M := by
  ext <;> simp <;> ring

/-- `M_L = [[1,1],[0,1]]`. -/
def ML : SL2 p := ⟨1, 1, 0, 1, by ring⟩
/-- `M_U = [[1,0],[1,1]]`. -/
def MU : SL2 p := ⟨1, 0, 1, 1, by ring⟩
/-- `M_C = [[0,-1],[1,0]]`. -/
def MC : SL2 p := ⟨0, -1, 1, 0, by ring⟩
/-- `[[1,x],[0,1]]`. -/
def Lx (x : ZMod p) : SL2 p := ⟨1, x, 0, 1, by ring⟩
/-- `[[1,0],[y,1]]`. -/
def Uy (y : ZMod p) : SL2 p := ⟨1, 0, y, 1, by ring⟩
/-- `-I`. -/
def negI : SL2 p := ⟨-1, 0, 0, -1, by ring⟩

lemma ML_pow (k : ℕ) : (ML : SL2 p) ^ k = Lx (k : ZMod p) := by
  induction k with
  | zero => ext <;> simp [Lx]
  | succ k ih => rw [pow_succ, ih]; ext <;> simp [Lx, ML] <;> ring
lemma MU_pow (k : ℕ) : (MU : SL2 p) ^ k = Uy (k : ZMod p) := by
  induction k with
  | zero => ext <;> simp [Uy]
  | succ k ih => rw [pow_succ, ih]; ext <;> simp [Uy, MU] <;> ring
lemma Lx_inv (x : ZMod p) : (Lx x)⁻¹ = Lx (-x) := by ext <;> simp [Lx]
lemma Uy_inv (y : ZMod p) : (Uy y)⁻¹ = Uy (-y) := by ext <;> simp [Uy]

end SL2

/-- `ASL(2,p)`: the affine maps `α_{M,w} : v ↦ v M + w`. -/
@[ext] structure ASL2 where
  M : SL2 p
  w : Vec p

namespace ASL2
variable {p}
open SL2

instance : Mul (ASL2 p) := ⟨fun α β => ⟨α.M * β.M, vecMul α.w β.M + β.w⟩⟩
instance : One (ASL2 p) := ⟨⟨1, 0⟩⟩
instance : Inv (ASL2 p) := ⟨fun α => ⟨α.M⁻¹, -vecMul α.w α.M⁻¹⟩⟩

@[simp] lemma mul_M (α β : ASL2 p) : (α * β).M = α.M * β.M := rfl
@[simp] lemma mul_w (α β : ASL2 p) : (α * β).w = vecMul α.w β.M + β.w := rfl
@[simp] lemma one_M : (1 : ASL2 p).M = 1 := rfl
@[simp] lemma one_w : (1 : ASL2 p).w = 0 := rfl
@[simp] lemma inv_M (α : ASL2 p) : α⁻¹.M = α.M⁻¹ := rfl
@[simp] lemma inv_w (α : ASL2 p) : α⁻¹.w = -vecMul α.w α.M⁻¹ := rfl

instance : Group (ASL2 p) where
  mul_assoc α β γ := by
    ext1
    · simp [mul_assoc]
    · simp only [mul_w, mul_M, vecMul_mul, vecMul_add]; abel
  one_mul α := by ext1 <;> simp
  mul_one α := by ext1 <;> simp
  inv_mul_cancel α := by
    ext1
    · simp
    · simp only [mul_w, inv_w, inv_M, one_w, vecMul_neg, ← vecMul_mul, inv_mul_cancel,
        vecMul_one, neg_add_cancel]

/-- The (right) action `v ↦ v^α = v M + w`. -/
def act (v : Vec p) (α : ASL2 p) : Vec p := vecMul v α.M + α.w

lemma act_mul (v : Vec p) (α β : ASL2 p) : act v (α * β) = act (act v α) β := by
  simp only [act, mul_M, mul_w, vecMul_mul, vecMul_add]; abel
@[simp] lemma act_one (v : Vec p) : act v (1 : ASL2 p) = v := by simp [act]

/-- The linear map `α_{M,0}`. -/
def lin (M : SL2 p) : ASL2 p := ⟨M, 0⟩
/-- The translation `t_w = α_{I,w}`. -/
def tr (w : Vec p) : ASL2 p := ⟨1, w⟩

@[simp] lemma act_lin (v : Vec p) (M : SL2 p) : act v (lin M) = vecMul v M := by simp [act, lin]
@[simp] lemma act_tr (v w : Vec p) : act v (tr w) = v + w := by simp [act, tr]

lemma lin_mul (M N : SL2 p) : lin M * lin N = lin (M * N) := by ext1 <;> simp [lin]
lemma lin_inv (M : SL2 p) : (lin M)⁻¹ = lin M⁻¹ := by ext1 <;> simp [lin]
lemma lin_one : lin (1 : SL2 p) = 1 := rfl
lemma tr_mul (v w : Vec p) : tr v * tr w = tr (v + w) := by ext1 <;> simp [tr]
lemma tr_inv (v : Vec p) : (tr v)⁻¹ = tr (-v) := by ext1 <;> simp [tr]
lemma tr_zero : tr (0 : Vec p) = 1 := rfl
lemma lin_mul_tr (M : SL2 p) (w : Vec p) : lin M * tr w = ⟨M, w⟩ := by ext1 <;> simp [lin, tr]

/-- Equation (1): `α_{M,w}⁻¹ t_u α_{M,w} = t_{uM}`. -/
lemma conj_tr (α : ASL2 p) (u : Vec p) : α⁻¹ * tr u * α = tr (vecMul u α.M) := by
  ext1
  · simp [tr]
  · simp only [mul_w, inv_w, tr, mul_M, inv_M, one_w, SL2.vecMul_add, SL2.vecMul_neg,
      ← SL2.vecMul_mul, mul_one, inv_mul_cancel, vecMul_one]
    abel

lemma tr_pow (v : Vec p) (k : ℕ) : tr v ^ k = tr ((k : ZMod p) * v.1, (k : ZMod p) * v.2) := by
  induction k with
  | zero => ext1 <;> simp [tr]; rfl
  | succ k ih => rw [pow_succ, ih, tr_mul]; congr 1; ext <;> simp <;> ring

end ASL2

end SnPres
