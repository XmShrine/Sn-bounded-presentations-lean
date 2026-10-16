/-
The four classical results cited in the paper, stated as axioms.

Each axiom is a *weakening* of the cited theorem: we only assume what the proof uses, namely
that a certain presented group is finite of order at most a given number (Sunday, Carmichael,
Moore), and the existence of primes in short intervals (Nagura).  The axioms are stated with
Mathlib's `FreeGroup`/`PresentedGroup` only, independently of the rest of the development.
-/
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.SetTheory.Cardinal.Finite

namespace SnPres.Classical

open FreeGroup

/-- Sunday's relators on `a = of 0`, `c = of 1`:
`a^p`, `a c a c a c⁻¹`, `(a^h c a^4 c)^2` with `h = (p+1)/2`. -/
def sundayRels (p : ℕ) : Set (FreeGroup (Fin 2)) :=
  {of 0 ^ p, of 0 * of 1 * of 0 * of 1 * of 0 * (of 1)⁻¹,
    (of 0 ^ ((p + 1) / 2) * of 1 * of 0 ^ 4 * of 1) ^ 2}

/-- **Sunday (1972)** [Canad. J. Math. 24, 1129–1131]; see also [BCLO, Prop. 3.3]:
for an odd prime `p`, `⟨a, c | a^p, a c a c a c⁻¹, (a^h c a^4 c)^2⟩ ≅ PSL(2,p)`, a group of order
`p(p²-1)/2`.  We assume only (and only for `p ≥ 5`) that this group is finite of order at most
`p(p²-1)/2`. -/
axiom sunday_bound (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    Finite (PresentedGroup (sundayRels p)) ∧
      Nat.card (PresentedGroup (sundayRels p)) ≤ p * (p ^ 2 - 1) / 2

/-- Carmichael's relators on `x_0, …, x_{M-1}`: `x_i^3` and `(x_i x_j)^2` for `i < j`. -/
def carmichaelRels (M : ℕ) : Set (FreeGroup (Fin M)) :=
  {r | ∃ i : Fin M, r = of i ^ 3} ∪ {r | ∃ i j : Fin M, i < j ∧ r = (of i * of j) ^ 2}

/-- **Carmichael (1923)** [Quart. J. Pure Appl. Math. 49]; see [Coxeter–Moser, §6.3]: for `M ≥ 1`
the group `⟨x_1, …, x_M | x_i^3, (x_i x_j)^2⟩` is isomorphic to `A_{M+2}`.  We assume only that it
is finite of order at most `(M+2)!/2`. -/
axiom carmichael_bound (M : ℕ) (hM : 1 ≤ M) :
    Finite (PresentedGroup (carmichaelRels M)) ∧
      Nat.card (PresentedGroup (carmichaelRels M)) ≤ (M + 2).factorial / 2

/-- Moore's (Coxeter) relators on `τ_0, …, τ_{n-2}`: `τ_i^2`, `(τ_i τ_{i+1})^3`, and
`(τ_i τ_j)^2` for `j ≥ i + 2`. -/
def mooreRels (n : ℕ) : Set (FreeGroup (Fin (n - 1))) :=
  {r | ∃ i : Fin (n - 1), r = of i ^ 2} ∪
  {r | ∃ i j : Fin (n - 1), j.val = i.val + 1 ∧ r = (of i * of j) ^ 3} ∪
  {r | ∃ i j : Fin (n - 1), i.val + 2 ≤ j.val ∧ r = (of i * of j) ^ 2}

/-- **Moore (1897)** [Proc. London Math. Soc. 28]; see [Coxeter–Moser, §6.2]: these relations
present `S_n`.  We assume only that the group is finite of order at most `n!`. -/
axiom moore_bound (n : ℕ) (hn : 2 ≤ n) :
    Finite (PresentedGroup (mooreRels n)) ∧ Nat.card (PresentedGroup (mooreRels n)) ≤ n.factorial

/-- **Nagura (1952)** [Proc. Japan Acad. 28, 177–181]: for every real `ξ ≥ 25` there is a prime in
`(ξ, 6ξ/5)`.  We use it only for integers `ξ = m`. -/
axiom nagura (m : ℕ) (hm : 25 ≤ m) : ∃ q, q.Prime ∧ m < q ∧ 5 * q < 6 * m

end SnPres.Classical
