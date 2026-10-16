# SnPres — a Lean 4 formalization

This repository formalizes the note

> *Bounded presentations of the symmetric groups on their standard generators with bit-length O(log n)* (October 2026)

in Lean 4 with Mathlib. Every argument of the note that the main theorem depends on is proved in Lean, without `sorry`. The four classical results the note cites are stated as axioms in a weakened form (see below).

## Versions and build

* Lean `v4.24.0` (see `lean-toolchain`)
* Mathlib `v4.24.0`, commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (see `lakefile.toml`)

```
lake exe cache get      # optional: download the Mathlib build
lake build              # builds the library SnPres
lake env lean Check.lean
```

`Check.lean` prints the main statements and the axioms they depend on. `#print axioms SnPres.main_theorem` gives `propext`, `Classical.choice`, `Quot.sound` and the four axioms `SnPres.Classical.{sunday_bound, carmichael_bound, moore_bound, nagura}`. Nothing else is assumed.

## Main results

All names are in the namespace `SnPres`.

* `main_theorem`: there are constants `r₀`, `c₀` such that for every `n ≥ 2` there is a finite set `R` of power expressions over `{x, y}` with
  `IsPresentation (xyv n _) R`, all of whose elements are genuine power expressions (`PE.WF`), with `R.card ≤ r₀` and `presLength R ≤ c₀ * Nat.log 2 n`.
* `main_theorem_62`: for `n ≥ 245` the same with `R.card ≤ 62`. The proof gives `c₀ = cLarge = 269991154`, and every relator has length at most `486816 + 773576 (⌊log₂ n⌋ + 4)` (`main_large`).
* `main_theorem_mathlib`, `main_theorem_mathlib_62`: the same statements for Mathlib's `Equiv.Perm (Fin n)` (composition `σ * τ = σ ∘ τ`) on the generators `Equiv.swap 0 1` and `finRotate n`; the relators are read backwards (`PE.rev`), which does not change their lengths.

`IsPresentation φ R` means that every relator has value `1` and that the induced homomorphism `PresentedGroup (toFreeGroup '' R) → G` is bijective (Definition 2.4). `presLength R = |{x,y}| + ∑_{E ∈ R} ℓ(E)`, where `ℓ` is the length of Definition 2.1 (`PE.length`, binary exponents).

## Conventions

As in the note, permutations act on the right: `Sym n := (Equiv.Perm (Fin n))ᵐᵒᵖ`, so `g * h` means "first `g`, then `h`". The generators are `x = (0,1)` (`xs`) and `y = (0,1,…,n-1)` (`ys`, `i ↦ i+1 mod n`); under `i ↦ i + 1` these are `(1,2)` and `(1,2,…,n)`. Points are handled through `nv g i : ℕ` (the image of `i`, and `i` itself for `i ≥ n`). Row vectors and affine maps follow the note: `α_{M,w} α_{M',w'} = α_{MM', wM'+w'}`.

## The axioms (`SnPres/Axioms.lean`)

Each axiom is weaker than the cited theorem: it only asserts what the proofs use.

| axiom | cited result | what is assumed |
|---|---|---|
| `sunday_bound p` (`p` prime, `p ≥ 5`) | Sunday 1972; BCLO Prop. 3.3: `⟨a,c ∣ a^p, acacac⁻¹, (a^h c a^4 c)²⟩ ≅ PSL(2,p)` | the group is finite of order `≤ p(p²−1)/2` |
| `carmichael_bound M` (`M ≥ 1`) | Carmichael 1923: `⟨x₁…x_M ∣ x_i³, (x_i x_j)²⟩ ≅ A_{M+2}` | finite of order `≤ (M+2)!/2` |
| `moore_bound n` (`n ≥ 2`) | Moore 1897: the Coxeter presentation of `S_n` | finite of order `≤ n!` |
| `nagura m` (`m ≥ 25`) | Nagura 1952: a prime in `(ξ, 6ξ/5)` for real `ξ ≥ 25` | the case of integers `ξ = m` |

`check_axioms.py` checks these exact relator sets numerically (coset enumeration: Sunday for `p ≤ 17`, Carmichael for `M ≤ 5`, Moore for `n ≤ 7`; Nagura for `m ≤ 2·10⁵`). This is a sanity check, not part of the proof.

## Correspondence with the note

| note | Lean (file: names) |
|---|---|
| Def. 2.1, ℓ, occ, pw, ex | `PE.lean`: `PE`, `PE.length`, `PE.occ`, `PE.pw`, `PE.ex`, `PE.WF`, `PE.normalize` |
| Lemma 2.2; eq. (2) | `PE.length_le`; `PE.occ_subst_le`, `PE.pw_subst_le`, `PE.ex_subst_le` |
| Def. 2.4 and the remark after it | `IsPresentation`, `isPresentation_of_card_le` |
| Lemma 2.5 | `elim_generators` |
| Lemmas 3.1–3.4 | `Section3.lean`: `telescoping`, `powexp`, `path_lemma`, `xconj`, `eval_Pk`, `nv_rho`, `nv_sig`, `nv_shift` |
| Setup 4.1 | `Theta.lean`: `iota0`, `iota1`, `theta`, `theta_injective` |
| Def. 4.2, Prop. 4.3 | `Section4.lean`: `PB` … `WQ`, `acts_B` … `acts_L`, `acts_U`, `acts_T`, `acts_X0`, `acts_X1`, `eval_Q`; `Theta.lean`: `thetaF_ML`, `thetaF_MU`, `thetaF_te1`, `thetaF_te2`; `Section8a.lean`: `eval_WG` |
| eq. (3), Lemma 4.4 | `Section5.lean`: `MC_eq`, `MU_eq`, `D_eq`; `Section5c.lean`: `eval_PCe_lutVal`; `Section6d.lean`: `eval_PEe_lutVal` |
| Prop. 5.2 | `Section5.lean`: `prop_5_2` |
| Prop. 5.3 | `Section5b.lean`: `prop_5_3` |
| Cor. 5.4 | `Section5c.lean`: `cor_5_4` |
| Lemma 5.5 | replaced by `normal_eq_top_of_mem` (Lemma 5.5′, see below) |
| Lemma 6.2 | `Section6a.lean`: `lemma_6_2a`, `lemma_6_2b` |
| Thm. 6.3 | `Section6b.lean`: `sixRels`, `sixVal`, `sixRels_hold` (Step 1); `Section6d.lean`: `thm_6_3` |
| Prop. 6.4 | `Section6c.lean`: `XiPE`, `UpsPE`, `prop_6_4`; `Bounds.lean`: `bnd_XiPE`, `bnd_UpsPE` |
| Lemma 7.1 | `Section7a.lean`: `lemma_7_1` |
| Setup 7.2, Thm. 7.3 | `Section7b.lean`: `gluList`, `gluVal`; `Section7c.lean`: `glu_rels_hold`; `Section7d.lean`: `thm_7_3` |
| Proof of Thm. 1.1 | `Section8a.lean`: `isPresentation_main`; `Bounds.lean`: `mainRels_length_le`; `Main.lean`: `exists_finite_presentation`, `main_theorem`, `main_theorem_62` |

## Where the proofs differ from the note

The statements are those of the note; in a few places the route of the proof differs.

1. **Lemma 5.5** (the list of all normal subgroups of `ASL(2,p)`, whose proof uses the simplicity of `PSL(2,p)`) is not formalized. Step 5 of Theorem 6.3 only needs: *a normal subgroup of `ASL(2,p)` containing `α_{M_L,e₁}` is everything*. This is `normal_eq_top_of_mem`, proved directly (for every prime `p`).
2. **Corollary 5.4** is derived from Proposition 5.3 directly (the group presented by the ten relators is a quotient of `ASL(2,p)`), instead of by a Tietze transformation and Lemma 2.5.
3. **Lemma 6.2(b)** is proved for cycles `C_i` of equal length `ℓ`, the only case used: then `gπ` maps each point to the next point of one of two explicit cycles of length `1 + ℓr/2`, and `(gπ)^{1+ℓr/2} = 1`.
4. **Theorem 6.3, Steps 6–7.** The order bound `|Γ| ≤ 2|K| ≤ N!` is the note's. That `L, U, T, X₀, X₁, Q` generate `S_N` is obtained from Proposition 6.4 (they produce `(0,1)` and `(0,1,…,N−1)`), instead of from the 3-cycles `(ω,⋆,∞)`. The side claim of Step 6 that `θ(α)` is even (so that `Γ_A ≅ A_N`) is not needed and not formalized.
5. **Uniformity** (Definition 2.3, Propositions 4.3 and 6.4, Theorem 7.3) is proved with explicit bounds on `occ`, `pw` and `ex` (`Bounds.lean`). The constants are crude upper bounds; the lengths computed numerically in Section 8 of the note are not part of the proof and are not formalized.
6. **Small `n`** (`n < 245`): the note's remark that each `S_n` has some finite presentation on `x, y` is proved with Mathlib's Schreier lemma (`exists_finite_presentation`).
7. The primitive root `λ` and `μ = λ⁻¹ mod p` are taken in `[1, p−1]` using that `(ℤ/p)ˣ` is cyclic.

No mathematical error in the note was found by the formalization.
