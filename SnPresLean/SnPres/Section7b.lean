/-
Section 7, part 2: Setup 7.2 and the relators (G1)–(G4) of Theorem 7.3; Step 1 (they hold).
-/
import SnPres.Section7a

namespace SnPres

open PE SL2 ASL2

/-! ### Relators as lists (for counting) -/

section lists
variable {α : Type*}

/-- the ten relators of Corollary 5.4, as a list -/
def lutListOf (L U T : PE α) (p lam mu : ℕ) : List (PE α) :=
  [RA1 L p, RA2 L (PCe L U), RA3 L (PCe L U) p, RA4 (PCe L U), RA5 T p,
   RA6 T U, RA7 T (PEe L U T), RA8 L T (PEe L U T), RA9 (PDe L U lam mu) T lam, R10 L U]

lemma lutRelsOf_eq (L U T : PE α) (p lam mu : ℕ) :
    lutRelsOf L U T p lam mu = {E | E ∈ lutListOf L U T p lam mu} := by
  ext E; simp [lutRelsOf, lutListOf]

end lists

/-- the 17 relators (R2)–(R6) of Theorem 6.3 -/
def sixRest (p : ℕ) : List (PE Six) :=
  [pow (gen .X0) 3, pow (gen .X1) 3,
   comm (gen .X0) (gen .L), comm (gen .X0) (gen .U), comm (gen .X1) (gen .L),
   comm (gen .X1) (gen .U),
   pow (mul (gen .X0) (conj (gen .X0) (gen .T))) 2,
   pow (mul (gen .X1) (conj (gen .X1) (gen .T))) 2,
   pow (mul (gen .X0) (gen .X1)) 2,
   pow (mul (gen .X0) (conj (gen .X1) (gen .T))) 2,
   pow (mul (mul (gen .L) (gen .T)) (sixW p)) ((p * p + 1 : ℕ) : ℤ),
   pow (gen .Q) 2, comm (gen .Q) (gen .L), comm (gen .Q) (gen .U), comm (gen .Q) (gen .T),
   pow (mul (gen .Q) (gen .X0)) 2, pow (mul (gen .Q) (gen .X1)) 2]

/-- the 27 relators of Theorem 6.3, as a list -/
def sixList (p lam mu : ℕ) : List (PE Six) :=
  (lutListOf (gen LUT.L) (gen .U) (gen .T) p lam mu).map (PE.map lutToSix) ++ sixRest p

lemma sixList_length (p lam mu : ℕ) : (sixList p lam mu).length = 27 := by
  simp [sixList, lutListOf, sixRest]

lemma sixRels_eq (p lam mu : ℕ) : sixRels p lam mu = {E | E ∈ sixList p lam mu} := by
  ext E
  simp only [sixRels, lutRels, lutRelsOf_eq, sixList, sixRest, Set.mem_union, Set.mem_image,
    Set.mem_setOf_eq, List.mem_append, List.mem_map]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false]

/-! ### Setup 7.2 -/

/-- The alphabet `𝒜 = {x, y} ⊔ {G⁽¹⁾ : G ∈ L,U,T,X₀,X₁,Q} ⊔ {G⁽²⁾}`. -/
abbrev GA := XY ⊕ (Six ⊕ Six)

/-- `G ↦ G⁽¹⁾` -/
def gi1 (G : Six) : GA := Sum.inr (Sum.inl G)
/-- `G ↦ G⁽²⁾` -/
def gi2 (G : Six) : GA := Sum.inr (Sum.inr G)

section pes
variable (p : ℕ)

/-- `Ξ⁽ᵏ⁾` -/
def XiK (ι : Six → GA) : PE GA := XiPE.map ι
/-- `Υ⁽ᵏ⁾` -/
def UpsK (ι : Six → GA) : PE GA := (UpsPE p).map ι
/-- a PE over `{x, y}` with `x ↦ Ξ⁽ᵏ⁾`, `y ↦ Υ⁽ᵏ⁾` -/
def onXY (ι : Six → GA) (F : PE XY) : PE GA :=
  F.subst (fun c => match c with | .x => XiK ι | .y => UpsK p ι)
/-- `ρ⁽ᵏ⁾_m = ((Ξ⁽ᵏ⁾ (Υ⁽ᵏ⁾)⁻¹)^{m-1} (Υ⁽ᵏ⁾)^{m-1})⁻¹` -/
def rhoK (ι : Six → GA) (m : ℕ) : PE GA := onXY p ι (rhoPE m)
/-- `F^{(Υ⁽ᵏ⁾)^r}` -/
def shUps (ι : Six → GA) (F : PE GA) (r : ℕ) : PE GA := conj F (pow (UpsK p ι) r)

end pes

section glue
variable (n p lam mu : ℕ)

/-- `N = 2q + 2`, `s = n - N`, `k = 2N - n` -/
abbrev sS : ℕ := n - NN p
abbrev kK : ℕ := 2 * NN p - n

/-- `ς⁽¹⁾ = (Ξ⁽¹⁾)^{(Υ⁽¹⁾)^s}` -/
def vs1 : PE GA := shUps p gi1 (XiK gi1) (sS n p)
/-- `γ⁽¹⁾ = (ρ⁽¹⁾_k)^{(Υ⁽¹⁾)^s}` -/
def ga1 : PE GA := shUps p gi1 (rhoK p gi1 (kK n p)) (sS n p)
/-- `ς⁽²⁾ = Ξ⁽²⁾` -/
def vs2 : PE GA := XiK gi2
/-- `γ⁽²⁾ = ρ⁽²⁾_k` -/
def ga2 : PE GA := rhoK p gi2 (kK n p)
/-- the elements of `Λ` -/
def LamList : List (PE GA) :=
  if sS n p = 1 then [XiK gi1] else [XiK gi1, rhoK p gi1 (sS n p + 1)]
/-- the first element of `ℛ` -/
def Rr1 : PE GA := shUps p gi2 (XiK gi2) (NN p - 1 - sS n p)
/-- the second element of `ℛ` (if `s ≥ 2`) -/
def Rr2 : PE GA := shUps p gi2 (rhoK p gi2 (sS n p + 1)) (NN p - 1 - sS n p)
/-- the elements of `ℛ` -/
def RList : List (PE GA) := if sS n p = 1 then [Rr1 n p] else [Rr1 n p, Rr2 n p]
/-- `r*`, the last element of `ℛ` -/
def rStar : PE GA := if sS n p = 1 then Rr1 n p else Rr2 n p

/-- **The relators of Theorem 7.3**: (G1) `Π⁽¹⁾, Π⁽²⁾`; (G2) `ς⁽¹⁾(ς⁽²⁾)⁻¹, γ⁽¹⁾(γ⁽²⁾)⁻¹`;
(G3) `[ℓ, r]` for `ℓ ∈ Λ`, `r ∈ ℛ`; (G4) `x (Ξ⁽¹⁾)⁻¹`, `y (r* Υ⁽¹⁾)⁻¹`. -/
def gluList : List (PE GA) :=
  (sixList p lam mu).map (PE.map gi1) ++ (sixList p lam mu).map (PE.map gi2) ++
  [mul (vs1 n p) (inv (vs2)), mul (ga1 n p) (inv (ga2 n p))] ++
  (LamList n p).flatMap (fun l => (RList n p).map (fun r => comm l r)) ++
  [mul (gen (Sum.inl .x)) (inv (XiK gi1)),
   mul (gen (Sum.inl .y)) (inv (mul (rStar n p) (UpsK p gi1)))]

lemma gluList_length : (gluList n p lam mu).length ≤ 62 := by
  unfold gluList LamList RList
  split_ifs <;> simp [sixList_length]

def gluRels : Set (PE GA) := {E | E ∈ gluList n p lam mu}

end glue

/-! ### The values -/

variable {p : ℕ} [Fact p.Prime]

/-- `φ : 𝒜 → S_n`: `x ↦ x`, `y ↦ y`, `G⁽¹⁾ ↦ G`, `G⁽²⁾ ↦ G^{y^s}` -/
def gluVal (n : ℕ) (hn : NN p ≤ n) : GA → Sym n
  | Sum.inl .x => xs n (by have := NN_eq (p := p); omega)
  | Sum.inl .y => ys n
  | Sum.inr (Sum.inl G) => embAt (NN p) n 0 (by omega) (sixVal G)
  | Sum.inr (Sum.inr G) =>
      (ys n ^ (n - NN p))⁻¹ * embAt (NN p) n 0 (by omega) (sixVal G) * ys n ^ (n - NN p)

section values
variable {n : ℕ} (hn : NN p ≤ n)

lemma gluVal_gi1 : gluVal n hn ∘ gi1 = embAt (NN p) n 0 (by omega) ∘ sixVal (p := p) := by
  funext G; rfl

lemma gluVal_gi2 :
    gluVal n hn ∘ gi2 = embAt (NN p) n (n - NN p) (by omega) ∘ sixVal (p := p) := by
  funext G
  show (ys n ^ (n - NN p))⁻¹ * embAt (NN p) n 0 _ (sixVal G) * ys n ^ (n - NN p) = _
  rw [conj_ys_embAt _ _ (by have := NN_eq (p := p); omega)]
  rfl

/-- the value of a PE over the six letters, written in the `κ`-th copy -/
lemma eval_map_gi1 (F : PE Six) :
    (F.map gi1).eval (gluVal n hn) = embAt (NN p) n 0 (by omega) (F.eval sixVal) := by
  rw [eval_map, gluVal_gi1, eval_hom]
lemma eval_map_gi2 (F : PE Six) :
    (F.map gi2).eval (gluVal n hn) = embAt (NN p) n (n - NN p) (by omega) (F.eval sixVal) := by
  rw [eval_map, gluVal_gi2, eval_hom]

/-- the value of a PE over `{x, y}`, written in `Ξ⁽ᵏ⁾, Υ⁽ᵏ⁾` -/
lemma eval_onXY (h5 : 5 ≤ p) (ι : Six → GA) (E : Sym (NN p) →* Sym n)
    (hι : ∀ F : PE Six, (F.map ι).eval (gluVal n hn) = E (F.eval sixVal)) (F : PE XY) :
    (onXY p ι F).eval (gluVal n hn) =
      E (F.eval (xyv (NN p) (by have := NN_eq (p := p); omega))) := by
  unfold onXY
  rw [eval_subst, ← eval_hom]
  apply eval_congr
  intro c
  cases c
  · show (XiK ι).eval _ = E (xs (NN p) _)
    rw [XiK, hι, (prop_6_4 h5).1]
  · show (UpsK p ι).eval _ = E (ys (NN p))
    rw [UpsK, hι, (prop_6_4 h5).2]

end values

end SnPres
