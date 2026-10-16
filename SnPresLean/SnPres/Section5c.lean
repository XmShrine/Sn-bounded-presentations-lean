/-
Section 5 (end): Corollary 5.4 and Lemma 5.5'.

* `cor_5_4`: the ten relators on `L, U, T` present `ASL(2,p)`.
  (The paper derives this from Proposition 5.3 by a Tietze transformation and Lemma 2.5; we prove
  the statement directly from Proposition 5.3: the presented group is a quotient of `ASL(2,p)`.)
* `normal_eq_top_of_mem` (Lemma 5.5'): a normal subgroup of `ASL(2,p)` containing
  `α_{M_L,e₁}` is all of `ASL(2,p)`.  This replaces the paper's Lemma 5.5 (the list of all
  normal subgroups, whose proof uses the simplicity of `PSL(2,p)`); Step 5 of Theorem 6.3 only
  uses this weaker statement, which we prove directly (for every prime `p`).
-/
import SnPres.Section5b

namespace SnPres

open PE SL2 ASL2

/-! ### The PEs `C, E, D` of (5) and the ten relators of Corollary 5.4 -/

section LUTdefs
variable {α : Type*}

/-- `C = L⁻¹ U L⁻¹` -/
def PCe (L U : PE α) : PE α := mul (mul (inv L) U) (inv L)
/-- `E = C T C⁻¹` -/
def PEe (L U T : PE α) : PE α := Peps (PCe L U) T
/-- `D = L^λ U^{-μ} L^λ C` -/
def PDe (L U : PE α) (lam mu : ℕ) : PE α := Pd L U (PCe L U) lam mu
/-- the tenth relator `U⁻¹ L U⁻¹ L⁻¹ U L⁻¹` -/
def R10 (L U : PE α) : PE α :=
  mul (mul (mul (mul (mul (inv U) L) (inv U)) (inv L)) U) (inv L)

/-- The ten relators of Corollary 5.4, written in PEs `L, U, T`:
`L^p, L C L C L C⁻¹, (L^h C L^4 C)^2 C^{-2}, C^4, T^p, [T,U], [T,E], T E L⁻¹ T⁻¹ L,
D⁻¹ T D T^{-λ}, U⁻¹ L U⁻¹ L⁻¹ U L⁻¹`. -/
def lutRelsOf (L U T : PE α) (p lam mu : ℕ) : Set (PE α) :=
  {RA1 L p, RA2 L (PCe L U), RA3 L (PCe L U) p, RA4 (PCe L U), RA5 T p,
   RA6 T U, RA7 T (PEe L U T), RA8 L T (PEe L U T), RA9 (PDe L U lam mu) T lam, R10 L U}

variable {G : Type*} [Group G] (f : α → G)

@[simp] lemma eval_PCe (L U : PE α) :
    (PCe L U).eval f = (L.eval f)⁻¹ * U.eval f * (L.eval f)⁻¹ := by simp [PCe]
@[simp] lemma eval_R10 (L U : PE α) : (R10 L U).eval f =
    (U.eval f)⁻¹ * L.eval f * (U.eval f)⁻¹ * (L.eval f)⁻¹ * U.eval f * (L.eval f)⁻¹ := by
  simp [R10]

end LUTdefs

/-- The alphabet `{L, U, T}`. -/
inductive LUT | L | U | T
  deriving DecidableEq

/-- The relators of Corollary 5.4. -/
def lutRels (p lam mu : ℕ) : Set (PE LUT) := lutRelsOf (gen .L) (gen .U) (gen .T) p lam mu

variable {p : ℕ} [Fact p.Prime]

/-- `L ↦ α_{M_L,0}`, `U ↦ α_{M_U,0}`, `T ↦ t_{e₁}` -/
def lutVal : LUT → ASL2 p
  | .L => lin ML
  | .U => lin MU
  | .T => ASL2.tr e1

/-- values `l, u, t` in a group -/
def lutF {K : Type*} (l u t : K) : LUT → K
  | .L => l
  | .U => u
  | .T => t

/-- the corresponding values of `a, c, t`: `a ↦ l`, `c ↦ l⁻¹ u l⁻¹`, `t ↦ t` -/
def aslF {K : Type*} [Group K] (l u t : K) : ACT → K
  | .a => l
  | .c => l⁻¹ * u * l⁻¹
  | .t => t

/-- If `l, u, t` satisfy the ten relators of Corollary 5.4, then `a = l`, `c = l⁻¹ u l⁻¹`, `t`
satisfy the relators (A1)–(A9) of Proposition 5.3. -/
lemma asl_rels_of_lut {K : Type*} [Group K] {lam mu : ℕ} (l u t : K)
    (hR : ∀ E ∈ lutRels p lam mu, E.eval (lutF l u t) = 1) :
    ∀ E ∈ aslRels p lam mu, E.eval (aslF l u t) = 1 := by
  have m : ∀ E, E ∈ lutRelsOf (gen LUT.L) (gen .U) (gen .T) p lam mu →
      E.eval (lutF l u t) = 1 := hR
  have r1 := m (RA1 (gen .L) p) (by simp [lutRelsOf])
  have r2 := m (RA2 (gen .L) (PCe (gen .L) (gen .U))) (by simp [lutRelsOf])
  have r3 := m (RA3 (gen .L) (PCe (gen .L) (gen .U)) p) (by simp [lutRelsOf])
  have r4 := m (RA4 (PCe (gen .L) (gen .U))) (by simp [lutRelsOf])
  have r5 := m (RA5 (gen .T) p) (by simp [lutRelsOf])
  have r6 := m (RA6 (gen .T) (gen .U)) (by simp [lutRelsOf])
  have r7 := m (RA7 (gen .T) (PEe (gen .L) (gen .U) (gen .T))) (by simp [lutRelsOf])
  have r8 := m (RA8 (gen .L) (gen .T) (PEe (gen .L) (gen .U) (gen .T))) (by simp [lutRelsOf])
  have r9 := m (RA9 (PDe (gen .L) (gen .U) lam mu) (gen .T) lam) (by simp [lutRelsOf])
  have r10 := m (R10 (gen .L) (gen .U)) (by simp [lutRelsOf])
  clear m
  simp only [eval_RA1, eval_RA2, eval_RA3, eval_RA4, eval_RA5, eval_RA6, eval_RA7, eval_RA8,
    eval_RA9, eval_R10, PEe, PDe, eval_Peps, eval_Pd, eval_PCe, eval_gen,
    lutF] at r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  -- `c⁻¹ a⁻¹ c = u`
  have hu : (l⁻¹ * u * l⁻¹)⁻¹ * l⁻¹ * (l⁻¹ * u * l⁻¹) = u := by
    have e : (l⁻¹ * u * l⁻¹)⁻¹ * l⁻¹ * (l⁻¹ * u * l⁻¹) =
        u * (u⁻¹ * l * u⁻¹ * l⁻¹ * u * l⁻¹) := by group
    rw [e, r10, mul_one]
  intro E hE
  simp only [aslRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [aslF] using r1
  · simpa [aslF] using r2
  · simpa [aslF] using r3
  · simpa [aslF] using r4
  · simpa [aslF] using r5
  · simp only [eval_RA6, eval_Pu, eval_gen, aslF]; rw [hu]; exact r6
  · simpa [aslF] using r7
  · simpa [aslF] using r8
  · simp only [eval_RA9, eval_Pd, eval_Pu, eval_gen, aslF]; rw [hu]; exact r9

lemma eval_PCe_lutVal : (PCe (gen LUT.L) (gen .U)).eval (lutVal (p := p)) = lin MC := by
  simp only [eval_PCe, eval_gen, lutVal]
  rw [lin_inv, lin_mul, lin_mul, MC_eq]

lemma eval_Pu_aslVal : (Pu (gen ACT.a) (gen .c)).eval (aslVal (p := p)) = lin MU := by
  simp only [eval_Pu, eval_gen, aslVal]
  rw [lin_inv, lin_inv, lin_mul, lin_mul, MU_eq]

/-- **Corollary 5.4.** -/
theorem cor_5_4 {lam mu : ℕ} (h5 : 5 ≤ p) (h : PrimRoot p lam mu) :
    IsPresentation (lutVal (p := p)) (lutRels p lam mu) := by
  have hA := relators_asl h5 h
  -- the substitution `a ↦ L`, `c ↦ C`, `t ↦ T`
  let W : ACT → PE LUT := fun x => match x with
    | .a => gen .L
    | .c => PCe (gen .L) (gen .U)
    | .t => gen .T
  have hW : ∀ x, (W x).eval (lutVal (p := p)) = aslVal x := by
    intro x; cases x
    · rfl
    · exact eval_PCe_lutVal
    · rfl
  have hsub : ∀ E ∈ aslRels p lam mu, (E.subst W).eval (lutVal (p := p)) = 1 := by
    intro E hE
    rw [eval_subst, eval_congr hW]
    exact hA E hE
  -- the relators hold in `ASL(2,p)`
  have hrel : ∀ E ∈ lutRels p lam mu, E.eval (lutVal (p := p)) = 1 := by
    intro E hE
    simp only [lutRels, lutRelsOf, Set.mem_insert_iff, Set.mem_singleton_iff] at hE
    rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsub (RA1 (gen .a) p) (by simp [aslRels])
    · exact hsub (RA2 (gen .a) (gen .c)) (by simp [aslRels])
    · exact hsub (RA3 (gen .a) (gen .c) p) (by simp [aslRels])
    · exact hsub (RA4 (gen .c)) (by simp [aslRels])
    · exact hsub (RA5 (gen .t) p) (by simp [aslRels])
    · have := hA (RA6 (gen .t) (Pu (gen .a) (gen .c))) (by simp [aslRels])
      simp only [eval_RA6, eval_Pu_aslVal] at this
      simpa only [eval_RA6, eval_gen] using this
    · exact hsub (RA7 (gen .t) (Peps (gen .c) (gen .t))) (by simp [aslRels])
    · exact hsub (RA8 (gen .a) (gen .t) (Peps (gen .c) (gen .t))) (by simp [aslRels])
    · have := hA (RA9 (Pd (gen .a) (Pu (gen .a) (gen .c)) (gen .c) lam mu) (gen .t) lam)
        (by simp [aslRels])
      simp only [eval_RA9, eval_Pd, eval_Pu_aslVal] at this
      simp only [eval_RA9, PDe, eval_Pd, eval_PCe_lutVal]
      exact this
    · simp only [eval_R10, eval_gen, lutVal]
      rw [lin_inv, lin_inv, lin_mul, lin_mul, lin_mul, lin_mul, lin_mul, ← lin_one]
      congr 1
      ext <;> simp [ML, MU]
  -- generation
  have hgen : Subgroup.closure (Set.range (lutVal (p := p))) = ⊤ := by
    rw [eq_top_iff, ← closure_aslVal h5, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    have hL : (lin ML : ASL2 p) ∈ Subgroup.closure (Set.range (lutVal (p := p))) :=
      Subgroup.subset_closure ⟨.L, rfl⟩
    have hU : (lin MU : ASL2 p) ∈ Subgroup.closure (Set.range (lutVal (p := p))) :=
      Subgroup.subset_closure ⟨.U, rfl⟩
    cases x
    · exact hL
    · show lin MC ∈ _
      rw [← eval_PCe_lutVal]
      simp only [eval_PCe, eval_gen, lutVal]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hL) hU)
        (Subgroup.inv_mem _ hL)
    · exact Subgroup.subset_closure ⟨.T, rfl⟩
  -- the presented group is a quotient of `ASL(2,p)`
  set P := Pres (lutRels p lam mu)
  let l : P := PresentedGroup.of LUT.L
  let u : P := PresentedGroup.of LUT.U
  let t : P := PresentedGroup.of LUT.T
  have hP : ∀ E ∈ lutRels p lam mu, E.eval (lutF l u t) = 1 := by
    intro E hE
    have : lutF l u t = fun x => (PresentedGroup.of x : P) := by
      funext x; cases x <;> rfl
    rw [this]
    exact eval_of_eq_one hE
  let Θ : ASL2 p →* P := (prop_5_3 h5 h).lift (asl_rels_of_lut l u t hP)
  have ΘL : Θ (lin ML) = l := (prop_5_3 h5 h).lift_apply _ ACT.a
  have ΘC : Θ (lin MC) = l⁻¹ * u * l⁻¹ := (prop_5_3 h5 h).lift_apply _ ACT.c
  have ΘT : Θ (ASL2.tr e1) = t := (prop_5_3 h5 h).lift_apply _ ACT.t
  have ΘU : Θ (lin MU) = u := by
    have r10 := hP (R10 (gen .L) (gen .U)) (by simp [lutRels, lutRelsOf])
    simp only [eval_R10, eval_gen, lutF] at r10
    rw [← MU_eq, ← lin_mul, ← lin_mul, ← lin_inv, ← lin_inv, map_mul, map_mul, map_inv, map_inv,
      ΘL, ΘC]
    calc (l⁻¹ * u * l⁻¹)⁻¹ * l⁻¹ * (l⁻¹ * u * l⁻¹) = u * (u⁻¹ * l * u⁻¹ * l⁻¹ * u * l⁻¹) := by
          group
      _ = u := by rw [r10, mul_one]
  have hsurj : Function.Surjective Θ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_range_of', Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    cases x
    · exact ⟨lin ML, ΘL⟩
    · exact ⟨lin MU, ΘU⟩
    · exact ⟨ASL2.tr e1, ΘT⟩
  exact isPresentation_of_card_le hrel hgen (Finite.of_surjective Θ hsurj)
    (Nat.card_le_card_of_surjective Θ hsurj)

/-- A homomorphism `ASL(2,p) → K` from elements `l, u, t` satisfying the ten relators of
Corollary 5.4 (the universal property of the presentation). -/
noncomputable def lutLift {K : Type*} [Group K] {lam mu : ℕ} (h5 : 5 ≤ p) (h : PrimRoot p lam mu)
    {l u t : K} (hR : ∀ E ∈ lutRels p lam mu, E.eval (lutF l u t) = 1) : ASL2 p →* K :=
  (cor_5_4 h5 h).lift hR

lemma lutLift_L {K : Type*} [Group K] {lam mu : ℕ} (h5 : 5 ≤ p) (h : PrimRoot p lam mu)
    {l u t : K} (hR : ∀ E ∈ lutRels p lam mu, E.eval (lutF l u t) = 1) :
    lutLift h5 h hR (lin ML) = l := (cor_5_4 h5 h).lift_apply hR LUT.L
lemma lutLift_U {K : Type*} [Group K] {lam mu : ℕ} (h5 : 5 ≤ p) (h : PrimRoot p lam mu)
    {l u t : K} (hR : ∀ E ∈ lutRels p lam mu, E.eval (lutF l u t) = 1) :
    lutLift h5 h hR (lin MU) = u := (cor_5_4 h5 h).lift_apply hR LUT.U
lemma lutLift_T {K : Type*} [Group K] {lam mu : ℕ} (h5 : 5 ≤ p) (h : PrimRoot p lam mu)
    {l u t : K} (hR : ∀ E ∈ lutRels p lam mu, E.eval (lutF l u t) = 1) :
    lutLift h5 h hR (ASL2.tr e1) = t := (cor_5_4 h5 h).lift_apply hR LUT.T

/-! ### Lemma 5.5' -/

/-- **Lemma 5.5'.** A normal subgroup of `ASL(2,p)` containing `α_{M_L,e₁}` is everything. -/
theorem normal_eq_top_of_mem (N : Subgroup (ASL2 p)) [hN : N.Normal]
    (h : (⟨ML, e1⟩ : ASL2 p) ∈ N) : N = ⊤ := by
  have hconj : ∀ x ∈ N, ∀ g : ASL2 p, g⁻¹ * x * g ∈ N := fun x hx g => by
    have := hN.conj_mem x hx g⁻¹
    rwa [inv_inv] at this
  set φ : ASL2 p := ⟨ML, e1⟩ with hφ
  -- `t_{-e₂} = [φ, t_{e₁}] ∈ N`
  have h1 : φ⁻¹ * ((ASL2.tr e1)⁻¹ * φ * ASL2.tr e1) ∈ N :=
    N.mul_mem (N.inv_mem h) (hconj φ h _)
  have h1' : φ⁻¹ * ((ASL2.tr e1)⁻¹ * φ * ASL2.tr e1) = ASL2.tr (-e2) := by
    rw [show φ⁻¹ * ((ASL2.tr e1)⁻¹ * φ * ASL2.tr e1) =
      φ⁻¹ * (ASL2.tr e1)⁻¹ * φ * ASL2.tr e1 by group]
    rw [ASL2.tr_inv, conj_tr, ASL2.tr_mul]
    congr 1
    ext <;> simp [φ, ML]
  rw [h1'] at h1
  have he2 : ASL2.tr e2 ∈ N := by
    have := N.inv_mem h1
    rwa [ASL2.tr_inv, neg_neg] at this
  -- all translations
  have htr : ∀ v : Vec p, ASL2.tr v ∈ N := by
    intro v
    by_cases hv : v = 0
    · rw [hv, ASL2.tr_zero]; exact N.one_mem
    · have e : vecMul e2 (MC * Mrow v) = v := by
        rw [vecMul_mul, show vecMul e2 (MC : SL2 p) = e1 by ext <;> simp [MC],
          vecMul_e1_Mrow hv]
      have := hconj _ he2 (lin (MC * Mrow v))
      rw [conj_tr] at this
      simpa only [lin, e] using this
  -- `α_{M_L,0}` and `α_{M_U,0}`
  have hL : lin (ML : SL2 p) ∈ N := by
    have e : lin (ML : SL2 p) = φ * (ASL2.tr e1)⁻¹ := by
      rw [hφ, ← lin_mul_tr, mul_inv_cancel_right]
    rw [e]
    exact N.mul_mem h (N.inv_mem (htr e1))
  have hU : lin (MU : SL2 p) ∈ N := by
    rw [← MU_eq, ← lin_mul, ← lin_mul, ← lin_inv, ← lin_inv]
    exact hconj _ (N.inv_mem hL) _
  have hlin : ∀ M : SL2 p, lin M ∈ N := by
    let linHom : SL2 p →* ASL2 p := ⟨⟨lin, lin_one⟩, fun M N => (lin_mul M N).symm⟩
    have : Subgroup.closure ({ML, MU} : Set (SL2 p)) ≤ N.comap linHom := by
      rw [Subgroup.closure_le]
      rintro M (rfl | rfl)
      · exact hL
      · exact hU
    rw [closure_ML_MU] at this
    intro M
    exact this trivial
  rw [eq_top_iff]
  intro α _
  rw [show α = lin α.M * ASL2.tr α.w by rw [lin_mul_tr]]
  exact N.mul_mem (hlin _) (htr _)

end SnPres
