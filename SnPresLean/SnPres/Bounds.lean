/-
Uniformity (Definition 2.3) of all the power expressions of the construction: explicit bounds on
`occ`, `pw` and `ex`.  These give the length bound of the main theorem via Lemma 2.2.
-/
import SnPres.Section8a

namespace SnPres

open PE

/-! ### The bound calculus -/

/-- `occ E ≤ o`, `pw E ≤ w` and `ex E ≤ e`. -/
structure Bnd {α : Type*} (e o w : ℕ) (E : PE α) : Prop where
  occ_le : E.occ ≤ o
  pw_le : E.pw ≤ w
  ex_le : E.ex ≤ e

namespace Bnd
variable {α β : Type*} {e o w o' w' : ℕ} {E F : PE α}

lemma mono (h : Bnd e o w E) (ho : o ≤ o') (hw : w ≤ w') : Bnd e o' w' E :=
  ⟨h.1.trans ho, h.2.trans hw, h.3⟩

lemma gen' (he : 1 ≤ e) (a : α) : Bnd e 1 0 (gen a) := ⟨by simp [occ], by simp [pw], by simp [ex]; omega⟩

lemma mul' (h1 : Bnd e o w E) (h2 : Bnd e o' w' F) : Bnd e (o + o') (w + w') (mul E F) :=
  ⟨by simp only [occ]; have := h1.1; have := h2.1; omega,
   by simp only [pw]; have := h1.2; have := h2.2; omega,
   by simp only [ex]; exact max_le h1.3 h2.3⟩

lemma pow' (h : Bnd e o w E) {k : ℤ} (hk : k.natAbs ≤ e) : Bnd e o (w + 1) (pow E k) :=
  ⟨by simp only [occ]; exact h.1, by simp only [pw]; have := h.2; omega,
   by simp only [ex]; exact max_le h.3 hk⟩

lemma powN (h : Bnd e o w E) {k : ℕ} (hk : k ≤ e) : Bnd e o (w + 1) (pow E (k : ℤ)) :=
  h.pow' (by simpa using hk)

lemma inv' (h : Bnd e o w E) (he : 1 ≤ e) : Bnd e o (w + 1) (inv E) :=
  h.pow' (by simpa using he)

lemma conj' (h1 : Bnd e o w E) (h2 : Bnd e o' w' F) (he : 1 ≤ e) :
    Bnd e (o + 2 * o') (w + 2 * w' + 1) (conj E F) := by
  have := ((h2.inv' he).mul' h1).mul' h2
  unfold conj
  exact this.mono (by omega) (by omega)

lemma comm' (h1 : Bnd e o w E) (h2 : Bnd e o' w' F) (he : 1 ≤ e) :
    Bnd e (2 * o + 2 * o') (2 * w + 2 * w' + 2) (comm E F) := by
  have := (((h1.inv' he).mul' (h2.inv' he)).mul' h1).mul' h2
  unfold PE.comm
  exact this.mono (by omega) (by omega)

lemma tel (h1 : Bnd e o w E) (h2 : Bnd e o' w' F) (he : 1 ≤ e) {K : ℕ} (hK : K ≤ e) :
    Bnd e (o + 2 * o') (w + 2 * w' + 3) (Tel E F K) := by
  unfold Tel
  split_ifs
  · exact h1.mono (by omega) (by omega)
  · have := ((h1.mul' (h2.inv' he)).powN hK).mul' (h2.powN hK)
    exact this.mono (by omega) (by omega)

lemma subst' (h : Bnd e o w E) {W : α → PE β} (hW : ∀ a, Bnd e o' w' (W a)) :
    Bnd e (o * o') (w + o * w') (E.subst W) :=
  ⟨(occ_subst_le W E o' (fun a => (hW a).1)).trans (Nat.mul_le_mul_right _ h.1),
   (pw_subst_le W E w' (fun a => (hW a).2)).trans
     (Nat.add_le_add h.2 (Nat.mul_le_mul_right _ h.1)),
   (ex_subst_le W E e (fun a => (hW a).3)).trans (max_le h.3 le_rfl)⟩

lemma map' (h : Bnd e o w E) (he : 1 ≤ e) (f : α → β) : Bnd e o w (E.map f) := by
  have := h.subst' (W := fun a => gen (f a)) (fun a => gen' he (f a))
  exact this.mono (by omega) (by omega)

end Bnd

/-! ### Section 3 -/

section s3
variable {e : ℕ} (he : 1 ≤ e)
include he

lemma bnd_Pk {k : ℕ} (hk : k ≤ e) : Bnd e 3 3 (Pk k) :=
  ((Bnd.gen' he XY.x).tel (Bnd.gen' he XY.y) he hk).mono (by norm_num) (by norm_num)

lemma bnd_rho {L : ℕ} (hL : L - 1 ≤ e) : Bnd e 3 4 (rhoPE L) :=
  (bnd_Pk he hL).inv' he

lemma bnd_sig {k : ℕ} (hk : k ≤ e) : Bnd e 6 7 (sigPE k) := by
  unfold sigPE
  split_ifs
  · exact (Bnd.gen' he XY.x).mono (by norm_num) (by norm_num)
  · exact ((bnd_Pk he hk).mul' ((bnd_Pk he (by omega)).inv' he)).mono (by norm_num) (by norm_num)

lemma bnd_Yp {k : ℕ} (hk : k ≤ e) : Bnd e 1 1 (Yp k) := (Bnd.gen' he XY.y).powN hk

end s3

/-! ### Section 4: the PEs `W_G` -/

section s4
variable {e p : ℕ} (hp : 1 ≤ p) (hpe : 2 * (p * p) + 2 ≤ e)
include hp hpe

lemma pp_le : p ≤ p * p := Nat.le_mul_of_pos_left p hp

lemma bnd_WL : Bnd e 19 36 (WL p) := by
  have h1 : 1 ≤ e := by omega
  have := pp_le hp hpe
  have hB : Bnd e 5 9 (PB p) :=
    ((bnd_rho h1 (by omega)).tel (bnd_Yp h1 (by omega)) h1 (by omega)).mono (by norm_num)
      (by norm_num)
  have hZ : Bnd e 7 14 (PZ p) :=
    (hB.tel (bnd_Yp h1 (by omega)) h1 (by omega)).mono (by norm_num) (by norm_num)
  have hB' : Bnd e 7 12 (PB' p) :=
    (hB.conj' (bnd_Yp h1 (by omega)) h1).mono (by norm_num) (by norm_num)
  exact ((hZ.mul' (hB.inv' h1)).mul' hB').mono (by norm_num) (by norm_num)

lemma bnd_WU : Bnd e 64 101 (WU p) := by
  have h1 : 1 ≤ e := by omega
  have := pp_le hp hpe
  have hV : Bnd e 8 13 (PV p) :=
    (((bnd_sig h1 (by omega)).tel (bnd_Yp h1 (by omega)) h1 (by omega)).inv' h1).mono
      (by norm_num) (by norm_num)
  have hBc : Bnd e 10 16 (PBc p) :=
    (hV.tel (Bnd.gen' h1 XY.y) h1 (by omega)).mono (by norm_num) (by norm_num)
  have hPhi : Bnd e 14 18 (PPhi p) :=
    (((bnd_rho h1 (by omega)).mul' ((bnd_rho h1 (by omega)).conj' (bnd_Yp h1 (by omega)) h1)).mul'
      (bnd_sig h1 (by omega))).mono (by norm_num) (by norm_num)
  have hSig : Bnd e 16 23 (PSigma p) :=
    (hPhi.tel (bnd_Yp h1 (by omega)) h1 (by omega)).mono (by norm_num) (by norm_num)
  have hZc : Bnd e 42 65 (PZc p) :=
    (hBc.tel hSig h1 (by omega)).mono (by norm_num) (by norm_num)
  have hBc' : Bnd e 12 19 (PBc' p) :=
    (hBc.conj' (bnd_Yp h1 (by omega)) h1).mono (by norm_num) (by norm_num)
  exact ((hZc.mul' (hBc.inv' h1)).mul' hBc').mono (by norm_num) (by norm_num)

lemma bnd_WT : Bnd e 8 13 (WT p) := by
  have h1 : 1 ≤ e := by omega
  have := pp_le hp hpe
  have hr : Bnd e 3 5 (pow (rhoPE (p * p)) (p : ℤ)) := (bnd_rho h1 (by omega)).powN (by omega)
  exact (hr.mul' (hr.conj' (bnd_Yp h1 (by omega)) h1)).mono (by norm_num) (by norm_num)

lemma bnd_WX0 : Bnd e 12 14 (WX0 p) := by
  have h1 : 1 ≤ e := by omega
  exact ((bnd_sig h1 (by omega)).mul' (bnd_sig h1 (by omega))).mono (by norm_num) (by norm_num)

lemma bnd_WX1 : Bnd e 14 17 (WX1 p) := by
  have h1 : 1 ≤ e := by omega
  exact (((bnd_sig h1 (by omega)).mul' (bnd_sig h1 (by omega))).conj' (bnd_Yp h1 (by omega))
    h1).mono (by norm_num) (by norm_num)

lemma bnd_WQ : Bnd e 3 3 (WQ p) := by
  have h1 : 1 ≤ e := by omega
  exact ((Bnd.gen' h1 XY.x).conj' (bnd_Yp h1 (by omega)) h1).mono (by norm_num) (by norm_num)

lemma bnd_WG (G : Six) : Bnd e 64 101 (WG p G) := by
  cases G
  · exact (bnd_WL hp hpe).mono (by norm_num) (by norm_num)
  · exact bnd_WU hp hpe
  · exact (bnd_WT hp hpe).mono (by norm_num) (by norm_num)
  · exact (bnd_WX0 hp hpe).mono (by norm_num) (by norm_num)
  · exact (bnd_WX1 hp hpe).mono (by norm_num) (by norm_num)
  · exact (bnd_WQ hp hpe).mono (by norm_num) (by norm_num)

lemma bnd_elimSubst {n : ℕ} (hs : n - NN p ≤ e) (a : GA) : Bnd e 66 104 (elimSubst n p a) := by
  have h1 : 1 ≤ e := by omega
  rcases a with c | G | G
  · exact (Bnd.gen' h1 c).mono (by norm_num) (by norm_num)
  · exact (bnd_WG hp hpe G).mono (by norm_num) (by norm_num)
  · exact ((bnd_WG hp hpe G).conj' (bnd_Yp h1 hs) h1).mono (by norm_num) (by norm_num)

end s4

/-! ### Sections 5–6: the 27 relators -/

section s56
variable {e : ℕ} (he : 1 ≤ e) {α : Type*}
include he

lemma bnd_PCe (L U : α) : Bnd e 3 2 (PCe (gen L) (gen U)) :=
  (((Bnd.gen' he L).inv' he).mul' (Bnd.gen' he U)).mul' ((Bnd.gen' he L).inv' he)

lemma bnd_PEe (L U T : α) : Bnd e 7 5 (PEe (gen L) (gen U) (gen T)) := by
  unfold PEe Peps
  exact (((bnd_PCe he L U).mul' (Bnd.gen' he T)).mul' ((bnd_PCe he L U).inv' he)).mono
    (by norm_num) (by norm_num)

lemma bnd_lut (L U T : α) {p lam mu : ℕ} (hp : p ≤ e) (hlam : lam ≤ e) (hmu : mu ≤ e)
    (h4 : 4 ≤ e) :
    ∀ E ∈ lutListOf (gen L) (gen U) (gen T) p lam mu, Bnd e 16 12 E := by
  have hh : hh p ≤ e := by unfold hh; omega
  have gL := Bnd.gen' he L
  have gU := Bnd.gen' he U
  have gT := Bnd.gen' he T
  have hC := bnd_PCe he L U
  have hE := bnd_PEe he L U T
  have hD : Bnd e 6 5 (PDe (gen L) (gen U) lam mu) := by
    unfold PDe Pd
    exact (((gL.powN hlam).mul' (gU.pow' (by simpa using hmu))).mul' (gL.powN hlam)).mul' hC
      |>.mono (by norm_num) (by norm_num)
  intro E hE'
  simp only [lutListOf, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hE'
  rcases hE' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (gL.powN hp).mono (by norm_num) (by norm_num)
  · unfold RA2
    exact (((((gL.mul' hC).mul' gL).mul' hC).mul' gL).mul' (hC.inv' he)).mono (by norm_num)
      (by norm_num)
  · unfold RA3
    exact ((((((gL.powN hh).mul' hC).mul' (gL.powN (show 4 ≤ e from h4))).mul' hC).powN
      (show 2 ≤ e by omega)).mul' (hC.pow' (by simp; omega))).mono (by norm_num) (by norm_num)
  · exact ((hC.powN (show 4 ≤ e from h4))).mono (by norm_num) (by norm_num)
  · exact (gT.powN hp).mono (by norm_num) (by norm_num)
  · exact (gT.comm' gU he).mono (by norm_num) (by norm_num)
  · exact (gT.comm' hE he).mono (by norm_num) (by norm_num)
  · unfold RA8
    exact (((((gT.mul' hE).mul' (gL.inv' he)).mul' (gT.inv' he)).mul' gL)).mono (by norm_num)
      (by norm_num)
  · unfold RA9
    exact ((((hD.inv' he).mul' gT).mul' hD).mul' (gT.pow' (by simpa using hlam))).mono
      (by norm_num) (by norm_num)
  · unfold R10
    exact ((((((gU.inv' he).mul' gL).mul' (gU.inv' he)).mul' (gL.inv' he)).mul' gU).mul'
      (gL.inv' he)).mono (by norm_num) (by norm_num)

lemma bnd_sixW {p : ℕ} (hp : p ≤ e) : Bnd e 30 26 (sixW p) := by
  unfold sixW sixE
  have hE := bnd_PEe he Six.L Six.U Six.T
  exact (((Bnd.gen' he Six.X0).tel hE he hp).mul' ((Bnd.gen' he Six.X1).tel hE he hp)).mono
    (by norm_num) (by norm_num)

lemma bnd_six {p lam mu : ℕ} (hp1 : 1 ≤ p) (hpe : 2 * (p * p) + 2 ≤ e) (hlam : lam ≤ e)
    (hmu : mu ≤ e) : ∀ E ∈ sixList p lam mu, Bnd e 32 27 E := by
  have := pp_le hp1 hpe
  intro E hE
  simp only [sixList, List.mem_append, List.mem_map] at hE
  rcases hE with ⟨F, hF, rfl⟩ | hE
  · exact ((bnd_lut he LUT.L LUT.U LUT.T (by omega) hlam hmu (by nlinarith) F hF).map' he
      lutToSix).mono (by norm_num) (by norm_num)
  have gL := Bnd.gen' he Six.L
  have gU := Bnd.gen' he Six.U
  have gT := Bnd.gen' he Six.T
  have gX0 := Bnd.gen' he Six.X0
  have gX1 := Bnd.gen' he Six.X1
  have gQ := Bnd.gen' he Six.Q
  have h2 : (2 : ℤ).natAbs ≤ e := by simp; omega
  have h3 : (3 : ℤ).natAbs ≤ e := by simp; omega
  simp only [sixRest, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact (gX0.pow' h3).mono (by norm_num) (by norm_num)
  · exact (gX1.pow' h3).mono (by norm_num) (by norm_num)
  · exact (gX0.comm' gL he).mono (by norm_num) (by norm_num)
  · exact (gX0.comm' gU he).mono (by norm_num) (by norm_num)
  · exact (gX1.comm' gL he).mono (by norm_num) (by norm_num)
  · exact (gX1.comm' gU he).mono (by norm_num) (by norm_num)
  · exact ((gX0.mul' (gX0.conj' gT he)).pow' h2).mono (by norm_num) (by norm_num)
  · exact ((gX1.mul' (gX1.conj' gT he)).pow' h2).mono (by norm_num) (by norm_num)
  · exact ((gX0.mul' gX1).pow' h2).mono (by norm_num) (by norm_num)
  · exact ((gX0.mul' (gX1.conj' gT he)).pow' h2).mono (by norm_num) (by norm_num)
  · exact (((gL.mul' gT).mul' (bnd_sixW he (by omega))).powN (by omega)).mono (by norm_num)
      (by norm_num)
  · exact (gQ.pow' h2).mono (by norm_num) (by norm_num)
  · exact (gQ.comm' gL he).mono (by norm_num) (by norm_num)
  · exact (gQ.comm' gU he).mono (by norm_num) (by norm_num)
  · exact (gQ.comm' gT he).mono (by norm_num) (by norm_num)
  · exact ((gQ.mul' gX0).pow' h2).mono (by norm_num) (by norm_num)
  · exact ((gQ.mul' gX1).pow' h2).mono (by norm_num) (by norm_num)

end s56

/-! ### Proposition 6.4 -/

section s64
variable {e p : ℕ} (hp : 1 ≤ p) (hpe : 2 * (p * p) + 2 ≤ e)
include hp hpe

lemma bnd_brPE (j a b j' a' b' : ℕ) (ha : a ≤ e) (hb : b ≤ e) (ha' : a' ≤ e) (hb' : b' ≤ e) :
    Bnd e 54 45 (brPE j a b j' a' b') := by
  have he : 1 ≤ e := by omega
  have hE := bnd_PEe he Six.L Six.U Six.T
  have hX : ∀ j, Bnd e 1 0 (gX j) := by
    intro j; unfold gX; split_ifs
    · exact Bnd.gen' he _
    · exact Bnd.gen' he _
  have hu : ∀ j a b, a ≤ e → b ≤ e → Bnd e 18 15 (uPE j a b) := by
    intro j a b ha hb
    unfold uPE xPE hPE
    exact (((hX j).conj' (((Bnd.gen' he Six.T).powN ha).mul' (hE.powN hb)) he).mul'
      (Bnd.gen' he Six.Q)).mono (by norm_num) (by norm_num)
  unfold brPE
  exact (((hu j a b ha hb).mul' (hu j' a' b' ha' hb')).mul' (hu j a b ha hb)).mono (by norm_num)
    (by norm_num)

lemma bnd_UpsPE : Bnd e 461 403 (UpsPE p) := by
  have he : 1 ≤ e := by omega
  have := pp_le hp hpe
  have hE := bnd_PEe he Six.L Six.U Six.T
  have hR0 : Bnd e 68 58 (R0PE p) := by
    unfold R0PE
    exact ((bnd_brPE hp hpe 0 0 0 0 0 1 (by omega) (by omega) (by omega) (by omega)).tel hE he
      (by omega)).mono (by norm_num) (by norm_num)
  have hR1 : Bnd e 68 60 (R1PE p) := by
    unfold R1PE
    exact ((bnd_brPE hp hpe 1 0 0 1 0 (p - 1) (by omega) (by omega) (by omega) (by omega)).tel
      (hE.inv' he) he (by omega)).mono (by norm_num) (by norm_num)
  have hJ0 : Bnd e 54 45 (J0PE p) :=
    bnd_brPE hp hpe 0 0 (p - 1) 0 1 0 (by omega) (by omega) (by omega) (by omega)
  have hJ1 : Bnd e 54 45 J1PE := bnd_brPE hp hpe 1 0 1 1 1 0 (by omega) (by omega) (by omega)
    (by omega)
  have hGam : ∀ R J, Bnd e 68 60 R → Bnd e 54 45 J → Bnd e 194 171 (GamPE p R J) := by
    intro R J hR hJ
    unfold GamPE
    exact (((hR.mul' hJ).tel (Bnd.gen' he Six.T) he (by omega)).mul'
      (hR.conj' ((Bnd.gen' he Six.T).powN (by omega)) he)).mono (by norm_num) (by norm_num)
  have hK1 : Bnd e 54 45 (K1PE p) :=
    bnd_brPE hp hpe 0 (p - 1) (p - 1) 1 0 0 (by omega) (by omega) (by omega) (by omega)
  have hK2 : Bnd e 18 15 (K2PE p) := by
    unfold K2PE xPE hPE gX
    exact ((Bnd.gen' he Six.Q).mul' ((Bnd.gen' he Six.X1).conj'
      (((Bnd.gen' he Six.T).powN (by omega)).mul' (hE.powN (by omega))) he)).mono (by norm_num)
      (by norm_num)
  unfold UpsPE
  exact (((((hGam _ _ (hR0.mono le_rfl (by norm_num)) hJ0).mul' hK1).mul' (hGam _ _ hR1 hJ1)).mul'
    hK2).mul' (Bnd.gen' he Six.Q)).inv' he |>.mono (by norm_num) (by norm_num)

lemma bnd_XiPE : Bnd e 54 45 XiPE :=
  bnd_brPE hp hpe 0 0 0 0 0 1 (by omega) (by omega) (by omega) (by omega)

end s64

/-! ### Section 7: the relators (G1)–(G4) -/

section s7
variable {e p : ℕ} (hp : 1 ≤ p) (hpe : 2 * (p * p) + 2 ≤ e)
include hp hpe

lemma bnd_XiK (ι : Six → GA) : Bnd e 54 45 (XiK ι) := (bnd_XiPE hp hpe).map' (by omega) ι
lemma bnd_UpsK (ι : Six → GA) : Bnd e 461 403 (UpsK p ι) := (bnd_UpsPE hp hpe).map' (by omega) ι

lemma bnd_rhoK (ι : Six → GA) {m : ℕ} (hm : m - 1 ≤ e) : Bnd e 1383 1213 (rhoK p ι m) := by
  have he : 1 ≤ e := by omega
  unfold rhoK onXY
  have hW : ∀ c : XY, Bnd e 461 403 (match c with | .x => XiK ι | .y => UpsK p ι) := by
    intro c; cases c
    · exact (bnd_XiK hp hpe ι).mono (by norm_num) (by norm_num)
    · exact bnd_UpsK hp hpe ι
  exact ((bnd_rho he hm).subst' hW).mono (by norm_num) (by norm_num)

lemma bnd_shUps (ι : Six → GA) {F : PE GA} {o w : ℕ} (hF : Bnd e o w F) {r : ℕ} (hr : r ≤ e) :
    Bnd e (o + 922) (w + 809) (shUps p ι F r) := by
  have he : 1 ≤ e := by omega
  unfold shUps
  exact (hF.conj' ((bnd_UpsK hp hpe ι).powN hr) he).mono (by omega) (by omega)

lemma bnd_glu {n lam mu : ℕ} (hn : n ≤ e) (hNn : NN p ≤ n) (hlam : lam ≤ e) (hmu : mu ≤ e) :
    ∀ E ∈ gluList n p lam mu, Bnd e 7376 6472 E := by
  have he : 1 ≤ e := by omega
  have hNNe : NN p = 2 * (p * p) + 2 := rfl
  have hsS : sS n p = n - NN p := rfl
  have hkK : kK n p = 2 * NN p - n := rfl
  have hsix := bnd_six he hp hpe hlam hmu
  have hXi1 := bnd_XiK hp hpe gi1
  have hXi2 := bnd_XiK hp hpe gi2
  have hU1 := bnd_UpsK hp hpe (p := p) gi1
  have hrho : ∀ ι m, m ≤ e → Bnd e 1383 1213 (rhoK p ι m) :=
    fun ι m hm => bnd_rhoK hp hpe ι (by omega)
  have hRr1 : Bnd e 976 854 (Rr1 n p) := bnd_shUps hp hpe gi2 hXi2 (by omega)
  have hRr2 : Bnd e 2305 2022 (Rr2 n p) :=
    bnd_shUps hp hpe gi2 (hrho gi2 _ (by simp only [sS]; omega)) (by omega)
  have hL : ∀ l ∈ LamList n p, Bnd e 1383 1213 l := by
    intro l hl
    unfold LamList at hl
    split_ifs at hl
    · rw [List.mem_singleton] at hl; subst hl; exact hXi1.mono (by norm_num) (by norm_num)
    · rcases List.mem_pair.mp hl with rfl | rfl
      · exact hXi1.mono (by norm_num) (by norm_num)
      · exact hrho gi1 _ (by simp only [sS]; omega)
  have hR : ∀ r ∈ RList n p, Bnd e 2305 2022 r := by
    intro r hr
    unfold RList at hr
    split_ifs at hr
    · rw [List.mem_singleton] at hr; subst hr; exact hRr1.mono (by norm_num) (by norm_num)
    · rcases List.mem_pair.mp hr with rfl | rfl
      · exact hRr1.mono (by norm_num) (by norm_num)
      · exact hRr2
  have hstar : Bnd e 2305 2022 (rStar n p) := by
    unfold rStar; split_ifs
    · exact hRr1.mono (by norm_num) (by norm_num)
    · exact hRr2
  intro E hE
  simp only [gluList, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hE
  rcases hE with ((((⟨F, hF, rfl⟩ | ⟨F, hF, rfl⟩) | (rfl | rfl)) | ⟨l, hl, r, hr, rfl⟩) | (rfl | rfl))
  · exact ((hsix F hF).map' he gi1).mono (by norm_num) (by norm_num)
  · exact ((hsix F hF).map' he gi2).mono (by norm_num) (by norm_num)
  · unfold vs1 vs2
    exact ((bnd_shUps hp hpe gi1 hXi1 (by simp only [sS]; omega)).mul' (hXi2.inv' he)).mono
      (by norm_num) (by norm_num)
  · unfold ga1 ga2
    exact ((bnd_shUps hp hpe gi1 (hrho gi1 _ (by simp only [kK]; omega))
      (by simp only [sS]; omega)).mul' ((hrho gi2 _ (by simp only [kK]; omega)).inv' he)).mono
      (by norm_num) (by norm_num)
  · exact ((hL l hl).comm' (hR r hr) he).mono (by norm_num) (by norm_num)
  · exact ((Bnd.gen' he _).mul' (hXi1.inv' he)).mono (by norm_num) (by norm_num)
  · exact ((Bnd.gen' he _).mul' ((hstar.mul' hU1).inv' he)).mono (by norm_num) (by norm_num)

end s7

/-- **The length bound**: every relator of the main construction has length at most
`486816 + 773576 (log₂ n + 4)`. -/
theorem mainRels_length_le {n p lam mu : ℕ} [Fact p.Prime] (hp : 1 ≤ p) (hpn : NN p ≤ n) (hlam : lam ≤ n)
    (hmu : mu ≤ n) :
    ∀ E ∈ mainRels n p lam mu, E.length ≤ 486816 + 773576 * (Nat.log 2 n + 4) := by
  have hpe : 2 * (p * p) + 2 ≤ n := by have := NN_eq (p := p); omega
  intro E hE
  obtain ⟨F, hF, hle⟩ := mainRels_le E hE
  have hB := (bnd_glu hp hpe (le_refl n) hpn hlam hmu F hF).subst'
    (bnd_elimSubst hp hpe (n := n) (by omega))
  refine hle.trans ((length_le _).trans ?_)
  have h1 : Nat.log 2 (F.subst (elimSubst n p)).ex ≤ Nat.log 2 n := Nat.log_mono_right hB.3
  have h2 := hB.1
  have h3 := hB.2
  calc (F.subst (elimSubst n p)).occ + (F.subst (elimSubst n p)).pw *
        (Nat.log 2 (F.subst (elimSubst n p)).ex + 4)
      ≤ 7376 * 66 + (6472 + 7376 * 104) * (Nat.log 2 n + 4) :=
        Nat.add_le_add h2 (Nat.mul_le_mul h3 (Nat.add_le_add_right h1 4))
    _ = 486816 + 773576 * (Nat.log 2 n + 4) := by norm_num

end SnPres
