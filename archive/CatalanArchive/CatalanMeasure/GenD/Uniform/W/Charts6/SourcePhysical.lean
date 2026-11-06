module
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourceExprSound
@[expose] public section
set_option Elab.async false
/-! Physical source transport without a numerical common-denominator check.
The extra zeta row is justified by its recurrence, not silently defaulted. -/
namespace CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD OAI.InternalCatalan CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : Nat} [Fact p.Prime]

theorem source_zeta_unit_extended (d : IntMomentData) (hd : d.Sound p)
    (hH : 0 < d.H) (hp : d.N + 2 < p) {u J : Nat}
    (hu : u ≤ d.H) (hJ : J < d.L) : ((zetaRat u J).den : ZMod p) ≠ 0 := by
  have hdim := hd.shape
  simp only [IntMomentData.shape, Bool.and_eq_true, decide_eq_true_eq] at hdim
  have hLH : d.L ≤ d.H := hdim.1.1.1.1
  have hHN : d.H + 2 ≤ d.N := hdim.1.1.1.2
  by_cases hlt : u < d.H
  · exact (hd.zt u J hlt hJ).1
  · have huH : u = d.H := by omega
    subst u
    cases J with
    | zero =>
      have he : zetaRat d.H 0 = harmonicRat 1 d.H * (1 / (d.H : Rat)) := by
        rw [zetaRat_of_ne (by omega)]
        simp [harmonicRat_zero, div_eq_mul_inv]
      exact (ResRec.Gd.of_eq he (ResRec.Gd.mul (hd.h1 d.H (by omega))
        (ResRec.Gd.inv_nat hH (by omega)))).1
    | succ j =>
      have hprev := hd.zt (d.H - 1) j (by omega) (by omega)
      have hinv := ResRec.Gd.mul
        (ResRec.Gd.inv_nat (p := p) (n := d.H) hH (by omega))
        (ResRec.Gd.inv_nat (p := p) (n := j + 1) (by omega) (by omega))
      have he : zetaRat d.H (j + 1) = zetaRat (d.H - 1) j -
          (1 / (d.H : Rat)) * (1 / ((j + 1 : Nat) : Rat)) := by
        have hs := zetaRat_step (d.H - 1) j
        have hh : d.H - 1 + 1 = d.H := by omega
        rw [hh] at hs
        rw [one_div_mul_one_div]
        linarith
      exact (ResRec.Gd.of_eq he (ResRec.Gd.sub hprev hinv)).1

theorem source_alpha_unit_extended (d : IntMomentData) (hd : d.Sound p)
    {u J : Nat} (hu : u ≤ d.H) (hJ : J < d.L) :
    ((ZoneZ.Q.alphaQ u J).den : ZMod p) ≠ 0 := by
  have hdim := hd.shape
  simp only [IntMomentData.shape, Bool.and_eq_true, decide_eq_true_eq] at hdim
  have hLH : d.L ≤ d.H := hdim.1.1.1.1
  have hHN : d.H + 2 ≤ d.N := hdim.1.1.1.2
  cases u with
  | zero =>
    simpa [ZoneZ.Q.alphaQ, momentRatNegOne_eq] using (hd.bp (J + 1) (by omega)).1
  | succ i =>
    have hi : i < d.H := by omega
    have he : ZoneZ.Q.alphaQ (i + 1) J = momentRat i J := by
      simp [ZoneZ.Q.alphaQ]
    rw [he]
    exact (hd.mt i J hi hJ).1

/-- Finite lcm units follow from native moment soundness, so no enormous
numeric Zmom literal or kernel divisibility computation is needed. -/
theorem source_Zmom_not_dvd (d : IntMomentData) (hd : d.Sound p)
    (hH : 0 < d.H) (hp : d.N + 2 < p) : ¬p ∣ Charts.Zmom (d.H + 1) d.L := by
  have prime : Nat.Prime p := Fact.out
  have unit_not_dvd (q : Rat) (hq : (q.den : ZMod p) ≠ 0) : ¬p ∣ q.den := by
    intro h
    exact hq ((ZMod.natCast_eq_zero_iff q.den p).mpr h)
  have not_lcm {a b : Nat} (ha : ¬p ∣ a) (hb : ¬p ∣ b) : ¬p ∣ Nat.lcm a b := by
    intro h
    exact (prime.dvd_mul.mp (h.trans (Nat.lcm_dvd_mul a b))).elim ha hb
  let f : Nat × Nat → Nat := fun x => Nat.lcm (ZoneZ.Q.alphaQ x.1 x.2).den (zetaRat x.1 x.2).den
  have hfin : ∀ s : Finset (Nat × Nat), (∀ x ∈ s, ¬p ∣ f x) → ¬p ∣ s.lcm f := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [prime.ne_one]
    | @insert x s hx ih =>
      intro hall
      rw [Finset.lcm_insert]
      exact not_lcm (hall x (by simp))
        (ih (fun y hy => hall y (Finset.mem_insert_of_mem hy)))
  have hL : ¬p ∣ Charts.Lmom (d.H + 1) d.L := by
    apply hfin
    intro x hx
    have hbounds := Finset.mem_product.mp hx
    have hu : x.1 ≤ d.H := by simpa using hbounds.1
    have hJ : x.2 < d.L := Finset.mem_range.mp hbounds.2
    exact not_lcm
      (unit_not_dvd _ (source_alpha_unit_extended d hd hu hJ))
      (unit_not_dvd _ (source_zeta_unit_extended d hd hH hp hu hJ))
  intro h
  rcases prime.dvd_mul.mp h with h2 | hl
  · exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega)) h2
  · exact hL hl

/-- The checked integer expression is the physical source covector on a
coordinate whose profile polynomials have the stated integer coefficients. -/
theorem SourceExpr.psi_sound (a : SourceExpr) (d : IntMomentData)
    (g t : IntSourceTree) (J : Nat) (hJ : J < d.L)
    (hp : d.N + 2 < p) (hz : (d.scale : ZMod p) ≠ 0)
    (hd : d.check = true) (hg : g.check d.H (sourceBaseG d J) = true)
    (ht : t.check d.H (sourceBaseT d J) = true)
    {K H : Nat} (F : Prof p K) (k : Fin K)
    (hG : ∀ i, (F.Gy (Pi.single k 1)).coeff i = (a.polys.1.coeff i : ZMod p))
    (hT : ∀ i, (F.Ty (Pi.single k 1)).coeff i = (a.polys.2.coeff i : ZMod p))
    {S : Int} (hS : S.toNat + 3 ≤ d.H + 1) (hSH : S.toNat + 3 ≤ H)
    {v : Int} (hv : a.eval? g t d.H S = some v) :
    F.psi H J S (Pi.single k 1) = ((v : ZMod p) / ((2 * d.scale : Int) : ZMod p)) := by
  have hgc := hg
  simp only [IntSourceTree.check, Bool.and_eq_true, decide_eq_true_eq] at hgc
  have hd' := IntMomentData.check_sound d hp hz hd
  have hZ := source_Zmom_not_dvd d hd' hgc.1 hp
  have he := Charts.digitPhi_eq_res_phiQ hZ a.polys.1.coeff a.polys.2.coeff
    (F.Gy (Pi.single k 1)) (F.Ty (Pi.single k 1)) hG hT hJ hS hSH
  have hr := a.phi_sound d g t J hJ hp hz hd hg ht S v hv
  unfold Prof.psi
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  exact he.trans hr.2

end
end CatalanMeasure.GenD.Uniform.W.Charts6
