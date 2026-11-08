module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.MaximaAssembly
public import Mathlib.Analysis.Calculus.MeanValue
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: generic Lipschitz/box-cap transfer; instance: one list abs-sum and one pole sum per field
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.FieldCap
noncomputable section
open Set CatalanMeasure.CellCert CatalanMeasure.Cert

/-- Mean value theorem on a box: a derivative bound gives the midpoint Lipschitz estimate. -/
theorem box_lipschitz {F g : Real → Real} {l r L : Real}
    (hF : ∀ y∈Icc l r,HasDerivAt F (g y) y) (hg : ∀ y∈Icc l r,|g y|≤L) :
    ∀ x∈Icc l r,|F x-F ((l+r)/2)|≤L*|x-(l+r)/2| := by
  intro x hx
  have hm : (l+r)/2∈Icc l r := by
    refine ⟨?_,?_⟩ <;> linarith [hx.1,hx.2]
  have := (convex_Icc l r).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f:=F) (f':=g) (C:=L) (fun y hy => (hF y hy).hasDerivWithinAt)
    (fun y hy => by simpa only [Real.norm_eq_abs] using hg y hy) hm hx
  simpa only [Real.norm_eq_abs] using this

theorem box_cap_of_deriv_bound {F g : Real → Real} {l r L M : Real}
    (hF : ∀ y∈Icc l r,HasDerivAt F (g y) y) (hg : ∀ y∈Icc l r,|g y|≤L)
    (hL : 0≤L) (hpoint : F ((l+r)/2)+L*((r-l)/2)≤M) :
    ∀ x∈Icc l r,F x≤M :=
  CatalanMeasure.GenD.Signed.RouteI.Maxima.MaximaAssembly.box_cap_of_midpoint hL (box_lipschitz hF hg) hpoint

/-- One pole term of the derivative is bounded by its residue size over its distance. -/
theorem qt_abs_le (q : PoleR) (x d : Real) (hd : 0<d) (hdist : d≤‖(x : Complex)-q.pc‖) :
    |qt q 0 x|≤(|(q.rr : Real)|+|(q.ri : Real)|)/d := by
  have h1 : |qt q 0 x|≤‖qe q 0 (x : Complex)‖ := Complex.abs_re_le_norm _
  have h2 : ‖qe q 0 (x : Complex)‖=‖q.rho‖*‖(x : Complex)-q.pc‖⁻¹ := by
    simp [qe]
  have h3 : ‖q.rho‖≤|(q.rr : Real)|+|(q.ri : Real)| := by
    have := Complex.norm_le_abs_re_add_abs_im q.rho
    simpa [PoleR.rho] using this
  have h4 : ‖(x : Complex)-q.pc‖⁻¹≤d⁻¹ := inv_anti₀ hd hdist
  rw [h2] at h1
  calc |qt q 0 x|≤‖q.rho‖*‖(x : Complex)-q.pc‖⁻¹ := h1
    _≤(|(q.rr : Real)|+|(q.ri : Real)|)*d⁻¹ :=
        mul_le_mul h3 h4 (by positivity) (by positivity)
    _=_ := by rw [div_eq_mul_inv]

theorem pole_sum_abs_le (poles : List PoleR) (x : Real) (d : PoleR → Real)
    (hd : ∀ q∈poles,0<d q ∧ d q≤‖(x : Complex)-q.pc‖) :
    |(poles.map (fun q => qt q 0 x)).sum|≤
      (poles.map (fun q => (|(q.rr : Real)|+|(q.ri : Real)|)/d q)).sum := by
  induction poles with
  | nil => simp
  | cons q qs ih =>
    simp only [List.map_cons,List.sum_cons]
    calc _≤|qt q 0 x|+|(qs.map (fun q => qt q 0 x)).sum| := abs_add_le _ _
      _≤_ := add_le_add (qt_abs_le q x (d q) (hd q (by simp)).1 (hd q (by simp)).2)
        (ih (fun p hp => hd p (by simp [hp])))

/-- Derivative size: scaled polynomial part plus residue-over-distance pole terms. -/
theorem ftZ_abs_le (Z : List Int) (poles : List PoleR) (x : Real) (hx : |x|≤1)
    (d : PoleR → Real) (hd : ∀ q∈poles,0<d q ∧ d q≤‖(x : Complex)-q.pc‖) :
    |ftZ Z poles 0 x|≤(lpAbsSum (zl Z) : Real)/1099511627776+
      (poles.map (fun q => (|(q.rr : Real)|+|(q.ri : Real)|)/d q)).sum := by
  have hp : |ptZ Z 0 x|≤(lpAbsSum (zl Z) : Real)/1099511627776 := by
    have h := abs_lpEval_le (p:=zl Z) hx
    simp only [ptZ,Function.iterate_zero,id]
    rw [abs_div, abs_of_pos (by norm_num : (0 : Real)<1099511627776)]
    exact div_le_div_of_nonneg_right h (by norm_num)
  unfold ftZ
  exact (abs_add_le _ _).trans (add_le_add hp (pole_sum_abs_le poles x d hd))

/-- Field box cap from the original `Spec.Sound` source and finite data: the box lies in the
open domain, poles stay at distance `d q`, and the derivative bound `L` plus the midpoint
value gives `F ≤ M` on the whole box. -/
theorem field_box_cap {S : Spec} {D : PolyData} {F : Real → Real}
    (hS : S.Sound D F) (hpeel : S.peel=none) {l r L M : Real}
    (hbox : Icc l r⊆Ioo (-1 : Real) 1) (d : PoleR → Real)
    (hd : ∀ y∈Icc l r,∀ q∈S.poles,0<d q ∧ d q≤‖(y : Complex)-q.pc‖)
    (hL : (lpAbsSum (zl D.Z) : Real)/1099511627776+
      (S.poles.map (fun q => (|(q.rr : Real)|+|(q.ri : Real)|)/d q)).sum≤L)
    (hpoint : F ((l+r)/2)+L*((r-l)/2)≤M) (hne : (l : Real)≤r) :
    ∀ x∈Icc l r,F x≤M := by
  have hmem : (l+r)/2∈Icc l r := ⟨by linarith,by linarith⟩
  have hL0 : 0≤L := by
    have h := ftZ_abs_le D.Z S.poles ((l+r)/2) (abs_le.mpr ⟨by linarith [(hbox hmem).1],
      by linarith [(hbox hmem).2]⟩) d (hd _ hmem)
    exact (abs_nonneg _).trans (h.trans hL)
  have hder : ∀ y∈Icc l r,HasDerivAt F (ftZ D.Z S.poles 0 y) y := by
    intro y hy
    apply CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative.source_derivative hS hpeel (hbox hy)
    intro q hq h
    have := (hd y hy q hq).2
    rw [h, sub_self, norm_zero] at this
    exact absurd (hd y hy q hq).1 (not_lt.mpr this)
  apply box_cap_of_deriv_bound hder _ hL0 hpoint
  intro y hy
  have hyy := hbox hy
  exact (ftZ_abs_le D.Z S.poles y (abs_le.mpr ⟨hyy.1.le,hyy.2.le⟩) d (hd y hy)).trans hL


/-- Same cap with the midpoint value supplied by the original evaluator `S.ev` (the `evLe`
enclosure `v+e`) at the rational midpoint. -/
theorem field_box_cap_ev {S : Spec} {D : PolyData} {F : Real → Real}
    (hS : S.Sound D F) (hpeel : S.peel=none) {l r : Rat} {L M : Real} {v e : Rat}
    (hbox : Icc (l : Real) r⊆Ioo (-1 : Real) 1) (d : PoleR → Real)
    (hd : ∀ y∈Icc (l : Real) r,∀ q∈S.poles,0<d q ∧ d q≤‖(y : Complex)-q.pc‖)
    (hL : (lpAbsSum (zl D.Z) : Real)/1099511627776+
      (S.poles.map (fun q => (|(q.rr : Real)|+|(q.ri : Real)|)/d q)).sum≤L)
    (hev : S.ev ((l+r)/2)=some (v,e))
    (hpoint : (v : Real)+e+L*(((r : Real)-l)/2)≤M) (hne : (l : Real)≤r) :
    ∀ x∈Icc (l : Real) r,F x≤M := by
  have hmem : ((l : Real)+r)/2∈Icc (l : Real) r := ⟨by linarith,by linarith⟩
  have hmid := hbox hmem
  have hS' := hS
  obtain ⟨Freg,hevs,_,_,hsplit,_⟩ := hS'
  have hq : ((((l+r)/2 : Rat)) : Real)=((l : Real)+r)/2 := by push_cast; ring
  have hF : F (((l : Real)+r)/2)=Freg (((l : Real)+r)/2) := by
    have h := hsplit (((l : Real)+r)/2) (by simp [hpeel])
    simpa [hpeel,peelTerm] using h
  have hp : ∀ p∈S.poles,((((((l+r)/2 : Rat)) : Real)) : Complex)≠p.pc := by
    intro p hp h
    rw [hq] at h
    have := (hd _ hmem p hp).2
    rw [h,sub_self,norm_zero] at this
    exact absurd (hd _ hmem p hp).1 (not_lt.mpr this)
  have hle := hevs _ v e hev (by rw [hq]; exact abs_le.mpr ⟨by linarith [hmid.1],by linarith [hmid.2]⟩) hp
  rw [hq] at hle
  refine field_box_cap hS hpeel hbox d hd hL ?_ hne
  rw [hF]; linarith

#print axioms box_lipschitz
#print axioms qt_abs_le
#print axioms ftZ_abs_le
#print axioms field_box_cap
#print axioms field_box_cap_ev
end
end CatalanMeasure.GenD.Signed.RouteI.Maxima.FieldCap
