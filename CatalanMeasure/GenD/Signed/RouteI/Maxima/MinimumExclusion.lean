module
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: estimated <=149 K shared R3 reserve; actual sign/uniqueness checks unmeasured
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.MinimumExclusion
open Set Filter
open scoped Topology

/-- A continuous numerator with its sole zero at the right endpoint retains a negative
left sign. An intermediate zero would contradict the certified uniqueness. -/
theorem numerator_negative_left {N : Real → Real} {l c : Real}
    (hc : ContinuousOn N (Icc l c)) (hl : N l<0)
    (hunique : ∀ z∈Icc l c,N z=0 → z=c) :
    ∀ x∈Ioo l c,N x<0 := by
  intro x hx
  by_contra hnot
  have hnonneg : 0≤N x := le_of_not_gt hnot
  have hsub : Icc l x⊆Icc l c := by
    intro z hz
    exact ⟨hz.1,hz.2.trans hx.2.le⟩
  obtain ⟨z,hz,hzero⟩ := intermediate_value_Icc hx.1.le (hc.mono hsub)
    ⟨hl.le,hnonneg⟩
  have he : z=c := hunique z (hsub hz) hzero
  linarith [hz.2,hx.2]

/-- A negative derivative immediately to the left of c excludes a local maximum there.
This is sufficient to omit a certified minimum's value; no second derivative is used. -/
theorem not_localMax_of_left_deriv_negative {F : Real → Real} {l c : Real}
    (hlc : l<c) (hc : ContinuousOn F (Icc l c))
    (hd : ∀ x∈Ioo l c,deriv F x<0) : ¬IsLocalMax F c := by
  intro hmax
  have hanti : StrictAntiOn F (Icc l c) :=
    strictAntiOn_of_deriv_neg (convex_Icc l c) hc (by
      intro x hx
      rw [interior_Icc] at hx
      exact hd x hx)
  have hevent : ∀ᶠ x in 𝓝[<] c,F x≤F c :=
    hmax.filter_mono nhdsWithin_le_nhds
  have hIoo : ∀ᶠ x in 𝓝[<] c,x∈Ioo l c := Ioo_mem_nhdsLT hlc
  obtain ⟨x,hx,hFx⟩ := (hIoo.and hevent).exists
  have hstrict : F c<F x := hanti ⟨hx.1.le,hx.2.le⟩ ⟨hlc.le,le_rfl⟩ hx.2
  exact (not_lt_of_ge hFx) hstrict

/-- Full numerator signs are retained: reduced-polynomial signs alone cannot replace
these premises because the cancelled factor may have either sign. -/
theorem exclude_root_of_negative_full_numerator
    {F N D : Real → Real} {l c r : Real} (hlc : l<c) (hcr : c<r)
    (hF : ContinuousOn F (Icc l r)) (hN : ContinuousOn N (Icc l r))
    (hD : ∀ x∈Icc l r,0<D x)
    (hderiv : ∀ x∈Ioo l r,deriv F x=N x/D x)
    (hleft : N l<0) (hunique : ∀ x∈Icc l r,N x=0 → x=c) :
    ¬IsLocalMax F c := by
  have hsub : Icc l c⊆Icc l r := by
    intro x hx
    exact ⟨hx.1,hx.2.trans hcr.le⟩
  have hneg : ∀ x∈Ioo l c,N x<0 := numerator_negative_left (hN.mono hsub) hleft
    (fun z hz he => hunique z (hsub hz) he)
  apply not_localMax_of_left_deriv_negative hlc (hF.mono hsub)
  intro x hx
  have hxlr : x∈Ioo l r := ⟨hx.1,hx.2.trans hcr⟩
  rw [hderiv x hxlr]
  exact div_neg_of_neg_of_pos (hneg x hx) (hD x ⟨hxlr.1.le,hxlr.2.le⟩)

#print axioms numerator_negative_left
#print axioms not_localMax_of_left_deriv_negative
#print axioms exclude_root_of_negative_full_numerator
end CatalanMeasure.GenD.Signed.RouteI.Maxima.MinimumExclusion
