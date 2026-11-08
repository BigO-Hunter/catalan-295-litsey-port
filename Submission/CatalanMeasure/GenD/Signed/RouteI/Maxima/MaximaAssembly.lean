module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCover
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.MinimumExclusion
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.MaximaEndpoint
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: estimated within outstanding generic reserves; actual source instances unmeasured
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.MaximaAssembly
noncomputable section
open Set CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCover CatalanMeasure.GenD.Signed.RouteI.Maxima.MinimumExclusion

theorem box_cap_of_midpoint {F : Real → Real} {l r L M : Real}
    (hL : 0≤L)
    (hbound : ∀ x∈Icc l r,
      |F x-F ((l+r)/2)|≤L*|x-(l+r)/2|)
    (hpoint : F ((l+r)/2)+L*((r-l)/2)≤M) :
    ∀ x∈Icc l r,F x≤M := by
  intro x hx
  have hdist : |x-(l+r)/2|≤(r-l)/2 := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have he := (le_abs_self (F x-F ((l+r)/2))).trans (hbound x hx)
  have hm := mul_le_mul_of_nonneg_left hdist hL
  linarith

/-- The global endpoint consumer only needs local maxima. Every discarded bracket is
excluded using its original numerator, without throwing away a cancelled-factor sign. -/
theorem maxima_cap_of_root_brackets
    (F N D : Real → Real) (p : Polynomial Real) (hp : p≠0)
    (s : Set Real) (n : Nat) (l r : Fin n → Real) (keep : Fin n → Prop) (M : Real)
    (hlr : ∀ i,l i<r i) (hsign : ∀ i,p.eval (l i)*p.eval (r i)<0)
    (hsub : ∀ i,Icc (l i) (r i)⊆s)
    (hdis : ∀ i j,i≠j → Disjoint (Icc (l i) (r i)) (Icc (l j) (r j)))
    (hupper : (rootSet p s).card≤n)
    (hF : ContinuousOn F s) (hN : ContinuousOn N s)
    (hD : ∀ x∈s,0<D x) (hderiv : ∀ x∈s,deriv F x=N x/D x)
    (hroots : ∀ x∈s,N x=0 ↔ p.IsRoot x)
    (hleft : ∀ i,¬keep i → N (l i)<0)
    (hcap : ∀ i,keep i → ∀ x∈Icc (l i) (r i),F x≤M) :
    ∀ x∈s,IsLocalMax F x → deriv F x=0 → F x≤M := by
  classical
  obtain ⟨rho,hrho,hinj,hcomplete,hunique⟩ :=
    bracket_saturation p hp s n l r hlr hsign hsub hdis hupper
  intro x hxs hmax hzero
  have hnzero : N x=0 := by
    have he : N x/D x=0 := by rw [← hderiv x hxs]; exact hzero
    exact (div_eq_zero_iff.mp he).resolve_right (ne_of_gt (hD x hxs))
  obtain ⟨i,hxi⟩ := hcomplete x hxs ((hroots x hxs).mp hnzero)
  by_cases hi : keep i
  · exact hcap i hi x (by rw [hxi]; exact ⟨(hrho i).1.1.le,(hrho i).1.2.le⟩)
  · have hnot : ¬IsLocalMax F (rho i) :=
      exclude_root_of_negative_full_numerator (hrho i).1.1 (hrho i).1.2
        (hF.mono (hsub i)) (hN.mono (hsub i))
        (fun z hz => hD z (hsub i hz))
        (fun z hz => hderiv z (hsub i ⟨hz.1.le,hz.2.le⟩)) (hleft i hi)
        (fun z hz he => hunique i z hz ((hroots z (hsub i hz)).mp he))
    exact False.elim (hnot (hxi ▸ hmax))

#print axioms box_cap_of_midpoint
#print axioms maxima_cap_of_root_brackets
end
end CatalanMeasure.GenD.Signed.RouteI.Maxima.MaximaAssembly
