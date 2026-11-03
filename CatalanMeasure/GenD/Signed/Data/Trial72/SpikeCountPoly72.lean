module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorstGlobal72
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCountPoly72
open Set RhoGlobal72
noncomputable section

/-- Multiply the physical count trial by its actual count before comparing.
The affine shift pays the difference between the normalized and physical scales. -/
theorem physical {N x m sr P F Q u ap : ℝ}
    (hN : 0 < N) (hx : 0 < x) (hm : 0 ≤ m) (hmx : m ≤ x) (ha : 0 < ap)
    (hu : u ∈ Icc (-1 : ℝ) 1) (hcount : SpikeWorstGlobal72.floor*N ≤ x)
    (hsr : sr ≤ sr0) (hdom : F ≤ sr*P)
    (hweighted : (m/N)*Real.sqrt (ap*(2+ap)) ≤
      (F-SpikeWorstGlobal72.shift)*(1+ap+u))
    (hQ : Q = 1+sr*N/x*(P-1)) :
    1/100 ≤ Q ∧
      (m/x)*(1-(1+ap-Real.sqrt (ap*(2+ap)))^2) ≤
        (Q-(1-m/x)*(1/100))*(1+2*(1+ap-Real.sqrt (ap*(2+ap)))*u+
          (1+ap-Real.sqrt (ap*(2+ap)))^2) := by
  have hshift : SpikeWorstGlobal72.shift = sr0-(99/100)*SpikeWorstGlobal72.floor := by
    norm_num [SpikeWorstGlobal72.shift,SpikeWorstGlobal72.floor,sr0]
  have hfactor : 0 < 1+ap+u := by linarith [hu.1]
  have hmN : 0 ≤ m/N := div_nonneg hm hN.le
  have hF : 0 ≤ F-SpikeWorstGlobal72.shift :=
    nonneg_of_mul_nonneg_left ((mul_nonneg hmN (Real.sqrt_nonneg _)).trans hweighted) hfactor
  have hxQ : x*(Q-1/100) = (99/100)*x+N*(sr*P-sr) := by
    rw [hQ]
    field_simp [hx.ne'] <;> ring
  have hbase : N*(F-SpikeWorstGlobal72.shift) ≤ x*(Q-1/100) := by
    rw [hxQ,hshift]
    have h1 := mul_le_mul_of_nonneg_left hcount (by norm_num : (0 : ℝ) ≤ 99/100)
    have h2 := mul_le_mul_of_nonneg_left (sub_le_sub hdom hsr) hN.le
    nlinarith only [h1,h2]
  have hQ0 : 1/100 ≤ Q := by
    have h := (mul_nonneg hN.le hF).trans hbase
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right h hx)
  refine ⟨hQ0,?_⟩
  let r := Real.sqrt (ap*(2+ap))
  let ρ := 1+ap-r
  have hr2 : r^2 = ap*(2+ap) := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hρ : 0 < ρ := by
    dsimp [ρ]
    by_contra! hn
    have hp := mul_nonneg (sub_nonneg.mpr (show 1+ap ≤ r by linarith))
      (show 0 ≤ r+(1+ap) by positivity)
    nlinarith only [hr2,hp]
  have hroot1 : 1-ρ^2 = 2*ρ*r := by dsimp [ρ]; nlinarith only [hr2]
  have hroot2 : 1+2*ρ*u+ρ^2 = 2*ρ*(1+ap+u) := by dsimp [ρ]; nlinarith only [hr2]
  have hmul := mul_le_mul_of_nonneg_left hweighted hN.le
  have hh := hmul.trans (by
    have h := mul_le_mul_of_nonneg_right hbase hfactor.le
    convert h using 1 <;> ring)
  have hpre : (m/x)*r ≤ (Q-1/100)*(1+ap+u) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hx).2
    have he : N*(m/N*r) = m*r := by field_simp [hN.ne']
    rw [he] at hh
    convert hh using 1 <;> ring
  have hκ : 0 ≤ m/x := div_nonneg hm hx.le
  have hrel : Q-1/100 ≤ Q-(1-m/x)*(1/100) := by linarith
  have hg := hpre.trans (mul_le_mul_of_nonneg_right hrel hfactor.le)
  change (m/x)*(1-ρ^2) ≤ _*(1+2*ρ*u+ρ^2)
  rw [hroot1,hroot2]
  have h := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*ρ by positivity)
  convert h using 1 <;> ring

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCountPoly72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCountPoly72.physical
