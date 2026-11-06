module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeQCover72
public import CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCostScalars0
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCostScalars1
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCostScalars2
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeLinear72
open Set
noncomputable section


def rhoHi : List ℚ := [CostRootData.A00.rhoHi, CostRootData.A01.rhoHi, CostRootData.A02.rhoHi, CostRootData.A03.rhoHi, CostRootData.A04.rhoHi, CostRootData.A05.rhoHi, CostRootData.A06.rhoHi, CostRootData.A07.rhoHi, CostRootData.A08.rhoHi, CostRootData.A09.rhoHi, CostRootData.A10.rhoHi, CostRootData.A11.rhoHi, CostRootData.A12.rhoHi, CostRootData.A13.rhoHi, CostRootData.A14.rhoHi, CostRootData.A15.rhoHi, CostRootData.A16.rhoHi, CostRootData.A17.rhoHi, CostRootData.A18.rhoHi, CostRootData.A19.rhoHi, CostRootData.A20.rhoHi, CostRootData.A21.rhoHi, CostRootData.A22.rhoHi, CostRootData.A23.rhoHi, CostRootData.A24.rhoHi, CostRootData.A25.rhoHi, CostRootData.A26.rhoHi]

theorem root_bound : ∀ a : Fin 27, rhoHi.getD a.val 0 ≤ (999001/1000000 : ℚ) := by
  decide +kernel

theorem root_high : ∀ i : Fin 200,
    (1/2 : ℚ) ≤ 71*(i.val : ℚ)/12500 →
    rhoHi.getD (RhoQAliases72.indices.getD i.val 0) 0 ≤ (499/500 : ℚ) := by
  decide +kernel
def sg (i : Fin 200) : ℚ :=
  if (1/2 : ℚ) ≤ 71*(i.val : ℚ)/12500 then -1/2 else 0

def linear (sr : ℚ) (de : List ℚ) (i : Fin 200) : ℚ :=
  72/1000 + sr * max 0 (de.getD (RhoQAliases72.indices.getD i.val 0) 0) +
    (71*(i.val : ℚ)/12500)/2 * sg i

theorem scalar0 : ∀ i : Fin 200, linear (5498093038080309/140737488355328)
    SpikeCostScalars0.deUpper i ≤ 11/10 := by decide +kernel
theorem scalar1 : ∀ i : Fin 200, linear (684782692610523/17592186044416)
    SpikeCostScalars1.deUpper i ≤ 11/10 := by decide +kernel
theorem scalar2 : ∀ i : Fin 200, linear (1311314498851535/35184372088832)
    SpikeCostScalars2.deUpper i ≤ 11/10 := by decide +kernel

/-- Direct uniform bound on the logarithm multiplying the actual 72N count. -/
theorem lambda_bound {τ : ℝ} (hτ : τ ∈ Icc (1-1/1073741824 : ℝ) 1) :
    Real.log (2 / (1 + τ^2*(1-1/1024))) ≤ 1/1000 := by
  have ht0 : 0 ≤ τ := by linarith [hτ.1]
  have hts : (1-1/1073741824 : ℝ)^2 ≤ τ^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hτ.1) (show 0 ≤ τ+(1-1/1073741824 : ℝ) by positivity)]
  have hd : 0 < 1+τ^2*(1-1/1024) := by positivity
  have hq : 2/(1+τ^2*(1-1/1024)) ≤ 1+1/1000 := by
    apply (div_le_iff₀ hd).2
    nlinarith only [hts]
  have h := Real.log_le_sub_one_of_pos (show 0 < 2/(1+τ^2*(1-1/1024)) by positivity)
  linarith only [h,hq]

/-- For the high q pieces it suffices to pay a uniform gain of 1/2;
no replay of the full directed logarithm table is required. -/
theorem sg_high {τ ρ : ℝ} (hτ : τ ∈ Icc (1-1/1073741824 : ℝ) 1)
    (hρ : ρ ∈ Icc (0 : ℝ) (499/500)) :
    Real.log (1-τ^2*(1-1/1024)^2) - Real.log (1-ρ^2) ≤ -1/2 := by
  have ht0 : 0 ≤ τ := by linarith [hτ.1]
  have hts : (1-1/1073741824 : ℝ)^2 ≤ τ^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hτ.1) (show 0 ≤ τ+(1-1/1073741824 : ℝ) by positivity)]
  have ht1 : τ^2 ≤ 1 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hτ.2)]
  have hr1 : ρ^2 ≤ (499/500 : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ.2) (show 0 ≤ ρ+(499/500 : ℝ) by linarith [hρ.1])]
  have hd : 0 < 1-ρ^2 := by linarith only [hr1]
  have hn : 0 < 1-τ^2*(1-1/1024)^2 := by nlinarith only [ht1]
  rw [← Real.log_div hn.ne' hd.ne']
  have hq : (1-τ^2*(1-1/1024)^2)/(1-ρ^2) ≤ 1/2 := by
    apply (div_le_iff₀ hd).2
    nlinarith only [hts,hr1]
  have h := Real.log_le_sub_one_of_pos (div_pos hn hd)
  linarith only [h,hq]


theorem root_geometry {τ ρ : ℝ} (hτ : τ ∈ Icc (1-1/1073741824 : ℝ) 1)
    (hρ : ρ ∈ Icc (0 : ℝ) (999001/1000000)) :
    |ρ| < 1 ∧ ρ ≤ τ^2*(1-1/1024) ∧
    Real.log (1-τ^2*(1-1/1024)^2) - Real.log (1-ρ^2) ≤ 0 := by
  have ht0 : 0 ≤ τ := by linarith [hτ.1]
  have hts : (1-1/1073741824 : ℝ)^2 ≤ τ^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hτ.1) (show 0 ≤ τ+(1-1/1073741824 : ℝ) by positivity)]
  have ht1 : τ^2 ≤ 1 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hτ.2)]
  have hlim : ρ ≤ τ^2*(1-1/1024) := by nlinarith only [hts,hρ.2]
  have hlim' : ρ ≤ τ*(1-1/1024) := by
    have hsq : τ^2 ≤ τ := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hτ.2)]
    nlinarith only [hlim,hsq]
  have htρ := mul_le_mul hlim' hlim' hρ.1 (show 0 ≤ τ*(1-1/1024) by positivity)
  have hpos : 0 < 1-τ^2*(1-1/1024)^2 := by nlinarith only [ht1]
  have hh := Real.log_le_log hpos (show 1-τ^2*(1-1/1024)^2 ≤ 1-ρ^2 by nlinarith only [htρ])
  refine ⟨?_,hlim,sub_nonpos.mpr hh⟩
  rw [abs_of_nonneg hρ.1]
  linarith [hρ.2]

/-- Transfer the normalized De estimate to the actual count, pay the
damping term, and reserve a uniform margin for the finite remainder. -/
theorem linear_withCount {N x m sr De Sg qlo A e : ℝ}
    (hN : 0 ≤ N) (hx : 0 < x) (hSg : Sg ≤ 0)
    (hm : qlo*N/2 ≤ m) (he : 0 ≤ e) (hemax : e ≤ 1/1073741824)
    (hA : 0 ≤ A) (hAmax : A ≤ 6100)
    (hlinear : 72/1000 + sr*De + qlo/2*Sg ≤ 11/10) :
    72*N*(1/1000) + 2*x*((sr*N/x)*(De/2)) + m*Sg + 2*(72*N)*e*A ≤
      (5/4-1/10)*N := by
  have hde : 2*x*((sr*N/x)*(De/2)) = sr*N*De := by field_simp [hx.ne'] <;> ring
  have hsg := mul_le_mul_of_nonpos_right hm hSg
  have hdamp := mul_le_mul hemax hAmax hA (by norm_num : (0 : ℝ) ≤ 1/1073741824)
  have hdamp' : 2*(72*N)*e*A ≤ (1/100 : ℝ)*N := by
    have h := mul_le_mul_of_nonneg_left hdamp (show 0 ≤ 2*(72*N) by positivity)
    nlinarith only [h,hN]
  rw [hde]
  have hlin := mul_le_mul_of_nonneg_right hlinear hN
  nlinarith only [hlin,hsg,hdamp',hN]
end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeLinear72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeLinear72.scalar0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeLinear72.scalar1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeLinear72.scalar2
