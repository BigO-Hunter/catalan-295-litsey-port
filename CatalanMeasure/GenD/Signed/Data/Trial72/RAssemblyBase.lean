module

public import CatalanMeasure.GenD.Signed.Data.Assembly.CurvFast
public import CatalanMeasure.GenD.Signed.Data.Trial72.Core

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RAssemblyBase
open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Cert
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.GenD.Signed.Data.Trial72 CatalanMeasure.GenD.Signed.Data.Assembly
noncomputable section

def rLimQ (η l2 Vq Pq Rq Aq raq iRRq Lq γ Sup σ Bq : ℚ) : ℚ :=
  -(1 + η) * l2 + Vq / 2 + 2 * η * Pq + (1 - η) * Rq + 2 * (Aq - γ * Sup - raq) + σ ^ 2 * Bq +
    iRRq / 2 - Lq / 2

theorem rLim_cast (η l2 Vq Pq Rq Aq raq iRRq Lq γ Sup σ Bq : ℚ) :
    rLim (η : ℝ) (l2 : ℝ) (Vq : ℝ) (Pq : ℝ) (Rq : ℝ) (Aq : ℝ) (raq : ℝ) (iRRq : ℝ) (Lq : ℝ) (γ : ℝ)
      (Sup : ℝ) (σ : ℝ) (Bq : ℝ) = ((rLimQ η l2 Vq Pq Rq Aq raq iRRq Lq γ Sup σ Bq : ℚ) : ℝ) := by
  unfold rLim rLimQ
  push_cast
  ring

theorem anti {η l2 Vq Pq Rq Aq raq raq' iRRq Lq Lq' γ Sup σ Bq : ℚ}
    (hra : raq' ≤ raq) (hip : Lq' ≤ Lq) :
    rLimQ η l2 Vq Pq Rq Aq raq iRRq Lq γ Sup σ Bq ≤
      rLimQ η l2 Vq Pq Rq Aq raq' iRRq Lq' γ Sup σ Bq := by
  unfold rLimQ
  linarith only [hra, hip]

def logTwoLower : ℚ := 6931471803 / 10000000000

theorem logTwo_bound : (logTwoLower : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num [logTwoLower] at h ⊢
  linarith

theorem g72 : ((dc72.g0 : ℕ) : ℝ) / (dc72.n0 : ℝ) = ((1 / 12 : ℚ) : ℝ) := by
  norm_num [dc72]

theorem s72 : ((dc72.sp : ℕ) : ℝ) / (dc72.n0 : ℝ) = ((5 / 18 : ℚ) : ℝ) := by
  norm_num [dc72]

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RAssemblyBase
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RAssemblyBase.rLim_cast
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RAssemblyBase.anti
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RAssemblyBase.logTwo_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RAssemblyBase.g72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RAssemblyBase.s72
