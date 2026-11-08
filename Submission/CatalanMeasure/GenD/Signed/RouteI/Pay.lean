module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Literals
public import Submission.CatalanMeasure.GenD.Signed.Gate

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 0

namespace CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD D58
noncomputable section

theorem pay296 :
    PayW' (3/5) (dc58.d0 : ℝ) rho296 eta296 (296/rho296) delta296 296 := by
  apply Signed.Generic.payB' dc58 (3/5) rho296 eta296 delta296 296 <;>
    norm_num [rho296, cost296, psi296, eta296, content296, shift296, delta296, dc58_d0]

/-- Conditional295 payment: the content provider must still supply growth/gain. -/
theorem pay295 :
    PayW' (3/5) (dc58.d0 : ℝ) rho296 eta295 (295/rho296) delta296 295 := by
  apply Signed.Generic.payB' dc58 (3/5) rho296 eta295 delta296 295 <;>
    norm_num [rho296,cost296,psi296,eta295,content295,shift296,delta296,dc58_d0]


end
end CatalanMeasure.GenD.Signed.RouteI
#print axioms CatalanMeasure.GenD.Signed.RouteI.pay296
#print axioms CatalanMeasure.GenD.Signed.RouteI.pay295
