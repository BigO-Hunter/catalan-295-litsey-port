module
public import Submission.CatalanMeasure.GenD.Signed.DesignConst
public import Submission.CatalanMeasure.GenD.DesignInstance.PositiveBudget

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 0

namespace CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD D58 CatalanMeasure.Parametric
noncomputable section

/-! FK literals. The exact content comparison is proved in Pay from seven cw areas. -/
def content296 : ℝ := (0x33b226df05efafb7e3 : ℝ) / 0x25c6ecd580a48ba00
def shift296 : ℝ := 57783 / 2500
def eta296 : ℝ := 798775/100000 + content296 + shift296 - 1/1000
def content295 : ℝ := 220607/10000
def eta295 : ℝ := 798775/100000 + content295 + shift296 - 1/1000
def G58 (x : ℝ) : Prop := x≤-19501/100000 ∨ (98749/1000000:ℝ)≤x
def T296 : ℝ := K590.target + shift296 / 58 ^ 2
def cost296 : ℝ := 3596893 / 1000000
def psi296 : ℝ := 8723 / 100
def rho296 : ℝ := 58 * cost296 + psi296
def alpha296 : ℝ := 51 / 500
def delta296 : ℝ := 29 / 100000000

theorem rho296_eq : rho296 = (147924897 / 500000 : ℝ) := by
  norm_num [rho296, cost296, psi296]

theorem dc58_normalizer_cut : dc58.toParameters.H 1 < 79 := by
  norm_num [dc58, Parameters.H, Parameters.C, Parameters.L,
    Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]

end
end CatalanMeasure.GenD.Signed.RouteI
#print axioms CatalanMeasure.GenD.Signed.RouteI.rho296_eq
#print axioms CatalanMeasure.GenD.Signed.RouteI.dc58_normalizer_cut




