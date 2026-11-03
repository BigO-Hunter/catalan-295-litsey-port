module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SheetBindings
public import CatalanMeasure.GenD.Budget
public import Mathlib.Analysis.Complex.ExponentialBounds
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneBudgets
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
open Davis.ScalarInstance72 ReferenceData
noncomputable section
/-! C23 shared standalone budget representative. Source stepB72/standalone-budgets.json
SHA256 1fb6ea37eda7903bb7b473d2a339585bfb0e82b89a2bb48e36dc1b5e2eb32a25. Fourteen distinct rational propositions plus
two existing log2 bounds; approximately63 primitive rational operations (0.0063s
arithmetic estimate, before proof checking). No norm or decay cap is asserted.
The alpha=0 reference uses baseTarget72, separately from target72. -/
theorem log_bounds : (6931471803/10000000000:ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (108304247/156250000:ℝ) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith
def secondNormCap : ℝ := (3880566911/5000000000:ℝ)
def secondMX : ℝ := -96992793/100000000
def secondMY : ℝ := -158005012/100000000
def secondFieldCap : ℝ := secondMX+secondMY
def secondResidual : ℝ := (-3454601/50000000:ℝ)
def secondNearCap : ℝ := (-77/100:ℝ)

theorem first_budget (a : ℝ) :
    (-gC0 dc72.toParameters+gC1 dc72.toParameters*a-a^2)*Real.log 2+firstNormCap+
      (1-a)*firstFieldCap+a*(2*firstLambda*((dc72.toParameters.g0:ℝ)/dc72.toParameters.n0)) ≤
        -target72+Real.log 2/2+cost72*a := by
  have h := Budget.first_budget' (ℓ := Real.log 2) (a := a) (lo := (6931471803/10000000000:ℝ)) (hi := (108304247/156250000:ℝ)) (c07 := (17/24:ℝ)) (c26 := (21/8:ℝ)) (res := (0/1:ℝ)) (cost1 := (3604373/1000000:ℝ)) (n1 := (53/100:ℝ)) (F1 := (-2329/1000:ℝ)) (Lm := (4/15:ℝ)) (T := (122434648561/54000000000:ℝ)) (m := (48969243419/2160000000000:ℝ))
    (by norm_num) log_bounds.1 log_bounds.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;>
    norm_num [gC0,gC1,gKappa,gRes,dc72,firstNormCap,firstFieldCap,firstLambda,
      target72,baseTarget72,gain72,cost72] <;> ring

theorem large_budget {a t : ℝ} (ha : (1/16:ℝ) ≤ a) (_ha0 : 0 ≤ a) (ht : 0 ≤ t) :
    (-gC0 dc72.toParameters+gC1 dc72.toParameters*a-a^2+t-t^2)*Real.log 2+
      secondNormCap+(1-a)*secondFieldCap+(a-t)*secondResidual+t*secondNearCap ≤
        -target72+Real.log 2/2+cost72*a := by
  have h := Budget.second_budget'_large (ℓ := Real.log 2) (a := a) (t := t) (lo := (6931471803/10000000000:ℝ)) (hi := (108304247/156250000:ℝ)) (c07 := (17/24:ℝ)) (c26 := (21/8:ℝ)) (res := (0/1:ℝ)) (cost := (3604373/1000000:ℝ)) (Nn := (3880566911/5000000000:ℝ)) (M := (-50999561/20000000:ℝ)) (r := (-3454601/50000000:ℝ)) (nc := (-77/100:ℝ)) (T := (122434648561/54000000000:ℝ)) (u := (5323074133/2160000000000:ℝ)) (α1 := (1/16:ℝ))
    (by norm_num) log_bounds.1 log_bounds.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha ht
  convert h using 1 <;>
    norm_num [gC0,gC1,gKappa,gRes,dc72,secondNormCap,secondFieldCap,secondMX,secondMY,
      secondResidual,secondNearCap,target72,baseTarget72,gain72,cost72] <;> ring

theorem reference_budget {a t : ℝ} (_ha : (0:ℝ) ≤ a) (ha0 : 0 ≤ a) (ht : 0 ≤ t) :
    (-gC0 dc72.toParameters+gC1 dc72.toParameters*a-a^2+t-t^2)*Real.log 2+
      secondNormCap+(1-a)*secondFieldCap+(a-t)*secondResidual+t*secondNearCap ≤
        -baseTarget72+Real.log 2/2+cost72*a := by
  have h := Budget.second_budget' (ℓ := Real.log 2) (a := a) (t := t) (lo := (6931471803/10000000000:ℝ)) (hi := (108304247/156250000:ℝ)) (c07 := (17/24:ℝ)) (c26 := (21/8:ℝ)) (res := (0/1:ℝ)) (cost := (3604373/1000000:ℝ)) (Nn := (3880566911/5000000000:ℝ)) (M := (-50999561/20000000:ℝ)) (r := (-3454601/50000000:ℝ)) (nc := (-77/100:ℝ)) (T := (1132420467/500000000:ℝ)) (m := (298609/100000000000:ℝ))
    (by norm_num) log_bounds.1 log_bounds.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ha0 ht
  convert h using 1 <;>
    norm_num [gC0,gC1,gKappa,gRes,dc72,secondNormCap,secondFieldCap,secondMX,secondMY,
      secondResidual,secondNearCap,baseTarget72,cost72] <;> ring
end
end CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneBudgets
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneBudgets.log_bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneBudgets.first_budget
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneBudgets.large_budget
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneBudgets.reference_budget
