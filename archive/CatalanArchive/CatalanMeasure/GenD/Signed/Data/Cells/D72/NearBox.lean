module
public import CatalanMeasure.GenD.DesignInstance.PositiveControl.Near
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.NearBox
open Set CatalanMeasure.Cert CatalanMeasure.GenD.Signed
noncomputable section
/-- A rational lower bound for the exact frozen positive72 first coefficient. -/
def p0 : ℚ := 1772688/10000000
def terms : List LogTerm := [⟨-11/12,0,1+(963/1250)^2,0⟩,⟨59/72,0,1541/2000,0⟩]
def boxOK : Bool := match sumLogs terms with
  | some ve => decide (ve.1+ve.2-p0*(963/1250) ≤ -(77/100:ℚ))
  | none => false

/-- kcost: two real log evaluator calls and one rational upper comparison; no cover grid. -/
theorem box : -(11/12:ℝ)*Real.log (1+(963/1250:ℝ)^2)+
    (59/72)*Real.log (1541/2000:ℝ)-(p0:ℝ)*(963/1250) ≤ -(77/100:ℝ) := by
  have hc : boxOK = true := by decide +kernel
  unfold boxOK at hc
  split at hc
  · rename_i ve he
    have hh := sumLogs_spec he
    have hv : (terms.map LogTerm.val).sum =
        -(11/12:ℝ)*Real.log (1+(963/1250:ℝ)^2)+
          (59/72)*Real.log (1541/2000:ℝ) := by
      simp only [terms,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      rw [realLogTerm (-11/12) (1+(963/1250)^2) (by norm_num),
        realLogTerm (59/72) (1541/2000) (by norm_num)]
      norm_num
    rw [hv] at hh
    have hq : ve.1+ve.2-p0*(963/1250) ≤ -(77/100:ℚ) := of_decide_eq_true hc
    have hr : ((ve.1+ve.2-p0*(963/1250):ℚ):ℝ) ≤ ((-(77/100):ℚ):ℝ) := by
      exact_mod_cast hq
    push_cast at hr
    norm_num at hr
    linarith only [(abs_le.mp hh).2,hr]
  · simp at hc

/-- The generic monotonicity route closes the entire near field from one log box. -/
theorem near_sup {p y : ℝ} (hp : (p0:ℝ) ≤ p) (hy : y ∈ Ioo (0:ℝ) 1) :
    -(11/12:ℝ)*Real.log (1+y^2)+(59/72)*Real.log y-p*y ≤ -(77/100:ℝ) := by
  apply near_residual_field_le (p0 := (p0:ℝ)) (l := 963/1250) (u := 1541/2000)
  · norm_num
  · norm_num
  · norm_num [p0]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num [p0]
  · norm_num [p0]
  · exact box
  · exact hp
  · exact hy.1
  · exact le_of_lt hy.2

/-- The frozen rational first coefficient exceeds the simple p0 used above. -/
theorem frozen_p1_lower : p0 ≤ (38981821736761334053339/219902325555200000000000:ℚ) := by
  norm_num [p0]
end
end CatalanMeasure.GenD.Signed.Data.Cells.D72.NearBox
#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.NearBox.box
#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.NearBox.near_sup
#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.NearBox.frozen_p1_lower
