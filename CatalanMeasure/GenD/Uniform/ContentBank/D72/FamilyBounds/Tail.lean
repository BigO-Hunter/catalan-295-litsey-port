module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
public import CatalanMeasure.GenD.Uniform.W.Thin.TRawTail
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section

#time theorem w137_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (222 / 11 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (146 / 7 : ℝ) * N) :
    (N : ℝ) * ((-20 : ℝ) + (1 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((tTailLB P72 p72_admissible).kap N p : ℝ) := by
  have hl : 222 * N < 11 * p := by
    exact_mod_cast (show (222 : ℝ) * N < 11 * p by linarith)
  have hh : 7 * p ≤ 146 * N := by
    exact_mod_cast (show (7 : ℝ) * p ≤ 146 * N by linarith)
  have ha : TTailApp P72 N p := by
    unfold TTailApp
    rw [p72_H, p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    repeat' apply And.intro
    all_goals omega
  let v := (tTailLB P72 p72_admissible).kap N p
  have hv : v = tTailVal P72 N p := by
    classical
    change (if TTailApp P72 N p then tTailVal P72 N p else 0) = _
    exact if_pos ha
  have hc : (2) * p ≤ (2) * v + (4) * 1 + (40) * N := by
    rw [hv]
    unfold tTailVal
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  have hcR : (2 : ℝ) * p ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (40 : ℝ) * N := by exact_mod_cast hc
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-20 : ℝ) + (1 : ℝ) * ((p : ℝ) / N)) = (-20 : ℝ) * N + (1 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  change _ ≤ (v : ℝ)
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
