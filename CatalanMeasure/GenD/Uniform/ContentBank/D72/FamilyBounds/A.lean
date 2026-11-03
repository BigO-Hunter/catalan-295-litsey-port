module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
public import CatalanMeasure.GenD.Interface
public import CatalanMeasure.GenD.Uniform.W.SlotsA.LB
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.Arithmetic
noncomputable section

open CatalanMeasure.GenD.Uniform.W.SlotsA
def aLB72 : NullityLB P72 := aLB P72 p72_admissible

#time theorem w127_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (74 / 5 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (15 : ℝ) * N) :
    (N : ℝ) * ((-74 : ℝ) + (5 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (aLB72.kap N p : ℝ) := by
  have hl : 74 * N < 5 * p := by
    exact_mod_cast (show (74 : ℝ) * N < 5 * p by linarith)
  have hh : 1 * p ≤ 15 * N := by
    exact_mod_cast (show (1 : ℝ) * p ≤ 15 * N by linarith)
  have ha : aApp P72 N p := by
    unfold aApp uM0
    rw [p72_H, p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  let v := aVal P72 N p
  have hc : (10) * p ≤ (2) * v + (4) * 1 + (148) * N := by
    unfold v aVal uM0 uM1 sE
    rw [p72_H, p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  have hv : v ≤ aLB72.kap N p := by
    classical
    change v ≤ (if aApp P72 N p then aVal P72 N p else 0)
    rw [if_pos ha]
  have hcR : (10 : ℝ) * p ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (148 : ℝ) * N := by exact_mod_cast hc
  have hvR : (v : ℝ) ≤ aLB72.kap N p := by exact_mod_cast hv
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-74 : ℝ) + (5 : ℝ) * ((p : ℝ) / N)) = (-74 : ℝ) * N + (5 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  linarith

#time theorem w128_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (15 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (16 : ℝ) * N) :
    (N : ℝ) * ((-14 : ℝ) + (1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (aLB72.kap N p : ℝ) := by
  have hl : 15 * N < 1 * p := by
    exact_mod_cast (show (15 : ℝ) * N < 1 * p by linarith)
  have hh : 1 * p ≤ 16 * N := by
    exact_mod_cast (show (1 : ℝ) * p ≤ 16 * N by linarith)
  have ha : aApp P72 N p := by
    unfold aApp uM0
    rw [p72_H, p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  let v := aVal P72 N p
  have hc : (2) * p ≤ (2) * v + (4) * 1 + (28) * N := by
    unfold v aVal uM0 uM1 sE
    rw [p72_H, p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  have hv : v ≤ aLB72.kap N p := by
    classical
    change v ≤ (if aApp P72 N p then aVal P72 N p else 0)
    rw [if_pos ha]
  have hcR : (2 : ℝ) * p ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (28 : ℝ) * N := by exact_mod_cast hc
  have hvR : (v : ℝ) ≤ aLB72.kap N p := by exact_mod_cast hv
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-14 : ℝ) + (1 : ℝ) * ((p : ℝ) / N)) = (-14 : ℝ) * N + (1 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  linarith

#time theorem w129_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (16 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (97 / 6 : ℝ) * N) :
    (N : ℝ) * ((-6 : ℝ) + (1 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (aLB72.kap N p : ℝ) := by
  have hl : 16 * N < 1 * p := by
    exact_mod_cast (show (16 : ℝ) * N < 1 * p by linarith)
  have hh : 6 * p ≤ 97 * N := by
    exact_mod_cast (show (6 : ℝ) * p ≤ 97 * N by linarith)
  have ha : aApp P72 N p := by
    unfold aApp uM0
    rw [p72_H, p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  let v := aVal P72 N p
  have hc : (1) * p ≤ (2) * v + (4) * 1 + (12) * N := by
    unfold v aVal uM0 uM1 sE
    rw [p72_H, p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  have hv : v ≤ aLB72.kap N p := by
    classical
    change v ≤ (if aApp P72 N p then aVal P72 N p else 0)
    rw [if_pos ha]
  have hcR : (1 : ℝ) * p ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (12 : ℝ) * N := by exact_mod_cast hc
  have hvR : (v : ℝ) ≤ aLB72.kap N p := by exact_mod_cast hv
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-6 : ℝ) + (1 / 2 : ℝ) * ((p : ℝ) / N)) = (-6 : ℝ) * N + (1 / 2 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  linarith

#time theorem w130_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (97 / 6 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (182 / 11 : ℝ) * N) :
    (N : ℝ) * ((91 : ℝ) + (-11 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (aLB72.kap N p : ℝ) := by
  have hl : 97 * N < 6 * p := by
    exact_mod_cast (show (97 : ℝ) * N < 6 * p by linarith)
  have hh : 11 * p ≤ 182 * N := by
    exact_mod_cast (show (11 : ℝ) * p ≤ 182 * N by linarith)
  have ha : aApp P72 N p := by
    unfold aApp uM0
    rw [p72_H, p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  let v := aVal P72 N p
  have hc : (182) * N ≤ (2) * v + (4) * 1 + (11) * p := by
    unfold v aVal uM0 uM1 sE
    rw [p72_H, p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  have hv : v ≤ aLB72.kap N p := by
    classical
    change v ≤ (if aApp P72 N p then aVal P72 N p else 0)
    rw [if_pos ha]
  have hcR : (182 : ℝ) * N ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (11 : ℝ) * p := by exact_mod_cast hc
  have hvR : (v : ℝ) ≤ aLB72.kap N p := by exact_mod_cast hv
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((91 : ℝ) + (-11 / 2 : ℝ) * ((p : ℝ) / N)) = (91 : ℝ) * N + (-11 / 2 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
