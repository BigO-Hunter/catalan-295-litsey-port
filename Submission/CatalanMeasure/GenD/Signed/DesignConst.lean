module

public import Submission.CatalanMeasure.Parametric.Parameters
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Shared determinant design and signed-proof choices

Field names and exact rational values agree with `phase2-data/design_config.py`.
Certificate outputs (norms, margins, C1, payment data) are supplied by consumers.
-/

namespace CatalanMeasure.GenD.Signed

open CatalanMeasure.Parametric

/-- The determinant parameters and independently chosen signed-proof geometry. -/
structure DesignConst extends Parameters where
  sp : ℕ
  spc : ℚ
  m_cuts_B1 : List ℚ
  m_cuts_B2 : List ℚ
  m_top : ℚ
  gstar : ℚ
  xc : ℚ
  thetaL : ℚ
  rc : ℚ
  bilin : ℚ
  sr_offset : ℚ
  hspq_qlo : ℚ
  near_shift_b : ℚ
  p1min : ℚ
  admissible : Admissible toParameters
  sp_pos : 0 < sp
  sp_le_n0 : sp ≤ n0
  spc_bounds : (sp : ℚ) ≤ spc ∧ spc ≤ (n0 : ℚ)
  thetaL_mem : 0 < thetaL ∧ thetaL < 1
  gstar_mem : 0 < gstar ∧ gstar < 1
  xc_mem : 0 < xc ∧ xc < 1
  gstar_lt_xc : gstar < xc
  rc_bounds : 1 < rc ∧ rc ≤ 2
  bilin_nonneg : 0 ≤ bilin
  p1min_nonneg : 0 ≤ p1min
  cuts_B1_ordered : m_cuts_B1.Pairwise (· ≤ ·)
  cuts_B2_ordered : m_cuts_B2.Pairwise (· ≤ ·)
  cuts_B1_bounds : ∀ x ∈ m_cuts_B1, 0 ≤ x ∧ x ≤ m_top
  cuts_B2_bounds : ∀ x ∈ m_cuts_B2, 0 ≤ x ∧ x ≤ m_top

namespace DesignConst

def d0 (dc : DesignConst) : ℕ := dc.n0 - dc.g0
def H (dc : DesignConst) : ℕ := dc.n0 + dc.b0 + dc.q0 + dc.g0 + dc.h0
def c (dc : DesignConst) : ℚ := dc.d0 / (dc.n0 : ℚ)
def cp (dc : DesignConst) : ℚ := ((dc.n0 : ℚ) - 2 * dc.g0) / dc.n0
def c' (dc : DesignConst) : ℚ := dc.cp
def «c′» (dc : DesignConst) : ℚ := dc.cp
def c_log (dc : DesignConst) : ℚ := ((dc.n0 : ℚ) - 2 * dc.g0 - 1) / dc.n0
def gap_m (dc : DesignConst) : ℕ := dc.q0 + dc.h0
def astar (dc : DesignConst) : ℚ := 2 * dc.gstar / (1 + dc.gstar ^ 2)
def θL (dc : DesignConst) : ℚ := dc.thetaL
def m_cuts (dc : DesignConst) : List ℚ × List ℚ := (dc.m_cuts_B1, dc.m_cuts_B2)
def cap_kappa_num (dc : DesignConst) : ℕ := dc.n0 + dc.b0 + dc.q0 + dc.g0
def c07 (dc : DesignConst) : ℚ := 1 - ((dc.b0 : ℚ) + dc.q0 + dc.g0) / dc.n0
def c26 (dc : DesignConst) : ℚ := 3 - ((dc.b0 : ℚ) + dc.q0 + 2 * dc.g0) / dc.n0
def emax_coef (dc : DesignConst) : ℕ := 2 * dc.n0
def AL (dc : DesignConst) : ℚ := ((dc.b0 : ℚ) + dc.q0 + 2 * dc.g0) / dc.n0
def BE (dc : DesignConst) : ℚ := 2 * (dc.h0 : ℚ) / dc.n0
def GA (dc : DesignConst) : ℚ := dc.H / (dc.n0 : ℚ)
def CB (dc : DesignConst) : ℚ := (dc.b0 : ℚ) / dc.n0
def CQ (dc : DesignConst) : ℚ := (dc.q0 : ℚ) / dc.n0
def GD (dc : DesignConst) : ℚ := dc.c
def ENF (dc : DesignConst) : ℚ := dc.cp
def sigma (dc : DesignConst) : ℚ := (dc.sp : ℚ) / dc.n0

theorem n0_pos (dc : DesignConst) : 0 < dc.n0 := dc.admissible.1

theorem g0_le_n0 (dc : DesignConst) : dc.g0 ≤ dc.n0 := by
  have h := dc.admissible.2.2.2.2
  omega

theorem d0_add_g0 (dc : DesignConst) : dc.d0 + dc.g0 = dc.n0 :=
  Nat.sub_add_cancel dc.g0_le_n0

theorem H_scale (dc : DesignConst) (N : ℕ) : dc.toParameters.H N = dc.H * N := by
  simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
    Parameters.q, Parameters.g, Parameters.h, H, Nat.add_mul]

end DesignConst

/-- The current design; the Python default is the same exact table. -/
def dc58 : DesignConst where
  toParameters := ⟨58, 9, 3, 5, 3⟩
  sp := 20
  spc := 63 / 2
  m_cuts_B1 := [9 / 32, 15 / 32]
  m_cuts_B2 := [19 / 100, 19 / 50, 1 / 2]
  m_top := 57 / 100
  gstar := 401 / 2500
  xc := 999 / 1000
  thetaL := 1 / 1024
  rc := 11 / 8
  bilin := 5 / 11
  sr_offset := 5
  hspq_qlo := 25 / 58
  near_shift_b := 11 / 4
  p1min := 9 / 50
  admissible := by norm_num [Admissible]
  sp_pos := by norm_num
  sp_le_n0 := by norm_num
  spc_bounds := by norm_num
  thetaL_mem := by norm_num
  gstar_mem := by norm_num
  xc_mem := by norm_num
  gstar_lt_xc := by norm_num
  rc_bounds := by norm_num
  bilin_nonneg := by norm_num
  p1min_nonneg := by norm_num
  cuts_B1_ordered := by norm_num [List.pairwise_cons]
  cuts_B2_ordered := by norm_num [List.pairwise_cons]
  cuts_B1_bounds := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> norm_num
  cuts_B2_bounds := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> norm_num

/-- D72, with p1min=17/100 from GATE0-D72 P72_p17. The node gap is provisional. -/
def dc72 : DesignConst where
  toParameters := ⟨72, 11, 4, 6, 4⟩
  sp := 20
  spc := 63 / 2
  m_cuts_B1 := [9 / 32, 15 / 32]
  m_cuts_B2 := [19 / 100, 19 / 50, 1 / 2]
  m_top := 57 / 100
  gstar := 401 / 2500
  xc := 999 / 1000
  thetaL := 1 / 1024
  rc := 11 / 8
  bilin := 5 / 11
  sr_offset := 6
  hspq_qlo := 25 / 58
  near_shift_b := 11 / 4
  p1min := 17 / 100
  admissible := by norm_num [Admissible]
  sp_pos := by norm_num
  sp_le_n0 := by norm_num
  spc_bounds := by norm_num
  thetaL_mem := by norm_num
  gstar_mem := by norm_num
  xc_mem := by norm_num
  gstar_lt_xc := by norm_num
  rc_bounds := by norm_num
  bilin_nonneg := by norm_num
  p1min_nonneg := by norm_num
  cuts_B1_ordered := by norm_num [List.pairwise_cons]
  cuts_B2_ordered := by norm_num [List.pairwise_cons]
  cuts_B1_bounds := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> norm_num
  cuts_B2_bounds := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> norm_num

@[simp] theorem dc72_toParameters : dc72.toParameters = ⟨72, 11, 4, 6, 4⟩ := rfl
@[simp] theorem dc72_n0 : dc72.n0 = 72 := rfl
@[simp] theorem dc72_b0 : dc72.b0 = 11 := rfl
@[simp] theorem dc72_q0 : dc72.q0 = 4 := rfl
@[simp] theorem dc72_g0 : dc72.g0 = 6 := rfl
@[simp] theorem dc72_h0 : dc72.h0 = 4 := rfl
@[simp] theorem dc72_d0 : dc72.d0 = 66 := rfl
@[simp] theorem dc72_H : dc72.H = 97 := rfl
@[simp] theorem dc72_H_succ : dc72.H + 1 = 98 := rfl
@[simp] theorem dc72_gstar : dc72.gstar = 401 / 2500 := rfl
@[simp] theorem dc72_p1min : dc72.p1min = 17 / 100 := rfl

@[simp] theorem dc58_toParameters : dc58.toParameters = ⟨58, 9, 3, 5, 3⟩ := rfl
@[simp] theorem dc58_n0 : dc58.n0 = 58 := rfl
@[simp] theorem dc58_b0 : dc58.b0 = 9 := rfl
@[simp] theorem dc58_q0 : dc58.q0 = 3 := rfl
@[simp] theorem dc58_g0 : dc58.g0 = 5 := rfl
@[simp] theorem dc58_h0 : dc58.h0 = 3 := rfl
@[simp] theorem dc58_sp : dc58.sp = 20 := rfl
@[simp] theorem dc58_spc : dc58.spc = 63 / 2 := rfl
@[simp] theorem dc58_m_cuts_B1 : dc58.m_cuts_B1 = [9 / 32, 15 / 32] := rfl
@[simp] theorem dc58_m_cuts_B2 : dc58.m_cuts_B2 = [19 / 100, 19 / 50, 1 / 2] := rfl
@[simp] theorem dc58_m_top : dc58.m_top = 57 / 100 := rfl
@[simp] theorem dc58_gstar : dc58.gstar = 401 / 2500 := rfl
@[simp] theorem dc58_xc : dc58.xc = 999 / 1000 := rfl
@[simp] theorem dc58_thetaL : dc58.thetaL = 1 / 1024 := rfl
@[simp] theorem dc58_rc : dc58.rc = 11 / 8 := rfl
@[simp] theorem dc58_bilin : dc58.bilin = 5 / 11 := rfl
@[simp] theorem dc58_sr_offset : dc58.sr_offset = 5 := rfl
@[simp] theorem dc58_hspq_qlo : dc58.hspq_qlo = 25 / 58 := rfl
@[simp] theorem dc58_near_shift_b : dc58.near_shift_b = 11 / 4 := rfl
@[simp] theorem dc58_p1min : dc58.p1min = 9 / 50 := rfl
@[simp] theorem dc58_d0 : dc58.d0 = 53 := rfl
@[simp] theorem dc58_H : dc58.H = 78 := rfl
@[simp] theorem dc58_H_succ : dc58.H + 1 = 79 := rfl
@[simp] theorem dc58_c : dc58.c = 53 / 58 := rfl
@[simp] theorem dc58_cp : dc58.cp = 24 / 29 := by norm_num [DesignConst.cp]
@[simp] theorem dc58_c' : dc58.c' = 24 / 29 := dc58_cp
@[simp] theorem «dc58_c′» : dc58.«c′» = 24 / 29 := dc58_cp
@[simp] theorem dc58_c_log : dc58.c_log = 47 / 58 := by norm_num [DesignConst.c_log]
@[simp] theorem dc58_gap_m : dc58.gap_m = 6 := rfl
@[simp] theorem dc58_astar : dc58.astar = 2005000 / 6410801 := by
  norm_num [DesignConst.astar]
@[simp] theorem dc58_θL : dc58.θL = 1 / 1024 := rfl
@[simp] theorem dc58_cap_kappa_num : dc58.cap_kappa_num = 75 := rfl
@[simp] theorem dc58_c07 : dc58.c07 = 41 / 58 := by norm_num [DesignConst.c07]
@[simp] theorem dc58_c26 : dc58.c26 = 76 / 29 := by norm_num [DesignConst.c26]
@[simp] theorem dc58_emax_coef : dc58.emax_coef = 116 := rfl
@[simp] theorem dc58_AL : dc58.AL = 11 / 29 := by norm_num [DesignConst.AL]
@[simp] theorem dc58_BE : dc58.BE = 3 / 29 := by norm_num [DesignConst.BE]
@[simp] theorem dc58_GA : dc58.GA = 39 / 29 := by norm_num [DesignConst.GA]
@[simp] theorem dc58_CB : dc58.CB = 9 / 58 := rfl
@[simp] theorem dc58_CQ : dc58.CQ = 3 / 58 := rfl
@[simp] theorem dc58_GD : dc58.GD = 53 / 58 := rfl
@[simp] theorem dc58_ENF : dc58.ENF = 24 / 29 := dc58_cp
@[simp] theorem dc58_sigma : dc58.sigma = 10 / 29 := by norm_num [DesignConst.sigma]

end CatalanMeasure.GenD.Signed

#print axioms CatalanMeasure.GenD.Signed.DesignConst.n0_pos
#print axioms CatalanMeasure.GenD.Signed.DesignConst.g0_le_n0
#print axioms CatalanMeasure.GenD.Signed.DesignConst.d0_add_g0
#print axioms CatalanMeasure.GenD.Signed.DesignConst.H_scale
#print axioms CatalanMeasure.GenD.Signed.dc58_toParameters
#print axioms CatalanMeasure.GenD.Signed.dc58_n0
#print axioms CatalanMeasure.GenD.Signed.dc58_b0
#print axioms CatalanMeasure.GenD.Signed.dc58_q0
#print axioms CatalanMeasure.GenD.Signed.dc58_g0
#print axioms CatalanMeasure.GenD.Signed.dc58_h0
#print axioms CatalanMeasure.GenD.Signed.dc58_sp
#print axioms CatalanMeasure.GenD.Signed.dc58_spc
#print axioms CatalanMeasure.GenD.Signed.dc58_m_cuts_B1
#print axioms CatalanMeasure.GenD.Signed.dc58_m_cuts_B2
#print axioms CatalanMeasure.GenD.Signed.dc58_m_top
#print axioms CatalanMeasure.GenD.Signed.dc58_gstar
#print axioms CatalanMeasure.GenD.Signed.dc58_xc
#print axioms CatalanMeasure.GenD.Signed.dc58_thetaL
#print axioms CatalanMeasure.GenD.Signed.dc58_rc
#print axioms CatalanMeasure.GenD.Signed.dc58_bilin
#print axioms CatalanMeasure.GenD.Signed.dc58_sr_offset
#print axioms CatalanMeasure.GenD.Signed.dc58_hspq_qlo
#print axioms CatalanMeasure.GenD.Signed.dc58_near_shift_b
#print axioms CatalanMeasure.GenD.Signed.dc58_p1min
#print axioms CatalanMeasure.GenD.Signed.dc58_d0
#print axioms CatalanMeasure.GenD.Signed.dc58_H
#print axioms CatalanMeasure.GenD.Signed.dc58_H_succ
#print axioms CatalanMeasure.GenD.Signed.dc58_c
#print axioms CatalanMeasure.GenD.Signed.dc58_cp
#print axioms CatalanMeasure.GenD.Signed.dc58_c'
#print axioms CatalanMeasure.GenD.Signed.«dc58_c′»
#print axioms CatalanMeasure.GenD.Signed.dc58_c_log
#print axioms CatalanMeasure.GenD.Signed.dc58_gap_m
#print axioms CatalanMeasure.GenD.Signed.dc58_astar
#print axioms CatalanMeasure.GenD.Signed.dc58_θL
#print axioms CatalanMeasure.GenD.Signed.dc58_cap_kappa_num
#print axioms CatalanMeasure.GenD.Signed.dc58_c07
#print axioms CatalanMeasure.GenD.Signed.dc58_c26
#print axioms CatalanMeasure.GenD.Signed.dc58_emax_coef
#print axioms CatalanMeasure.GenD.Signed.dc58_AL
#print axioms CatalanMeasure.GenD.Signed.dc58_BE
#print axioms CatalanMeasure.GenD.Signed.dc58_GA
#print axioms CatalanMeasure.GenD.Signed.dc58_CB
#print axioms CatalanMeasure.GenD.Signed.dc58_CQ
#print axioms CatalanMeasure.GenD.Signed.dc58_GD
#print axioms CatalanMeasure.GenD.Signed.dc58_ENF
#print axioms CatalanMeasure.GenD.Signed.dc58_sigma

#print axioms CatalanMeasure.GenD.Signed.dc72_toParameters
#print axioms CatalanMeasure.GenD.Signed.dc72_n0
#print axioms CatalanMeasure.GenD.Signed.dc72_b0
#print axioms CatalanMeasure.GenD.Signed.dc72_q0
#print axioms CatalanMeasure.GenD.Signed.dc72_g0
#print axioms CatalanMeasure.GenD.Signed.dc72_h0
#print axioms CatalanMeasure.GenD.Signed.dc72_d0
#print axioms CatalanMeasure.GenD.Signed.dc72_H
#print axioms CatalanMeasure.GenD.Signed.dc72_H_succ
#print axioms CatalanMeasure.GenD.Signed.dc72_gstar
#print axioms CatalanMeasure.GenD.Signed.dc72_p1min
