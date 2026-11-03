module

public import CatalanMeasure.GenD.Signed.Data.Consts.LinkSigns
public import CatalanMeasure.GenD.Signed.Data.Consts.LinkSlope
public import CatalanMeasure.GenD.Signed.Data.Consts.LinkStatP
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
public import CatalanMeasure.GenD.Signed.Data.Trial72.LMeanPilot
public import CatalanMeasure.GenD.Signed.Data.Trial72.LRows00
public import CatalanMeasure.GenD.Signed.Data.Trial72.LRows01
public import CatalanMeasure.GenD.Signed.Data.Trial72.LRows02
public import CatalanMeasure.GenD.Signed.Data.Trial72.LRows03
public import CatalanMeasure.GenD.Signed.Data.Trial72.LRows04

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
namespace CatalanMeasure.GenD.Signed.Data.Trial72.LControl72
open Set CatalanMeasure.Signed CatalanMeasure.Signed.Consts CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
open CatalanMeasure.GenD.Signed.TaylorCell (vecAdd)
noncomputable section

theorem physical_eq : ReferenceData.secondP =
    trialSeqS NormData.secondPInt ReferenceData.secondPData.tail := by
  change tseqE (fQE ReferenceData.secondPData.f) (ReferenceData.secondPData.tail.map TailQ.toC) = _
  have h := perturb_seq NormData.secondPInt [] ReferenceData.secondPData.tail
  have hv (l : List ℚ) : vecAdd l [] = l := by cases l <;> rfl
  rw [hv, NormData.secondPInt_eq] at h
  simpa [fQE] using h

theorem certH_sum (e : ℚ) (g : List ℚ) : certH g.length (gcertG (e : ℝ) g) =
    ((∑ k ∈ Finset.range g.length, (g.getD k 0 / (1-e)^(k+1))^2 * (k+1) : ℚ) : ℝ) := by
  rw [certH_gcert, Hq, idxSum_cast]
  simp only [Nat.zero_add]
  push_cast <;> rfl

theorem gCp_eq : LRows00.Row0.g = gCp := by decide +kernel
theorem cCp_eq : LRows00.Row0.c0 = c0Cp := by decide +kernel

theorem actualStatCp : certH LRows00.Row0.g.length (gcertG (LRows00.Row0.e : ℝ) LRows00.Row0.g) * (13/5000 : ℝ) ≤ (LRows00.Row0.s : ℝ)^2 := by
  rw [certH_sum, ← LRows00.Row0.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows00.Row0.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginCp {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((25/58 : ℚ) : ℝ) ≤ (1-α)*(LRows00.Row0.c0 : ℝ) +
      certMean LRows00.Row0.g.length (gcertG (LRows00.Row0.e : ℝ) LRows00.Row0.g) ReferenceData.secondP - (LRows00.Row0.s : ℝ) := by
  rw [physical_eq]
  exact LRows00.Row0.selected_row hα

theorem actualCpMean : certMean LRows00.Row0.g.length (gcertG (LRows00.Row0.e : ℝ) LRows00.Row0.g) ReferenceData.secondP = (LRows00.Row0.m : ℝ) := by
  unfold certMean
  have h := certMean_eval LRows00.Row0.e LRows00.Row0.g NormData.secondPInt ReferenceData.secondPData.tail (n := 60)
    (G := gcertG (LRows00.Row0.e : ℝ) LRows00.Row0.g) (pp := ReferenceData.secondP)
    (by decide +kernel) rfl (fun _ => rfl) (fun k => congrFun physical_eq k)
  rw [← LRows00.Row0.table_checked, ← LRows00.Row0.mean_checked] at h
  exact h

theorem actualCpHalf {α : ℝ} (hα : 0 ≤ α) : 1-α - ((1-α)*(LRows00.Row0.c0 : ℝ) +
    certMean LRows00.Row0.g.length (gcertG (LRows00.Row0.e : ℝ) LRows00.Row0.g) ReferenceData.secondP - (LRows00.Row0.s : ℝ)) ≤ 1/2 := by
  rw [actualCpMean]
  have hc : (LRows00.Row0.c0 : ℝ) ≤ 1 := by exact_mod_cast (show LRows00.Row0.c0 ≤ 1 by decide +kernel)
  have hd : 1 - (LRows00.Row0.c0 : ℝ) - (LRows00.Row0.m : ℝ) + (LRows00.Row0.s : ℝ) ≤ 1/2 := by
    exact_mod_cast (show 1 - LRows00.Row0.c0 - LRows00.Row0.m + LRows00.Row0.s ≤ (1/2 : ℚ) by decide +kernel)
  linarith only [hd, mul_nonneg hα (sub_nonneg.mpr hc)]

theorem actualCp_neg {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) (hy0 : y < 0) :
    evalCert (LRows00.Row0.e : ℝ) LRows00.Row0.g.length (gcertG (LRows00.Row0.e : ℝ) LRows00.Row0.g) (LRows00.Row0.c0 : ℝ) y ≤ 0 := by
  have he : (LRows00.Row0.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows00.Row0.e]
  rw [gCp_eq, cCp_eq]
  exact Cp_neg he hy hy0

theorem actualCp_pos {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) (hy0 : 0 < y) :
    evalCert (LRows00.Row0.e : ℝ) LRows00.Row0.g.length (gcertG (LRows00.Row0.e : ℝ) LRows00.Row0.g) (LRows00.Row0.c0 : ℝ) y ≤ 1 := by
  have he : (LRows00.Row0.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows00.Row0.e]
  rw [gCp_eq, cCp_eq]
  exact Cp_pos he hy hy0

theorem gCm_eq : LRows00.Row1.g = gCm := by decide +kernel
theorem cCm_eq : LRows00.Row1.c0 = c0Cm := by decide +kernel

theorem actualStatCm : certH LRows00.Row1.g.length (gcertG (LRows00.Row1.e : ℝ) LRows00.Row1.g) * (13/5000 : ℝ) ≤ (LRows00.Row1.s : ℝ)^2 := by
  rw [certH_sum, ← LRows00.Row1.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows00.Row1.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginCm {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((1/4 : ℚ) : ℝ) ≤ (1-α)*(LRows00.Row1.c0 : ℝ) +
      certMean LRows00.Row1.g.length (gcertG (LRows00.Row1.e : ℝ) LRows00.Row1.g) ReferenceData.secondP - (LRows00.Row1.s : ℝ) := by
  rw [physical_eq]
  exact LRows00.Row1.selected_row hα

theorem actualCm_neg {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) (hy0 : y < 0) :
    evalCert (LRows00.Row1.e : ℝ) LRows00.Row1.g.length (gcertG (LRows00.Row1.e : ℝ) LRows00.Row1.g) (LRows00.Row1.c0 : ℝ) y ≤ 1 := by
  have he : (LRows00.Row1.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows00.Row1.e]
  rw [gCm_eq, cCm_eq]
  exact Cm_neg he hy hy0

theorem actualCm_pos {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) (hy0 : 0 < y) :
    evalCert (LRows00.Row1.e : ℝ) LRows00.Row1.g.length (gcertG (LRows00.Row1.e : ℝ) LRows00.Row1.g) (LRows00.Row1.c0 : ℝ) y ≤ 0 := by
  have he : (LRows00.Row1.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows00.Row1.e]
  rw [gCm_eq, cCm_eq]
  exact Cm_pos he hy hy0

theorem gS0_eq : LRows00.Row2.g = gS0 := by decide +kernel
theorem cS0_eq : LRows00.Row2.c0 = c0S0 := by decide +kernel

theorem actualStatS0 : certH LRows00.Row2.g.length (gcertG (LRows00.Row2.e : ℝ) LRows00.Row2.g) * (13/5000 : ℝ) ≤ (LRows00.Row2.s : ℝ)^2 := by
  rw [certH_sum, ← LRows00.Row2.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows00.Row2.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS0 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows00.Row2.c0 : ℝ) +
      certMean LRows00.Row2.g.length (gcertG (LRows00.Row2.e : ℝ) LRows00.Row2.g) ReferenceData.secondP - (LRows00.Row2.s : ℝ) := by
  rw [physical_eq]
  exact LRows00.Row2.selected_row hα

theorem actualS0 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows00.Row2.e : ℝ) LRows00.Row2.g.length (gcertG (LRows00.Row2.e : ℝ) LRows00.Row2.g) (LRows00.Row2.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((247 : ℝ) / 2 ^ 11) y := by
  have he : (LRows00.Row2.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows00.Row2.e]
  rw [gS0_eq, cS0_eq]
  exact slope0 he hy

theorem gS1_eq : LRows00.Row3.g = gS1 := by decide +kernel
theorem cS1_eq : LRows00.Row3.c0 = c0S1 := by decide +kernel

theorem actualStatS1 : certH LRows00.Row3.g.length (gcertG (LRows00.Row3.e : ℝ) LRows00.Row3.g) * (13/5000 : ℝ) ≤ (LRows00.Row3.s : ℝ)^2 := by
  rw [certH_sum, ← LRows00.Row3.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows00.Row3.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS1 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows00.Row3.c0 : ℝ) +
      certMean LRows00.Row3.g.length (gcertG (LRows00.Row3.e : ℝ) LRows00.Row3.g) ReferenceData.secondP - (LRows00.Row3.s : ℝ) := by
  rw [physical_eq]
  exact LRows00.Row3.selected_row hα

theorem actualS1 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows00.Row3.e : ℝ) LRows00.Row3.g.length (gcertG (LRows00.Row3.e : ℝ) LRows00.Row3.g) (LRows00.Row3.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((325 : ℝ) / 2 ^ 11) y := by
  have he : (LRows00.Row3.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows00.Row3.e]
  rw [gS1_eq, cS1_eq]
  exact slope1 he hy

theorem gS2_eq : LRows00.Row4.g = gS2 := by decide +kernel
theorem cS2_eq : LRows00.Row4.c0 = c0S2 := by decide +kernel

theorem actualStatS2 : certH LRows00.Row4.g.length (gcertG (LRows00.Row4.e : ℝ) LRows00.Row4.g) * (13/5000 : ℝ) ≤ (LRows00.Row4.s : ℝ)^2 := by
  rw [certH_sum, ← LRows00.Row4.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows00.Row4.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS2 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows00.Row4.c0 : ℝ) +
      certMean LRows00.Row4.g.length (gcertG (LRows00.Row4.e : ℝ) LRows00.Row4.g) ReferenceData.secondP - (LRows00.Row4.s : ℝ) := by
  rw [physical_eq]
  exact LRows00.Row4.selected_row hα

theorem actualS2 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows00.Row4.e : ℝ) LRows00.Row4.g.length (gcertG (LRows00.Row4.e : ℝ) LRows00.Row4.g) (LRows00.Row4.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((403 : ℝ) / 2 ^ 11) y := by
  have he : (LRows00.Row4.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows00.Row4.e]
  rw [gS2_eq, cS2_eq]
  exact slope2 he hy

theorem gS3_eq : LRows01.Row5.g = gS3 := by decide +kernel
theorem cS3_eq : LRows01.Row5.c0 = c0S3 := by decide +kernel

theorem actualStatS3 : certH LRows01.Row5.g.length (gcertG (LRows01.Row5.e : ℝ) LRows01.Row5.g) * (13/5000 : ℝ) ≤ (LRows01.Row5.s : ℝ)^2 := by
  rw [certH_sum, ← LRows01.Row5.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows01.Row5.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS3 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows01.Row5.c0 : ℝ) +
      certMean LRows01.Row5.g.length (gcertG (LRows01.Row5.e : ℝ) LRows01.Row5.g) ReferenceData.secondP - (LRows01.Row5.s : ℝ) := by
  rw [physical_eq]
  exact LRows01.Row5.selected_row hα

theorem actualS3 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows01.Row5.e : ℝ) LRows01.Row5.g.length (gcertG (LRows01.Row5.e : ℝ) LRows01.Row5.g) (LRows01.Row5.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((481 : ℝ) / 2 ^ 11) y := by
  have he : (LRows01.Row5.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows01.Row5.e]
  rw [gS3_eq, cS3_eq]
  exact slope3 he hy

theorem gS4_eq : LMeanPilot.g = gS4 := by decide +kernel
theorem cS4_eq : LMeanPilot.c0 = c0S4 := by decide +kernel

theorem actualStatS4 : certH LMeanPilot.g.length (gcertG (LMeanPilot.e : ℝ) LMeanPilot.g) * (13/5000 : ℝ) ≤ (LMeanPilot.s : ℝ)^2 := by
  rw [certH_sum, ← LMeanPilot.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LMeanPilot.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS4 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LMeanPilot.c0 : ℝ) +
      certMean LMeanPilot.g.length (gcertG (LMeanPilot.e : ℝ) LMeanPilot.g) ReferenceData.secondP - (LMeanPilot.s : ℝ) := by
  rw [physical_eq]
  exact LMeanPilot.selected_row hα

theorem actualS4 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LMeanPilot.e : ℝ) LMeanPilot.g.length (gcertG (LMeanPilot.e : ℝ) LMeanPilot.g) (LMeanPilot.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((559 : ℝ) / 2 ^ 11) y := by
  have he : (LMeanPilot.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LMeanPilot.e]
  rw [gS4_eq, cS4_eq]
  exact slope4 he hy

theorem gS5_eq : LRows01.Row7.g = gS5 := by decide +kernel
theorem cS5_eq : LRows01.Row7.c0 = c0S5 := by decide +kernel

theorem actualStatS5 : certH LRows01.Row7.g.length (gcertG (LRows01.Row7.e : ℝ) LRows01.Row7.g) * (13/5000 : ℝ) ≤ (LRows01.Row7.s : ℝ)^2 := by
  rw [certH_sum, ← LRows01.Row7.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows01.Row7.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS5 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows01.Row7.c0 : ℝ) +
      certMean LRows01.Row7.g.length (gcertG (LRows01.Row7.e : ℝ) LRows01.Row7.g) ReferenceData.secondP - (LRows01.Row7.s : ℝ) := by
  rw [physical_eq]
  exact LRows01.Row7.selected_row hα

theorem actualS5 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows01.Row7.e : ℝ) LRows01.Row7.g.length (gcertG (LRows01.Row7.e : ℝ) LRows01.Row7.g) (LRows01.Row7.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((637 : ℝ) / 2 ^ 11) y := by
  have he : (LRows01.Row7.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows01.Row7.e]
  rw [gS5_eq, cS5_eq]
  exact slope5 he hy

theorem gS6_eq : LRows01.Row8.g = gS6 := by decide +kernel
theorem cS6_eq : LRows01.Row8.c0 = c0S6 := by decide +kernel

theorem actualStatS6 : certH LRows01.Row8.g.length (gcertG (LRows01.Row8.e : ℝ) LRows01.Row8.g) * (13/5000 : ℝ) ≤ (LRows01.Row8.s : ℝ)^2 := by
  rw [certH_sum, ← LRows01.Row8.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows01.Row8.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS6 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows01.Row8.c0 : ℝ) +
      certMean LRows01.Row8.g.length (gcertG (LRows01.Row8.e : ℝ) LRows01.Row8.g) ReferenceData.secondP - (LRows01.Row8.s : ℝ) := by
  rw [physical_eq]
  exact LRows01.Row8.selected_row hα

theorem actualS6 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows01.Row8.e : ℝ) LRows01.Row8.g.length (gcertG (LRows01.Row8.e : ℝ) LRows01.Row8.g) (LRows01.Row8.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((715 : ℝ) / 2 ^ 11) y := by
  have he : (LRows01.Row8.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows01.Row8.e]
  rw [gS6_eq, cS6_eq]
  exact slope6 he hy

theorem gS7_eq : LRows01.Row9.g = gS7 := by decide +kernel
theorem cS7_eq : LRows01.Row9.c0 = c0S7 := by decide +kernel

theorem actualStatS7 : certH LRows01.Row9.g.length (gcertG (LRows01.Row9.e : ℝ) LRows01.Row9.g) * (13/5000 : ℝ) ≤ (LRows01.Row9.s : ℝ)^2 := by
  rw [certH_sum, ← LRows01.Row9.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows01.Row9.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS7 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows01.Row9.c0 : ℝ) +
      certMean LRows01.Row9.g.length (gcertG (LRows01.Row9.e : ℝ) LRows01.Row9.g) ReferenceData.secondP - (LRows01.Row9.s : ℝ) := by
  rw [physical_eq]
  exact LRows01.Row9.selected_row hα

theorem actualS7 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows01.Row9.e : ℝ) LRows01.Row9.g.length (gcertG (LRows01.Row9.e : ℝ) LRows01.Row9.g) (LRows01.Row9.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((793 : ℝ) / 2 ^ 11) y := by
  have he : (LRows01.Row9.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows01.Row9.e]
  rw [gS7_eq, cS7_eq]
  exact slope7 he hy

theorem gS8_eq : LRows01.Row10.g = gS8 := by decide +kernel
theorem cS8_eq : LRows01.Row10.c0 = c0S8 := by decide +kernel

theorem actualStatS8 : certH LRows01.Row10.g.length (gcertG (LRows01.Row10.e : ℝ) LRows01.Row10.g) * (13/5000 : ℝ) ≤ (LRows01.Row10.s : ℝ)^2 := by
  rw [certH_sum, ← LRows01.Row10.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows01.Row10.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS8 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows01.Row10.c0 : ℝ) +
      certMean LRows01.Row10.g.length (gcertG (LRows01.Row10.e : ℝ) LRows01.Row10.g) ReferenceData.secondP - (LRows01.Row10.s : ℝ) := by
  rw [physical_eq]
  exact LRows01.Row10.selected_row hα

theorem actualS8 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows01.Row10.e : ℝ) LRows01.Row10.g.length (gcertG (LRows01.Row10.e : ℝ) LRows01.Row10.g) (LRows01.Row10.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((871 : ℝ) / 2 ^ 11) y := by
  have he : (LRows01.Row10.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows01.Row10.e]
  rw [gS8_eq, cS8_eq]
  exact slope8 he hy

theorem gS9_eq : LRows02.Row11.g = gS9 := by decide +kernel
theorem cS9_eq : LRows02.Row11.c0 = c0S9 := by decide +kernel

theorem actualStatS9 : certH LRows02.Row11.g.length (gcertG (LRows02.Row11.e : ℝ) LRows02.Row11.g) * (13/5000 : ℝ) ≤ (LRows02.Row11.s : ℝ)^2 := by
  rw [certH_sum, ← LRows02.Row11.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows02.Row11.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS9 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows02.Row11.c0 : ℝ) +
      certMean LRows02.Row11.g.length (gcertG (LRows02.Row11.e : ℝ) LRows02.Row11.g) ReferenceData.secondP - (LRows02.Row11.s : ℝ) := by
  rw [physical_eq]
  exact LRows02.Row11.selected_row hα

theorem actualS9 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows02.Row11.e : ℝ) LRows02.Row11.g.length (gcertG (LRows02.Row11.e : ℝ) LRows02.Row11.g) (LRows02.Row11.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((949 : ℝ) / 2 ^ 11) y := by
  have he : (LRows02.Row11.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows02.Row11.e]
  rw [gS9_eq, cS9_eq]
  exact slope9 he hy

theorem gS10_eq : LRows02.Row12.g = gS10 := by decide +kernel
theorem cS10_eq : LRows02.Row12.c0 = c0S10 := by decide +kernel

theorem actualStatS10 : certH LRows02.Row12.g.length (gcertG (LRows02.Row12.e : ℝ) LRows02.Row12.g) * (13/5000 : ℝ) ≤ (LRows02.Row12.s : ℝ)^2 := by
  rw [certH_sum, ← LRows02.Row12.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows02.Row12.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS10 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows02.Row12.c0 : ℝ) +
      certMean LRows02.Row12.g.length (gcertG (LRows02.Row12.e : ℝ) LRows02.Row12.g) ReferenceData.secondP - (LRows02.Row12.s : ℝ) := by
  rw [physical_eq]
  exact LRows02.Row12.selected_row hα

theorem actualS10 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows02.Row12.e : ℝ) LRows02.Row12.g.length (gcertG (LRows02.Row12.e : ℝ) LRows02.Row12.g) (LRows02.Row12.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((1027 : ℝ) / 2 ^ 11) y := by
  have he : (LRows02.Row12.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows02.Row12.e]
  rw [gS10_eq, cS10_eq]
  exact slope10 he hy

theorem gS11_eq : LRows02.Row13.g = gS11 := by decide +kernel
theorem cS11_eq : LRows02.Row13.c0 = c0S11 := by decide +kernel

theorem actualStatS11 : certH LRows02.Row13.g.length (gcertG (LRows02.Row13.e : ℝ) LRows02.Row13.g) * (13/5000 : ℝ) ≤ (LRows02.Row13.s : ℝ)^2 := by
  rw [certH_sum, ← LRows02.Row13.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows02.Row13.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS11 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows02.Row13.c0 : ℝ) +
      certMean LRows02.Row13.g.length (gcertG (LRows02.Row13.e : ℝ) LRows02.Row13.g) ReferenceData.secondP - (LRows02.Row13.s : ℝ) := by
  rw [physical_eq]
  exact LRows02.Row13.selected_row hα

theorem actualS11 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows02.Row13.e : ℝ) LRows02.Row13.g.length (gcertG (LRows02.Row13.e : ℝ) LRows02.Row13.g) (LRows02.Row13.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((1105 : ℝ) / 2 ^ 11) y := by
  have he : (LRows02.Row13.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows02.Row13.e]
  rw [gS11_eq, cS11_eq]
  exact slope11 he hy

theorem gS12_eq : LRows02.Row14.g = gS12 := by decide +kernel
theorem cS12_eq : LRows02.Row14.c0 = c0S12 := by decide +kernel

theorem actualStatS12 : certH LRows02.Row14.g.length (gcertG (LRows02.Row14.e : ℝ) LRows02.Row14.g) * (13/5000 : ℝ) ≤ (LRows02.Row14.s : ℝ)^2 := by
  rw [certH_sum, ← LRows02.Row14.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows02.Row14.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS12 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows02.Row14.c0 : ℝ) +
      certMean LRows02.Row14.g.length (gcertG (LRows02.Row14.e : ℝ) LRows02.Row14.g) ReferenceData.secondP - (LRows02.Row14.s : ℝ) := by
  rw [physical_eq]
  exact LRows02.Row14.selected_row hα

theorem actualS12 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows02.Row14.e : ℝ) LRows02.Row14.g.length (gcertG (LRows02.Row14.e : ℝ) LRows02.Row14.g) (LRows02.Row14.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((1183 : ℝ) / 2 ^ 11) y := by
  have he : (LRows02.Row14.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows02.Row14.e]
  rw [gS12_eq, cS12_eq]
  exact slope12 he hy

theorem gS13_eq : LRows02.Row15.g = gS13 := by decide +kernel
theorem cS13_eq : LRows02.Row15.c0 = c0S13 := by decide +kernel

theorem actualStatS13 : certH LRows02.Row15.g.length (gcertG (LRows02.Row15.e : ℝ) LRows02.Row15.g) * (13/5000 : ℝ) ≤ (LRows02.Row15.s : ℝ)^2 := by
  rw [certH_sum, ← LRows02.Row15.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows02.Row15.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS13 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows02.Row15.c0 : ℝ) +
      certMean LRows02.Row15.g.length (gcertG (LRows02.Row15.e : ℝ) LRows02.Row15.g) ReferenceData.secondP - (LRows02.Row15.s : ℝ) := by
  rw [physical_eq]
  exact LRows02.Row15.selected_row hα

theorem actualS13 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows02.Row15.e : ℝ) LRows02.Row15.g.length (gcertG (LRows02.Row15.e : ℝ) LRows02.Row15.g) (LRows02.Row15.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((1261 : ℝ) / 2 ^ 11) y := by
  have he : (LRows02.Row15.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows02.Row15.e]
  rw [gS13_eq, cS13_eq]
  exact slope13 he hy

theorem gS14_eq : LRows03.Row16.g = gS14 := by decide +kernel
theorem cS14_eq : LRows03.Row16.c0 = c0S14 := by decide +kernel

theorem actualStatS14 : certH LRows03.Row16.g.length (gcertG (LRows03.Row16.e : ℝ) LRows03.Row16.g) * (13/5000 : ℝ) ≤ (LRows03.Row16.s : ℝ)^2 := by
  rw [certH_sum, ← LRows03.Row16.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows03.Row16.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS14 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows03.Row16.c0 : ℝ) +
      certMean LRows03.Row16.g.length (gcertG (LRows03.Row16.e : ℝ) LRows03.Row16.g) ReferenceData.secondP - (LRows03.Row16.s : ℝ) := by
  rw [physical_eq]
  exact LRows03.Row16.selected_row hα

theorem actualS14 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows03.Row16.e : ℝ) LRows03.Row16.g.length (gcertG (LRows03.Row16.e : ℝ) LRows03.Row16.g) (LRows03.Row16.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((1339 : ℝ) / 2 ^ 11) y := by
  have he : (LRows03.Row16.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows03.Row16.e]
  rw [gS14_eq, cS14_eq]
  exact slope14 he hy

theorem gS15_eq : LRows03.Row17.g = gS15 := by decide +kernel
theorem cS15_eq : LRows03.Row17.c0 = c0S15 := by decide +kernel

theorem actualStatS15 : certH LRows03.Row17.g.length (gcertG (LRows03.Row17.e : ℝ) LRows03.Row17.g) * (13/5000 : ℝ) ≤ (LRows03.Row17.s : ℝ)^2 := by
  rw [certH_sum, ← LRows03.Row17.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows03.Row17.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS15 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows03.Row17.c0 : ℝ) +
      certMean LRows03.Row17.g.length (gcertG (LRows03.Row17.e : ℝ) LRows03.Row17.g) ReferenceData.secondP - (LRows03.Row17.s : ℝ) := by
  rw [physical_eq]
  exact LRows03.Row17.selected_row hα

theorem actualS15 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows03.Row17.e : ℝ) LRows03.Row17.g.length (gcertG (LRows03.Row17.e : ℝ) LRows03.Row17.g) (LRows03.Row17.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((1417 : ℝ) / 2 ^ 11) y := by
  have he : (LRows03.Row17.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows03.Row17.e]
  rw [gS15_eq, cS15_eq]
  exact slope15 he hy

theorem gS16_eq : LRows03.Row18.g = gS16 := by decide +kernel
theorem cS16_eq : LRows03.Row18.c0 = c0S16 := by decide +kernel

theorem actualStatS16 : certH LRows03.Row18.g.length (gcertG (LRows03.Row18.e : ℝ) LRows03.Row18.g) * (13/5000 : ℝ) ≤ (LRows03.Row18.s : ℝ)^2 := by
  rw [certH_sum, ← LRows03.Row18.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows03.Row18.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS16 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows03.Row18.c0 : ℝ) +
      certMean LRows03.Row18.g.length (gcertG (LRows03.Row18.e : ℝ) LRows03.Row18.g) ReferenceData.secondP - (LRows03.Row18.s : ℝ) := by
  rw [physical_eq]
  exact LRows03.Row18.selected_row hα

theorem actualS16 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows03.Row18.e : ℝ) LRows03.Row18.g.length (gcertG (LRows03.Row18.e : ℝ) LRows03.Row18.g) (LRows03.Row18.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((1495 : ℝ) / 2 ^ 11) y := by
  have he : (LRows03.Row18.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows03.Row18.e]
  rw [gS16_eq, cS16_eq]
  exact slope16 he hy

theorem gS17_eq : LRows03.Row19.g = gS17 := by decide +kernel
theorem cS17_eq : LRows03.Row19.c0 = c0S17 := by decide +kernel

theorem actualStatS17 : certH LRows03.Row19.g.length (gcertG (LRows03.Row19.e : ℝ) LRows03.Row19.g) * (13/5000 : ℝ) ≤ (LRows03.Row19.s : ℝ)^2 := by
  rw [certH_sum, ← LRows03.Row19.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows03.Row19.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS17 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows03.Row19.c0 : ℝ) +
      certMean LRows03.Row19.g.length (gcertG (LRows03.Row19.e : ℝ) LRows03.Row19.g) ReferenceData.secondP - (LRows03.Row19.s : ℝ) := by
  rw [physical_eq]
  exact LRows03.Row19.selected_row hα

theorem actualS17 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows03.Row19.e : ℝ) LRows03.Row19.g.length (gcertG (LRows03.Row19.e : ℝ) LRows03.Row19.g) (LRows03.Row19.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((1573 : ℝ) / 2 ^ 11) y := by
  have he : (LRows03.Row19.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows03.Row19.e]
  rw [gS17_eq, cS17_eq]
  exact slope17 he hy

theorem gS18_eq : LRows03.Row20.g = gS18 := by decide +kernel
theorem cS18_eq : LRows03.Row20.c0 = c0S18 := by decide +kernel

theorem actualStatS18 : certH LRows03.Row20.g.length (gcertG (LRows03.Row20.e : ℝ) LRows03.Row20.g) * (13/5000 : ℝ) ≤ (LRows03.Row20.s : ℝ)^2 := by
  rw [certH_sum, ← LRows03.Row20.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows03.Row20.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS18 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows03.Row20.c0 : ℝ) +
      certMean LRows03.Row20.g.length (gcertG (LRows03.Row20.e : ℝ) LRows03.Row20.g) ReferenceData.secondP - (LRows03.Row20.s : ℝ) := by
  rw [physical_eq]
  exact LRows03.Row20.selected_row hα

theorem actualS18 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows03.Row20.e : ℝ) LRows03.Row20.g.length (gcertG (LRows03.Row20.e : ℝ) LRows03.Row20.g) (LRows03.Row20.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((1651 : ℝ) / 2 ^ 11) y := by
  have he : (LRows03.Row20.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows03.Row20.e]
  rw [gS18_eq, cS18_eq]
  exact slope18 he hy

theorem gS19_eq : LRows04.Row21.g = gS19 := by decide +kernel
theorem cS19_eq : LRows04.Row21.c0 = c0S19 := by decide +kernel

theorem actualStatS19 : certH LRows04.Row21.g.length (gcertG (LRows04.Row21.e : ℝ) LRows04.Row21.g) * (13/5000 : ℝ) ≤ (LRows04.Row21.s : ℝ)^2 := by
  rw [certH_sum, ← LRows04.Row21.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows04.Row21.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS19 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows04.Row21.c0 : ℝ) +
      certMean LRows04.Row21.g.length (gcertG (LRows04.Row21.e : ℝ) LRows04.Row21.g) ReferenceData.secondP - (LRows04.Row21.s : ℝ) := by
  rw [physical_eq]
  exact LRows04.Row21.selected_row hα

theorem actualS19 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows04.Row21.e : ℝ) LRows04.Row21.g.length (gcertG (LRows04.Row21.e : ℝ) LRows04.Row21.g) (LRows04.Row21.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((1729 : ℝ) / 2 ^ 11) y := by
  have he : (LRows04.Row21.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows04.Row21.e]
  rw [gS19_eq, cS19_eq]
  exact slope19 he hy

theorem gS20_eq : LRows04.Row22.g = gS20 := by decide +kernel
theorem cS20_eq : LRows04.Row22.c0 = c0S20 := by decide +kernel

theorem actualStatS20 : certH LRows04.Row22.g.length (gcertG (LRows04.Row22.e : ℝ) LRows04.Row22.g) * (13/5000 : ℝ) ≤ (LRows04.Row22.s : ℝ)^2 := by
  rw [certH_sum, ← LRows04.Row22.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows04.Row22.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS20 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows04.Row22.c0 : ℝ) +
      certMean LRows04.Row22.g.length (gcertG (LRows04.Row22.e : ℝ) LRows04.Row22.g) ReferenceData.secondP - (LRows04.Row22.s : ℝ) := by
  rw [physical_eq]
  exact LRows04.Row22.selected_row hα

theorem actualS20 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows04.Row22.e : ℝ) LRows04.Row22.g.length (gcertG (LRows04.Row22.e : ℝ) LRows04.Row22.g) (LRows04.Row22.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((1807 : ℝ) / 2 ^ 11) y := by
  have he : (LRows04.Row22.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows04.Row22.e]
  rw [gS20_eq, cS20_eq]
  exact slope20 he hy

theorem gS21_eq : LRows04.Row23.g = gS21 := by decide +kernel
theorem cS21_eq : LRows04.Row23.c0 = c0S21 := by decide +kernel

theorem actualStatS21 : certH LRows04.Row23.g.length (gcertG (LRows04.Row23.e : ℝ) LRows04.Row23.g) * (13/5000 : ℝ) ≤ (LRows04.Row23.s : ℝ)^2 := by
  rw [certH_sum, ← LRows04.Row23.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows04.Row23.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS21 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows04.Row23.c0 : ℝ) +
      certMean LRows04.Row23.g.length (gcertG (LRows04.Row23.e : ℝ) LRows04.Row23.g) ReferenceData.secondP - (LRows04.Row23.s : ℝ) := by
  rw [physical_eq]
  exact LRows04.Row23.selected_row hα

theorem actualS21 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows04.Row23.e : ℝ) LRows04.Row23.g.length (gcertG (LRows04.Row23.e : ℝ) LRows04.Row23.g) (LRows04.Row23.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((1885 : ℝ) / 2 ^ 11) y := by
  have he : (LRows04.Row23.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows04.Row23.e]
  rw [gS21_eq, cS21_eq]
  exact slope21 he hy

theorem gS22_eq : LRows04.Row24.g = gS22 := by decide +kernel
theorem cS22_eq : LRows04.Row24.c0 = c0S22 := by decide +kernel

theorem actualStatS22 : certH LRows04.Row24.g.length (gcertG (LRows04.Row24.e : ℝ) LRows04.Row24.g) * (13/5000 : ℝ) ≤ (LRows04.Row24.s : ℝ)^2 := by
  rw [certH_sum, ← LRows04.Row24.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows04.Row24.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS22 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows04.Row24.c0 : ℝ) +
      certMean LRows04.Row24.g.length (gcertG (LRows04.Row24.e : ℝ) LRows04.Row24.g) ReferenceData.secondP - (LRows04.Row24.s : ℝ) := by
  rw [physical_eq]
  exact LRows04.Row24.selected_row hα

theorem actualS22 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows04.Row24.e : ℝ) LRows04.Row24.g.length (gcertG (LRows04.Row24.e : ℝ) LRows04.Row24.g) (LRows04.Row24.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((1963 : ℝ) / 2 ^ 11) y := by
  have he : (LRows04.Row24.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows04.Row24.e]
  rw [gS22_eq, cS22_eq]
  exact slope22 he hy

theorem gS23_eq : LRows04.Row25.g = gS23 := by decide +kernel
theorem cS23_eq : LRows04.Row25.c0 = c0S23 := by decide +kernel

theorem actualStatS23 : certH LRows04.Row25.g.length (gcertG (LRows04.Row25.e : ℝ) LRows04.Row25.g) * (13/5000 : ℝ) ≤ (LRows04.Row25.s : ℝ)^2 := by
  rw [certH_sum, ← LRows04.Row25.statistic_checked]
  have h := (Rat.cast_le (K := ℝ)).mpr LRows04.Row25.statistic_bound
  push_cast at h
  simpa only [mul_comm] using h

theorem actualMarginS23 {α : ℝ} (hα : α ∈ Icc ((0 : ℚ) : ℝ) ((1/16 : ℚ) : ℝ)) :
    ((13/60 : ℚ) : ℝ) ≤ (1-α)*(LRows04.Row25.c0 : ℝ) +
      certMean LRows04.Row25.g.length (gcertG (LRows04.Row25.e : ℝ) LRows04.Row25.g) ReferenceData.secondP - (LRows04.Row25.s : ℝ) := by
  rw [physical_eq]
  exact LRows04.Row25.selected_row hα

theorem actualS23 {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    evalCert (LRows04.Row25.e : ℝ) LRows04.Row25.g.length (gcertG (LRows04.Row25.e : ℝ) LRows04.Row25.g) (LRows04.Row25.c0 : ℝ) y + 3 / 16 ≤ 1 - slopeKernel ((2041 : ℝ) / 2 ^ 11) y := by
  have he : (LRows04.Row25.e : ℝ) ∈ Ioo (0 : ℝ) (1 / 8) := by constructor <;> norm_num [LRows04.Row25.e]
  rw [gS23_eq, cS23_eq]
  exact slope23 he hy

end
end CatalanMeasure.GenD.Signed.Data.Trial72.LControl72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatCp
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginCp
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualCpMean
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualCpHalf
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualCp_neg
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualCp_pos
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatCm
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginCm
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualCm_neg
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualCm_pos
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS3
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS3
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS3
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS4
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS4
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS4
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS5
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS5
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS5
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS6
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS6
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS6
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS7
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS7
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS7
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS8
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS8
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS8
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS9
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS9
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS9
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS10
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS10
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS10
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS11
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS11
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS11
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS12
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS12
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS12
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS13
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS13
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS13
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS14
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS14
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS14
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS15
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS15
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS15
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS16
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS16
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS16
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS17
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS17
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS17
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS18
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS18
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS18
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS19
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS19
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS19
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS20
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS20
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS20
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS21
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS21
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS21
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS22
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS22
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS22
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualStatS23
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualMarginS23
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LControl72.actualS23
