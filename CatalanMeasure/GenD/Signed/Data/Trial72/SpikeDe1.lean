module
public import CatalanMeasure.GenD.Signed.Data.Trial72.CostRootData
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeChebInteger1
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCostScalars1
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeDe1
open Set CatalanMeasure.Signed CatalanMeasure.Signed.Consts OAI.InternalCatalan
noncomputable section

abbrev bs := SpikeChebInteger1.bs
def c := sbPosCoeffs bs 0

theorem sign : c.all (fun x => decide (0 ≤ x)) = true := by decide +kernel

private theorem value {z : ℚ} :
    barrierTrialS (bSeq bs) (-(z : ℝ)) = ((z * sbHorQ z c : ℚ) : ℝ) := by
  simp only [barrierTrialS_horner, Rat.cast_mul, sbHorQ_cast, c]

private theorem difference {z : ℚ} {ρ y : ℝ}
    (hz : 0 ≤ z) (hr : (z : ℝ) ≤ ρ) (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-ρ)) ≤
      ((2 * (sbHorQ 1 c - z * sbHorQ z c) : ℚ) : ℝ) := by
  have h1 := barrierTrialS_neg_mono sign hy.1 hy.2
  have h2 := barrierTrialS_neg_mono sign (show (0 : ℝ) ≤ (z : ℝ) by exact_mod_cast hz) hr
  have h1' := value (z := 1)
  simp only [Rat.cast_one, one_mul] at h1'
  rw [h1'] at h1
  rw [value] at h2
  push_cast
  linarith only [h1,h2]


private theorem numeric00 :
    2*(sbHorQ 1 c - CostRootData.A00.rhoLo * sbHorQ CostRootData.A00.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 0 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row00 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A00.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 0 0 : ℝ) :=
  (difference CostRootData.A00.rhoLo_nonneg CostRootData.A00.rho_bounds.1 hy).trans (by exact_mod_cast numeric00)

private theorem numeric01 :
    2*(sbHorQ 1 c - CostRootData.A01.rhoLo * sbHorQ CostRootData.A01.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 1 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row01 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A01.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 1 0 : ℝ) :=
  (difference CostRootData.A01.rhoLo_nonneg CostRootData.A01.rho_bounds.1 hy).trans (by exact_mod_cast numeric01)

private theorem numeric02 :
    2*(sbHorQ 1 c - CostRootData.A02.rhoLo * sbHorQ CostRootData.A02.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 2 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row02 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A02.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 2 0 : ℝ) :=
  (difference CostRootData.A02.rhoLo_nonneg CostRootData.A02.rho_bounds.1 hy).trans (by exact_mod_cast numeric02)

private theorem numeric03 :
    2*(sbHorQ 1 c - CostRootData.A03.rhoLo * sbHorQ CostRootData.A03.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 3 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row03 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A03.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 3 0 : ℝ) :=
  (difference CostRootData.A03.rhoLo_nonneg CostRootData.A03.rho_bounds.1 hy).trans (by exact_mod_cast numeric03)

private theorem numeric04 :
    2*(sbHorQ 1 c - CostRootData.A04.rhoLo * sbHorQ CostRootData.A04.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 4 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row04 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A04.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 4 0 : ℝ) :=
  (difference CostRootData.A04.rhoLo_nonneg CostRootData.A04.rho_bounds.1 hy).trans (by exact_mod_cast numeric04)

private theorem numeric05 :
    2*(sbHorQ 1 c - CostRootData.A05.rhoLo * sbHorQ CostRootData.A05.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 5 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row05 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A05.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 5 0 : ℝ) :=
  (difference CostRootData.A05.rhoLo_nonneg CostRootData.A05.rho_bounds.1 hy).trans (by exact_mod_cast numeric05)

private theorem numeric06 :
    2*(sbHorQ 1 c - CostRootData.A06.rhoLo * sbHorQ CostRootData.A06.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 6 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row06 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A06.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 6 0 : ℝ) :=
  (difference CostRootData.A06.rhoLo_nonneg CostRootData.A06.rho_bounds.1 hy).trans (by exact_mod_cast numeric06)

private theorem numeric07 :
    2*(sbHorQ 1 c - CostRootData.A07.rhoLo * sbHorQ CostRootData.A07.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 7 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row07 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A07.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 7 0 : ℝ) :=
  (difference CostRootData.A07.rhoLo_nonneg CostRootData.A07.rho_bounds.1 hy).trans (by exact_mod_cast numeric07)

private theorem numeric08 :
    2*(sbHorQ 1 c - CostRootData.A08.rhoLo * sbHorQ CostRootData.A08.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 8 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row08 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A08.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 8 0 : ℝ) :=
  (difference CostRootData.A08.rhoLo_nonneg CostRootData.A08.rho_bounds.1 hy).trans (by exact_mod_cast numeric08)

private theorem numeric09 :
    2*(sbHorQ 1 c - CostRootData.A09.rhoLo * sbHorQ CostRootData.A09.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 9 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row09 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A09.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 9 0 : ℝ) :=
  (difference CostRootData.A09.rhoLo_nonneg CostRootData.A09.rho_bounds.1 hy).trans (by exact_mod_cast numeric09)

private theorem numeric10 :
    2*(sbHorQ 1 c - CostRootData.A10.rhoLo * sbHorQ CostRootData.A10.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 10 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row10 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A10.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 10 0 : ℝ) :=
  (difference CostRootData.A10.rhoLo_nonneg CostRootData.A10.rho_bounds.1 hy).trans (by exact_mod_cast numeric10)

private theorem numeric11 :
    2*(sbHorQ 1 c - CostRootData.A11.rhoLo * sbHorQ CostRootData.A11.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 11 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row11 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A11.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 11 0 : ℝ) :=
  (difference CostRootData.A11.rhoLo_nonneg CostRootData.A11.rho_bounds.1 hy).trans (by exact_mod_cast numeric11)

private theorem numeric12 :
    2*(sbHorQ 1 c - CostRootData.A12.rhoLo * sbHorQ CostRootData.A12.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 12 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row12 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A12.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 12 0 : ℝ) :=
  (difference CostRootData.A12.rhoLo_nonneg CostRootData.A12.rho_bounds.1 hy).trans (by exact_mod_cast numeric12)

private theorem numeric13 :
    2*(sbHorQ 1 c - CostRootData.A13.rhoLo * sbHorQ CostRootData.A13.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 13 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row13 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A13.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 13 0 : ℝ) :=
  (difference CostRootData.A13.rhoLo_nonneg CostRootData.A13.rho_bounds.1 hy).trans (by exact_mod_cast numeric13)

private theorem numeric14 :
    2*(sbHorQ 1 c - CostRootData.A14.rhoLo * sbHorQ CostRootData.A14.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 14 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row14 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A14.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 14 0 : ℝ) :=
  (difference CostRootData.A14.rhoLo_nonneg CostRootData.A14.rho_bounds.1 hy).trans (by exact_mod_cast numeric14)

private theorem numeric15 :
    2*(sbHorQ 1 c - CostRootData.A15.rhoLo * sbHorQ CostRootData.A15.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 15 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row15 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A15.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 15 0 : ℝ) :=
  (difference CostRootData.A15.rhoLo_nonneg CostRootData.A15.rho_bounds.1 hy).trans (by exact_mod_cast numeric15)

private theorem numeric16 :
    2*(sbHorQ 1 c - CostRootData.A16.rhoLo * sbHorQ CostRootData.A16.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 16 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row16 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A16.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 16 0 : ℝ) :=
  (difference CostRootData.A16.rhoLo_nonneg CostRootData.A16.rho_bounds.1 hy).trans (by exact_mod_cast numeric16)

private theorem numeric17 :
    2*(sbHorQ 1 c - CostRootData.A17.rhoLo * sbHorQ CostRootData.A17.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 17 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row17 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A17.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 17 0 : ℝ) :=
  (difference CostRootData.A17.rhoLo_nonneg CostRootData.A17.rho_bounds.1 hy).trans (by exact_mod_cast numeric17)

private theorem numeric18 :
    2*(sbHorQ 1 c - CostRootData.A18.rhoLo * sbHorQ CostRootData.A18.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 18 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row18 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A18.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 18 0 : ℝ) :=
  (difference CostRootData.A18.rhoLo_nonneg CostRootData.A18.rho_bounds.1 hy).trans (by exact_mod_cast numeric18)

private theorem numeric19 :
    2*(sbHorQ 1 c - CostRootData.A19.rhoLo * sbHorQ CostRootData.A19.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 19 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row19 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A19.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 19 0 : ℝ) :=
  (difference CostRootData.A19.rhoLo_nonneg CostRootData.A19.rho_bounds.1 hy).trans (by exact_mod_cast numeric19)

private theorem numeric20 :
    2*(sbHorQ 1 c - CostRootData.A20.rhoLo * sbHorQ CostRootData.A20.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 20 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row20 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A20.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 20 0 : ℝ) :=
  (difference CostRootData.A20.rhoLo_nonneg CostRootData.A20.rho_bounds.1 hy).trans (by exact_mod_cast numeric20)

private theorem numeric21 :
    2*(sbHorQ 1 c - CostRootData.A21.rhoLo * sbHorQ CostRootData.A21.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 21 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row21 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A21.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 21 0 : ℝ) :=
  (difference CostRootData.A21.rhoLo_nonneg CostRootData.A21.rho_bounds.1 hy).trans (by exact_mod_cast numeric21)

private theorem numeric22 :
    2*(sbHorQ 1 c - CostRootData.A22.rhoLo * sbHorQ CostRootData.A22.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 22 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row22 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A22.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 22 0 : ℝ) :=
  (difference CostRootData.A22.rhoLo_nonneg CostRootData.A22.rho_bounds.1 hy).trans (by exact_mod_cast numeric22)

private theorem numeric23 :
    2*(sbHorQ 1 c - CostRootData.A23.rhoLo * sbHorQ CostRootData.A23.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 23 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row23 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A23.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 23 0 : ℝ) :=
  (difference CostRootData.A23.rhoLo_nonneg CostRootData.A23.rho_bounds.1 hy).trans (by exact_mod_cast numeric23)

private theorem numeric24 :
    2*(sbHorQ 1 c - CostRootData.A24.rhoLo * sbHorQ CostRootData.A24.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 24 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row24 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A24.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 24 0 : ℝ) :=
  (difference CostRootData.A24.rhoLo_nonneg CostRootData.A24.rho_bounds.1 hy).trans (by exact_mod_cast numeric24)

private theorem numeric25 :
    2*(sbHorQ 1 c - CostRootData.A25.rhoLo * sbHorQ CostRootData.A25.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 25 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row25 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A25.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 25 0 : ℝ) :=
  (difference CostRootData.A25.rhoLo_nonneg CostRootData.A25.rho_bounds.1 hy).trans (by exact_mod_cast numeric25)

private theorem numeric26 :
    2*(sbHorQ 1 c - CostRootData.A26.rhoLo * sbHorQ CostRootData.A26.rhoLo c) ≤
      SpikeCostScalars1.deUpper.getD 26 0 := by
  -- kcost: .3 s conservative model; two exact Horner evaluations.
  decide +kernel

theorem row26 {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    2*(barrierTrialS (bSeq bs) (-y) - barrierTrialS (bSeq bs) (-CostRootData.A26.rho)) ≤
      (SpikeCostScalars1.deUpper.getD 26 0 : ℝ) :=
  (difference CostRootData.A26.rhoLo_nonneg CostRootData.A26.rho_bounds.1 hy).trans (by exact_mod_cast numeric26)

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeDe1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeDe1.row00
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeDe1.row26
