module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1End01
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1ZeroTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroSeriesPoint
public import CatalanMeasure.GenD.Signed.Data.Trial72.T1Fields
public import CatalanMeasure.GenD.Signed.Data.Assembly.RowsCell

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1LowBinding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1HighBinding

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Endpoints
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

theorem lowLog : ∀ y ∈ Ioc 0 (ceSignedSpT1End00Hi : ℝ),
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T1.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T1.spFq.poles) 0 y + lfieldTower terms 0 y ≤
    ((ceSignedSpT1End00TR + ceSignedSpT1End00U + zeroE : ℚ) : ℝ) + (zeroC : ℝ) * Real.log |y| := by
  intro y hy
  have hlo : ceSignedSpT1End00Lo = 0 := by decide +kernel
  have hsite : ceSignedSpT1End00Site = 0 := by decide +kernel
  have hhi : ceSignedSpT1End00Hi ≤ ceSignedSpT1ZeroHi := by decide +kernel
  have hx : y ∈ Icc (ceSignedSpT1End00Lo : ℝ) (ceSignedSpT1End00Hi : ℝ) :=
    ⟨by simpa only [hlo, Rat.cast_zero] using hy.1.le, hy.2⟩
  have h := endOK_sound ceSignedSpT1End00FullFq ceSignedSpT1End00FullTs ceSignedSpT1End00Site ceSignedSpT1End00Lo ceSignedSpT1End00Hi 10
    ceSignedSpT1End00U ceSignedSpT1End00TR (endOK_of_endUOK ceSignedSpT1End00Singular) ceSignedSpT1End00Regular y hx
  rw [fieldNFCheck_sound lowPlainCheck y] at h
  have hsiteR : (ceSignedSpT1End00Site : ℝ) = 0 := by rw [hsite, Rat.cast_zero]
  simp only [ceSignedSpT1End00FullTs, lfieldTower_nil_zero, add_zero, hsiteR, sub_zero] at h
  have h' := D72.zeroSeries_point ceSignedSpT1ZeroInputFq ceSignedSpT1ZeroPlain ceSignedSpT1ZeroInputTs ceSignedSpT1ZeroHi 64 0
    ceSignedSpT1ZeroSeriesOK ceSignedSpT1ZeroSeriesCancel rfl rfl ceSignedSpT1ZeroSeriesPoly
    (x := y) ⟨hy.1, hy.2.trans ((Rat.cast_le (K := ℝ)).mpr hhi)⟩
  rw [fieldNFCheck_sound lowFieldCheck y, lowTermsEq y] at h'
  have hb := (Rat.cast_le (K := ℝ)).mpr ceSignedSpT1ZeroSeriesBudget
  simp only [zeroC, zeroE, ceSignedSpT1End00FullTs, Rat.cast_add, Rat.cast_sub, Rat.cast_zero, add_zero, zero_add] at h' hb ⊢
  linarith only [h, h', hb]

theorem highLog : ∀ y ∈ Icc (ceSignedSpT1End01Lo : ℝ) 1, y ≠ 1 →
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T1.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T1.spFq.poles) 0 y + lfieldTower terms 0 y ≤
    ((ceSignedSpT1End01TR + ceSignedSpT1End01U : ℚ) : ℝ) + (oneC : ℝ) * Real.log |y - 1| := by
  intro y hy _
  have hhi : ceSignedSpT1End01Hi = 1 := by decide +kernel
  have hsite : ceSignedSpT1End01Site = 1 := by decide +kernel
  have hsiteR : (ceSignedSpT1End01Site : ℝ) = 1 := by rw [hsite, Rat.cast_one]
  have h := endOK_sound ceSignedSpT1End01FullFq ceSignedSpT1End01FullTs ceSignedSpT1End01Site ceSignedSpT1End01Lo ceSignedSpT1End01Hi 40
    ceSignedSpT1End01U ceSignedSpT1End01TR (endOK_of_endUOK ceSignedSpT1End01Singular) ceSignedSpT1End01Regular y
    (by simpa only [hhi, Rat.cast_one] using hy)
  rw [fieldNFCheck_sound highFieldCheck y, ← laurentNF_sound ceSignedSpT1End01FullTs y,
    highTermsCheck, laurentNF_sound terms y] at h
  simpa only [oneC, Rat.cast_add, hsiteR] using h

theorem lowCap :
    ((ceSignedSpT1End00TR + ceSignedSpT1End00U + zeroE : ℚ) : ℝ) + (zeroC : ℝ) * Real.log (ceSignedSpT1End00Hi : ℝ) ≤ (ceSignedSpT1ZeroCap : ℝ) := by
  have hr : endR ceSignedSpT1End00Site ceSignedSpT1End00Lo ceSignedSpT1End00Hi = ceSignedSpT1End00Hi := by decide +kernel
  have ht : ceSignedSpT1End00Target + zeroE ≤ ceSignedSpT1ZeroCap := by decide +kernel
  have h := endUOK_cmp ceSignedSpT1End00Singular
  rw [hr] at h
  have h' := (Rat.cast_le (K := ℝ)).mpr ht
  simp only [zeroC, Rat.cast_add] at h' ⊢
  linarith only [h, h']

theorem highCap :
    ((ceSignedSpT1End01TR + ceSignedSpT1End01U : ℚ) : ℝ) + (oneC : ℝ) * Real.log (1 - (ceSignedSpT1End01Lo : ℝ)) ≤ (ceSignedSpT1End01Target : ℝ) := by
  have hr : endR ceSignedSpT1End01Site ceSignedSpT1End01Lo ceSignedSpT1End01Hi = 1 - ceSignedSpT1End01Lo := by decide +kernel
  have h := endUOK_cmp ceSignedSpT1End01Singular
  rw [hr] at h
  simpa only [oneC, Rat.cast_add, Rat.cast_sub, Rat.cast_one] using h

#print axioms lowLog
#print axioms highLog
#print axioms lowCap
#print axioms highCap
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Endpoints
