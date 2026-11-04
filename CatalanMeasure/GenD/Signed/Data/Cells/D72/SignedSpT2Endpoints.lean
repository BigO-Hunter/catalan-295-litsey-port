module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2End01
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2ZeroTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroSeriesPoint
public import CatalanMeasure.GenD.Signed.Data.Trial72.T2Fields
public import CatalanMeasure.GenD.Signed.Data.Assembly.RowsCell

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2LowBinding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2HighBinding

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Endpoints
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

theorem lowLog : ∀ y ∈ Ioc 0 (ceSignedSpT2End00Hi : ℝ),
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq.poles) 0 y + lfieldTower terms 0 y ≤
    ((ceSignedSpT2End00TR + ceSignedSpT2End00U + zeroE : ℚ) : ℝ) + (zeroC : ℝ) * Real.log |y| := by
  intro y hy
  have hlo : ceSignedSpT2End00Lo = 0 := by decide +kernel
  have hsite : ceSignedSpT2End00Site = 0 := by decide +kernel
  have hhi : ceSignedSpT2End00Hi ≤ ceSignedSpT2ZeroHi := by decide +kernel
  have hx : y ∈ Icc (ceSignedSpT2End00Lo : ℝ) (ceSignedSpT2End00Hi : ℝ) :=
    ⟨by simpa only [hlo, Rat.cast_zero] using hy.1.le, hy.2⟩
  have h := endOK_sound ceSignedSpT2End00FullFq ceSignedSpT2End00FullTs ceSignedSpT2End00Site ceSignedSpT2End00Lo ceSignedSpT2End00Hi 10
    ceSignedSpT2End00U ceSignedSpT2End00TR (endOK_of_endUOK ceSignedSpT2End00Singular) ceSignedSpT2End00Regular y hx
  rw [fieldNFCheck_sound lowPlainCheck y] at h
  have hsiteR : (ceSignedSpT2End00Site : ℝ) = 0 := by rw [hsite, Rat.cast_zero]
  simp only [ceSignedSpT2End00FullTs, lfieldTower_nil_zero, add_zero, hsiteR, sub_zero] at h
  have h' := D72.zeroSeries_point ceSignedSpT2ZeroInputFq ceSignedSpT2ZeroPlain ceSignedSpT2ZeroInputTs ceSignedSpT2ZeroHi 64 0
    ceSignedSpT2ZeroSeriesOK ceSignedSpT2ZeroSeriesCancel rfl rfl ceSignedSpT2ZeroSeriesPoly
    (x := y) ⟨hy.1, hy.2.trans ((Rat.cast_le (K := ℝ)).mpr hhi)⟩
  rw [fieldNFCheck_sound lowFieldCheck y, lowTermsEq y] at h'
  have hb := (Rat.cast_le (K := ℝ)).mpr ceSignedSpT2ZeroSeriesBudget
  simp only [zeroC, zeroE, ceSignedSpT2End00FullTs, Rat.cast_add, Rat.cast_sub, Rat.cast_zero, add_zero, zero_add] at h' hb ⊢
  linarith only [h, h', hb]

theorem highLog : ∀ y ∈ Icc (ceSignedSpT2End01Lo : ℝ) 1, y ≠ 1 →
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq.poles) 0 y + lfieldTower terms 0 y ≤
    ((ceSignedSpT2End01TR + ceSignedSpT2End01U : ℚ) : ℝ) + (oneC : ℝ) * Real.log |y - 1| := by
  intro y hy _
  have hhi : ceSignedSpT2End01Hi = 1 := by decide +kernel
  have hsite : ceSignedSpT2End01Site = 1 := by decide +kernel
  have hsiteR : (ceSignedSpT2End01Site : ℝ) = 1 := by rw [hsite, Rat.cast_one]
  have h := endOK_sound ceSignedSpT2End01FullFq ceSignedSpT2End01FullTs ceSignedSpT2End01Site ceSignedSpT2End01Lo ceSignedSpT2End01Hi 40
    ceSignedSpT2End01U ceSignedSpT2End01TR (endOK_of_endUOK ceSignedSpT2End01Singular) ceSignedSpT2End01Regular y
    (by simpa only [hhi, Rat.cast_one] using hy)
  rw [fieldNFCheck_sound highFieldCheck y, ← laurentNF_sound ceSignedSpT2End01FullTs y,
    highTermsCheck, laurentNF_sound terms y] at h
  simpa only [oneC, Rat.cast_add, hsiteR] using h

theorem lowCap :
    ((ceSignedSpT2End00TR + ceSignedSpT2End00U + zeroE : ℚ) : ℝ) + (zeroC : ℝ) * Real.log (ceSignedSpT2End00Hi : ℝ) ≤ (ceSignedSpT2ZeroCap : ℝ) := by
  have hr : endR ceSignedSpT2End00Site ceSignedSpT2End00Lo ceSignedSpT2End00Hi = ceSignedSpT2End00Hi := by decide +kernel
  have ht : ceSignedSpT2End00Target + zeroE ≤ ceSignedSpT2ZeroCap := by decide +kernel
  have h := endUOK_cmp ceSignedSpT2End00Singular
  rw [hr] at h
  have h' := (Rat.cast_le (K := ℝ)).mpr ht
  simp only [zeroC, Rat.cast_add] at h' ⊢
  linarith only [h, h']

theorem highCap :
    ((ceSignedSpT2End01TR + ceSignedSpT2End01U : ℚ) : ℝ) + (oneC : ℝ) * Real.log (1 - (ceSignedSpT2End01Lo : ℝ)) ≤ (ceSignedSpT2End01Target : ℝ) := by
  have hr : endR ceSignedSpT2End01Site ceSignedSpT2End01Lo ceSignedSpT2End01Hi = 1 - ceSignedSpT2End01Lo := by decide +kernel
  have h := endUOK_cmp ceSignedSpT2End01Singular
  rw [hr] at h
  simpa only [oneC, Rat.cast_add, Rat.cast_sub, Rat.cast_one] using h

#print axioms lowLog
#print axioms highLog
#print axioms lowCap
#print axioms highCap
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Endpoints
