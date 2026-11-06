module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0End01
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0ZeroTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroSeriesPoint
public import CatalanMeasure.GenD.Signed.Data.Trial72.T0Fields
public import CatalanMeasure.GenD.Signed.Data.Assembly.RowsCell

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0LowBinding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0HighBinding

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Endpoints
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

theorem lowLog : ∀ y ∈ Ioc 0 (ceSignedSpT0End00Hi : ℝ),
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T0.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T0.spFq.poles) 0 y + lfieldTower terms 0 y ≤
    ((ceSignedSpT0End00TR + ceSignedSpT0End00U + zeroE : ℚ) : ℝ) + (zeroC : ℝ) * Real.log |y| := by
  intro y hy
  have hlo : ceSignedSpT0End00Lo = 0 := by decide +kernel
  have hsite : ceSignedSpT0End00Site = 0 := by decide +kernel
  have hhi : ceSignedSpT0End00Hi ≤ ceSignedSpT0ZeroHi := by decide +kernel
  have hx : y ∈ Icc (ceSignedSpT0End00Lo : ℝ) (ceSignedSpT0End00Hi : ℝ) :=
    ⟨by simpa only [hlo, Rat.cast_zero] using hy.1.le, hy.2⟩
  have h := endOK_sound ceSignedSpT0End00FullFq ceSignedSpT0End00FullTs ceSignedSpT0End00Site ceSignedSpT0End00Lo ceSignedSpT0End00Hi 10
    ceSignedSpT0End00U ceSignedSpT0End00TR (endOK_of_endUOK ceSignedSpT0End00Singular) ceSignedSpT0End00Regular y hx
  rw [fieldNFCheck_sound lowPlainCheck y] at h
  have hsiteR : (ceSignedSpT0End00Site : ℝ) = 0 := by rw [hsite, Rat.cast_zero]
  simp only [ceSignedSpT0End00FullTs, lfieldTower_nil_zero, add_zero, hsiteR, sub_zero] at h
  have h' := D72.zeroSeries_point ceSignedSpT0ZeroInputFq ceSignedSpT0ZeroPlain ceSignedSpT0ZeroInputTs ceSignedSpT0ZeroHi 64 0
    ceSignedSpT0ZeroSeriesOK ceSignedSpT0ZeroSeriesCancel rfl rfl ceSignedSpT0ZeroSeriesPoly
    (x := y) ⟨hy.1, hy.2.trans ((Rat.cast_le (K := ℝ)).mpr hhi)⟩
  rw [fieldNFCheck_sound lowFieldCheck y, lowTermsEq y] at h'
  have hb := (Rat.cast_le (K := ℝ)).mpr ceSignedSpT0ZeroSeriesBudget
  simp only [zeroC, zeroE, ceSignedSpT0End00FullTs, Rat.cast_add, Rat.cast_sub, Rat.cast_zero, add_zero, zero_add] at h' hb ⊢
  linarith only [h, h', hb]

theorem highLog : ∀ y ∈ Icc (ceSignedSpT0End01Lo : ℝ) 1, y ≠ 1 →
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T0.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T0.spFq.poles) 0 y + lfieldTower terms 0 y ≤
    ((ceSignedSpT0End01TR + ceSignedSpT0End01U : ℚ) : ℝ) + (oneC : ℝ) * Real.log |y - 1| := by
  intro y hy _
  have hhi : ceSignedSpT0End01Hi = 1 := by decide +kernel
  have hsite : ceSignedSpT0End01Site = 1 := by decide +kernel
  have hsiteR : (ceSignedSpT0End01Site : ℝ) = 1 := by rw [hsite, Rat.cast_one]
  have h := endOK_sound ceSignedSpT0End01FullFq ceSignedSpT0End01FullTs ceSignedSpT0End01Site ceSignedSpT0End01Lo ceSignedSpT0End01Hi 40
    ceSignedSpT0End01U ceSignedSpT0End01TR (endOK_of_endUOK ceSignedSpT0End01Singular) ceSignedSpT0End01Regular y
    (by simpa only [hhi, Rat.cast_one] using hy)
  rw [fieldNFCheck_sound highFieldCheck y, ← laurentNF_sound ceSignedSpT0End01FullTs y,
    highTermsCheck, laurentNF_sound terms y] at h
  simpa only [oneC, Rat.cast_add, hsiteR] using h

theorem lowCap :
    ((ceSignedSpT0End00TR + ceSignedSpT0End00U + zeroE : ℚ) : ℝ) + (zeroC : ℝ) * Real.log (ceSignedSpT0End00Hi : ℝ) ≤ (ceSignedSpT0ZeroCap : ℝ) := by
  have hr : endR ceSignedSpT0End00Site ceSignedSpT0End00Lo ceSignedSpT0End00Hi = ceSignedSpT0End00Hi := by decide +kernel
  have ht : ceSignedSpT0End00Target + zeroE ≤ ceSignedSpT0ZeroCap := by decide +kernel
  have h := endUOK_cmp ceSignedSpT0End00Singular
  rw [hr] at h
  have h' := (Rat.cast_le (K := ℝ)).mpr ht
  simp only [zeroC, Rat.cast_add] at h' ⊢
  linarith only [h, h']

theorem highCap :
    ((ceSignedSpT0End01TR + ceSignedSpT0End01U : ℚ) : ℝ) + (oneC : ℝ) * Real.log (1 - (ceSignedSpT0End01Lo : ℝ)) ≤ (ceSignedSpT0End01Target : ℝ) := by
  have hr : endR ceSignedSpT0End01Site ceSignedSpT0End01Lo ceSignedSpT0End01Hi = 1 - ceSignedSpT0End01Lo := by decide +kernel
  have h := endUOK_cmp ceSignedSpT0End01Singular
  rw [hr] at h
  simpa only [oneC, Rat.cast_add, Rat.cast_sub, Rat.cast_one] using h

#print axioms lowLog
#print axioms highLog
#print axioms lowCap
#print axioms highCap
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Endpoints
