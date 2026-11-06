module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverBinding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2ZeroTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Endpoints
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


theorem beforeOf
    (plain : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 8) : ℚ) : ℝ),
      x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ))
    (pre : ∀ x ∈ Icc ((((1 : ℚ) / 8) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ),
      x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ)) : ∀ x ∈ Ioc (ceSignedSpT2End00Hi : ℝ) (1023/1024 : ℝ),
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq.poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qTn) 0 x ≤ (ceSignedSpT2ZeroCap : ℝ) := by
  intro x hx
  have hx0 : 0 < x := (by norm_num [ceSignedSpT2End00Hi, ceSignedSpT2End00EndLiteral.q2] : (0 : ℝ) < (ceSignedSpT2End00Hi : ℝ)).trans hx.1
  have hx1 : x < 1 := hx.2.trans_lt (by norm_num)
  by_cases hcut : x ≤ (1/8 : ℝ)
  · have h := ceSignedSpT2ZeroTransfer (by
      intro y hy
      have hh := plain y (by norm_num [ceSignedSpT2ZeroHi, SignedSpT2ZeroTransferLiteral.q2, Set.mem_Ioc, Set.mem_Icc] at hy ⊢; exact ⟨hy.1.le,hy.2⟩)
        ⟨hy.1, hy.2.trans_lt (by norm_num [ceSignedSpT2ZeroHi, SignedSpT2ZeroTransferLiteral.q2])⟩
      norm_num [ceSignedSpT2ZeroPlainCap, SignedSpT2ZeroTransferLiteral.q2] at hh ⊢
      simpa only [lfieldTower_nil_zero,add_zero] using hh)
      x ⟨hx0, by norm_num [ceSignedSpT2ZeroHi, SignedSpT2ZeroTransferLiteral.q2]; exact hcut⟩
    rw [fieldNFCheck_sound CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Endpoints.lowFieldCheck x, CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Endpoints.lowTermsEq x] at h
    exact h
  · have h := pre x (by norm_num [Set.mem_Icc]; exact ⟨le_of_not_ge hcut,hx.2⟩) ⟨hx0,hx1⟩
    rw [namedValue x] at h
    norm_num [ceSignedSpT2ZeroCap, SignedSpT2ZeroTransferLiteral.q2] at h ⊢
    exact h

theorem afterOf
    (post : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ),
      x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ)) : ∀ x ∈ Ico (1023/1024 : ℝ) 1,
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq.poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qTn) 0 x ≤ (ceSignedSpT2End01Target : ℝ) := by
  intro x hx
  have h := post x (by norm_num [Set.mem_Icc]; exact ⟨hx.1,hx.2.le⟩)
    ⟨(by norm_num : (0 : ℝ) < 1023/1024).trans_le hx.1,hx.2⟩
  rw [namedValue x] at h
  norm_num [ceSignedSpT2End01Target, ceSignedSpT2End01EndLiteral.q2] at h ⊢
  exact h
#print axioms beforeOf
#print axioms afterOf

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
