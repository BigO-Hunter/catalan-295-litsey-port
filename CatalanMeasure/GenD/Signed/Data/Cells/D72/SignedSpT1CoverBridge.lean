module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverBinding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1ZeroTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Endpoints
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


theorem beforeOf
    (plain : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 8) : ℚ) : ℝ),
      x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ))
    (pre : ∀ x ∈ Icc ((((1 : ℚ) / 8) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ),
      x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ)) : ∀ x ∈ Ioc (ceSignedSpT1End00Hi : ℝ) (1023/1024 : ℝ),
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T1.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T1.spFq.poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qTn) 0 x ≤ (ceSignedSpT1ZeroCap : ℝ) := by
  intro x hx
  have hx0 : 0 < x := (by norm_num [ceSignedSpT1End00Hi, ceSignedSpT1End00EndLiteral.q2] : (0 : ℝ) < (ceSignedSpT1End00Hi : ℝ)).trans hx.1
  have hx1 : x < 1 := hx.2.trans_lt (by norm_num)
  by_cases hcut : x ≤ (1/8 : ℝ)
  · have h := ceSignedSpT1ZeroTransfer (by
      intro y hy
      have hh := plain y (by norm_num [ceSignedSpT1ZeroHi, SignedSpT1ZeroTransferLiteral.q2, Set.mem_Ioc, Set.mem_Icc] at hy ⊢; exact ⟨hy.1.le,hy.2⟩)
        ⟨hy.1, hy.2.trans_lt (by norm_num [ceSignedSpT1ZeroHi, SignedSpT1ZeroTransferLiteral.q2])⟩
      norm_num [ceSignedSpT1ZeroPlainCap, SignedSpT1ZeroTransferLiteral.q2] at hh ⊢
      simpa only [lfieldTower_nil_zero,add_zero] using hh)
      x ⟨hx0, by norm_num [ceSignedSpT1ZeroHi, SignedSpT1ZeroTransferLiteral.q2]; exact hcut⟩
    rw [fieldNFCheck_sound CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Endpoints.lowFieldCheck x, CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Endpoints.lowTermsEq x] at h
    exact h
  · have h := pre x (by norm_num [Set.mem_Icc]; exact ⟨le_of_not_ge hcut,hx.2⟩) ⟨hx0,hx1⟩
    rw [namedValue x] at h
    norm_num [ceSignedSpT1ZeroCap, SignedSpT1ZeroTransferLiteral.q2] at h ⊢
    exact h

theorem afterOf
    (post : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ),
      x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ)) : ∀ x ∈ Ico (1023/1024 : ℝ) 1,
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T1.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T1.spFq.poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qTn) 0 x ≤ (ceSignedSpT1End01Target : ℝ) := by
  intro x hx
  have h := post x (by norm_num [Set.mem_Icc]; exact ⟨hx.1,hx.2.le⟩)
    ⟨(by norm_num : (0 : ℝ) < 1023/1024).trans_le hx.1,hx.2⟩
  rw [namedValue x] at h
  norm_num [ceSignedSpT1End01Target, ceSignedSpT1End01EndLiteral.q2] at h ⊢
  exact h
#print axioms beforeOf
#print axioms afterOf

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
