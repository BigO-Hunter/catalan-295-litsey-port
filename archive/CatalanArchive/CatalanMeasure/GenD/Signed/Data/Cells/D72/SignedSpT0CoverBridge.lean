module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverBinding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0ZeroTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Endpoints
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


theorem beforeOf
    (plain : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 8) : ℚ) : ℝ),
      x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ))
    (pre : ∀ x ∈ Icc ((((1 : ℚ) / 8) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ),
      x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ)) : ∀ x ∈ Ioc (ceSignedSpT0End00Hi : ℝ) (1023/1024 : ℝ),
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T0.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T0.spFq.poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn) 0 x ≤ (ceSignedSpT0ZeroCap : ℝ) := by
  intro x hx
  have hx0 : 0 < x := (by norm_num [ceSignedSpT0End00Hi, ceSignedSpT0End00EndLiteral.q2] : (0 : ℝ) < (ceSignedSpT0End00Hi : ℝ)).trans hx.1
  have hx1 : x < 1 := hx.2.trans_lt (by norm_num)
  by_cases hcut : x ≤ (1/8 : ℝ)
  · have h := ceSignedSpT0ZeroTransfer (by
      intro y hy
      have hh := plain y (by norm_num [ceSignedSpT0ZeroHi, SignedSpT0ZeroTransferLiteral.q2, Set.mem_Ioc, Set.mem_Icc] at hy ⊢; exact ⟨hy.1.le,hy.2⟩)
        ⟨hy.1, hy.2.trans_lt (by norm_num [ceSignedSpT0ZeroHi, SignedSpT0ZeroTransferLiteral.q2])⟩
      norm_num [ceSignedSpT0ZeroPlainCap, SignedSpT0ZeroTransferLiteral.q2] at hh ⊢
      simpa only [lfieldTower_nil_zero,add_zero] using hh)
      x ⟨hx0, by norm_num [ceSignedSpT0ZeroHi, SignedSpT0ZeroTransferLiteral.q2]; exact hcut⟩
    rw [fieldNFCheck_sound CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Endpoints.lowFieldCheck x, CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Endpoints.lowTermsEq x] at h
    exact h
  · have h := pre x (by norm_num [Set.mem_Icc]; exact ⟨le_of_not_ge hcut,hx.2⟩) ⟨hx0,hx1⟩
    rw [namedValue x] at h
    norm_num [ceSignedSpT0ZeroCap, SignedSpT0ZeroTransferLiteral.q2] at h ⊢
    exact h

theorem afterOf
    (post : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ),
      x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ)) : ∀ x ∈ Ico (1023/1024 : ℝ) 1,
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T0.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T0.spFq.poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn) 0 x ≤ (ceSignedSpT0End01Target : ℝ) := by
  intro x hx
  have h := post x (by norm_num [Set.mem_Icc]; exact ⟨hx.1,hx.2.le⟩)
    ⟨(by norm_num : (0 : ℝ) < 1023/1024).trans_le hx.1,hx.2⟩
  rw [namedValue x] at h
  norm_num [ceSignedSpT0End01Target, ceSignedSpT0End01EndLiteral.q2] at h ⊢
  exact h
#print axioms beforeOf
#print axioms afterOf

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
