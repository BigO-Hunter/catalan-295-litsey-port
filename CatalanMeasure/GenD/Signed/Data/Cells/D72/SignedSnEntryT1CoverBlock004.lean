module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core062
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core063
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core064
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core065
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core066
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core067
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core068
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core069
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core070
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core071
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core072
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core073
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core074
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core075
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core076
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core077
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell064 : ∀ y ∈ Icc ((((-18879329 : ℚ) / 122880000) : ℚ) : ℝ) ((((-74701693 : ℚ) / 491520000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P062Lo : ℝ) (ceSignedSnEntryT1P062Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P062Lo, ceSignedSnEntryT1P062Hi, SignedSnEntryT1Core062Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P062Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core062Literal.q2] at h ⊢
  exact h

private theorem cell065 : ∀ y ∈ Icc ((((-74701693 : ℚ) / 491520000) : ℚ) : ℝ) ((((-9031853 : ℚ) / 61440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P063Lo : ℝ) (ceSignedSnEntryT1P063Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P063Lo, ceSignedSnEntryT1P063Hi, SignedSnEntryT1Core063Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P063Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core063Literal.q2] at h ⊢
  exact h

private theorem cell066 : ∀ y ∈ Icc ((((-9031853 : ℚ) / 61440000) : ℚ) : ℝ) ((((-5749361 : ℚ) / 40960000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P064Lo : ℝ) (ceSignedSnEntryT1P064Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P064Lo, ceSignedSnEntryT1P064Hi, SignedSnEntryT1Core064Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P064Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core064Literal.q2] at h ⊢
  exact h

private theorem cell067 : ∀ y ∈ Icc ((((-5749361 : ℚ) / 40960000) : ℚ) : ℝ) ((((-821623 : ℚ) / 6144000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P065Lo : ℝ) (ceSignedSnEntryT1P065Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P065Lo, ceSignedSnEntryT1P065Hi, SignedSnEntryT1Core065Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P065Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core065Literal.q2] at h ⊢
  exact h

private theorem cell068 : ∀ y ∈ Icc ((((-821623 : ℚ) / 6144000) : ℚ) : ℝ) ((((-822023 : ℚ) / 6553600) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P066Lo : ℝ) (ceSignedSnEntryT1P066Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P066Lo, ceSignedSnEntryT1P066Hi, SignedSnEntryT1Core066Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P066Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core066Literal.q2] at h ⊢
  exact h

private theorem cell069 : ∀ y ∈ Icc ((((-822023 : ℚ) / 6553600) : ℚ) : ℝ) ((((-30418051 : ℚ) / 245760000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P067Lo : ℝ) (ceSignedSnEntryT1P067Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P067Lo, ceSignedSnEntryT1P067Hi, SignedSnEntryT1Core067Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P067Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core067Literal.q2] at h ⊢
  exact h

private theorem cell070 : ∀ y ∈ Icc ((((-30418051 : ℚ) / 245760000) : ℚ) : ℝ) ((((-60020479 : ℚ) / 491520000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P068Lo : ℝ) (ceSignedSnEntryT1P068Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P068Lo, ceSignedSnEntryT1P068Hi, SignedSnEntryT1Core068Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P068Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core068Literal.q2] at h ⊢
  exact h

private theorem cell071 : ∀ y ∈ Icc ((((-60020479 : ℚ) / 491520000) : ℚ) : ℝ) ((((-2466869 : ℚ) / 20480000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P069Lo : ℝ) (ceSignedSnEntryT1P069Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P069Lo, ceSignedSnEntryT1P069Hi, SignedSnEntryT1Core069Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P069Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core069Literal.q2] at h ⊢
  exact h

private theorem cell072 : ∀ y ∈ Icc ((((-2466869 : ℚ) / 20480000) : ℚ) : ℝ) ((((-5757361 : ℚ) / 49152000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P070Lo : ℝ) (ceSignedSnEntryT1P070Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P070Lo, ceSignedSnEntryT1P070Hi, SignedSnEntryT1Core070Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P070Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core070Literal.q2] at h ⊢
  exact h

private theorem cell073 : ∀ y ∈ Icc ((((-5757361 : ℚ) / 49152000) : ℚ) : ℝ) ((((-13985591 : ℚ) / 122880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P071Lo : ℝ) (ceSignedSnEntryT1P071Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P071Lo, ceSignedSnEntryT1P071Hi, SignedSnEntryT1Core071Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P071Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core071Literal.q2] at h ⊢
  exact h

private theorem cell074 : ∀ y ∈ Icc ((((-13985591 : ℚ) / 122880000) : ℚ) : ℝ) ((((-823123 : ℚ) / 7680000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P072Lo : ℝ) (ceSignedSnEntryT1P072Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P072Lo, ceSignedSnEntryT1P072Hi, SignedSnEntryT1Core072Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P072Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core072Literal.q2] at h ⊢
  exact h

private theorem cell075 : ∀ y ∈ Icc ((((-823123 : ℚ) / 7680000) : ℚ) : ℝ) ((((-823623 : ℚ) / 8192000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P073Lo : ℝ) (ceSignedSnEntryT1P073Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P073Lo, ceSignedSnEntryT1P073Hi, SignedSnEntryT1Core073Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P073Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core073Literal.q2] at h ⊢
  exact h

private theorem cell076 : ∀ y ∈ Icc ((((-823623 : ℚ) / 8192000) : ℚ) : ℝ) ((((-5769361 : ℚ) / 61440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P074Lo : ℝ) (ceSignedSnEntryT1P074Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P074Lo, ceSignedSnEntryT1P074Hi, SignedSnEntryT1Core074Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P074Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core074Literal.q2] at h ⊢
  exact h

private theorem cell077 : ∀ y ∈ Icc ((((-5769361 : ℚ) / 61440000) : ℚ) : ℝ) ((((-10723099 : ℚ) / 122880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P075Lo : ℝ) (ceSignedSnEntryT1P075Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P075Lo, ceSignedSnEntryT1P075Hi, SignedSnEntryT1Core075Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P075Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core075Literal.q2] at h ⊢
  exact h

private theorem cell078 : ∀ y ∈ Icc ((((-10723099 : ℚ) / 122880000) : ℚ) : ℝ) ((((-825623 : ℚ) / 10240000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P076Lo : ℝ) (ceSignedSnEntryT1P076Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P076Lo, ceSignedSnEntryT1P076Hi, SignedSnEntryT1Core076Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P076Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core076Literal.q2] at h ⊢
  exact h

private theorem cell079 : ∀ y ∈ Icc ((((-825623 : ℚ) / 10240000) : ℚ) : ℝ) ((((-9091853 : ℚ) / 122880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P077Lo : ℝ) (ceSignedSnEntryT1P077Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P077Lo, ceSignedSnEntryT1P077Hi, SignedSnEntryT1Core077Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P077Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core077Literal.q2] at h ⊢
  exact h

theorem cover004 : ∀ y ∈ Icc ((((-18879329 : ℚ) / 122880000) : ℚ) : ℝ) ((((-9091853 : ℚ) / 122880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell064 cell065) (cover_union cell066 cell067)) (cover_union (cover_union cell068 cell069) (cover_union cell070 cell071))) (cover_union (cover_union (cover_union cell072 cell073) (cover_union cell074 cell075)) (cover_union (cover_union cell076 cell077) (cover_union cell078 cell079))))
#print axioms cover004
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Cover
