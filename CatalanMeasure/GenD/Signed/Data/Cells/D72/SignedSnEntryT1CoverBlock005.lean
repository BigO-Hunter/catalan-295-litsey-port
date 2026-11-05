module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core078
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core079
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core080
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core081
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core082
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core083
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core084
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core085
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core086
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core087
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core088
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1End02
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell080 : ∀ y ∈ Icc ((((-9091853 : ℚ) / 122880000) : ℚ) : ℝ) ((((-827623 : ℚ) / 12288000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P078Lo : ℝ) (ceSignedSnEntryT1P078Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P078Lo, ceSignedSnEntryT1P078Hi, SignedSnEntryT1Core078Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P078Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core078Literal.q2] at h ⊢
  exact h

private theorem cell081 : ∀ y ∈ Icc ((((-827623 : ℚ) / 12288000) : ℚ) : ℝ) ((((-2486869 : ℚ) / 40960000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P079Lo : ℝ) (ceSignedSnEntryT1P079Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P079Lo, ceSignedSnEntryT1P079Hi, SignedSnEntryT1Core079Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P079Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core079Literal.q2] at h ⊢
  exact h

private theorem cell082 : ∀ y ∈ Icc ((((-2486869 : ℚ) / 40960000) : ℚ) : ℝ) ((((-830623 : ℚ) / 15360000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P080Lo : ℝ) (ceSignedSnEntryT1P080Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P080Lo, ceSignedSnEntryT1P080Hi, SignedSnEntryT1Core080Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P080Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core080Literal.q2] at h ⊢
  exact h

private theorem cell083 : ∀ y ∈ Icc ((((-830623 : ℚ) / 15360000) : ℚ) : ℝ) ((((-5829361 : ℚ) / 122880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P081Lo : ℝ) (ceSignedSnEntryT1P081Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P081Lo, ceSignedSnEntryT1P081Hi, SignedSnEntryT1Core081Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P081Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core081Literal.q2] at h ⊢
  exact h

private theorem cell084 : ∀ y ∈ Icc ((((-5829361 : ℚ) / 122880000) : ℚ) : ℝ) ((((-835623 : ℚ) / 20480000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P082Lo : ℝ) (ceSignedSnEntryT1P082Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P082Lo, ceSignedSnEntryT1P082Hi, SignedSnEntryT1Core082Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P082Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core082Literal.q2] at h ⊢
  exact h

private theorem cell085 : ∀ y ∈ Icc ((((-835623 : ℚ) / 20480000) : ℚ) : ℝ) ((((-839623 : ℚ) / 24576000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P083Lo : ℝ) (ceSignedSnEntryT1P083Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P083Lo, ceSignedSnEntryT1P083Hi, SignedSnEntryT1Core083Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P083Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core083Literal.q2] at h ⊢
  exact h

private theorem cell086 : ∀ y ∈ Icc ((((-839623 : ℚ) / 24576000) : ℚ) : ℝ) ((((-845623 : ℚ) / 30720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P084Lo : ℝ) (ceSignedSnEntryT1P084Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P084Lo, ceSignedSnEntryT1P084Hi, SignedSnEntryT1Core084Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P084Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core084Literal.q2] at h ⊢
  exact h

private theorem cell087 : ∀ y ∈ Icc ((((-845623 : ℚ) / 30720000) : ℚ) : ℝ) ((((-855623 : ℚ) / 40960000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P085Lo : ℝ) (ceSignedSnEntryT1P085Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P085Lo, ceSignedSnEntryT1P085Hi, SignedSnEntryT1Core085Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P085Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core085Literal.q2] at h ⊢
  exact h

private theorem cell088 : ∀ y ∈ Icc ((((-855623 : ℚ) / 40960000) : ℚ) : ℝ) ((((-875623 : ℚ) / 61440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P086Lo : ℝ) (ceSignedSnEntryT1P086Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P086Lo, ceSignedSnEntryT1P086Hi, SignedSnEntryT1Core086Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P086Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core086Literal.q2] at h ⊢
  exact h

private theorem cell089 : ∀ y ∈ Icc ((((-875623 : ℚ) / 61440000) : ℚ) : ℝ) ((((-935623 : ℚ) / 122880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P087Lo : ℝ) (ceSignedSnEntryT1P087Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P087Lo, ceSignedSnEntryT1P087Hi, SignedSnEntryT1Core087Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P087Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core087Literal.q2] at h ⊢
  exact h

private theorem cell090 : ∀ y ∈ Icc ((((-935623 : ℚ) / 122880000) : ℚ) : ℝ) ((((-1 : ℚ) / 1024) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P088Lo : ℝ) (ceSignedSnEntryT1P088Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P088Lo, ceSignedSnEntryT1P088Hi, SignedSnEntryT1Core088Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P088Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core088Literal.q2] at h ⊢
  exact h

theorem endIdentity91 : fieldNFCheck ceSignedSnEntryT1E02FullFq ceSignedSnEntryT1Fq = true := by decide +kernel
    
private theorem cell091 : ∀ y ∈ Icc ((((-1 : ℚ) / 1024) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1E02Lo : ℝ) (ceSignedSnEntryT1E02Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1E02Lo, ceSignedSnEntryT1E02Hi, SignedSnEntryT1End02Literal.q2, ceSignedSnEntryT1E02EndLiteral.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1E02Bound y hx (by norm_num [ceSignedSnEntryT1E02Site, ceSignedSnEntryT1E02EndLiteral.q2]; exact ne_of_lt hd.2)
  rw [fieldNFCheck_sound endIdentity91 y] at h
  simp only [ceSignedSnEntryT1E02FullTs, lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1End02Literal.q2, ceSignedSnEntryT1E02Target, ceSignedSnEntryT1E02EndLiteral.q2] at h ⊢
  exact h

theorem cover005 : ∀ y ∈ Icc ((((-9091853 : ℚ) / 122880000) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union cell080 (cover_union cell081 cell082)) (cover_union cell083 (cover_union cell084 cell085))) (cover_union (cover_union cell086 (cover_union cell087 cell088)) (cover_union cell089 (cover_union cell090 cell091))))
#print axioms cover005
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Cover
