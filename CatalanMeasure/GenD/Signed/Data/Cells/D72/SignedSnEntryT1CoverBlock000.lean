module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core014
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

theorem endIdentity0 : fieldNFCheck ceSignedSnEntryT1E00FullFq ceSignedSnEntryT1Fq = true := by decide +kernel
    
private theorem cell000 : ∀ y ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1E00Lo : ℝ) (ceSignedSnEntryT1E00Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1E00Lo, ceSignedSnEntryT1E00Hi, SignedSnEntryT1End00Literal.q2, ceSignedSnEntryT1E00EndLiteral.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1E00Full y hx
  rw [fieldNFCheck_sound endIdentity0 y] at h
  simp only [ceSignedSnEntryT1E00FullTs, lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1End00Literal.q2, ceSignedSnEntryT1E00Target, ceSignedSnEntryT1E00EndLiteral.q2] at h ⊢
  exact h

private theorem cell001 : ∀ y ∈ Icc ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((-2490310449371639703405169 : ℚ) / 2490310449950789468160000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P000Lo : ℝ) (ceSignedSnEntryT1P000Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P000Lo, ceSignedSnEntryT1P000Hi, SignedSnEntryT1Core000Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P000Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core000Literal.q2] at h ⊢
  exact h

private theorem cell002 : ∀ y ∈ Icc ((((-2490310449371639703405169 : ℚ) / 2490310449950789468160000) : ℚ) : ℝ) ((((-622577611910246295405169 : ℚ) / 622577612487697367040000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P001Lo : ℝ) (ceSignedSnEntryT1P001Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P001Lo, ceSignedSnEntryT1P001Hi, SignedSnEntryT1Core001Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P001Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core001Literal.q2] at h ⊢
  exact h

private theorem cell003 : ∀ y ∈ Icc ((((-622577611910246295405169 : ℚ) / 622577612487697367040000) : ℚ) : ℝ) ((((-311288805666680727405169 : ℚ) / 311288806243848683520000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P002Lo : ℝ) (ceSignedSnEntryT1P002Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P002Lo, ceSignedSnEntryT1P002Hi, SignedSnEntryT1Core002Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P002Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core002Literal.q2] at h ⊢
  exact h

private theorem cell004 : ∀ y ∈ Icc ((((-311288805666680727405169 : ℚ) / 311288806243848683520000) : ℚ) : ℝ) ((((-155644402544897943405169 : ℚ) / 155644403121924341760000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P003Lo : ℝ) (ceSignedSnEntryT1P003Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P003Lo, ceSignedSnEntryT1P003Hi, SignedSnEntryT1Core003Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P003Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core003Literal.q2] at h ⊢
  exact h

private theorem cell005 : ∀ y ∈ Icc ((((-155644402544897943405169 : ℚ) / 155644403121924341760000) : ℚ) : ℝ) ((((-77822200984006551405169 : ℚ) / 77822201560962170880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P004Lo : ℝ) (ceSignedSnEntryT1P004Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P004Lo, ceSignedSnEntryT1P004Hi, SignedSnEntryT1Core004Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P004Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core004Literal.q2] at h ⊢
  exact h

private theorem cell006 : ∀ y ∈ Icc ((((-77822200984006551405169 : ℚ) / 77822201560962170880000) : ℚ) : ℝ) ((((-38911100203560855405169 : ℚ) / 38911100780481085440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P005Lo : ℝ) (ceSignedSnEntryT1P005Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P005Lo, ceSignedSnEntryT1P005Hi, SignedSnEntryT1Core005Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P005Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core005Literal.q2] at h ⊢
  exact h

private theorem cell007 : ∀ y ∈ Icc ((((-38911100203560855405169 : ℚ) / 38911100780481085440000) : ℚ) : ℝ) ((((-19455549813338007405169 : ℚ) / 19455550390240542720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P006Lo : ℝ) (ceSignedSnEntryT1P006Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P006Lo, ceSignedSnEntryT1P006Hi, SignedSnEntryT1Core006Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P006Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core006Literal.q2] at h ⊢
  exact h

private theorem cell008 : ∀ y ∈ Icc ((((-19455549813338007405169 : ℚ) / 19455550390240542720000) : ℚ) : ℝ) ((((-9727774618226583405169 : ℚ) / 9727775195120271360000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P007Lo : ℝ) (ceSignedSnEntryT1P007Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P007Lo, ceSignedSnEntryT1P007Hi, SignedSnEntryT1Core007Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P007Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core007Literal.q2] at h ⊢
  exact h

private theorem cell009 : ∀ y ∈ Icc ((((-9727774618226583405169 : ℚ) / 9727775195120271360000) : ℚ) : ℝ) ((((-4863887020670871405169 : ℚ) / 4863887597560135680000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P008Lo : ℝ) (ceSignedSnEntryT1P008Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P008Lo, ceSignedSnEntryT1P008Hi, SignedSnEntryT1Core008Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P008Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core008Literal.q2] at h ⊢
  exact h

private theorem cell010 : ∀ y ∈ Icc ((((-4863887020670871405169 : ℚ) / 4863887597560135680000) : ℚ) : ℝ) ((((-2431943221893015405169 : ℚ) / 2431943798780067840000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P009Lo : ℝ) (ceSignedSnEntryT1P009Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P009Lo, ceSignedSnEntryT1P009Hi, SignedSnEntryT1Core009Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P009Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core009Literal.q2] at h ⊢
  exact h

private theorem cell011 : ∀ y ∈ Icc ((((-2431943221893015405169 : ℚ) / 2431943798780067840000) : ℚ) : ℝ) ((((-1215971322504087405169 : ℚ) / 1215971899390033920000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P010Lo : ℝ) (ceSignedSnEntryT1P010Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P010Lo, ceSignedSnEntryT1P010Hi, SignedSnEntryT1Core010Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P010Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core010Literal.q2] at h ⊢
  exact h

private theorem cell012 : ∀ y ∈ Icc ((((-1215971322504087405169 : ℚ) / 1215971899390033920000) : ℚ) : ℝ) ((((-607985372809623405169 : ℚ) / 607985949695016960000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P011Lo : ℝ) (ceSignedSnEntryT1P011Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P011Lo, ceSignedSnEntryT1P011Hi, SignedSnEntryT1Core011Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P011Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core011Literal.q2] at h ⊢
  exact h

private theorem cell013 : ∀ y ∈ Icc ((((-607985372809623405169 : ℚ) / 607985949695016960000) : ℚ) : ℝ) ((((-303992397962391405169 : ℚ) / 303992974847508480000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P012Lo : ℝ) (ceSignedSnEntryT1P012Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P012Lo, ceSignedSnEntryT1P012Hi, SignedSnEntryT1Core012Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P012Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core012Literal.q2] at h ⊢
  exact h

private theorem cell014 : ∀ y ∈ Icc ((((-303992397962391405169 : ℚ) / 303992974847508480000) : ℚ) : ℝ) ((((-151995910538775405169 : ℚ) / 151996487423754240000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P013Lo : ℝ) (ceSignedSnEntryT1P013Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P013Lo, ceSignedSnEntryT1P013Hi, SignedSnEntryT1Core013Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P013Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core013Literal.q2] at h ⊢
  exact h

private theorem cell015 : ∀ y ∈ Icc ((((-151995910538775405169 : ℚ) / 151996487423754240000) : ℚ) : ℝ) ((((-75997666826967405169 : ℚ) / 75998243711877120000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P014Lo : ℝ) (ceSignedSnEntryT1P014Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P014Lo, ceSignedSnEntryT1P014Hi, SignedSnEntryT1Core014Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P014Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core014Literal.q2] at h ⊢
  exact h

theorem cover000 : ∀ y ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-75997666826967405169 : ℚ) / 75998243711877120000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell000 cell001) (cover_union cell002 cell003)) (cover_union (cover_union cell004 cell005) (cover_union cell006 cell007))) (cover_union (cover_union (cover_union cell008 cell009) (cover_union cell010 cell011)) (cover_union (cover_union cell012 cell013) (cover_union cell014 cell015))))
#print axioms cover000
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Cover
