module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core014
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

theorem endIdentity0 : fieldNFCheck ceSignedSnEntryT2E00FullFq ceSignedSnEntryT2Fq = true := by decide +kernel
    
private theorem cell000 : ∀ y ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2E00Lo : ℝ) (ceSignedSnEntryT2E00Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2E00Lo, ceSignedSnEntryT2E00Hi, SignedSnEntryT2End00Literal.q2, ceSignedSnEntryT2E00EndLiteral.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2E00Full y hx
  rw [fieldNFCheck_sound endIdentity0 y] at h
  simp only [ceSignedSnEntryT2E00FullTs, lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2End00Literal.q2, ceSignedSnEntryT2E00Target, ceSignedSnEntryT2E00EndLiteral.q2] at h ⊢
  exact h

private theorem cell001 : ∀ y ∈ Icc ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((-92233720347119515035747 : ℚ) / 92233720368547758080000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P000Lo : ℝ) (ceSignedSnEntryT2P000Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P000Lo, ceSignedSnEntryT2P000Hi, SignedSnEntryT2Core000Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P000Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core000Literal.q2] at h ⊢
  exact h

private theorem cell002 : ∀ y ∈ Icc ((((-92233720347119515035747 : ℚ) / 92233720368547758080000) : ℚ) : ℝ) ((((-23058430070771611035747 : ℚ) / 23058430092136939520000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P001Lo : ℝ) (ceSignedSnEntryT2P001Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P001Lo, ceSignedSnEntryT2P001Hi, SignedSnEntryT2Core001Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P001Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core001Literal.q2] at h ⊢
  exact h

private theorem cell003 : ∀ y ∈ Icc ((((-23058430070771611035747 : ℚ) / 23058430092136939520000) : ℚ) : ℝ) ((((-5764607501684635035747 : ℚ) / 5764607523034234880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P002Lo : ℝ) (ceSignedSnEntryT2P002Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P002Lo, ceSignedSnEntryT2P002Hi, SignedSnEntryT2Core002Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P002Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core002Literal.q2] at h ⊢
  exact h

private theorem cell004 : ∀ y ∈ Icc ((((-5764607501684635035747 : ℚ) / 5764607523034234880000) : ℚ) : ℝ) ((((-2882303740170139035747 : ℚ) / 2882303761517117440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P003Lo : ℝ) (ceSignedSnEntryT2P003Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P003Lo, ceSignedSnEntryT2P003Hi, SignedSnEntryT2Core003Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P003Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core003Literal.q2] at h ⊢
  exact h

private theorem cell005 : ∀ y ∈ Icc ((((-2882303740170139035747 : ℚ) / 2882303761517117440000) : ℚ) : ℝ) ((((-1441151859412891035747 : ℚ) / 1441151880758558720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P004Lo : ℝ) (ceSignedSnEntryT2P004Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P004Lo, ceSignedSnEntryT2P004Hi, SignedSnEntryT2Core004Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P004Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core004Literal.q2] at h ⊢
  exact h

private theorem cell006 : ∀ y ∈ Icc ((((-1441151859412891035747 : ℚ) / 1441151880758558720000) : ℚ) : ℝ) ((((-720575919034267035747 : ℚ) / 720575940379279360000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P005Lo : ℝ) (ceSignedSnEntryT2P005Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P005Lo, ceSignedSnEntryT2P005Hi, SignedSnEntryT2Core005Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P005Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core005Literal.q2] at h ⊢
  exact h

private theorem cell007 : ∀ y ∈ Icc ((((-720575919034267035747 : ℚ) / 720575940379279360000) : ℚ) : ℝ) ((((-360287948844955035747 : ℚ) / 360287970189639680000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P006Lo : ℝ) (ceSignedSnEntryT2P006Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P006Lo, ceSignedSnEntryT2P006Hi, SignedSnEntryT2Core006Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P006Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core006Literal.q2] at h ⊢
  exact h

private theorem cell008 : ∀ y ∈ Icc ((((-360287948844955035747 : ℚ) / 360287970189639680000) : ℚ) : ℝ) ((((-180143963750299035747 : ℚ) / 180143985094819840000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P007Lo : ℝ) (ceSignedSnEntryT2P007Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P007Lo, ceSignedSnEntryT2P007Hi, SignedSnEntryT2Core007Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P007Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core007Literal.q2] at h ⊢
  exact h

private theorem cell009 : ∀ y ∈ Icc ((((-180143963750299035747 : ℚ) / 180143985094819840000) : ℚ) : ℝ) ((((-90071971202971035747 : ℚ) / 90071992547409920000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P008Lo : ℝ) (ceSignedSnEntryT2P008Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P008Lo, ceSignedSnEntryT2P008Hi, SignedSnEntryT2Core008Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P008Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core008Literal.q2] at h ⊢
  exact h

private theorem cell010 : ∀ y ∈ Icc ((((-90071971202971035747 : ℚ) / 90071992547409920000) : ℚ) : ℝ) ((((-45035974929307035747 : ℚ) / 45035996273704960000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P009Lo : ℝ) (ceSignedSnEntryT2P009Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P009Lo, ceSignedSnEntryT2P009Hi, SignedSnEntryT2Core009Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P009Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core009Literal.q2] at h ⊢
  exact h

private theorem cell011 : ∀ y ∈ Icc ((((-45035974929307035747 : ℚ) / 45035996273704960000) : ℚ) : ℝ) ((((-22517976792475035747 : ℚ) / 22517998136852480000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P010Lo : ℝ) (ceSignedSnEntryT2P010Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P010Lo, ceSignedSnEntryT2P010Hi, SignedSnEntryT2Core010Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P010Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core010Literal.q2] at h ⊢
  exact h

private theorem cell012 : ∀ y ∈ Icc ((((-22517976792475035747 : ℚ) / 22517998136852480000) : ℚ) : ℝ) ((((-11258977724059035747 : ℚ) / 11258999068426240000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P011Lo : ℝ) (ceSignedSnEntryT2P011Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P011Lo, ceSignedSnEntryT2P011Hi, SignedSnEntryT2Core011Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P011Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core011Literal.q2] at h ⊢
  exact h

private theorem cell013 : ∀ y ∈ Icc ((((-11258977724059035747 : ℚ) / 11258999068426240000) : ℚ) : ℝ) ((((-5629478189851035747 : ℚ) / 5629499534213120000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P012Lo : ℝ) (ceSignedSnEntryT2P012Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P012Lo, ceSignedSnEntryT2P012Hi, SignedSnEntryT2Core012Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P012Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core012Literal.q2] at h ⊢
  exact h

private theorem cell014 : ∀ y ∈ Icc ((((-5629478189851035747 : ℚ) / 5629499534213120000) : ℚ) : ℝ) ((((-2814728422747035747 : ℚ) / 2814749767106560000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P013Lo : ℝ) (ceSignedSnEntryT2P013Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P013Lo, ceSignedSnEntryT2P013Hi, SignedSnEntryT2Core013Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P013Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core013Literal.q2] at h ⊢
  exact h

private theorem cell015 : ∀ y ∈ Icc ((((-2814728422747035747 : ℚ) / 2814749767106560000) : ℚ) : ℝ) ((((-1407353539195035747 : ℚ) / 1407374883553280000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P014Lo : ℝ) (ceSignedSnEntryT2P014Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P014Lo, ceSignedSnEntryT2P014Hi, SignedSnEntryT2Core014Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P014Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core014Literal.q2] at h ⊢
  exact h

theorem cover000 : ∀ y ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-1407353539195035747 : ℚ) / 1407374883553280000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell000 cell001) (cover_union cell002 cell003)) (cover_union (cover_union cell004 cell005) (cover_union cell006 cell007))) (cover_union (cover_union (cover_union cell008 cell009) (cover_union cell010 cell011)) (cover_union (cover_union cell012 cell013) (cover_union cell014 cell015))))
#print axioms cover000
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
