module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core014
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

theorem endIdentity0 : fieldNFCheck ceSignedSnEntryT0E00FullFq ceSignedSnEntryT0Fq = true := by decide +kernel
    
private theorem cell000 : ∀ y ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0E00Lo : ℝ) (ceSignedSnEntryT0E00Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0E00Lo, ceSignedSnEntryT0E00Hi, SignedSnEntryT0End00Literal.q2, ceSignedSnEntryT0E00EndLiteral.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0E00Full y hx
  rw [fieldNFCheck_sound endIdentity0 y] at h
  simp only [ceSignedSnEntryT0E00FullTs, lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0End00Literal.q2, ceSignedSnEntryT0E00Target, ceSignedSnEntryT0E00EndLiteral.q2] at h ⊢
  exact h

private theorem cell001 : ∀ y ∈ Icc ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((-4722366481766912360449 : ℚ) / 4722366482869645213696) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P000Lo : ℝ) (ceSignedSnEntryT0P000Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P000Lo, ceSignedSnEntryT0P000Hi, SignedSnEntryT0Core000Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P000Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core000Literal.q2] at h ⊢
  exact h

private theorem cell002 : ∀ y ∈ Icc ((((-4722366481766912360449 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((-1180591619617899675649 : ℚ) / 1180591620717411303424) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P001Lo : ℝ) (ceSignedSnEntryT0P001Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P001Lo, ceSignedSnEntryT0P001Hi, SignedSnEntryT0Core001Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P001Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core001Literal.q2] at h ⊢
  exact h

private theorem cell003 : ∀ y ∈ Icc ((((-1180591619617899675649 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((-590295809259730894849 : ℚ) / 590295810358705651712) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P002Lo : ℝ) (ceSignedSnEntryT0P002Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P002Lo, ceSignedSnEntryT0P002Hi, SignedSnEntryT0Core002Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P002Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core002Literal.q2] at h ⊢
  exact h

private theorem cell004 : ∀ y ∈ Icc ((((-590295809259730894849 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((-295147904080646504449 : ℚ) / 295147905179352825856) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P003Lo : ℝ) (ceSignedSnEntryT0P003Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P003Lo, ceSignedSnEntryT0P003Hi, SignedSnEntryT0Core003Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P003Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core003Literal.q2] at h ⊢
  exact h

private theorem cell005 : ∀ y ∈ Icc ((((-295147904080646504449 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((-147573951491104309249 : ℚ) / 147573952589676412928) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P004Lo : ℝ) (ceSignedSnEntryT0P004Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P004Lo, ceSignedSnEntryT0P004Hi, SignedSnEntryT0Core004Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P004Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core004Literal.q2] at h ⊢
  exact h

private theorem cell006 : ∀ y ∈ Icc ((((-147573951491104309249 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((-73786975196333211649 : ℚ) / 73786976294838206464) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P005Lo : ℝ) (ceSignedSnEntryT0P005Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P005Lo, ceSignedSnEntryT0P005Hi, SignedSnEntryT0Core005Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P005Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core005Literal.q2] at h ⊢
  exact h

private theorem cell007 : ∀ y ∈ Icc ((((-73786975196333211649 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((-36893487048947662849 : ℚ) / 36893488147419103232) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P006Lo : ℝ) (ceSignedSnEntryT0P006Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P006Lo, ceSignedSnEntryT0P006Hi, SignedSnEntryT0Core006Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P006Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core006Literal.q2] at h ⊢
  exact h

private theorem cell008 : ∀ y ∈ Icc ((((-36893487048947662849 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((-18446742975254888449 : ℚ) / 18446744073709551616) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P007Lo : ℝ) (ceSignedSnEntryT0P007Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P007Lo, ceSignedSnEntryT0P007Hi, SignedSnEntryT0Core007Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P007Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core007Literal.q2] at h ⊢
  exact h

private theorem cell009 : ∀ y ∈ Icc ((((-18446742975254888449 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((-9223370938408501249 : ℚ) / 9223372036854775808) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P008Lo : ℝ) (ceSignedSnEntryT0P008Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P008Lo, ceSignedSnEntryT0P008Hi, SignedSnEntryT0Core008Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P008Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core008Literal.q2] at h ⊢
  exact h

private theorem cell010 : ∀ y ∈ Icc ((((-9223370938408501249 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((-4611684919985307649 : ℚ) / 4611686018427387904) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P009Lo : ℝ) (ceSignedSnEntryT0P009Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P009Lo, ceSignedSnEntryT0P009Hi, SignedSnEntryT0Core009Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P009Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core009Literal.q2] at h ⊢
  exact h

private theorem cell011 : ∀ y ∈ Icc ((((-4611684919985307649 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((-2305841910773710849 : ℚ) / 2305843009213693952) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P010Lo : ℝ) (ceSignedSnEntryT0P010Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P010Lo, ceSignedSnEntryT0P010Hi, SignedSnEntryT0Core010Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P010Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core010Literal.q2] at h ⊢
  exact h

private theorem cell012 : ∀ y ∈ Icc ((((-2305841910773710849 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((-1152920406167912449 : ℚ) / 1152921504606846976) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P011Lo : ℝ) (ceSignedSnEntryT0P011Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P011Lo, ceSignedSnEntryT0P011Hi, SignedSnEntryT0Core011Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P011Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core011Literal.q2] at h ⊢
  exact h

private theorem cell013 : ∀ y ∈ Icc ((((-1152920406167912449 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((-576459653865013249 : ℚ) / 576460752303423488) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P012Lo : ℝ) (ceSignedSnEntryT0P012Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P012Lo, ceSignedSnEntryT0P012Hi, SignedSnEntryT0Core012Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P012Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core012Literal.q2] at h ⊢
  exact h

private theorem cell014 : ∀ y ∈ Icc ((((-576459653865013249 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((-288229277713563649 : ℚ) / 288230376151711744) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P013Lo : ℝ) (ceSignedSnEntryT0P013Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P013Lo, ceSignedSnEntryT0P013Hi, SignedSnEntryT0Core013Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P013Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core013Literal.q2] at h ⊢
  exact h

private theorem cell015 : ∀ y ∈ Icc ((((-288229277713563649 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((-144114089637838849 : ℚ) / 144115188075855872) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P014Lo : ℝ) (ceSignedSnEntryT0P014Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P014Lo, ceSignedSnEntryT0P014Hi, SignedSnEntryT0Core014Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P014Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core014Literal.q2] at h ⊢
  exact h

theorem cover000 : ∀ y ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-144114089637838849 : ℚ) / 144115188075855872) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell000 cell001) (cover_union cell002 cell003)) (cover_union (cover_union cell004 cell005) (cover_union cell006 cell007))) (cover_union (cover_union (cover_union cell008 cell009) (cover_union cell010 cell011)) (cover_union (cover_union cell012 cell013) (cover_union cell014 cell015))))
#print axioms cover000
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover
