module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Core000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Core001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Core002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Core003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Core004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Core005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Core006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Core007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Core008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Core009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Core010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Core011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Core012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Core013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Binding
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem endIdentity : fieldNFCheck ceSignedSmEntryT2E00FullFq ceSignedSmEntryT2Fq = true := by decide +kernel

private theorem cell000 : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT2Fq (poleF ceSignedSmEntryT2Fq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT2E00Lo : ℝ) (ceSignedSmEntryT2E00Hi : ℝ) := by
    norm_num [ceSignedSmEntryT2E00Lo, ceSignedSmEntryT2E00Hi, SignedSmEntryT2End00Literal.q2, ceSignedSmEntryT2E00EndLiteral.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT2E00Full x hx'
  rw [fieldNFCheck_sound endIdentity x] at h
  simp only [ceSignedSmEntryT2E00FullTs, lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT2End00Literal.q2, ceSignedSmEntryT2E00Target, ceSignedSmEntryT2E00EndLiteral.q2] at h ⊢
  exact h


private theorem cell001 : ∀ x ∈ Icc ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((-5714694539851117493 : ℚ) / 5717460464435200000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT2Fq (poleF ceSignedSmEntryT2Fq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT2P000Lo : ℝ) (ceSignedSmEntryT2P000Hi : ℝ) := by
    norm_num [ceSignedSmEntryT2P000Lo, ceSignedSmEntryT2P000Hi, SignedSmEntryT2Core000Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT2P000Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT2Core000Literal.q2] at h ⊢
  exact h


private theorem cell002 : ∀ x ∈ Icc ((((-5714694539851117493 : ℚ) / 5717460464435200000) : ℚ) : ℝ) ((((-1426599191528617493 : ℚ) / 1429365116108800000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT2Fq (poleF ceSignedSmEntryT2Fq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT2P001Lo : ℝ) (ceSignedSmEntryT2P001Hi : ℝ) := by
    norm_num [ceSignedSmEntryT2P001Lo, ceSignedSmEntryT2P001Hi, SignedSmEntryT2Core001Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT2P001Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT2Core001Literal.q2] at h ⊢
  exact h


private theorem cell003 : ∀ x ∈ Icc ((((-1426599191528617493 : ℚ) / 1429365116108800000) : ℚ) : ℝ) ((((-711916633474867493 : ℚ) / 714682558054400000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT2Fq (poleF ceSignedSmEntryT2Fq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT2P002Lo : ℝ) (ceSignedSmEntryT2P002Hi : ℝ) := by
    norm_num [ceSignedSmEntryT2P002Lo, ceSignedSmEntryT2P002Hi, SignedSmEntryT2Core002Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT2P002Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT2Core002Literal.q2] at h ⊢
  exact h


private theorem cell004 : ∀ x ∈ Icc ((((-711916633474867493 : ℚ) / 714682558054400000) : ℚ) : ℝ) ((((-354575354447992493 : ℚ) / 357341279027200000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT2Fq (poleF ceSignedSmEntryT2Fq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT2P003Lo : ℝ) (ceSignedSmEntryT2P003Hi : ℝ) := by
    norm_num [ceSignedSmEntryT2P003Lo, ceSignedSmEntryT2P003Hi, SignedSmEntryT2Core003Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT2P003Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT2Core003Literal.q2] at h ⊢
  exact h


private theorem cell005 : ∀ x ∈ Icc ((((-354575354447992493 : ℚ) / 357341279027200000) : ℚ) : ℝ) ((((-175904714934554993 : ℚ) / 178670639513600000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT2Fq (poleF ceSignedSmEntryT2Fq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT2P004Lo : ℝ) (ceSignedSmEntryT2P004Hi : ℝ) := by
    norm_num [ceSignedSmEntryT2P004Lo, ceSignedSmEntryT2P004Hi, SignedSmEntryT2Core004Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT2P004Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT2Core004Literal.q2] at h ⊢
  exact h


private theorem cell006 : ∀ x ∈ Icc ((((-175904714934554993 : ℚ) / 178670639513600000) : ℚ) : ℝ) ((((-86569395177836243 : ℚ) / 89335319756800000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT2Fq (poleF ceSignedSmEntryT2Fq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT2P005Lo : ℝ) (ceSignedSmEntryT2P005Hi : ℝ) := by
    norm_num [ceSignedSmEntryT2P005Lo, ceSignedSmEntryT2P005Hi, SignedSmEntryT2Core005Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT2P005Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT2Core005Literal.q2] at h ⊢
  exact h


private theorem cell007 : ∀ x ∈ Icc ((((-86569395177836243 : ℚ) / 89335319756800000) : ℚ) : ℝ) ((((-81037546020071229 : ℚ) / 89335319756800000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT2Fq (poleF ceSignedSmEntryT2Fq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT2P006Lo : ℝ) (ceSignedSmEntryT2P006Hi : ℝ) := by
    norm_num [ceSignedSmEntryT2P006Lo, ceSignedSmEntryT2P006Hi, SignedSmEntryT2Core006Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT2P006Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT2Core006Literal.q2] at h ⊢
  exact h


private theorem cell008 : ∀ x ∈ Icc ((((-81037546020071229 : ℚ) / 89335319756800000) : ℚ) : ℝ) ((((-64441998546776187 : ℚ) / 89335319756800000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT2Fq (poleF ceSignedSmEntryT2Fq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT2P007Lo : ℝ) (ceSignedSmEntryT2P007Hi : ℝ) := by
    norm_num [ceSignedSmEntryT2P007Lo, ceSignedSmEntryT2P007Hi, SignedSmEntryT2Core007Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT2P007Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT2Core007Literal.q2] at h ⊢
  exact h


private theorem cell009 : ∀ x ∈ Icc ((((-64441998546776187 : ℚ) / 89335319756800000) : ℚ) : ℝ) ((((-42314601915716131 : ℚ) / 89335319756800000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT2Fq (poleF ceSignedSmEntryT2Fq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT2P008Lo : ℝ) (ceSignedSmEntryT2P008Hi : ℝ) := by
    norm_num [ceSignedSmEntryT2P008Lo, ceSignedSmEntryT2P008Hi, SignedSmEntryT2Core008Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT2P008Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT2Core008Literal.q2] at h ⊢
  exact h


private theorem cell010 : ∀ x ∈ Icc ((((-42314601915716131 : ℚ) / 89335319756800000) : ℚ) : ℝ) ((((-11476564931769291 : ℚ) / 44667659878400000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT2Fq (poleF ceSignedSmEntryT2Fq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT2P009Lo : ℝ) (ceSignedSmEntryT2P009Hi : ℝ) := by
    norm_num [ceSignedSmEntryT2P009Lo, ceSignedSmEntryT2P009Hi, SignedSmEntryT2Core009Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT2P009Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT2Core009Literal.q2] at h ⊢
  exact h


private theorem cell011 : ∀ x ∈ Icc ((((-11476564931769291 : ℚ) / 44667659878400000) : ℚ) : ℝ) ((((-72451047401976779 : ℚ) / 357341279027200000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT2Fq (poleF ceSignedSmEntryT2Fq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT2P010Lo : ℝ) (ceSignedSmEntryT2P010Hi : ℝ) := by
    norm_num [ceSignedSmEntryT2P010Lo, ceSignedSmEntryT2P010Hi, SignedSmEntryT2Core010Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT2P010Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT2Core010Literal.q2] at h ⊢
  exact h


private theorem cell012 : ∀ x ∈ Icc ((((-72451047401976779 : ℚ) / 357341279027200000) : ℚ) : ℝ) ((((-560246907163636683 : ℚ) / 2858730232217600000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT2Fq (poleF ceSignedSmEntryT2Fq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT2P011Lo : ℝ) (ceSignedSmEntryT2P011Hi : ℝ) := by
    norm_num [ceSignedSmEntryT2P011Lo, ceSignedSmEntryT2P011Hi, SignedSmEntryT2Core011Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT2P011Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT2Core011Literal.q2] at h ⊢
  exact h


private theorem cell013 : ∀ x ∈ Icc ((((-560246907163636683 : ℚ) / 2858730232217600000) : ℚ) : ℝ) ((((-1117727889748390859 : ℚ) / 5717460464435200000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT2Fq (poleF ceSignedSmEntryT2Fq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT2P012Lo : ℝ) (ceSignedSmEntryT2P012Hi : ℝ) := by
    norm_num [ceSignedSmEntryT2P012Lo, ceSignedSmEntryT2P012Hi, SignedSmEntryT2Core012Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT2P012Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT2Core012Literal.q2] at h ⊢
  exact h


private theorem cell014 : ∀ x ∈ Icc ((((-1117727889748390859 : ℚ) / 5717460464435200000) : ℚ) : ℝ) ((((-19501 : ℚ) / 100000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT2Fq (poleF ceSignedSmEntryT2Fq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT2P013Lo : ℝ) (ceSignedSmEntryT2P013Hi : ℝ) := by
    norm_num [ceSignedSmEntryT2P013Lo, ceSignedSmEntryT2P013Hi, SignedSmEntryT2Core013Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT2P013Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT2Core013Literal.q2] at h ⊢
  exact h


theorem named : ∀ x ∈ Ioc (-1 : ℝ) ((((-19501 : ℚ) / 100000) : ℚ) : ℝ),
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.smFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.smFq.poles) 0 x ≤ ((((-2784600393893 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-19501 : ℚ) / 100000) : ℚ) : ℝ) := by simpa using (show x ∈ Icc (-1 : ℝ) ((((-19501 : ℚ) / 100000) : ℚ) : ℝ) from ⟨hx.1.le, hx.2⟩)
  have h := (cover_union (cover_union (cover_union cell000 (cover_union cell001 cell002)) (cover_union (cover_union cell003 cell004) (cover_union cell005 cell006))) (cover_union (cover_union (cover_union cell007 cell008) (cover_union cell009 cell010)) (cover_union (cover_union cell011 cell012) (cover_union cell013 cell014)))) x hx'
  rw [ceSignedSmEntryT2FieldEq x] at h
  exact h
#print axioms named
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT2Cover
