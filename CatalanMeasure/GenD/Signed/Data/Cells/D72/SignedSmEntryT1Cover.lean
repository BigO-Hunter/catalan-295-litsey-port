module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Core000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Core001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Core002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Core003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Core004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Core005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Core006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Core007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Core008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Core009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Core010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Core011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Binding
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem endIdentity : fieldNFCheck ceSignedSmEntryT1E00FullFq ceSignedSmEntryT1Fq = true := by decide +kernel

private theorem cell000 : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT1Fq (poleF ceSignedSmEntryT1Fq.poles) 0 x ≤ ((((-5570396054187 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT1E00Lo : ℝ) (ceSignedSmEntryT1E00Hi : ℝ) := by
    norm_num [ceSignedSmEntryT1E00Lo, ceSignedSmEntryT1E00Hi, SignedSmEntryT1End00Literal.q2, ceSignedSmEntryT1E00EndLiteral.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT1E00Full x hx'
  rw [fieldNFCheck_sound endIdentity x] at h
  simp only [ceSignedSmEntryT1E00FullTs, lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT1End00Literal.q2, ceSignedSmEntryT1E00Target, ceSignedSmEntryT1E00EndLiteral.q2] at h ⊢
  exact h


private theorem cell001 : ∀ x ∈ Icc ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((-11432155004281117493 : ℚ) / 11434920928870400000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT1Fq (poleF ceSignedSmEntryT1Fq.poles) 0 x ≤ ((((-5570396054187 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT1P000Lo : ℝ) (ceSignedSmEntryT1P000Hi : ℝ) := by
    norm_num [ceSignedSmEntryT1P000Lo, ceSignedSmEntryT1P000Hi, SignedSmEntryT1Core000Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT1P000Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT1Core000Literal.q2] at h ⊢
  exact h


private theorem cell002 : ∀ x ∈ Icc ((((-11432155004281117493 : ℚ) / 11434920928870400000) : ℚ) : ℝ) ((((-2855964307636117493 : ℚ) / 2858730232217600000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT1Fq (poleF ceSignedSmEntryT1Fq.poles) 0 x ≤ ((((-5570396054187 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT1P001Lo : ℝ) (ceSignedSmEntryT1P001Hi : ℝ) := by
    norm_num [ceSignedSmEntryT1P001Lo, ceSignedSmEntryT1P001Hi, SignedSmEntryT1Core001Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT1P001Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT1Core001Literal.q2] at h ⊢
  exact h


private theorem cell003 : ∀ x ∈ Icc ((((-2855964307636117493 : ℚ) / 2858730232217600000) : ℚ) : ℝ) ((((-1426599191528617493 : ℚ) / 1429365116108800000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT1Fq (poleF ceSignedSmEntryT1Fq.poles) 0 x ≤ ((((-5570396054187 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT1P002Lo : ℝ) (ceSignedSmEntryT1P002Hi : ℝ) := by
    norm_num [ceSignedSmEntryT1P002Lo, ceSignedSmEntryT1P002Hi, SignedSmEntryT1Core002Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT1P002Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT1Core002Literal.q2] at h ⊢
  exact h


private theorem cell004 : ∀ x ∈ Icc ((((-1426599191528617493 : ℚ) / 1429365116108800000) : ℚ) : ℝ) ((((-711916633474867493 : ℚ) / 714682558054400000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT1Fq (poleF ceSignedSmEntryT1Fq.poles) 0 x ≤ ((((-5570396054187 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT1P003Lo : ℝ) (ceSignedSmEntryT1P003Hi : ℝ) := by
    norm_num [ceSignedSmEntryT1P003Lo, ceSignedSmEntryT1P003Hi, SignedSmEntryT1Core003Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT1P003Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT1Core003Literal.q2] at h ⊢
  exact h


private theorem cell005 : ∀ x ∈ Icc ((((-711916633474867493 : ℚ) / 714682558054400000) : ℚ) : ℝ) ((((-354575354447992493 : ℚ) / 357341279027200000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT1Fq (poleF ceSignedSmEntryT1Fq.poles) 0 x ≤ ((((-5570396054187 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT1P004Lo : ℝ) (ceSignedSmEntryT1P004Hi : ℝ) := by
    norm_num [ceSignedSmEntryT1P004Lo, ceSignedSmEntryT1P004Hi, SignedSmEntryT1Core004Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT1P004Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT1Core004Literal.q2] at h ⊢
  exact h


private theorem cell006 : ∀ x ∈ Icc ((((-354575354447992493 : ℚ) / 357341279027200000) : ℚ) : ℝ) ((((-175904714934554993 : ℚ) / 178670639513600000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT1Fq (poleF ceSignedSmEntryT1Fq.poles) 0 x ≤ ((((-5570396054187 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT1P005Lo : ℝ) (ceSignedSmEntryT1P005Hi : ℝ) := by
    norm_num [ceSignedSmEntryT1P005Lo, ceSignedSmEntryT1P005Hi, SignedSmEntryT1Core005Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT1P005Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT1Core005Literal.q2] at h ⊢
  exact h


private theorem cell007 : ∀ x ∈ Icc ((((-175904714934554993 : ℚ) / 178670639513600000) : ℚ) : ℝ) ((((-86569395177836243 : ℚ) / 89335319756800000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT1Fq (poleF ceSignedSmEntryT1Fq.poles) 0 x ≤ ((((-5570396054187 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT1P006Lo : ℝ) (ceSignedSmEntryT1P006Hi : ℝ) := by
    norm_num [ceSignedSmEntryT1P006Lo, ceSignedSmEntryT1P006Hi, SignedSmEntryT1Core006Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT1P006Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT1Core006Literal.q2] at h ⊢
  exact h


private theorem cell008 : ∀ x ∈ Icc ((((-86569395177836243 : ℚ) / 89335319756800000) : ℚ) : ℝ) ((((-81037546020071229 : ℚ) / 89335319756800000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT1Fq (poleF ceSignedSmEntryT1Fq.poles) 0 x ≤ ((((-5570396054187 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT1P007Lo : ℝ) (ceSignedSmEntryT1P007Hi : ℝ) := by
    norm_num [ceSignedSmEntryT1P007Lo, ceSignedSmEntryT1P007Hi, SignedSmEntryT1Core007Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT1P007Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT1Core007Literal.q2] at h ⊢
  exact h


private theorem cell009 : ∀ x ∈ Icc ((((-81037546020071229 : ℚ) / 89335319756800000) : ℚ) : ℝ) ((((-64441998546776187 : ℚ) / 89335319756800000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT1Fq (poleF ceSignedSmEntryT1Fq.poles) 0 x ≤ ((((-5570396054187 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT1P008Lo : ℝ) (ceSignedSmEntryT1P008Hi : ℝ) := by
    norm_num [ceSignedSmEntryT1P008Lo, ceSignedSmEntryT1P008Hi, SignedSmEntryT1Core008Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT1P008Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT1Core008Literal.q2] at h ⊢
  exact h


private theorem cell010 : ∀ x ∈ Icc ((((-64441998546776187 : ℚ) / 89335319756800000) : ℚ) : ℝ) ((((-42314601915716131 : ℚ) / 89335319756800000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT1Fq (poleF ceSignedSmEntryT1Fq.poles) 0 x ≤ ((((-5570396054187 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT1P009Lo : ℝ) (ceSignedSmEntryT1P009Hi : ℝ) := by
    norm_num [ceSignedSmEntryT1P009Lo, ceSignedSmEntryT1P009Hi, SignedSmEntryT1Core009Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT1P009Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT1Core009Literal.q2] at h ⊢
  exact h


private theorem cell011 : ∀ x ∈ Icc ((((-42314601915716131 : ℚ) / 89335319756800000) : ℚ) : ℝ) ((((-11476564931769291 : ℚ) / 44667659878400000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT1Fq (poleF ceSignedSmEntryT1Fq.poles) 0 x ≤ ((((-5570396054187 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT1P010Lo : ℝ) (ceSignedSmEntryT1P010Hi : ℝ) := by
    norm_num [ceSignedSmEntryT1P010Lo, ceSignedSmEntryT1P010Hi, SignedSmEntryT1Core010Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT1P010Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT1Core010Literal.q2] at h ⊢
  exact h


private theorem cell012 : ∀ x ∈ Icc ((((-11476564931769291 : ℚ) / 44667659878400000) : ℚ) : ℝ) ((((-19501 : ℚ) / 100000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT1Fq (poleF ceSignedSmEntryT1Fq.poles) 0 x ≤ ((((-5570396054187 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT1P011Lo : ℝ) (ceSignedSmEntryT1P011Hi : ℝ) := by
    norm_num [ceSignedSmEntryT1P011Lo, ceSignedSmEntryT1P011Hi, SignedSmEntryT1Core011Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT1P011Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT1Core011Literal.q2] at h ⊢
  exact h


theorem named : ∀ x ∈ Ioc (-1 : ℝ) ((((-19501 : ℚ) / 100000) : ℚ) : ℝ),
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T1.smFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T1.smFq.poles) 0 x ≤ ((((-5570396054187 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-19501 : ℚ) / 100000) : ℚ) : ℝ) := by simpa using (show x ∈ Icc (-1 : ℝ) ((((-19501 : ℚ) / 100000) : ℚ) : ℝ) from ⟨hx.1.le, hx.2⟩)
  have h := (cover_union (cover_union (cover_union cell000 (cover_union cell001 cell002)) (cover_union cell003 (cover_union cell004 cell005))) (cover_union (cover_union cell006 (cover_union cell007 cell008)) (cover_union (cover_union cell009 cell010) (cover_union cell011 cell012)))) x hx'
  rw [ceSignedSmEntryT1FieldEq x] at h
  exact h
#print axioms named
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT1Cover
