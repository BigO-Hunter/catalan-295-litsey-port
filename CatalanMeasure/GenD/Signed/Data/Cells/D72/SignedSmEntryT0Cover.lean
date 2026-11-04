module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Core000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Core001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Core002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Core003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Core004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Core005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Core006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Core007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Core008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Core009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Core010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Core011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Binding
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem endIdentity : fieldNFCheck ceSignedSmEntryT0E00FullFq ceSignedSmEntryT0Fq = true := by decide +kernel

private theorem cell000 : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT0Fq (poleF ceSignedSmEntryT0Fq.poles) 0 x ≤ ((((-349229889121 : ℚ) / 68719476736) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT0E00Lo : ℝ) (ceSignedSmEntryT0E00Hi : ℝ) := by
    norm_num [ceSignedSmEntryT0E00Lo, ceSignedSmEntryT0E00Hi, SignedSmEntryT0End00Literal.q2, ceSignedSmEntryT0E00EndLiteral.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT0E00Full x hx'
  rw [fieldNFCheck_sound endIdentity x] at h
  simp only [ceSignedSmEntryT0E00FullTs, lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT0End00Literal.q2, ceSignedSmEntryT0E00Target, ceSignedSmEntryT0E00EndLiteral.q2] at h ⊢
  exact h


private theorem cell001 : ∀ x ∈ Icc ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((-11432155004281117493 : ℚ) / 11434920928870400000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT0Fq (poleF ceSignedSmEntryT0Fq.poles) 0 x ≤ ((((-349229889121 : ℚ) / 68719476736) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT0P000Lo : ℝ) (ceSignedSmEntryT0P000Hi : ℝ) := by
    norm_num [ceSignedSmEntryT0P000Lo, ceSignedSmEntryT0P000Hi, SignedSmEntryT0Core000Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT0P000Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT0Core000Literal.q2] at h ⊢
  exact h


private theorem cell002 : ∀ x ∈ Icc ((((-11432155004281117493 : ℚ) / 11434920928870400000) : ℚ) : ℝ) ((((-2855964307636117493 : ℚ) / 2858730232217600000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT0Fq (poleF ceSignedSmEntryT0Fq.poles) 0 x ≤ ((((-349229889121 : ℚ) / 68719476736) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT0P001Lo : ℝ) (ceSignedSmEntryT0P001Hi : ℝ) := by
    norm_num [ceSignedSmEntryT0P001Lo, ceSignedSmEntryT0P001Hi, SignedSmEntryT0Core001Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT0P001Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT0Core001Literal.q2] at h ⊢
  exact h


private theorem cell003 : ∀ x ∈ Icc ((((-2855964307636117493 : ℚ) / 2858730232217600000) : ℚ) : ℝ) ((((-1426599191528617493 : ℚ) / 1429365116108800000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT0Fq (poleF ceSignedSmEntryT0Fq.poles) 0 x ≤ ((((-349229889121 : ℚ) / 68719476736) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT0P002Lo : ℝ) (ceSignedSmEntryT0P002Hi : ℝ) := by
    norm_num [ceSignedSmEntryT0P002Lo, ceSignedSmEntryT0P002Hi, SignedSmEntryT0Core002Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT0P002Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT0Core002Literal.q2] at h ⊢
  exact h


private theorem cell004 : ∀ x ∈ Icc ((((-1426599191528617493 : ℚ) / 1429365116108800000) : ℚ) : ℝ) ((((-711916633474867493 : ℚ) / 714682558054400000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT0Fq (poleF ceSignedSmEntryT0Fq.poles) 0 x ≤ ((((-349229889121 : ℚ) / 68719476736) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT0P003Lo : ℝ) (ceSignedSmEntryT0P003Hi : ℝ) := by
    norm_num [ceSignedSmEntryT0P003Lo, ceSignedSmEntryT0P003Hi, SignedSmEntryT0Core003Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT0P003Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT0Core003Literal.q2] at h ⊢
  exact h


private theorem cell005 : ∀ x ∈ Icc ((((-711916633474867493 : ℚ) / 714682558054400000) : ℚ) : ℝ) ((((-354575354447992493 : ℚ) / 357341279027200000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT0Fq (poleF ceSignedSmEntryT0Fq.poles) 0 x ≤ ((((-349229889121 : ℚ) / 68719476736) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT0P004Lo : ℝ) (ceSignedSmEntryT0P004Hi : ℝ) := by
    norm_num [ceSignedSmEntryT0P004Lo, ceSignedSmEntryT0P004Hi, SignedSmEntryT0Core004Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT0P004Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT0Core004Literal.q2] at h ⊢
  exact h


private theorem cell006 : ∀ x ∈ Icc ((((-354575354447992493 : ℚ) / 357341279027200000) : ℚ) : ℝ) ((((-175904714934554993 : ℚ) / 178670639513600000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT0Fq (poleF ceSignedSmEntryT0Fq.poles) 0 x ≤ ((((-349229889121 : ℚ) / 68719476736) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT0P005Lo : ℝ) (ceSignedSmEntryT0P005Hi : ℝ) := by
    norm_num [ceSignedSmEntryT0P005Lo, ceSignedSmEntryT0P005Hi, SignedSmEntryT0Core005Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT0P005Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT0Core005Literal.q2] at h ⊢
  exact h


private theorem cell007 : ∀ x ∈ Icc ((((-175904714934554993 : ℚ) / 178670639513600000) : ℚ) : ℝ) ((((-86569395177836243 : ℚ) / 89335319756800000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT0Fq (poleF ceSignedSmEntryT0Fq.poles) 0 x ≤ ((((-349229889121 : ℚ) / 68719476736) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT0P006Lo : ℝ) (ceSignedSmEntryT0P006Hi : ℝ) := by
    norm_num [ceSignedSmEntryT0P006Lo, ceSignedSmEntryT0P006Hi, SignedSmEntryT0Core006Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT0P006Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT0Core006Literal.q2] at h ⊢
  exact h


private theorem cell008 : ∀ x ∈ Icc ((((-86569395177836243 : ℚ) / 89335319756800000) : ℚ) : ℝ) ((((-81037546020071229 : ℚ) / 89335319756800000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT0Fq (poleF ceSignedSmEntryT0Fq.poles) 0 x ≤ ((((-349229889121 : ℚ) / 68719476736) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT0P007Lo : ℝ) (ceSignedSmEntryT0P007Hi : ℝ) := by
    norm_num [ceSignedSmEntryT0P007Lo, ceSignedSmEntryT0P007Hi, SignedSmEntryT0Core007Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT0P007Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT0Core007Literal.q2] at h ⊢
  exact h


private theorem cell009 : ∀ x ∈ Icc ((((-81037546020071229 : ℚ) / 89335319756800000) : ℚ) : ℝ) ((((-64441998546776187 : ℚ) / 89335319756800000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT0Fq (poleF ceSignedSmEntryT0Fq.poles) 0 x ≤ ((((-349229889121 : ℚ) / 68719476736) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT0P008Lo : ℝ) (ceSignedSmEntryT0P008Hi : ℝ) := by
    norm_num [ceSignedSmEntryT0P008Lo, ceSignedSmEntryT0P008Hi, SignedSmEntryT0Core008Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT0P008Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT0Core008Literal.q2] at h ⊢
  exact h


private theorem cell010 : ∀ x ∈ Icc ((((-64441998546776187 : ℚ) / 89335319756800000) : ℚ) : ℝ) ((((-42314601915716131 : ℚ) / 89335319756800000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT0Fq (poleF ceSignedSmEntryT0Fq.poles) 0 x ≤ ((((-349229889121 : ℚ) / 68719476736) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT0P009Lo : ℝ) (ceSignedSmEntryT0P009Hi : ℝ) := by
    norm_num [ceSignedSmEntryT0P009Lo, ceSignedSmEntryT0P009Hi, SignedSmEntryT0Core009Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT0P009Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT0Core009Literal.q2] at h ⊢
  exact h


private theorem cell011 : ∀ x ∈ Icc ((((-42314601915716131 : ℚ) / 89335319756800000) : ℚ) : ℝ) ((((-11476564931769291 : ℚ) / 44667659878400000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT0Fq (poleF ceSignedSmEntryT0Fq.poles) 0 x ≤ ((((-349229889121 : ℚ) / 68719476736) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT0P010Lo : ℝ) (ceSignedSmEntryT0P010Hi : ℝ) := by
    norm_num [ceSignedSmEntryT0P010Lo, ceSignedSmEntryT0P010Hi, SignedSmEntryT0Core010Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT0P010Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT0Core010Literal.q2] at h ⊢
  exact h


private theorem cell012 : ∀ x ∈ Icc ((((-11476564931769291 : ℚ) / 44667659878400000) : ℚ) : ℝ) ((((-19501 : ℚ) / 100000) : ℚ) : ℝ),
    fieldTower ceSignedSmEntryT0Fq (poleF ceSignedSmEntryT0Fq.poles) 0 x ≤ ((((-349229889121 : ℚ) / 68719476736) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc (ceSignedSmEntryT0P011Lo : ℝ) (ceSignedSmEntryT0P011Hi : ℝ) := by
    norm_num [ceSignedSmEntryT0P011Lo, ceSignedSmEntryT0P011Hi, SignedSmEntryT0Core011Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSmEntryT0P011Bound x hx'
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSmEntryT0Core011Literal.q2] at h ⊢
  exact h


theorem named : ∀ x ∈ Ioc (-1 : ℝ) ((((-19501 : ℚ) / 100000) : ℚ) : ℝ),
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T0.smFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T0.smFq.poles) 0 x ≤ ((((-349229889121 : ℚ) / 68719476736) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-19501 : ℚ) / 100000) : ℚ) : ℝ) := by simpa using (show x ∈ Icc (-1 : ℝ) ((((-19501 : ℚ) / 100000) : ℚ) : ℝ) from ⟨hx.1.le, hx.2⟩)
  have h := (cover_union (cover_union (cover_union cell000 (cover_union cell001 cell002)) (cover_union cell003 (cover_union cell004 cell005))) (cover_union (cover_union cell006 (cover_union cell007 cell008)) (cover_union (cover_union cell009 cell010) (cover_union cell011 cell012)))) x hx'
  rw [ceSignedSmEntryT0FieldEq x] at h
  exact h
#print axioms named
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Cover
