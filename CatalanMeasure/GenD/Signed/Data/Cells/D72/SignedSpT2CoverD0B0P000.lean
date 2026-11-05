module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0014
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT2CoverD0B0P000L000Field : fieldNFCheck ceSignedSpT2End00FullFq ceSignedSpT2ZeroPlain = true := by decide +kernel
private theorem SignedSpT2CoverD0B0P000L000Terms : laurentNF ceSignedSpT2End00FullTs = laurentNF [] := by decide +kernel

private theorem SignedSpT2CoverD0B0P000L000 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2End00Lo : ℝ) (ceSignedSpT2End00Hi : ℝ) := by
    norm_num [ceSignedSpT2End00Lo, ceSignedSpT2End00Hi, SignedSpT2End00Literal.q2, ceSignedSpT2End00EndLiteral.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2End00Bound x h' (by norm_num [ceSignedSpT2End00Site, ceSignedSpT2End00EndLiteral.q2]; exact ne_of_gt hd.1)
  rw [fieldNFCheck_sound SignedSpT2CoverD0B0P000L000Field x, ← laurentNF_sound ceSignedSpT2End00FullTs x, SignedSpT2CoverD0B0P000L000Terms, laurentNF_sound [] x] at h
  norm_num [SignedSpT2End00Literal.q2, ceSignedSpT2End00EndLiteral.q2, ceSignedSpT2End00Target] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P000L001 : ∀ x ∈ Icc ((((1 : ℚ) / 1024) : ℚ) : ℝ) ((((143 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0000Lo : ℝ) (ceSignedSpT2P0000Hi : ℝ) := by
    norm_num [ceSignedSpT2P0000Lo, ceSignedSpT2P0000Hi, SignedSpT2P0000Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0000Bound x h'
  norm_num [SignedSpT2P0000Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P000L002 : ∀ x ∈ Icc ((((143 : ℚ) / 16384) : ℚ) : ℝ) ((((135 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0001Lo : ℝ) (ceSignedSpT2P0001Hi : ℝ) := by
    norm_num [ceSignedSpT2P0001Lo, ceSignedSpT2P0001Hi, SignedSpT2P0001Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0001Bound x h'
  norm_num [SignedSpT2P0001Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P000L003 : ∀ x ∈ Icc ((((135 : ℚ) / 8192) : ℚ) : ℝ) ((((397 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0002Lo : ℝ) (ceSignedSpT2P0002Hi : ℝ) := by
    norm_num [ceSignedSpT2P0002Lo, ceSignedSpT2P0002Hi, SignedSpT2P0002Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0002Bound x h'
  norm_num [SignedSpT2P0002Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P000L004 : ∀ x ∈ Icc ((((397 : ℚ) / 16384) : ℚ) : ℝ) ((((131 : ℚ) / 4096) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0003Lo : ℝ) (ceSignedSpT2P0003Hi : ℝ) := by
    norm_num [ceSignedSpT2P0003Lo, ceSignedSpT2P0003Hi, SignedSpT2P0003Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0003Bound x h'
  norm_num [SignedSpT2P0003Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P000L005 : ∀ x ∈ Icc ((((131 : ℚ) / 4096) : ℚ) : ℝ) ((((651 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0004Lo : ℝ) (ceSignedSpT2P0004Hi : ℝ) := by
    norm_num [ceSignedSpT2P0004Lo, ceSignedSpT2P0004Hi, SignedSpT2P0004Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0004Bound x h'
  norm_num [SignedSpT2P0004Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P000L006 : ∀ x ∈ Icc ((((651 : ℚ) / 16384) : ℚ) : ℝ) ((((389 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0005Lo : ℝ) (ceSignedSpT2P0005Hi : ℝ) := by
    norm_num [ceSignedSpT2P0005Lo, ceSignedSpT2P0005Hi, SignedSpT2P0005Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0005Bound x h'
  norm_num [SignedSpT2P0005Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P000L007 : ∀ x ∈ Icc ((((389 : ℚ) / 8192) : ℚ) : ℝ) ((((905 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0006Lo : ℝ) (ceSignedSpT2P0006Hi : ℝ) := by
    norm_num [ceSignedSpT2P0006Lo, ceSignedSpT2P0006Hi, SignedSpT2P0006Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0006Bound x h'
  norm_num [SignedSpT2P0006Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P000L008 : ∀ x ∈ Icc ((((905 : ℚ) / 16384) : ℚ) : ℝ) ((((129 : ℚ) / 2048) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0007Lo : ℝ) (ceSignedSpT2P0007Hi : ℝ) := by
    norm_num [ceSignedSpT2P0007Lo, ceSignedSpT2P0007Hi, SignedSpT2P0007Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0007Bound x h'
  norm_num [SignedSpT2P0007Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P000L009 : ∀ x ∈ Icc ((((129 : ℚ) / 2048) : ℚ) : ℝ) ((((1159 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0008Lo : ℝ) (ceSignedSpT2P0008Hi : ℝ) := by
    norm_num [ceSignedSpT2P0008Lo, ceSignedSpT2P0008Hi, SignedSpT2P0008Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0008Bound x h'
  norm_num [SignedSpT2P0008Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P000L010 : ∀ x ∈ Icc ((((1159 : ℚ) / 16384) : ℚ) : ℝ) ((((643 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0009Lo : ℝ) (ceSignedSpT2P0009Hi : ℝ) := by
    norm_num [ceSignedSpT2P0009Lo, ceSignedSpT2P0009Hi, SignedSpT2P0009Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0009Bound x h'
  norm_num [SignedSpT2P0009Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P000L011 : ∀ x ∈ Icc ((((643 : ℚ) / 8192) : ℚ) : ℝ) ((((1413 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0010Lo : ℝ) (ceSignedSpT2P0010Hi : ℝ) := by
    norm_num [ceSignedSpT2P0010Lo, ceSignedSpT2P0010Hi, SignedSpT2P0010Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0010Bound x h'
  norm_num [SignedSpT2P0010Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P000L012 : ∀ x ∈ Icc ((((1413 : ℚ) / 16384) : ℚ) : ℝ) ((((385 : ℚ) / 4096) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0011Lo : ℝ) (ceSignedSpT2P0011Hi : ℝ) := by
    norm_num [ceSignedSpT2P0011Lo, ceSignedSpT2P0011Hi, SignedSpT2P0011Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0011Bound x h'
  norm_num [SignedSpT2P0011Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P000L013 : ∀ x ∈ Icc ((((385 : ℚ) / 4096) : ℚ) : ℝ) ((((1667 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0012Lo : ℝ) (ceSignedSpT2P0012Hi : ℝ) := by
    norm_num [ceSignedSpT2P0012Lo, ceSignedSpT2P0012Hi, SignedSpT2P0012Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0012Bound x h'
  norm_num [SignedSpT2P0012Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P000L014 : ∀ x ∈ Icc ((((1667 : ℚ) / 16384) : ℚ) : ℝ) ((((897 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0013Lo : ℝ) (ceSignedSpT2P0013Hi : ℝ) := by
    norm_num [ceSignedSpT2P0013Lo, ceSignedSpT2P0013Hi, SignedSpT2P0013Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0013Bound x h'
  norm_num [SignedSpT2P0013Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P000L015 : ∀ x ∈ Icc ((((897 : ℚ) / 8192) : ℚ) : ℝ) ((((3715 : ℚ) / 32768) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0014Lo : ℝ) (ceSignedSpT2P0014Hi : ℝ) := by
    norm_num [ceSignedSpT2P0014Lo, ceSignedSpT2P0014Hi, SignedSpT2P0014Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0014Bound x h'
  norm_num [SignedSpT2P0014Literal.q2] at h ⊢
  exact h

theorem SignedSpT2CoverD0B0P000 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((3715 : ℚ) / 32768) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT2CoverD0B0P000L000 SignedSpT2CoverD0B0P000L001) (cover_union SignedSpT2CoverD0B0P000L002 SignedSpT2CoverD0B0P000L003)) (cover_union (cover_union SignedSpT2CoverD0B0P000L004 SignedSpT2CoverD0B0P000L005) (cover_union SignedSpT2CoverD0B0P000L006 SignedSpT2CoverD0B0P000L007))) (cover_union (cover_union (cover_union SignedSpT2CoverD0B0P000L008 SignedSpT2CoverD0B0P000L009) (cover_union SignedSpT2CoverD0B0P000L010 SignedSpT2CoverD0B0P000L011)) (cover_union (cover_union SignedSpT2CoverD0B0P000L012 SignedSpT2CoverD0B0P000L013) (cover_union SignedSpT2CoverD0B0P000L014 SignedSpT2CoverD0B0P000L015))))
#print axioms SignedSpT2CoverD0B0P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
