module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0015
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0017
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT2CoverD0B0P001L016 : ∀ x ∈ Icc ((((3715 : ℚ) / 32768) : ℚ) : ℝ) ((((1921 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0015Lo : ℝ) (ceSignedSpT2P0015Hi : ℝ) := by
    norm_num [ceSignedSpT2P0015Lo, ceSignedSpT2P0015Hi, SignedSpT2P0015Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0015Bound x h'
  norm_num [SignedSpT2P0015Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P001L017 : ∀ x ∈ Icc ((((1921 : ℚ) / 16384) : ℚ) : ℝ) ((((3969 : ℚ) / 32768) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0016Lo : ℝ) (ceSignedSpT2P0016Hi : ℝ) := by
    norm_num [ceSignedSpT2P0016Lo, ceSignedSpT2P0016Hi, SignedSpT2P0016Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0016Bound x h'
  norm_num [SignedSpT2P0016Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B0P001L018 : ∀ x ∈ Icc ((((3969 : ℚ) / 32768) : ℚ) : ℝ) ((((1 : ℚ) / 8) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0017Lo : ℝ) (ceSignedSpT2P0017Hi : ℝ) := by
    norm_num [ceSignedSpT2P0017Lo, ceSignedSpT2P0017Hi, SignedSpT2P0017Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0017Bound x h'
  norm_num [SignedSpT2P0017Literal.q2] at h ⊢
  exact h

theorem SignedSpT2CoverD0B0P001 : ∀ x ∈ Icc ((((3715 : ℚ) / 32768) : ℚ) : ℝ) ((((1 : ℚ) / 8) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) :=
  (cover_union SignedSpT2CoverD0B0P001L016 (cover_union SignedSpT2CoverD0B0P001L017 SignedSpT2CoverD0B0P001L018))
#print axioms SignedSpT2CoverD0B0P001

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
