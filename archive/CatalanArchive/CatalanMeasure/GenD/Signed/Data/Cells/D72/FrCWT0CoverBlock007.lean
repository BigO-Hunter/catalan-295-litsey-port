module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0056
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0057
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0058
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0059
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0060
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0061
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0062
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0063

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0056 : ∀ x ∈ Icc ((((-1011 : ℚ) / 1024) : ℚ) : ℝ) ((((-505 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0056Lo = ((-1011 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0056Hi = ((-505 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0056Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0056Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0057 : ∀ x ∈ Icc ((((-505 : ℚ) / 512) : ℚ) : ℝ) ((((-1009 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0057Lo = ((-505 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0057Hi = ((-1009 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0057Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0057Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0058 : ∀ x ∈ Icc ((((-1009 : ℚ) / 1024) : ℚ) : ℝ) ((((-63 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0058Lo = ((-1009 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0058Hi = ((-63 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0058Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0058Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0059 : ∀ x ∈ Icc ((((-63 : ℚ) / 64) : ℚ) : ℝ) ((((-2015 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0059Lo = ((-63 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0059Hi = ((-2015 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT0P0059Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0059Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0060 : ∀ x ∈ Icc ((((-2015 : ℚ) / 2048) : ℚ) : ℝ) ((((-503 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0060Lo = ((-2015 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT0P0060Hi = ((-503 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0060Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0060Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0061 : ∀ x ∈ Icc ((((-503 : ℚ) / 512) : ℚ) : ℝ) ((((-1005 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0061Lo = ((-503 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0061Hi = ((-1005 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0061Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0061Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0062 : ∀ x ∈ Icc ((((-1005 : ℚ) / 1024) : ℚ) : ℝ) ((((-2009 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0062Lo = ((-1005 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0062Hi = ((-2009 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT0P0062Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0062Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0063 : ∀ x ∈ Icc ((((-2009 : ℚ) / 2048) : ℚ) : ℝ) ((((-501 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0063Lo = ((-2009 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT0P0063Hi = ((-501 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0063Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0063Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock007 : ∀ x ∈ Icc ((((-1011 : ℚ) / 1024) : ℚ) : ℝ) ((((-501 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0056 liftFrCWT0P0057) (cover_union liftFrCWT0P0058 liftFrCWT0P0059)) (cover_union (cover_union liftFrCWT0P0060 liftFrCWT0P0061) (cover_union liftFrCWT0P0062 liftFrCWT0P0063)))
#print axioms FrCWT0CoverBlock007

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
