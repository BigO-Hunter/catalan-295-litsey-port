module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0007

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0000 : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-4398046511103 : ℚ) / 4398046511104) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0000Lo = ((-1 : ℚ) / 1) := by decide +kernel
  have hhi : ceFrCWT0P0000Hi = ((-4398046511103 : ℚ) / 4398046511104) := by decide +kernel
  have hcap : FrCWT0P0000Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0000Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0001 : ∀ x ∈ Icc ((((-4398046511103 : ℚ) / 4398046511104) : ℚ) : ℝ) ((((-2199023255551 : ℚ) / 2199023255552) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0001Lo = ((-4398046511103 : ℚ) / 4398046511104) := by decide +kernel
  have hhi : ceFrCWT0P0001Hi = ((-2199023255551 : ℚ) / 2199023255552) := by decide +kernel
  have hcap : FrCWT0P0001Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0001Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0002 : ∀ x ∈ Icc ((((-2199023255551 : ℚ) / 2199023255552) : ℚ) : ℝ) ((((-4398046511101 : ℚ) / 4398046511104) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0002Lo = ((-2199023255551 : ℚ) / 2199023255552) := by decide +kernel
  have hhi : ceFrCWT0P0002Hi = ((-4398046511101 : ℚ) / 4398046511104) := by decide +kernel
  have hcap : FrCWT0P0002Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0002Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0003 : ∀ x ∈ Icc ((((-4398046511101 : ℚ) / 4398046511104) : ℚ) : ℝ) ((((-8796093022201 : ℚ) / 8796093022208) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0003Lo = ((-4398046511101 : ℚ) / 4398046511104) := by decide +kernel
  have hhi : ceFrCWT0P0003Hi = ((-8796093022201 : ℚ) / 8796093022208) := by decide +kernel
  have hcap : FrCWT0P0003Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0003Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0004 : ∀ x ∈ Icc ((((-8796093022201 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0004Lo = ((-8796093022201 : ℚ) / 8796093022208) := by decide +kernel
  have hhi : ceFrCWT0P0004Hi = ((-1099511627775 : ℚ) / 1099511627776) := by decide +kernel
  have hcap : FrCWT0P0004Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0004Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0005 : ∀ x ∈ Icc ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((-8796093022199 : ℚ) / 8796093022208) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0005Lo = ((-1099511627775 : ℚ) / 1099511627776) := by decide +kernel
  have hhi : ceFrCWT0P0005Hi = ((-8796093022199 : ℚ) / 8796093022208) := by decide +kernel
  have hcap : FrCWT0P0005Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0005Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0006 : ∀ x ∈ Icc ((((-8796093022199 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((-4398046511099 : ℚ) / 4398046511104) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0006Lo = ((-8796093022199 : ℚ) / 8796093022208) := by decide +kernel
  have hhi : ceFrCWT0P0006Hi = ((-4398046511099 : ℚ) / 4398046511104) := by decide +kernel
  have hcap : FrCWT0P0006Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0006Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0007 : ∀ x ∈ Icc ((((-4398046511099 : ℚ) / 4398046511104) : ℚ) : ℝ) ((((-2199023255549 : ℚ) / 2199023255552) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0007Lo = ((-4398046511099 : ℚ) / 4398046511104) := by decide +kernel
  have hhi : ceFrCWT0P0007Hi = ((-2199023255549 : ℚ) / 2199023255552) := by decide +kernel
  have hcap : FrCWT0P0007Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0007Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock000 : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-2199023255549 : ℚ) / 2199023255552) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0000 liftFrCWT0P0001) (cover_union liftFrCWT0P0002 liftFrCWT0P0003)) (cover_union (cover_union liftFrCWT0P0004 liftFrCWT0P0005) (cover_union liftFrCWT0P0006 liftFrCWT0P0007)))
#print axioms FrCWT0CoverBlock000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
