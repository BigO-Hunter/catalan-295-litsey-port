module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock014
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock015
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock023
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock030
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock031
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock039
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock046
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0CoverBlock047
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0SpikeAdapter

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000


open CatalanMeasure.GenD.Signed.Data.Trial
theorem frRawCover : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union (cover_union FrCWT0CoverBlock000 (cover_union FrCWT0CoverBlock001 FrCWT0CoverBlock002)) (cover_union FrCWT0CoverBlock003 (cover_union FrCWT0CoverBlock004 FrCWT0CoverBlock005))) (cover_union (cover_union FrCWT0CoverBlock006 (cover_union FrCWT0CoverBlock007 FrCWT0CoverBlock008)) (cover_union FrCWT0CoverBlock009 (cover_union FrCWT0CoverBlock010 FrCWT0CoverBlock011)))) (cover_union (cover_union (cover_union FrCWT0CoverBlock012 (cover_union FrCWT0CoverBlock013 FrCWT0CoverBlock014)) (cover_union FrCWT0CoverBlock015 (cover_union FrCWT0CoverBlock016 FrCWT0CoverBlock017))) (cover_union (cover_union FrCWT0CoverBlock018 (cover_union FrCWT0CoverBlock019 FrCWT0CoverBlock020)) (cover_union FrCWT0CoverBlock021 (cover_union FrCWT0CoverBlock022 FrCWT0CoverBlock023))))) (cover_union (cover_union (cover_union (cover_union FrCWT0CoverBlock024 (cover_union FrCWT0CoverBlock025 FrCWT0CoverBlock026)) (cover_union FrCWT0CoverBlock027 (cover_union FrCWT0CoverBlock028 FrCWT0CoverBlock029))) (cover_union (cover_union FrCWT0CoverBlock030 (cover_union FrCWT0CoverBlock031 FrCWT0CoverBlock032)) (cover_union FrCWT0CoverBlock033 (cover_union FrCWT0CoverBlock034 FrCWT0CoverBlock035)))) (cover_union (cover_union (cover_union FrCWT0CoverBlock036 (cover_union FrCWT0CoverBlock037 FrCWT0CoverBlock038)) (cover_union FrCWT0CoverBlock039 (cover_union FrCWT0CoverBlock040 FrCWT0CoverBlock041))) (cover_union (cover_union FrCWT0CoverBlock042 (cover_union FrCWT0CoverBlock043 FrCWT0CoverBlock044)) (cover_union FrCWT0CoverBlock045 (cover_union FrCWT0CoverBlock046 FrCWT0CoverBlock047))))))

theorem frCover :
    ∀ x ∈ Icc (-1 : ℝ) 1, frLim CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.form x ≤ ((((7554721 : ℚ) / 1073741824) : ℚ) : ℝ) :=
  frCoverOf frRawCover

theorem spikeEnv : ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (CatalanMeasure.GenD.Signed.Data.Trial72.T0.D N)) :=
  spikeEnvOf frRawCover
#print axioms frRawCover
#print axioms frCover
#print axioms spikeEnv

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
