module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock014
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock015
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock023
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock030
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock031
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock039
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock046
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1CoverBlock047
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1SpikeAdapter

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000


open CatalanMeasure.GenD.Signed.Data.Trial
theorem frRawCover : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union (cover_union FrCWT1CoverBlock000 (cover_union FrCWT1CoverBlock001 FrCWT1CoverBlock002)) (cover_union FrCWT1CoverBlock003 (cover_union FrCWT1CoverBlock004 FrCWT1CoverBlock005))) (cover_union (cover_union FrCWT1CoverBlock006 (cover_union FrCWT1CoverBlock007 FrCWT1CoverBlock008)) (cover_union FrCWT1CoverBlock009 (cover_union FrCWT1CoverBlock010 FrCWT1CoverBlock011)))) (cover_union (cover_union (cover_union FrCWT1CoverBlock012 (cover_union FrCWT1CoverBlock013 FrCWT1CoverBlock014)) (cover_union FrCWT1CoverBlock015 (cover_union FrCWT1CoverBlock016 FrCWT1CoverBlock017))) (cover_union (cover_union FrCWT1CoverBlock018 (cover_union FrCWT1CoverBlock019 FrCWT1CoverBlock020)) (cover_union FrCWT1CoverBlock021 (cover_union FrCWT1CoverBlock022 FrCWT1CoverBlock023))))) (cover_union (cover_union (cover_union (cover_union FrCWT1CoverBlock024 (cover_union FrCWT1CoverBlock025 FrCWT1CoverBlock026)) (cover_union FrCWT1CoverBlock027 (cover_union FrCWT1CoverBlock028 FrCWT1CoverBlock029))) (cover_union (cover_union FrCWT1CoverBlock030 (cover_union FrCWT1CoverBlock031 FrCWT1CoverBlock032)) (cover_union FrCWT1CoverBlock033 (cover_union FrCWT1CoverBlock034 FrCWT1CoverBlock035)))) (cover_union (cover_union (cover_union FrCWT1CoverBlock036 (cover_union FrCWT1CoverBlock037 FrCWT1CoverBlock038)) (cover_union FrCWT1CoverBlock039 (cover_union FrCWT1CoverBlock040 FrCWT1CoverBlock041))) (cover_union (cover_union FrCWT1CoverBlock042 (cover_union FrCWT1CoverBlock043 FrCWT1CoverBlock044)) (cover_union FrCWT1CoverBlock045 (cover_union FrCWT1CoverBlock046 FrCWT1CoverBlock047))))))

theorem frCover :
    ∀ x ∈ Icc (-1 : ℝ) 1, frLim CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.form x ≤ ((((30445483 : ℚ) / 4294967296) : ℚ) : ℝ) :=
  frCoverOf frRawCover

theorem spikeEnv : ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (CatalanMeasure.GenD.Signed.Data.Trial72.T1.D N)) :=
  spikeEnvOf frRawCover
#print axioms frRawCover
#print axioms frCover
#print axioms spikeEnv

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
