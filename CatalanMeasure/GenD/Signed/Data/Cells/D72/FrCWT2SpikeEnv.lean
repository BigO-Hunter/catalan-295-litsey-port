module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock014
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock015
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock023
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock030
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock031
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock039
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2CoverBlock045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2SpikeAdapter

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000


open CatalanMeasure.GenD.Signed.Data.Trial
theorem frRawCover : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union (cover_union FrCWT2CoverBlock000 FrCWT2CoverBlock001) (cover_union FrCWT2CoverBlock002 (cover_union FrCWT2CoverBlock003 FrCWT2CoverBlock004))) (cover_union (cover_union FrCWT2CoverBlock005 (cover_union FrCWT2CoverBlock006 FrCWT2CoverBlock007)) (cover_union FrCWT2CoverBlock008 (cover_union FrCWT2CoverBlock009 FrCWT2CoverBlock010)))) (cover_union (cover_union (cover_union FrCWT2CoverBlock011 (cover_union FrCWT2CoverBlock012 FrCWT2CoverBlock013)) (cover_union FrCWT2CoverBlock014 (cover_union FrCWT2CoverBlock015 FrCWT2CoverBlock016))) (cover_union (cover_union FrCWT2CoverBlock017 (cover_union FrCWT2CoverBlock018 FrCWT2CoverBlock019)) (cover_union FrCWT2CoverBlock020 (cover_union FrCWT2CoverBlock021 FrCWT2CoverBlock022))))) (cover_union (cover_union (cover_union (cover_union FrCWT2CoverBlock023 FrCWT2CoverBlock024) (cover_union FrCWT2CoverBlock025 (cover_union FrCWT2CoverBlock026 FrCWT2CoverBlock027))) (cover_union (cover_union FrCWT2CoverBlock028 (cover_union FrCWT2CoverBlock029 FrCWT2CoverBlock030)) (cover_union FrCWT2CoverBlock031 (cover_union FrCWT2CoverBlock032 FrCWT2CoverBlock033)))) (cover_union (cover_union (cover_union FrCWT2CoverBlock034 (cover_union FrCWT2CoverBlock035 FrCWT2CoverBlock036)) (cover_union FrCWT2CoverBlock037 (cover_union FrCWT2CoverBlock038 FrCWT2CoverBlock039))) (cover_union (cover_union FrCWT2CoverBlock040 (cover_union FrCWT2CoverBlock041 FrCWT2CoverBlock042)) (cover_union FrCWT2CoverBlock043 (cover_union FrCWT2CoverBlock044 FrCWT2CoverBlock045))))))

theorem frCover :
    ∀ x ∈ Icc (-1 : ℝ) 1, frLim CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.form x ≤ ((((16790563 : ℚ) / 2147483648) : ℚ) : ℝ) :=
  frCoverOf frRawCover

theorem spikeEnv : ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (CatalanMeasure.GenD.Signed.Data.Trial72.T2.D N)) :=
  spikeEnvOf frRawCover
#print axioms frRawCover
#print axioms frCover
#print axioms spikeEnv

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
