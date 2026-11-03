module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormV2Data
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormV2Cross00
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormV2Cross01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormV2Cross02
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormV2Cross03
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormV2Cross04
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondV

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormV2
open CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan
open CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.TaylorCell (vecAdd)
open CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section

open RationalNormV2Data
open RawNormBounds
theorem shards : ∀ j < caps.length, qCross f ((tails.drop (4 * j)).take 4) ≤ caps.getD j 0 := by
  intro j hj
  change j < 19 at hj
  interval_cases j
  · exact RationalNormV2Cross00.cross0
  · exact RationalNormV2Cross00.cross1
  · exact RationalNormV2Cross00.cross2
  · exact RationalNormV2Cross00.cross3
  · exact RationalNormV2Cross01.cross4
  · exact RationalNormV2Cross01.cross5
  · exact RationalNormV2Cross01.cross6
  · exact RationalNormV2Cross01.cross7
  · exact RationalNormV2Cross02.cross8
  · exact RationalNormV2Cross02.cross9
  · exact RationalNormV2Cross02.cross10
  · exact RationalNormV2Cross02.cross11
  · exact RationalNormV2Cross03.cross12
  · exact RationalNormV2Cross03.cross13
  · exact RationalNormV2Cross03.cross14
  · exact RationalNormV2Cross03.cross15
  · exact RationalNormV2Cross04.cross16
  · exact RationalNormV2Cross04.cross17
  · exact RationalNormV2Cross04.cross18

theorem cross_bound : qCross f tails ≤ caps.sum := by
  exact sum_le_of_chunks (crossH f) 4 caps tails (by decide +kernel) shards

theorem sq_bound : qSq f 0 ≤ squareUb := by decide +kernel

theorem dot_bound : qDot NormData.secondVInt f 0 ≤ dotUb := by decide +kernel
theorem total : secondVNormUB + 2 * (caps.sum + dotUb) + squareUb ≤ normUb := by decide +kernel

theorem finite_eq : T2.trial.v.f = vecAdd ReferenceData.secondVData.f f := rfl
theorem tail_eq : T2.trial.v.tail = tails := rfl

theorem norm_bound : barrierTrialNormSq (tseq (fQ T2.trial.v.f) (T2.trial.v.tail.map TailQ.toC)) ≤ (normUb : ℝ) := by
  rw [finite_eq, tail_eq, ← NormData.secondVInt_eq]
  exact norm_perturb_le_of_bounds RawNormSecondV.raw_norm RawNormSecondV.disk cross_bound dot_bound sq_bound total

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormV2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormV2.norm_bound
