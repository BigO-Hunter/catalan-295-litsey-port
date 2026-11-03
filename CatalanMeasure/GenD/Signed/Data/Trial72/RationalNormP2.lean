module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP2Data
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP2Cross00
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP2Cross01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP2Cross02
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP2Cross03
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP2Cross04
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondP

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP2
open CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan
open CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.TaylorCell (vecAdd)
open CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section

open RationalNormP2Data
open RawNormBounds
theorem shards : ∀ j < caps.length, qCross f ((tails.drop (4 * j)).take 4) ≤ caps.getD j 0 := by
  intro j hj
  change j < 19 at hj
  interval_cases j
  · exact RationalNormP2Cross00.cross0
  · exact RationalNormP2Cross00.cross1
  · exact RationalNormP2Cross00.cross2
  · exact RationalNormP2Cross00.cross3
  · exact RationalNormP2Cross01.cross4
  · exact RationalNormP2Cross01.cross5
  · exact RationalNormP2Cross01.cross6
  · exact RationalNormP2Cross01.cross7
  · exact RationalNormP2Cross02.cross8
  · exact RationalNormP2Cross02.cross9
  · exact RationalNormP2Cross02.cross10
  · exact RationalNormP2Cross02.cross11
  · exact RationalNormP2Cross03.cross12
  · exact RationalNormP2Cross03.cross13
  · exact RationalNormP2Cross03.cross14
  · exact RationalNormP2Cross03.cross15
  · exact RationalNormP2Cross04.cross16
  · exact RationalNormP2Cross04.cross17
  · exact RationalNormP2Cross04.cross18

theorem cross_bound : qCross f tails ≤ caps.sum := by
  exact sum_le_of_chunks (crossH f) 4 caps tails (by decide +kernel) shards

theorem sq_bound : qSq f 0 ≤ squareUb := by decide +kernel

theorem dot_bound : qDot NormData.secondPInt f 0 ≤ dotUb := by decide +kernel
theorem total : secondPNormUB + 2 * (caps.sum + dotUb) + squareUb ≤ normUb := by decide +kernel

theorem finite_eq : T2.trial.p.f = vecAdd ReferenceData.secondPData.f f := rfl
theorem tail_eq : T2.trial.p.tail = tails := rfl

theorem norm_bound : barrierTrialNormSq (tseq (fQ T2.trial.p.f) (T2.trial.p.tail.map TailQ.toC)) ≤ (normUb : ℝ) := by
  rw [finite_eq, tail_eq, ← NormData.secondPInt_eq]
  exact norm_perturb_le_of_bounds RawNormSecondP.raw_norm RawNormSecondP.disk cross_bound dot_bound sq_bound total

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP2.norm_bound
