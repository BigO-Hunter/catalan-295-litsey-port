module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0Data
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0Cross00
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0Cross01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0
public import CatalanMeasure.GenD.Signed.Data.Trial72.T0Binding

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0
open CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan
open CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.TaylorCell (vecAdd)
open CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section

open RationalNormA0Data
open RawNormBounds
theorem shards : ∀ j < caps.length, qCross f ((tails.drop (4 * j)).take 4) ≤ caps.getD j 0 := by
  intro j hj
  change j < 5 at hj
  interval_cases j
  · exact RationalNormA0Cross00.cross0
  · exact RationalNormA0Cross00.cross1
  · exact RationalNormA0Cross00.cross2
  · exact RationalNormA0Cross00.cross3
  · exact RationalNormA0Cross01.cross4

theorem cross_bound : qCross f tails ≤ caps.sum := by
  exact sum_le_of_chunks (crossH f) 4 caps tails (by decide +kernel) shards

theorem sq_bound : qSq f 0 ≤ squareUb := by decide +kernel

theorem disk : tailsInDisk tails = true := by
  have hh := (T0.dataOK (C := (T0.Cb : ℝ)) le_rfl).haT
  unfold tailsInDisk
  apply List.all_eq_true.mpr
  intro z hz
  have hz1 := List.all_eq_true.mp hh z hz
  simp only [Bool.and_eq_true] at hz1
  exact hz1.1.1

theorem total : A0LogUBs.sum + 2 * caps.sum + squareUb ≤ normUb := by decide +kernel

theorem norm_bound : barrierTrialNormSq (tseq (fQ T0.trial.a.f) (T0.trial.a.tail.map TailQ.toC)) ≤ (normUb : ℝ) :=
  norm_tail_of_bounds disk RawNormA0.log_bound cross_bound sq_bound total

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0.norm_bound
