module

public import CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstP
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstV
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondP
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondV

@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormPhysical
open CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan
open CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
open CatalanMeasure.GenD.Signed.TaylorCell (vecAdd)
open CatalanMeasure.GenD.Signed.Data.Trial72 RawNormBounds
noncomputable section

/-! Bind the source-only raw norm bank to the physical reference sequences.
In particular, firstP is twice the raw sequence and its squared norm pays a factor four. -/
theorem raw_eq {cs : List ℤ} {d : SeqQ}
    (h : cs.map (fun n : ℤ => (n : ℚ) / 2^40) = d.f) :
    trialSeqS cs d.tail = tseq (fQ d.f) (d.tail.map TailQ.toC) := by
  change trialSeqS cs d.tail = tseqE (fQE d.f) (d.tail.map TailQ.toC)
  have hv (l : List ℚ) : vecAdd l [] = l := by cases l <;> rfl
  have he := perturb_seq cs [] d.tail
  rw [hv, h] at he
  simpa [fQE] using he.symm

theorem firstP_eq : ReferenceData.firstP = fun j => 2 * trialSeqS NormData.firstPInt firstPTail j := by
  unfold ReferenceData.firstP
  rw [raw_eq (cs := NormData.firstPInt) (d := ReferenceData.firstPData)
    NormData.firstPInt_eq]

theorem firstV_eq : ReferenceData.firstV = trialSeqS NormData.firstVInt firstVTail :=
  (raw_eq (cs := NormData.firstVInt) (d := ReferenceData.firstVData)
    NormData.firstVInt_eq).symm

theorem secondP_eq : ReferenceData.secondP = trialSeqS NormData.secondPInt secondPTail :=
  (raw_eq (cs := NormData.secondPInt) (d := ReferenceData.secondPData)
    NormData.secondPInt_eq).symm

theorem secondV_eq : ReferenceData.secondV = trialSeqS NormData.secondVInt secondVTail :=
  (raw_eq (cs := NormData.secondVInt) (d := ReferenceData.secondVData)
    NormData.secondVInt_eq).symm

theorem first_scalar : 4 * firstPNormUB + firstVNormUB / 2 ≤ (53/100 : ℚ) := by decide +kernel

theorem second_scalar : 2 * secondPNormUB + secondVNormUB / 2 ≤ (3880566911/5000000000 : ℚ) := by
  decide +kernel

theorem first_weighted :
    barrierTrialNormSq ReferenceData.firstP + barrierTrialNormSq ReferenceData.firstV / 2 ≤ (53/100 : ℝ) := by
  have hscale (c : ℝ) (u : ℕ → ℝ) :
      barrierTrialNormSq (fun j => c * u j) = c ^ 2 * barrierTrialNormSq u := by
    unfold barrierTrialNormSq
    rw [← tsum_mul_left]
    congr 1
    funext j
    ring
  rw [firstP_eq, firstV_eq, hscale]
  have hb := (Rat.cast_le (K := ℝ)).mpr first_scalar
  push_cast at hb
  nlinarith only [RawNormFirstP.raw_norm, RawNormFirstV.raw_norm, hb]

theorem second_weighted :
    2 * barrierTrialNormSq ReferenceData.secondP + barrierTrialNormSq ReferenceData.secondV / 2 ≤
      (3880566911/5000000000 : ℝ) := by
  rw [secondP_eq, secondV_eq]
  have hb := (Rat.cast_le (K := ℝ)).mpr second_scalar
  push_cast at hb
  linarith only [RawNormSecondP.raw_norm, RawNormSecondV.raw_norm, hb]

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormPhysical
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormPhysical.first_weighted
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormPhysical.second_weighted
