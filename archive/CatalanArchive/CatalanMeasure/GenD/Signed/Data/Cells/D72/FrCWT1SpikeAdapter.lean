module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Literal
public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalKappaT

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000


open CatalanMeasure.GenD.Signed.Data.Trial
theorem frFieldCheck : fieldNFCheck ceFrCWT1Raw CatalanMeasure.GenD.Signed.Data.Trial72.T1.frFq = true := by decide +kernel

theorem frOffset : frK CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial ≤ ((((96853441725 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  CatalanMeasure.GenD.Signed.Data.Consts.EvalKappaT.frK_le (T := CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial) (B := ((96853441725 : ℚ) / 1099511627776)) (by decide +kernel)

theorem frGap : ((((30445483 : ℚ) / 4294967296) : ℚ) : ℝ) < (CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.Sup : ℝ) :=
  (Rat.cast_lt (K := ℝ)).mpr (show ((30445483 : ℚ) / 4294967296) < CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.Sup from by decide +kernel)

theorem frCoverOf (h : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ)) :
    ∀ x ∈ Icc (-1 : ℝ) 1, frLim CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.form x ≤ ((((30445483 : ℚ) / 4294967296) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ) := by simpa using hx
  have h' := h x hx'
  rw [fieldNFCheck_sound frFieldCheck x] at h'
  rw [CatalanMeasure.GenD.Signed.Data.Trial72.T1.hidFR x]
  have hsum := add_le_add h' frOffset
  have hcap : ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((96853441725 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((30445483 : ℚ) / 4294967296) : ℚ) : ℝ) := by norm_num
  rw [hcap] at hsum
  exact hsum

theorem spikeEnvOf (h : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ)) :
    ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (CatalanMeasure.GenD.Signed.Data.Trial72.T1.D N)) :=
  CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings.spikeEnv1 (frCoverOf h) frGap
#print axioms frOffset
#print axioms frGap
#print axioms frCoverOf
#print axioms spikeEnvOf

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
