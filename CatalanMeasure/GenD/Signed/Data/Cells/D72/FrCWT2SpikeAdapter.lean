module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Literal
public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalKappaT

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000


open CatalanMeasure.GenD.Signed.Data.Trial
theorem frFieldCheck : fieldNFCheck ceFrCWT2Raw CatalanMeasure.GenD.Signed.Data.Trial72.T2.frFq = true := by decide +kernel

theorem frOffset : frK CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial ≤ ((((83314720257 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  CatalanMeasure.GenD.Signed.Data.Consts.EvalKappaT.frK_le (T := CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial) (B := ((83314720257 : ℚ) / 1099511627776)) (by decide +kernel)

theorem frGap : ((((16790563 : ℚ) / 2147483648) : ℚ) : ℝ) < (CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.Sup : ℝ) :=
  (Rat.cast_lt (K := ℝ)).mpr (show ((16790563 : ℚ) / 2147483648) < CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.Sup from by decide +kernel)

theorem frCoverOf (h : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ)) :
    ∀ x ∈ Icc (-1 : ℝ) 1, frLim CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.form x ≤ ((((16790563 : ℚ) / 2147483648) : ℚ) : ℝ) := by
  intro x hx
  have hx' : x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ) := by simpa using hx
  have h' := h x hx'
  rw [fieldNFCheck_sound frFieldCheck x] at h'
  rw [CatalanMeasure.GenD.Signed.Data.Trial72.T2.hidFR x]
  have hsum := add_le_add h' frOffset
  have hcap : ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((83314720257 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((16790563 : ℚ) / 2147483648) : ℚ) : ℝ) := by norm_num
  rw [hcap] at hsum
  exact hsum

theorem spikeEnvOf (h : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ)) :
    ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (CatalanMeasure.GenD.Signed.Data.Trial72.T2.D N)) :=
  CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings.spikeEnv2 (frCoverOf h) frGap
#print axioms frOffset
#print axioms frGap
#print axioms frCoverOf
#print axioms spikeEnvOf

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
