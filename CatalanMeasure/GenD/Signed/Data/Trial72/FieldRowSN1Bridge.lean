module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Zero
public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN1Bridge
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
open AssemblyBindings
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0

abbrev T : ℚ := ((-8736680003909 : ℚ) / 1099511627776)
private abbrev K : ℚ := ((3409774073479 : ℚ) / 549755813888)
abbrev S : ℚ := ((-1917131856951 : ℚ) / 1099511627776)

private theorem offset : snK T1.trial ≤ (K : ℝ) := by
  have ev : encS T1.trial.v.tail = some (219958300254890109, 319) := KappaBasics.sV_checked
  have ep : encT T1.trial.p.tail = some (-374182068496652202, 281) := KappaBasics.tP_checked
  have ea : encS T1.trial.a.tail = some (3321757840045031, 40) := KappaBasics.sA1_checked
  have hv := encl_sConst T1.trial.v.tail
  have hp := encl_tConst T1.trial.p.tail
  have ha := encl_sConst T1.trial.a.tail
  rw [ev] at hv
  rw [ep] at hp
  rw [ea] at ha
  change Encl (cSv T1.trial) (ivOf (some (219958300254890109,319))) at hv
  change Encl (cTp T1.trial) (ivOf (some (-374182068496652202,281))) at hp
  change Encl (cSa T1.trial) (ivOf (some (3321757840045031,40))) at ha
  -- kcost: 0.01 s estimated for a scalar comparison. Reuse the three checked pole sums.
  exact sn_le (η := T1.trial.η) (B := K) hv hp ha (by decide +kernel)

private theorem selfDistance (p : List ℚ) : l1Q p p ≤ 0 := by
  induction p with
  | nil => simp [l1Q]
  | cons a p ih => simpa [l1Q, qAbs] using ih

theorem eventualOf (named : ∀ y ∈ Ioo (-1 : ℝ) 0,
    fieldTower T1.snFq (poleF T1.snFq.poles) 0 y ≤ (T : ℝ)) : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y ∈ Ioo (-1 : ℝ) 0, (T1.D N).fNeg y ≤ (S : ℝ) + ε := by
  have hs : ceSignedSnEntryT1E02Site = 0 := by decide +kernel
  have hh : ceSignedSnEntryT1E02Hi = 0 := by decide +kernel
  have hlo0 : -1 < ceSignedSnEntryT1E02Lo := by decide +kernel
  have hlo1 : ceSignedSnEntryT1E02Lo < 0 := by decide +kernel
  have hc : 0 < endC ceSignedSnEntryT1E02FullFq ceSignedSnEntryT1E02FullTs ceSignedSnEntryT1E02Site := by decide +kernel
  have hT : ceSignedSnEntryT1E02Target ≤ T := by decide +kernel
  have hcmp := endUOK_cmp ceSignedSnEntryT1E02Singular
  rw [hs, hh, endR_zero hlo1.le] at hcmp
  have key := boundSN1 T1.snFq rfl rfl (δ := 0) (selfDistance _)
    (T := (T : ℝ)) (TR := ((ceSignedSnEntryT1E02TR + ceSignedSnEntryT1E02U : ℚ) : ℝ))
    (lo := (ceSignedSnEntryT1E02Lo : ℝ)) (c := (endC ceSignedSnEntryT1E02FullFq ceSignedSnEntryT1E02FullTs ceSignedSnEntryT1E02Site : ℝ))
    named (by exact_mod_cast hlo0) (by exact_mod_cast hlo1)
    CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Zero.zeroLog (by exact_mod_cast hc) ?_
  · intro ε hε
    filter_upwards [key ε hε] with N hN y hy
    have h := hN y hy
    have hS : ((T + K : ℚ) : ℝ) ≤ (S : ℝ) :=
      (Rat.cast_le (K := ℝ)).mpr (show T + K ≤ S from by decide +kernel)
    simp only [Rat.cast_add, Rat.cast_zero, add_zero] at hS h
    linarith [offset]
  · have hT' := (Rat.cast_le (K := ℝ)).mpr hT
    simpa only [Rat.cast_add, Rat.cast_neg, hs] using hcmp.trans hT'
#print axioms eventualOf
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN1Bridge
