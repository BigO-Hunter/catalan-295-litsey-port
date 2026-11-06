module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Zero
public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN0Bridge
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
open AssemblyBindings
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0

abbrev T : ℚ := ((-8755850689279 : ℚ) / 1099511627776)
private abbrev K : ℚ := ((1709008384221 : ℚ) / 274877906944)
abbrev S : ℚ := ((-1919817152395 : ℚ) / 1099511627776)

private theorem offset : snK T0.trial ≤ (K : ℝ) := by
  have ev : encS T0.trial.v.tail = some (219958300254890109, 319) := KappaBasics.sV_checked
  have ep : encT T0.trial.p.tail = some (-374182068496652202, 281) := KappaBasics.tP_checked
  have ea : encS T0.trial.a.tail = some (2781564582940640, 40) := KappaBasics.sA0_checked
  have hv := encl_sConst T0.trial.v.tail
  have hp := encl_tConst T0.trial.p.tail
  have ha := encl_sConst T0.trial.a.tail
  rw [ev] at hv
  rw [ep] at hp
  rw [ea] at ha
  change Encl (cSv T0.trial) (ivOf (some (219958300254890109,319))) at hv
  change Encl (cTp T0.trial) (ivOf (some (-374182068496652202,281))) at hp
  change Encl (cSa T0.trial) (ivOf (some (2781564582940640,40))) at ha
  -- kcost: 0.01 s estimated for a scalar comparison. Reuse the three checked pole sums.
  exact sn_le (η := T0.trial.η) (B := K) hv hp ha (by decide +kernel)

private theorem selfDistance (p : List ℚ) : l1Q p p ≤ 0 := by
  induction p with
  | nil => simp [l1Q]
  | cons a p ih => simpa [l1Q, qAbs] using ih

theorem eventualOf (named : ∀ y ∈ Ioo (-1 : ℝ) 0,
    fieldTower T0.snFq (poleF T0.snFq.poles) 0 y ≤ (T : ℝ)) : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y ∈ Ioo (-1 : ℝ) 0, (T0.D N).fNeg y ≤ (S : ℝ) + ε := by
  have hs : ceSignedSnEntryT0E01Site = 0 := by decide +kernel
  have hh : ceSignedSnEntryT0E01Hi = 0 := by decide +kernel
  have hlo0 : -1 < ceSignedSnEntryT0E01Lo := by decide +kernel
  have hlo1 : ceSignedSnEntryT0E01Lo < 0 := by decide +kernel
  have hc : 0 < endC ceSignedSnEntryT0E01FullFq ceSignedSnEntryT0E01FullTs ceSignedSnEntryT0E01Site := by decide +kernel
  have hT : ceSignedSnEntryT0E01Target ≤ T := by decide +kernel
  have hcmp := endUOK_cmp ceSignedSnEntryT0E01Singular
  rw [hs, hh, endR_zero hlo1.le] at hcmp
  have key := boundSN0 T0.snFq rfl rfl (δ := 0) (selfDistance _)
    (T := (T : ℝ)) (TR := ((ceSignedSnEntryT0E01TR + ceSignedSnEntryT0E01U : ℚ) : ℝ))
    (lo := (ceSignedSnEntryT0E01Lo : ℝ)) (c := (endC ceSignedSnEntryT0E01FullFq ceSignedSnEntryT0E01FullTs ceSignedSnEntryT0E01Site : ℝ))
    named (by exact_mod_cast hlo0) (by exact_mod_cast hlo1)
    CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Zero.zeroLog (by exact_mod_cast hc) ?_
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
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN0Bridge
