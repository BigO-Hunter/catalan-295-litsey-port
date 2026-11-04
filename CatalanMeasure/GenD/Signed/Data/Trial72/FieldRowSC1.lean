module

public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScRowEnd1
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT1Assembly

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSC1
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.Data.Cells
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly
open CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa

set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private abbrev T : ℚ := -1263460671503/68719476736
private abbrev K : ℚ := 4622991321585 / 274877906944
abbrev S : ℚ := -430851364427/274877906944

private theorem offset : scK T1.trial ≤ (K : ℝ) := by
  have hEnc : encT T1.trial.v.tail = some (605944718502765539, 290) :=
    KappaBasics.tV_checked
  have h := encl_tConst T1.trial.v.tail
  rw [hEnc] at h
  change Encl (cTv T1.trial) (ivOf (some (605944718502765539, 290))) at h
  -- kcost: 0.01 s estimated for one interval comparison. The checked 75-pole sum is reused.
  exact sc_le (B := K) h (by decide +kernel)

private theorem selfDistance (p : List ℚ) : l1Q p p ≤ 0 := by
  induction p with
  | nil => simp [l1Q]
  | cons a p ih => simpa [l1Q, qAbs] using ih

theorem eventual :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1,
      (T1.D N).fCol x ≤ (S : ℝ) + ε := by
  have hsite : ceSignedScRowEnd1Site = 1 := by decide +kernel
  have hhi : ceSignedScRowEnd1Hi = 1 := by decide +kernel
  have hlo0 : 0 < ceSignedScRowEnd1Lo := by decide +kernel
  have hlo1 : ceSignedScRowEnd1Lo < 1 := by decide +kernel
  have hpos : 0 < endC ceSignedScRowEnd1FullFq ceSignedScRowEnd1FullTs ceSignedScRowEnd1Site := by decide +kernel
  have hcap : ceSignedScRowEnd1Target ≤ T := by decide +kernel
  have hcmp := endUOK_cmp ceSignedScRowEnd1Singular
  rw [hsite, hhi, endR_one hlo1.le] at hcmp
  have hend := endOK_sound ceSignedScRowEnd1FullFq ceSignedScRowEnd1FullTs ceSignedScRowEnd1Site
    ceSignedScRowEnd1Lo ceSignedScRowEnd1Hi 40 ceSignedScRowEnd1U ceSignedScRowEnd1TR
    (endOK_of_endUOK ceSignedScRowEnd1Singular) ceSignedScRowEnd1Regular
  have key := AssemblyBindings.boundSC1 T1.scFq rfl rfl
    (δ := 0) (selfDistance _)
    (T := (T : ℝ)) (TR := ((ceSignedScRowEnd1TR + ceSignedScRowEnd1U : ℚ) : ℝ))
    (c := (endC ceSignedScRowEnd1FullFq ceSignedScRowEnd1FullTs ceSignedScRowEnd1Site : ℝ))
    (lo := (ceSignedScRowEnd1Lo : ℝ)) (fun x hx => ceSignedScDeltaT1Named x hx)
    (by exact_mod_cast hlo0) (by exact_mod_cast hlo1) ?_ (by exact_mod_cast hpos) ?_
  · intro ε hε
    filter_upwards [key ε hε] with N hN x hx
    have h := hN x hx
    have hS : ((T + K : ℚ) : ℝ) ≤ (S : ℝ) :=
      (Rat.cast_le (K := ℝ)).mpr (show T + K ≤ S from by decide +kernel)
    simp only [Rat.cast_add, Rat.cast_zero, add_zero] at hS h
    linarith [offset]
  · intro x hx _
    have h := hend x (by simpa only [hhi, Rat.cast_one] using hx)
    rw [fieldNFCheck_sound ceSignedScRowEnd1Identity x] at h
    simpa only [ceSignedScRowEnd1FullTs, lfieldTower_nil_zero, add_zero, Rat.cast_add,
      show (ceSignedScRowEnd1Site : ℝ) = 1 by rw [hsite, Rat.cast_one]] using h
  · have hT := (Rat.cast_le (K := ℝ)).mpr hcap
    simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_one, hsite] using hcmp.trans hT

#print axioms eventual
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSC1
