module

public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScRowEnd2
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Assembly

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSC2
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.Data.Cells
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly
open CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa

set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private abbrev T : ℚ := -20131905246341/1099511627776
private abbrev K : ℚ := 4622991321585 / 274877906944
abbrev S : ℚ := -1639939960001/1099511627776

private theorem offset : scK T2.trial ≤ (K : ℝ) := by
  have hEnc : encT T2.trial.v.tail = some (605944718502765539, 290) :=
    KappaBasics.tV_checked
  have h := encl_tConst T2.trial.v.tail
  rw [hEnc] at h
  change Encl (cTv T2.trial) (ivOf (some (605944718502765539, 290))) at h
  -- kcost: 0.01 s estimated for one interval comparison. The checked 75-pole sum is reused.
  exact sc_le (B := K) h (by decide +kernel)

private theorem selfDistance (p : List ℚ) : l1Q p p ≤ 0 := by
  induction p with
  | nil => simp [l1Q]
  | cons a p ih => simpa [l1Q, qAbs] using ih

theorem eventual :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1,
      (T2.D N).fCol x ≤ (S : ℝ) + ε := by
  have hsite : ceSignedScRowEnd2Site = 1 := by decide +kernel
  have hhi : ceSignedScRowEnd2Hi = 1 := by decide +kernel
  have hlo0 : 0 < ceSignedScRowEnd2Lo := by decide +kernel
  have hlo1 : ceSignedScRowEnd2Lo < 1 := by decide +kernel
  have hpos : 0 < endC ceSignedScRowEnd2FullFq ceSignedScRowEnd2FullTs ceSignedScRowEnd2Site := by decide +kernel
  have hcap : ceSignedScRowEnd2Target ≤ T := by decide +kernel
  have hcmp := endUOK_cmp ceSignedScRowEnd2Singular
  rw [hsite, hhi, endR_one hlo1.le] at hcmp
  have hend := endOK_sound ceSignedScRowEnd2FullFq ceSignedScRowEnd2FullTs ceSignedScRowEnd2Site
    ceSignedScRowEnd2Lo ceSignedScRowEnd2Hi 40 ceSignedScRowEnd2U ceSignedScRowEnd2TR
    (endOK_of_endUOK ceSignedScRowEnd2Singular) ceSignedScRowEnd2Regular
  have key := AssemblyBindings.boundSC2 T2.scFq rfl rfl
    (δ := 0) (selfDistance _)
    (T := (T : ℝ)) (TR := ((ceSignedScRowEnd2TR + ceSignedScRowEnd2U : ℚ) : ℝ))
    (c := (endC ceSignedScRowEnd2FullFq ceSignedScRowEnd2FullTs ceSignedScRowEnd2Site : ℝ))
    (lo := (ceSignedScRowEnd2Lo : ℝ)) (fun x hx => by have h := ceSignedScDeltaT2Named x hx; norm_num [T, SignedScDeltaT2AssemblyLiteral.q2] at h ⊢; exact h)
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
    rw [fieldNFCheck_sound ceSignedScRowEnd2Identity x] at h
    simpa only [ceSignedScRowEnd2FullTs, lfieldTower_nil_zero, add_zero, Rat.cast_add,
      show (ceSignedScRowEnd2Site : ℝ) = 1 by rw [hsite, Rat.cast_one]] using h
  · have hT := (Rat.cast_le (K := ℝ)).mpr hcap
    simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_one, hsite] using hcmp.trans hT

#print axioms eventual
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSC2
