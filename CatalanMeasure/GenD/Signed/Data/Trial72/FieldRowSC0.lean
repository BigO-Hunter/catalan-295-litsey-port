module

public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCoverJointSC

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSC0
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.Data.Cells
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly
open CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa

set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private abbrev T : ℚ := -20222538696221 / 1099511627776
private abbrev K : ℚ := 4622991321585 / 274877906944
abbrev S : ℚ := -1730573409881 / 1099511627776

private theorem offset : scK T0.trial ≤ (K : ℝ) := by
  have hEnc : encT T0.trial.v.tail = some (605944718502765539, 290) :=
    KappaBasics.tV_checked
  have h := encl_tConst T0.trial.v.tail
  rw [hEnc] at h
  change Encl (cTv T0.trial) (ivOf (some (605944718502765539, 290))) at h
  -- kcost: 0.01 s estimated for one interval comparison. The checked 75-pole sum is reused.
  exact sc_le (B := K) h (by decide +kernel)

private theorem selfDistance (p : List ℚ) : l1Q p p ≤ 0 := by
  induction p with
  | nil => simp [l1Q]
  | cons a p ih => simpa [l1Q, qAbs] using ih

theorem eventual :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1,
      (T0.D N).fCol x ≤ (S : ℝ) + ε := by
  have hsite : d2SAE009Site = 1 := by decide +kernel
  have hhi : d2SAE009Hi = 1 := by decide +kernel
  have hlo0 : 0 < d2SAE009Lo := by decide +kernel
  have hlo1 : d2SAE009Lo < 1 := by decide +kernel
  have hpos : 0 < endC d2SAE009FullFq d2SAE009FullTs d2SAE009Site := by decide +kernel
  have hcap : d2SAE009Target ≤ T := by decide +kernel
  have hcmp := endUOK_cmp d2SAE009Singular
  rw [hsite, hhi, endR_one hlo1.le] at hcmp
  have hend := endOK_sound d2SAE009FullFq d2SAE009FullTs d2SAE009Site
    d2SAE009Lo d2SAE009Hi 20 d2SAE009U d2SAE009TR
    (endOK_of_endUOK d2SAE009Singular) d2SAE009Regular
  have key := AssemblyBindings.boundSC0 T0.scFq rfl rfl
    (δ := 0) (selfDistance _)
    (T := (T : ℝ)) (TR := ((d2SAE009TR + d2SAE009U : ℚ) : ℝ))
    (c := (endC d2SAE009FullFq d2SAE009FullTs d2SAE009Site : ℝ))
    (lo := (d2SAE009Lo : ℝ)) (fun x hx => D72.StandaloneCoverJointSC.signedSC x hx)
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
    rw [fieldNFCheck_sound D72.StandaloneCoverJointSC.d2SAE009RawIdentity x,
      fieldNFCheck_sound D72.StandaloneCoverJointSC.scFieldCheck x] at h
    simpa only [d2SAE009FullTs, lfieldTower_nil_zero, add_zero, Rat.cast_add,
      show (d2SAE009Site : ℝ) = 1 by rw [hsite, Rat.cast_one]] using h
  · have hT := (Rat.cast_le (K := ℝ)).mpr hcap
    simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_one, hsite] using hcmp.trans hT

#print axioms eventual
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSC0
