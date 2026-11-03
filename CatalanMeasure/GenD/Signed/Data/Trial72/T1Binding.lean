module
public import CatalanMeasure.GenD.Signed.Data.Trial72.Core
public import CatalanMeasure.GenD.Signed.Data.Trial72.T1Spec
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 1000000
namespace CatalanMeasure.GenD.Signed.Data.Trial72.T1
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
noncomputable section
def params : Core.FamPar := ⟨trial, bsL, 5 / 4, Cb⟩
def D : ℕ → SignedData := Core.famD dc72 params
theorem specD (N : ℕ) : trial.form.Spec (D N) :=
  Core.famD_spec dc72 params (fun C h => dataOK h) N
theorem familyD : Family D trial.form :=
  Core.famD_family dc72 params (fun C h => dataOK h)
theorem regularD (N : ℕ) : SignedRegular (D N) := by
  apply Core.famD_regular dc72 params (fun C h => dataOK h)
  norm_num [params, Cb]
theorem massD (N : ℕ) : (D N).μ.mass = 1 - (alpha : ℝ) / 2 := by
  have hm := Core.famD_mass dc72 params (fun C h => dataOK h) N mass
  simpa only [D, params, Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hm
theorem trialEta_eq : trial.η = (9 / 20 : ℚ) := rfl
theorem etaD (N : ℕ) : (D N).η = (9 / 20 : ℝ) := by
  change ((trial.η : ℚ) : ℝ) = 9 / 20
  rw [trialEta_eq]
  norm_num
theorem nuD (N : ℕ) : (D N).ν = 72 * (N : ℝ) := rfl
theorem csD (N : ℕ) : (D N).cs = (5 / 288 : ℝ) := by
  change (((5 / 4 : ℚ) : ℝ) / 72) = 5 / 288
  norm_num
theorem p_summable (N : ℕ) : Summable (fun j => |(D N).p j|) :=
  Core.Spec_summable_p (specD N)
theorem v_summable (N : ℕ) : Summable (fun j => |(D N).v j|) :=
  Core.Spec_summable_v (specD N)
end
end CatalanMeasure.GenD.Signed.Data.Trial72.T1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.T1.specD
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.T1.familyD
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.T1.massD
