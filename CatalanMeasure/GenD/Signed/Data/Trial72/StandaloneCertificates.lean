module
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormPhysical
public import CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneBudgets
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneCertificates
open ReferenceData SheetBindings StandaloneBudgets Davis.ScalarInstance72
noncomputable section

theorem first : FirstTrialCertificate where
  norm := by simpa only [firstNormCap] using RawNormPhysical.first_weighted
  budget := first_budget

private theorem residual_eq : secondResidual = (-6909202/100000000 : ℝ) := by
  norm_num [secondResidual]

theorem large : SecondTrialCertificate (1/16) target72 cost72 secondMX secondMY
    secondNormCap secondFieldCap (-6909202/100000000) secondNearCap where
  norm := RawNormPhysical.second_weighted
  field_sum := rfl
  budget ha ha0 ht := by
    rw [← residual_eq]
    exact large_budget ha ha0 ht

theorem reference : SecondTrialCertificate 0 baseTarget72 cost72 secondMX secondMY
    secondNormCap secondFieldCap (-6909202/100000000) secondNearCap where
  norm := RawNormPhysical.second_weighted
  field_sum := rfl
  budget ha ha0 ht := by
    rw [← residual_eq]
    exact reference_budget ha ha0 ht

end
end CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneCertificates
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneCertificates.first
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneCertificates.large
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneCertificates.reference
