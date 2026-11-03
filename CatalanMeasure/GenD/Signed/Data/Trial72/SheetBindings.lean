module
public import CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceData
public import CatalanMeasure.GenD.Signed.Data.Trial72.EndpointAdapters
public import CatalanMeasure.GenD.Signed.Davis.ScalarInstance72
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SheetBindings
open Set Filter CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.CellCert
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
open ReferenceData Davis.ScalarInstance72
noncomputable section
local notation "P72" => dc72.toParameters

/-- Exact analytic field obligations owed for the standalone first trial.
Arb JSON is provenance, not a proof of either field of this record. -/
structure FirstDecayBounds : Prop where
  row : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
    firstRowFieldG (3/8) (1/9) (97/72-1/2) firstLambda (1/6) firstP firstV x ≤ firstMX
  column : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG (11/72) (1/18) firstV s ≤ firstMY

/-- These are trial norm/budget obligations, separate from decay Bounds. -/
structure FirstTrialCertificate : Prop where
  norm : barrierTrialNormSq firstP + barrierTrialNormSq firstV / 2 ≤ firstNormCap
  budget : ∀ a : ℝ,
    (-gC0 P72 + gC1 P72 * a - a^2) * Real.log 2 + firstNormCap +
      (1-a)*firstFieldCap + a*(2*firstLambda*(((P72).g0:ℝ)/(P72).n0)) ≤
        -target72 + Real.log 2/2 + cost72*a

def firstBounds (C : FirstTrialCertificate) (B : FirstDecayBounds) :
    FirstTrialBoundsEnd P72 target72 cost72 :=
  EndpointAdapters.firstEnd_of_fields dc72.admissible firstP firstV firstLambda
    first_lambda_nonneg firstP_summable firstV_summable
    (3/8) (1/9) (97/72-1/2) (1/6) (11/72) (1/18)
    (by norm_num [dc72]) (by norm_num [dc72]) (by norm_num [dc72])
    (by norm_num [dc72]) (by norm_num [dc72]) (by norm_num [dc72])
    firstMX firstMY C.norm first_field_sum B.row B.column C.budget

theorem hfirst (C : FirstTrialCertificate) (B : FirstDecayBounds) :
    FreeFirstBound P72 target72 (72*cost72) :=
  freeFirstBound_of_end dc72.admissible (firstBounds C B)

/- C22 / chebengine standalone manifest pins the reference caps to
MX = -96992793/100000000, MY = -158005012/100000000,
residual = -6909202/100000000, nearCap = -77/100.
The near proof uses near_residual_field_le with l=7704/10000, u=7705/10000.
The record stays parameterized so the same certified fields serve both endpoints.
No numerical cap or Arb assertion is treated as a proof here. -/
/-- Exact field obligations for the standalone second/reference sequences. -/
structure SecondDecayBounds (MX MY residual nearCap : ℝ) : Prop where
  row : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
    rowFieldG (3/8) (1/9) (97/72) secondP secondV x ≤ MX
  column : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG (11/72) (1/18) secondV s ≤ MY
  residual : ∀ x ∈ Icc (-1 : ℝ) 1, G72 x → resFieldGen (gRes P72) secondP x ≤ residual
  near : ∀ y ∈ Ioo (0 : ℝ) 1,
    -gRes P72 * Real.log (1+y^2) + ((((P72).n0:ℝ)-2*(P72).g0-1)/(P72).n0)*Real.log y -
      secondP 1*y ≤ nearCap

structure SecondTrialCertificate (α1 target cost MX MY normCap fieldCap residual nearCap : ℝ) : Prop where
  norm : 2*barrierTrialNormSq secondP + barrierTrialNormSq secondV/2 ≤ normCap
  field_sum : MX+MY=fieldCap
  budget : ∀ {a t : ℝ}, α1 ≤ a → 0 ≤ a → 0 ≤ t →
    (-gC0 P72+gC1 P72*a-a^2+t-t^2)*Real.log 2 + normCap+(1-a)*fieldCap+
      (a-t)*residual+t*nearCap ≤ -target+Real.log 2/2+cost*a

def secondBounds {α1 target cost MX MY normCap fieldCap residual nearCap : ℝ}
    (C : SecondTrialCertificate α1 target cost MX MY normCap fieldCap residual nearCap)
    (B : SecondDecayBounds MX MY residual nearCap) :
    SecondTrialBoundsEnd P72 α1 target residual nearCap cost G72 :=
  EndpointAdapters.secondEnd_of_fields dc72.admissible secondP secondV secondP_summable secondV_summable
    (3/8) (1/9) (97/72) (11/72) (1/18)
    (by norm_num [dc72]) (by norm_num [dc72]) (by norm_num [dc72])
    (by norm_num [dc72]) (by norm_num [dc72]) MX MY nearCap
    B.near C.norm C.field_sum B.row B.column B.residual C.budget

theorem hlarge {MX MY normCap fieldCap residual nearCap : ℝ}
    (C : SecondTrialCertificate (1/16) target72 cost72 MX MY normCap fieldCap residual nearCap)
    (B : SecondDecayBounds MX MY residual nearCap) :
    FreeLargeBound P72 G72 target72 (72*cost72) (1/16) :=
  freeLargeBound_of_end dc72.admissible (secondBounds C B)

/-- A distinct alpha=0 reference endpoint is needed by near/link. Its target need
not equal the improved target72; the producer supplies this separate budget. -/
def nearReference {target cost MX MY normCap fieldCap residual nearCap : ℝ}
    (C : SecondTrialCertificate 0 target cost MX MY normCap fieldCap residual nearCap)
    (B : SecondDecayBounds MX MY residual nearCap) :
    SecondTrialBoundsEnd P72 0 target residual nearCap cost G72 := secondBounds C B

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SheetBindings

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SheetBindings.hfirst
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SheetBindings.hlarge
