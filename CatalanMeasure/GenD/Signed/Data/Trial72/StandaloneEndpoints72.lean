module
public import CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneCertificates
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneDecayBounds
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneEndpoints72
open CatalanMeasure.GenD.Analytic OAI.InternalCatalan
open Davis.ScalarInstance72 SheetBindings StandaloneBudgets
open CatalanMeasure.GenD.Signed.Data.Cells.D72
noncomputable section

theorem first : FreeFirstBound dc72.toParameters target72 (72*cost72) :=
  hfirst StandaloneCertificates.first StandaloneDecayBounds.first

theorem large : FreeLargeBound dc72.toParameters G72 target72 (72*cost72) (1/16) :=
  hlarge StandaloneCertificates.large StandaloneDecayBounds.reference

def reference : SecondTrialBoundsEnd dc72.toParameters 0 baseTarget72
    (-6909202/100000000) secondNearCap cost72 G72 :=
  nearReference StandaloneCertificates.reference StandaloneDecayBounds.reference

end
end CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneEndpoints72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneEndpoints72.first
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneEndpoints72.large
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.StandaloneEndpoints72.reference
