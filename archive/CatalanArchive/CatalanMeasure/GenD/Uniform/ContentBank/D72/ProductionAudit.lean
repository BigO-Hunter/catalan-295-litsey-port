module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.WindowPrice
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Response
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostSeenPositions
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostLowGraph
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostJetPrefix
@[expose] public section
set_option Elab.async false
#print axioms CatalanMeasure.GenD.Uniform.ContentBank.D72.fullLedger_eq
#print axioms CatalanMeasure.GenD.Uniform.ContentBank.D72.fallbackLedger_eq
#print axioms CatalanMeasure.GenD.Uniform.ContentBank.D72.full_window_price72
#print axioms CatalanMeasure.GenD.Uniform.ContentBank.D72.fallback_window_price72
#print axioms CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.sourceFoldedCoeff?_sound
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.low_eq_zero_of_cover
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.hG_of_checked_prefix
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.jetPrefixCheck_kill
