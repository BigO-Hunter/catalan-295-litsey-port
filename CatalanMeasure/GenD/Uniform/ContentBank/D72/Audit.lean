module
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketSparse
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostGeneric
@[expose] public section
set_option Elab.async false

/-! Axiom audit for the D72 content dependency chain. Extend with bank roots
as their generic and data proofs are completed. -/
#print axioms CatalanMeasure.GenD.Uniform.W.Prof.factor_kill
#print axioms CatalanMeasure.GenD.Uniform.W.Prof.FactorData.check_kill
#print axioms CatalanMeasure.GenD.Uniform.W.Prof.Chart.sound_of_factor
#print axioms CatalanMeasure.GenD.Uniform.W.Prof.Packet.factorCheck_sound

#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.RowSpanData.kill
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.monoHostKernel
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.map_zTy
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.map_zGy
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.zProfileData_realises
