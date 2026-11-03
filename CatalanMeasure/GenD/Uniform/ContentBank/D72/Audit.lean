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

#print axioms CatalanMeasure.GenD.Uniform.W.Prof.radixEval_zero
#print axioms CatalanMeasure.GenD.Uniform.W.Prof.packed_kernel_kill

#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.scaledResidues_at
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.int_ms_sound
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.intScalarCheck_sound

#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.int_bm_sound
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.int_inverse_sound
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.int_bp_sound
