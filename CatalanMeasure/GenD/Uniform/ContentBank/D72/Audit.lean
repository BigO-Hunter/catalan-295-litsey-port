module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Table001
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

#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.int_h1_sound
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.int_moment_sound
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.int_zeta_sound

#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.IntMomentData.check_sound
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.source_phi_mul_X
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.source_phi_add
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.source_phi_sub
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.source_phi_mul
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.source_phi_zero_below
#print axioms CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.scalarValues_check
#print axioms CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.scalarValues_sound
#print axioms CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.momentData_check
#print axioms CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.momentData_sound

#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.source_key_recurrence
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.IntSourceTree.all_get?
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.IntSourceTree.check_sound
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.source_double_scale_unit
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.source_gd_double_scale
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.source_gd_beta_double_scale
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.source_phi_Ug_step
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.source_phi_Ut_step
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.source_phi_one_g_boundary
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.source_phi_one_t_boundary
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.source_phi_one_g_nat
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.source_phi_one_t_nat
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.sourceUg_key_base
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.sourceUt_key_base
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.sourceTreeUg_sound
#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.sourceTreeUt_sound
