module
public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom0
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom1
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom2
public import CatalanMeasure.GenD.Signed.Data.Assembly.Spike
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantomBindings72
open CatalanMeasure.Signed.Consts
open CatalanMeasure.GenD.Signed.Data.Assembly
open AssemblyBindings
noncomputable section

theorem ref0 {N : ℕ} (hN : 0 < N) :
    CatalanMeasure.Signed.Consts.Generic.RefTrial dc72 (T0.D N) N X0.bs
      X0.T.a.f X0.T.a.tail X0.CSP SpikePhantom0.A1q SpikePhantom0.B1q
      (SpikePhantom0.BRq : ℝ) ((dc72.n0*N : ℕ) : ℝ) (((dc72.n0*N : ℕ) : ℝ)+1) := by
  refine CatalanMeasure.GenD.Signed.Data.Assembly.Generic.famD_refTrial dc72 X0 hN (Lθ := SpikePhantom0.Lθ) ?_
    SpikePhantom0.tail_disk SpikePhantom0.ref_bound ?_
  · simpa [dc72] using SpikePhantom0.log_bound
  · convert SpikePhantom0.phantom_bound using 1 <;> norm_num [dc72, X0, toAssembly, T0.params] <;> ring

theorem ref1 {N : ℕ} (hN : 0 < N) :
    CatalanMeasure.Signed.Consts.Generic.RefTrial dc72 (T1.D N) N X1.bs
      X1.T.a.f X1.T.a.tail X1.CSP SpikePhantom1.A1q SpikePhantom1.B1q
      (SpikePhantom1.BRq : ℝ) ((dc72.n0*N : ℕ) : ℝ) (((dc72.n0*N : ℕ) : ℝ)+1) := by
  refine CatalanMeasure.GenD.Signed.Data.Assembly.Generic.famD_refTrial dc72 X1 hN (Lθ := SpikePhantom1.Lθ) ?_
    SpikePhantom1.tail_disk SpikePhantom1.ref_bound ?_
  · simpa [dc72] using SpikePhantom1.log_bound
  · convert SpikePhantom1.phantom_bound using 1 <;> norm_num [dc72, X1, toAssembly, T1.params] <;> ring

theorem ref2 {N : ℕ} (hN : 0 < N) :
    CatalanMeasure.Signed.Consts.Generic.RefTrial dc72 (T2.D N) N X2.bs
      X2.T.a.f X2.T.a.tail X2.CSP SpikePhantom2.A1q SpikePhantom2.B1q
      (SpikePhantom2.BRq : ℝ) ((dc72.n0*N : ℕ) : ℝ) (((dc72.n0*N : ℕ) : ℝ)+1) := by
  refine CatalanMeasure.GenD.Signed.Data.Assembly.Generic.famD_refTrial dc72 X2 hN (Lθ := SpikePhantom2.Lθ) ?_
    SpikePhantom2.tail_disk SpikePhantom2.ref_bound ?_
  · simpa [dc72] using SpikePhantom2.log_bound
  · convert SpikePhantom2.phantom_bound using 1 <;> norm_num [dc72, X2, toAssembly, T2.params] <;> ring

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantomBindings72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantomBindings72.ref0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantomBindings72.ref1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantomBindings72.ref2
