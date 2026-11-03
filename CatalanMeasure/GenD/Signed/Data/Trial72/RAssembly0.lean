module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RAssemblyBase
public import CatalanMeasure.GenD.Signed.Data.Trial72.RACached00
public import CatalanMeasure.GenD.Signed.Data.Trial72.MomentBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyActualBounds
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormV0
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP0
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly0
open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Cert
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.GenD.Signed.Data.Trial72 CatalanMeasure.GenD.Signed.Data.Assembly
noncomputable section

open RAssemblyBase

def X : FamPar := ⟨T0.trial, T0.bsL, 5 / 4, T0.Cb⟩
def cap : ℚ := 86517434737 / 549755813888

theorem dataOK (C : ℝ) (h : (X.Cb : ℝ) ≤ C) : X.T.DataOK C := T0.dataOK h
theorem family_eq (N : ℕ) : Generic.famD dc72 X N = T0.D N := rfl
theorem a_real : ∀ z ∈ X.T.a.tail, z.zi = 0 := by decide +kernel

theorem dot_eq : raQ X = RACached00.exactDot := by
  rw [raQ_eq_rbQ, rbQ_eq X X a_real]
  rfl

theorem scalar : rLimQ X.T.η logTwoLower RationalNormV0Data.normUb RationalNormP0Data.normUb EnergyCacheTotal00.upper RationalNormA0Data.normUb RACached00.frozenLower (iRRQ X)
    RInstPilot.Lip (1 / 12) X.T.Sup (5 / 18) (bQ X) ≤ cap := by
  -- kcost: 6.49 s C25 measured finite-sum scalar class; 520 rational summands.
  decide +kernel

theorem constant_bound (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop,
    (T0.D N).constTotal (72 * N) - (T0.D N).constant ≤ (cap : ℝ) + ε := by
  have hRef : refEnergy (famMu X) ≤ (EnergyCacheTotal00.upper : ℝ) := (EnergyActualBounds.bounds00 0).2
  have h := Generic.famD_const dc72 X dataOK 1000 (logTwoLower : ℝ) _ _ _ _ logTwo_bound
    RationalNormV0.norm_bound RationalNormP0.norm_bound RationalNormA0.norm_bound hRef ε hε
  have hd : RACached00.frozenLower ≤ raQ X := by rw [dot_eq]; exact RACached00.frozen_lower
  have hi : RInstPilot.Lip ≤ ipPartQ (ofTrial X.T) 1000 := MomentBindings.cap0
  have hcap := (Rat.cast_le (K := ℝ)).mpr (le_trans (anti hd hi) scalar)
  filter_upwards [h] with N hN
  rw [family_eq, g72, s72, rLim_cast] at hN
  exact hN.trans (add_le_add_right hcap ε)

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly0.dot_eq
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly0.scalar
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly0.constant_bound
