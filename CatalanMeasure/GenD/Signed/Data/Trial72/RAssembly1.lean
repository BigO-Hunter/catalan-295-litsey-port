module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RAssemblyBase
public import CatalanMeasure.GenD.Signed.Data.Trial72.RACached11
public import CatalanMeasure.GenD.Signed.Data.Trial72.MomentBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyActualBounds
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormV1
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP1
public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA1

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly1
open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Cert
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.GenD.Signed.Data.Trial72 CatalanMeasure.GenD.Signed.Data.Assembly
noncomputable section

open RAssemblyBase

def X : FamPar := ⟨T1.trial, T1.bsL, 5 / 4, T1.Cb⟩
def cap : ℚ := 163208789379 / 1099511627776

theorem dataOK (C : ℝ) (h : (X.Cb : ℝ) ≤ C) : X.T.DataOK C := T1.dataOK h
theorem family_eq (N : ℕ) : Generic.famD dc72 X N = T1.D N := rfl
theorem a_real : ∀ z ∈ X.T.a.tail, z.zi = 0 := by decide +kernel

theorem dot_eq : raQ X = RACached11.exactDot := by
  rw [raQ_eq_rbQ, rbQ_eq X X a_real]
  rfl

theorem scalar : rLimQ X.T.η logTwoLower RationalNormV1Data.normUb RationalNormP1Data.normUb EnergyCacheTotal11.upper RationalNormA1Data.normUb RACached11.frozenLower (iRRQ X)
    MomentReduction1.bound (1 / 12) X.T.Sup (5 / 18) (bQ X) ≤ cap := by
  -- kcost: 6.49 s C25 measured finite-sum scalar class; 520 rational summands.
  decide +kernel

theorem constant_bound (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop,
    (T1.D N).constTotal (72 * N) - (T1.D N).constant ≤ (cap : ℝ) + ε := by
  have hRef : refEnergy (famMu X) ≤ (EnergyCacheTotal11.upper : ℝ) := (EnergyActualBounds.bounds11 0).2
  have h := Generic.famD_const dc72 X dataOK 1000 (logTwoLower : ℝ) _ _ _ _ logTwo_bound
    RationalNormV1.norm_bound RationalNormP1.norm_bound RationalNormA1.norm_bound hRef ε hε
  have hd : RACached11.frozenLower ≤ raQ X := by rw [dot_eq]; exact RACached11.frozen_lower
  have hi : MomentReduction1.bound ≤ ipPartQ (ofTrial X.T) 1000 := MomentBindings.cap1
  have hcap := (Rat.cast_le (K := ℝ)).mpr (le_trans (anti hd hi) scalar)
  filter_upwards [h] with N hN
  rw [family_eq, g72, s72, rLim_cast] at hN
  exact hN.trans (add_le_add_right hcap ε)

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly1.dot_eq
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly1.scalar
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly1.constant_bound
