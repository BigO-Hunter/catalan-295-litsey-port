module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly1
public import CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly2
public import CatalanMeasure.GenD.Signed.Data.Trial72.ADifferenceCached12
public import CatalanMeasure.GenD.Signed.Data.Trial72.RACached12
public import CatalanMeasure.GenD.Signed.Data.Trial72.RACached21
public import CatalanMeasure.GenD.Signed.Data.Trial72.MomentDiffPilot

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.CurvAssembly12
open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Cert CatalanMeasure.CellCert
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.GenD.Signed.Data.Trial72 CatalanMeasure.GenD.Signed.Data.Assembly
noncomputable section

abbrev X : FamPar := RAssembly1.X
abbrev Y : FamPar := RAssembly2.X
def cap : ℚ := (qlist (raw_ints% [3073407623, 1099511627776])).headD 0
def vLower : ℚ := (qlist (raw_ints% [169894324744187845094054590097850870642148023933843997666384707647551377502954267227593, 40658981119626862276513426018947224922356222483921079627208979741568456125520211555123200])).headD 0
def pLower : ℚ := (qlist (raw_ints% [4453218962691247875589456267432713776428779829478624558070682031616074735441656223188171, 20817398333248953485574874121700979160246385911767592769130997627683049536266348316223078400])).headD 0
def raUpper : ℚ := (qlist (raw_ints% [199612625053349, 1152921504606846976])).headD 0
def momentTail : ℚ := 975 / 26335232
def momentUpper : ℚ := MomentDiffPilot.bound + momentTail
def rbLower : ℚ := EnergyCacheTotal11.lower + EnergyCacheTotal22.lower - 2 * EnergyCacheTotal12.upper

theorem hv : vLower ≤ lbNorm X.T.v Y.T.v 1000 := by
  rw [lbNorm_same (show X.T.v.tail = Y.T.v.tail from rfl)]
  -- kcost: 3 s conservative TL exact finite-difference class; shared tails cancel before evaluation.
  decide +kernel

theorem hp : pLower ≤ lbNorm X.T.p Y.T.p 1000 := by
  rw [lbNorm_same (show X.T.p.tail = Y.T.p.tail from rfl)]
  -- kcost: 3 s conservative TL exact finite-difference class; shared tails cancel before evaluation.
  decide +kernel

theorem ha : ADifferenceCached12.lower ≤ lbNorm X.T.a Y.T.a 1000 :=
  lbNorm_ge_cached RAssembly1.a_real RAssembly2.a_real 1000 ATailTable1.table ATailTable2.table
    ATailTable1.table_checked ATailTable2.table_checked ADifferenceCached12.lower ADifferenceCached12.checked

theorem crossXY : rbQ X Y = RACached12.exactDot := by rw [rbQ_eq X Y RAssembly2.a_real]; rfl
theorem crossYX : rbQ Y X = RACached21.exactDot := by rw [rbQ_eq Y X RAssembly1.a_real]; rfl

theorem hra : ubRaQ X Y ≤ raUpper := by
  have h := (RACached11.bounds.2 : RACached11.exactDot ≤ RACached11.upper)
  have h' := (RACached22.bounds.2 : RACached22.exactDot ≤ RACached22.upper)
  have hc := RACached12.bounds.1
  have hc' := RACached21.bounds.1
  have hu : RACached11.upper - RACached12.lower - RACached21.lower + RACached22.upper ≤ raUpper := by decide +kernel
  unfold ubRaQ
  rw [← raQ_eq_rbQ, RAssembly1.dot_eq, crossXY, crossYX, ← raQ_eq_rbQ, RAssembly2.dot_eq]
  linarith only [h,h',hc,hc',hu]

theorem hrb : (rbLower : ℝ) ≤ refBil (famMu X) (famMu X) - refBil (famMu X) (famMu Y) -
    refBil (famMu Y) (famMu X) + refBil (famMu Y) (famMu Y) :=
  famD_RB X Y RAssembly1.dataOK RAssembly2.dataOK (EnergyActualBounds.bounds11 0).1
    (EnergyActualBounds.bounds22 0).1 (EnergyActualBounds.bounds12 0 0).2

theorem hcX : (0 : ℝ) ≤ X.Cb := by norm_num [X, RAssembly1.X, T1.Cb]
theorem hcY : (0 : ℝ) ≤ Y.Cb := by norm_num [Y, RAssembly2.X, T2.Cb]

theorem hmoment (N : ℕ) :
    ip (fun n => mpos (famMu X) (Generic.famD dc72 X N).τ n - mpos (famMu Y) (Generic.famD dc72 X N).τ n)
      (fun n => mpos (famMu X) (Generic.famD dc72 X N).τ n - mpos (famMu Y) (Generic.famD dc72 X N).τ n) ≤ (momentUpper : ℝ) := by
  have h := Generic.famD_IM dc72 X Y RAssembly1.dataOK RAssembly2.dataOK hcX 1000 N
  have hm : ipDiffQ X Y 1000 ≤ MomentDiffPilot.bound := MomentBindings.cap12
  have hm' := (Rat.cast_le (K := ℝ)).mpr hm
  have ht : (2 * max (X.Cb : ℝ) (Y.Cb : ℝ)) ^ 2 / (((1000 : ℝ) + 1) * ((1000 : ℝ) + 2)) ≤
      (momentTail : ℝ) := by norm_num [X, Y, RAssembly1.X, RAssembly2.X, T1.Cb, T2.Cb, momentTail, qlist, max_def]
  rw [Rat.cast_add]
  exact h.trans (add_le_add hm' ht)

theorem scalar : cap ≤ vLower / 2 + 2 * ADifferenceCached12.lower + (1 - (9/20 : ℚ)) * rbLower +
    2 * (9/20 : ℚ) * pLower - 2 * raUpper + Generic.lbBQ dc72 X Y + lbRRQ X Y / 2 - momentUpper / 2 := by
  -- kcost: 6.49 s conservative C25 finite-sum class; no infinite sum or pole recurrence.
  decide +kernel

theorem curvature_bound : ∀ᶠ N : ℕ in atTop,
    (cap : ℝ) ≤ curvQ (T1.D N) (T2.D N) (72 * N) := by
  have hηq : X.T.η = (9/20 : ℚ) := rfl
  have h := Generic.famD_curv dc72 X Y RAssembly1.dataOK RAssembly2.dataOK hcX hcY rfl rfl
    (by rw [hηq]; norm_num) 1000 rbLower hrb (momentUpper : ℝ) hmoment
  have sc := (Rat.cast_le (K := ℝ)).mpr scalar
  have hv' := (Rat.cast_le (K := ℝ)).mpr hv
  have hp' := (Rat.cast_le (K := ℝ)).mpr hp
  have ha' := (Rat.cast_le (K := ℝ)).mpr ha
  have hra' := (Rat.cast_le (K := ℝ)).mpr hra
  push_cast at sc
  filter_upwards [h] with N hN
  rw [RAssembly1.family_eq, RAssembly2.family_eq, hηq] at hN
  push_cast at hN
  norm_num at hN sc
  linarith only [sc, hv', hp', ha', hra', hN]

end
end CatalanMeasure.GenD.Signed.Data.Trial72.CurvAssembly12
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CurvAssembly12.curvature_bound
