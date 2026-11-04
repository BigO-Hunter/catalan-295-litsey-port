module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly0
public import CatalanMeasure.GenD.Signed.Data.Trial72.RAssembly1
public import CatalanMeasure.GenD.Signed.Data.Trial72.ADifferenceCached01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RACached01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RACached10
public import CatalanMeasure.GenD.Signed.Data.Trial72.MomentReduction01

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.CurvAssembly01
open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Cert CatalanMeasure.CellCert
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.GenD.Signed.Data.Trial72 CatalanMeasure.GenD.Signed.Data.Assembly
noncomputable section

abbrev X : FamPar := RAssembly0.X
abbrev Y : FamPar := RAssembly1.X
def cap : ℚ := (qlist (raw_ints% [3774131, 274877906944])).headD 0
def vLower : ℚ := (qlist (raw_ints% [846664456471031423354723354267470078510917540940706447376606922611490459725711253, 26962189071370598326600415131927867985647362389868089938467493197326562417453721190400])).headD 0
def pLower : ℚ := (qlist (raw_ints% [10002943525935168094510331886226495613765417770850772938419194066922690880430421634791, 7240834202869201212373869259722079707911786404093075745784694827020191143049164631729766400])).headD 0
def raUpper : ℚ := (qlist (raw_ints% [376658506431, 288230376151711744])).headD 0
def momentTail : ℚ := 1083 / 85589504
def momentUpper : ℚ := MomentReduction01.bound + momentTail
def rbLower : ℚ := EnergyCacheTotal00.lower + EnergyCacheTotal11.lower - 2 * EnergyCacheTotal01.upper

theorem hv : vLower ≤ lbNorm X.T.v Y.T.v 1000 := by
  rw [lbNorm_same (show X.T.v.tail = Y.T.v.tail from rfl)]
  -- kcost: 3 s conservative TL exact finite-difference class; shared tails cancel before evaluation.
  decide +kernel

theorem hp : pLower ≤ lbNorm X.T.p Y.T.p 1000 := by
  rw [lbNorm_same (show X.T.p.tail = Y.T.p.tail from rfl)]
  -- kcost: 3 s conservative TL exact finite-difference class; shared tails cancel before evaluation.
  decide +kernel

theorem ha : ADifferenceCached01.lower ≤ lbNorm X.T.a Y.T.a 1000 :=
  lbNorm_ge_cached RAssembly0.a_real RAssembly1.a_real 1000 ATailTable0.table ATailTable1.table
    ATailTable0.table_checked ATailTable1.table_checked ADifferenceCached01.lower ADifferenceCached01.checked

theorem crossXY : rbQ X Y = RACached01.exactDot := by rw [rbQ_eq X Y RAssembly1.a_real]; rfl
theorem crossYX : rbQ Y X = RACached10.exactDot := by rw [rbQ_eq Y X RAssembly0.a_real]; rfl

theorem hra : ubRaQ X Y ≤ raUpper := by
  have h := (RACached00.bounds.2 : RACached00.exactDot ≤ RACached00.upper)
  have h' := (RACached11.bounds.2 : RACached11.exactDot ≤ RACached11.upper)
  have hc := RACached01.bounds.1
  have hc' := RACached10.bounds.1
  have hu : RACached00.upper - RACached01.lower - RACached10.lower + RACached11.upper ≤ raUpper := by decide +kernel
  unfold ubRaQ
  rw [← raQ_eq_rbQ, RAssembly0.dot_eq, crossXY, crossYX, ← raQ_eq_rbQ, RAssembly1.dot_eq]
  linarith only [h,h',hc,hc',hu]

theorem hrb : (rbLower : ℝ) ≤ refBil (famMu X) (famMu X) - refBil (famMu X) (famMu Y) -
    refBil (famMu Y) (famMu X) + refBil (famMu Y) (famMu Y) :=
  famD_RB X Y RAssembly0.dataOK RAssembly1.dataOK (EnergyActualBounds.bounds00 0).1
    (EnergyActualBounds.bounds11 0).1 (EnergyActualBounds.bounds01 0 0).2

theorem hcX : (0 : ℝ) ≤ X.Cb := by norm_num [X, RAssembly0.X, T0.Cb]
theorem hcY : (0 : ℝ) ≤ Y.Cb := by norm_num [Y, RAssembly1.X, T1.Cb]

theorem hmoment (N : ℕ) :
    ip (fun n => mpos (famMu X) (Generic.famD dc72 X N).τ n - mpos (famMu Y) (Generic.famD dc72 X N).τ n)
      (fun n => mpos (famMu X) (Generic.famD dc72 X N).τ n - mpos (famMu Y) (Generic.famD dc72 X N).τ n) ≤ (momentUpper : ℝ) := by
  have h := Generic.famD_IM dc72 X Y RAssembly0.dataOK RAssembly1.dataOK hcX 1000 N
  have hm : ipDiffQ X Y 1000 ≤ MomentReduction01.bound := MomentBindings.cap01
  have hm' := (Rat.cast_le (K := ℝ)).mpr hm
  have ht : (2 * max (X.Cb : ℝ) (Y.Cb : ℝ)) ^ 2 / (((1000 : ℝ) + 1) * ((1000 : ℝ) + 2)) ≤
      (momentTail : ℝ) := by norm_num [X, Y, RAssembly0.X, RAssembly1.X, T0.Cb, T1.Cb, momentTail, qlist, max_def]
  first | rw [Rat.cast_add] | (unfold momentUpper; rw [Rat.cast_add]) | (simp only [momentUpper, Rat.cast_add])
  exact h.trans (add_le_add hm' ht)

theorem scalar : cap ≤ vLower / 2 + 2 * ADifferenceCached01.lower + (1 - (9/20 : ℚ)) * rbLower +
    2 * (9/20 : ℚ) * pLower - 2 * raUpper + Generic.lbBQ dc72 X Y + lbRRQ X Y / 2 - momentUpper / 2 := by
  -- kcost: 6.49 s conservative C25 finite-sum class; no infinite sum or pole recurrence.
  decide +kernel

theorem curvature_bound : ∀ᶠ N : ℕ in atTop,
    (cap : ℝ) ≤ curvQ (T0.D N) (T1.D N) (72 * N) := by
  have hηq : X.T.η = (9/20 : ℚ) := rfl
  have h := Generic.famD_curv dc72 X Y RAssembly0.dataOK RAssembly1.dataOK hcX hcY rfl rfl
    (by rw [hηq]; norm_num) 1000 rbLower hrb (momentUpper : ℝ) hmoment
  have sc := (Rat.cast_le (K := ℝ)).mpr scalar
  have hv' := (Rat.cast_le (K := ℝ)).mpr hv
  have hp' := (Rat.cast_le (K := ℝ)).mpr hp
  have ha' := (Rat.cast_le (K := ℝ)).mpr ha
  have hra' := (Rat.cast_le (K := ℝ)).mpr hra
  push_cast at sc
  filter_upwards [h] with N hN
  rw [RAssembly0.family_eq, RAssembly1.family_eq, hηq] at hN
  push_cast at hN
  norm_num at hN sc
  linarith only [sc, hv', hp', ha', hra', hN]

end
end CatalanMeasure.GenD.Signed.Data.Trial72.CurvAssembly01
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.CurvAssembly01.curvature_bound
