module
public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCorners1
open Set CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
open AssemblyBindings
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev terms : List LTerm := scaleL (-1) (reflL (dilTermsS T1.trial.qF T1.trial.qFn))
abbrev topField (a b : ℚ) : FieldQ :=
  let f := T1.nearAt a b
  { f with plogs := f.plogs.take (f.plogs.length - 2) }

theorem nearIdentity (a b : ℚ) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Generic.nearLim dc72 AssemblyBindings.X1 a b y =
      fval (T1.nearAt a b) y + lfieldTower terms 0 y + nearK T1.trial a b +
      ((AssemblyBindings.X1.CSP : ℝ) / 72) * (if 1 - 1 / 1024 < y then 1 else 0) := by
  have hR : (fun y : ℝ => -((11 : ℝ) / 12) * Real.log (1 + y ^ 2) +
      (5 / 6) * Real.log |y|) = rnQ (11 / 12) (5 / 6) := by
    funext y
    simp only [rnQ]
    push_cast
    ring
  have hσ : (20 : ℝ) / 72 = ((5/18 : ℚ) : ℝ) := by norm_num
  have h := T1.nearIdentityAt a b (csL := (AssemblyBindings.X1.CSP : ℝ) / 72) (θL := 1 / 1024) hy
  simp only [Generic.nearLim, dc72_n0, dc72_g0, Nat.cast_ofNat]
  have hSp : dc72.sp = 20 := rfl
  have hTheta : (dc72.thetaL : ℝ) = 1/1024 := by norm_num [dc72]
  simp only [hSp, Nat.cast_ofNat, hTheta]
  have hR' : (fun y : ℝ => -(((72 : ℝ) - 6) / 72) * Real.log (1 + y ^ 2) +
      (((72 : ℝ) - 2 * 6) / 72) * Real.log |y|) = rnQ (11 / 12) (5 / 6) := by
    rw [← hR]
    funext y
    ring
  rw [hR', hσ]
  exact h

theorem offset (a b B : ℚ)
    (check : lin3 (2 * T1.trial.Sup) 2 (11/4*b + T1.trial.η + a/2) 0
      (ivOf (some (3321757840045031, 40))) ivL2 ivZero B = true) :
    nearK T1.trial a b ≤ (B : ℝ) := by
  have hEnc : encS T1.trial.a.tail = some (3321757840045031, 40) := KappaBasics.sA1_checked
  have h := encl_sConst T1.trial.a.tail
  rw [hEnc] at h
  change Encl (cSa T1.trial) (ivOf (some (3321757840045031, 40))) at h
  have hr : remC (1 - 2 * (T1.trial.η : ℝ)) = 11 / 8 := by
    change remC (1 - 2 * ((9/20 : ℚ) : ℝ)) = 11/8
    norm_num [remC]
  exact near_le (η := T1.trial.η) (Sup := T1.trial.Sup) hr h check

theorem splitTop (a b : ℚ)
    (hpl : (T1.nearAt a b).plogs =
      (topField a b).plogs ++ (fqScale (b / (4 * (1 - T1.trial.η))) m1sqFQ).plogs)
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    fval (T1.nearAt a b) y = fval (topField a b) y +
      (5/11 * (b : ℝ)) * (-Real.log (1 - y ^ 2)) := by
  have hm : plogSumTower (fqScale (b / (4 * (1 - T1.trial.η))) m1sqFQ).plogs 0 y =
      fval (fqScale (b / (4 * (1 - T1.trial.η))) m1sqFQ) y := by
    simp [fval, fqScale, m1sqFQ, polyTow, poleFn]
  have hc : ((b / (4 * (1 - T1.trial.η)) : ℚ) : ℝ) = 5/11 * (b : ℝ) := by
    change ((b / (4 * (1 - 9/20)) : ℚ) : ℝ) = _
    push_cast
    ring
  unfold fval
  rw [hpl, l1_plogSum_append, hm, fval_scale, fval_m1sq hy, hc]
  change _ = polyTow (T1.nearAt a b).poly 0 y + plogSumTower (topField a b).plogs 0 y +
    poleFn (T1.nearAt a b).poles y + _
  ring

#print axioms nearIdentity
#print axioms offset
#print axioms splitTop
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCorners1
