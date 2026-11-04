module
public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCorners2
open Set CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
open AssemblyBindings
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev terms : List LTerm := scaleL (-1) (reflL (dilTermsS T2.trial.qF T2.trial.qFn))
abbrev topField (a b : ℚ) : FieldQ :=
  let f := T2.nearAt a b
  { f with plogs := f.plogs.take (f.plogs.length - 2) }

theorem nearIdentity (a b : ℚ) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Generic.nearLim dc72 AssemblyBindings.X2 a b y =
      fval (T2.nearAt a b) y + lfieldTower terms 0 y + nearK T2.trial a b +
      ((AssemblyBindings.X2.CSP : ℝ) / 72) * (if 1 - 1 / 1024 < y then 1 else 0) := by
  have hR : (fun y : ℝ => -((11 : ℝ) / 12) * Real.log (1 + y ^ 2) +
      (5 / 6) * Real.log |y|) = rnQ (11 / 12) (5 / 6) := by
    funext y
    simp only [rnQ]
    push_cast
    ring
  have hσ : (20 : ℝ) / 72 = ((5/18 : ℚ) : ℝ) := by norm_num
  have h := T2.nearIdentityAt a b (csL := (AssemblyBindings.X2.CSP : ℝ) / 72) (θL := 1 / 1024) hy
  change fNearMSLim T2.trial.form
    (fun y : ℝ => -(((72 : ℝ) - 6) / 72) * Real.log (1 + y ^ 2) +
      (((72 : ℝ) - 2 * 6) / 72) * Real.log |y|) a b ((20 : ℝ) / 72)
      (fQ T2.bsL) T2.bsL.length ((AssemblyBindings.X2.CSP : ℝ) / 72) (1 / 1024) y = _
  have hR' : (fun y : ℝ => -(((72 : ℝ) - 6) / 72) * Real.log (1 + y ^ 2) +
      (((72 : ℝ) - 2 * 6) / 72) * Real.log |y|) = rnQ (11 / 12) (5 / 6) := by
    rw [← hR]
    funext y
    ring
  rw [hR', hσ]
  exact h

theorem offset (a b B : ℚ)
    (check : lin3 (2 * T2.trial.Sup) 2 (11/4*b + T2.trial.η + a/2) 0
      (ivOf (some (3225998431658358, 40))) ivL2 ivZero B = true) :
    nearK T2.trial a b ≤ (B : ℝ) := by
  have hEnc : encS T2.trial.a.tail = some (3225998431658358, 40) := KappaBasics.sA2_checked
  have h := encl_sConst T2.trial.a.tail
  rw [hEnc] at h
  change Encl (cSa T2.trial) (ivOf (some (3225998431658358, 40))) at h
  have hr : remC (1 - 2 * (T2.trial.η : ℝ)) = 11 / 8 := by
    change remC (1 - 2 * ((9/20 : ℚ) : ℝ)) = 11/8
    norm_num [remC]
  exact near_le (η := T2.trial.η) (Sup := T2.trial.Sup) hr h check

theorem splitTop (a b : ℚ)
    (hpl : (T2.nearAt a b).plogs =
      (topField a b).plogs ++ (fqScale (b / (4 * (1 - T2.trial.η))) m1sqFQ).plogs)
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    fval (T2.nearAt a b) y = fval (topField a b) y +
      (5/11 * (b : ℝ)) * (-Real.log (1 - y ^ 2)) := by
  have hm : plogSumTower (fqScale (b / (4 * (1 - T2.trial.η))) m1sqFQ).plogs 0 y =
      fval (fqScale (b / (4 * (1 - T2.trial.η))) m1sqFQ) y := by
    simp [fval, fqScale, m1sqFQ, polyTow, poleFn]
  have hc : ((b / (4 * (1 - T2.trial.η)) : ℚ) : ℝ) = 5/11 * (b : ℝ) := by
    change ((b / (4 * (1 - 9/20)) : ℚ) : ℝ) = _
    push_cast
    ring
  unfold fval
  rw [hpl, l1_plogSum_append, hm, fval_scale, fval_m1sq hy, hc]
  change _ = polyTow (T2.nearAt a b).poly 0 y + plogSumTower (topField a b).plogs 0 y +
    poleFn (T2.nearAt a b).poles y + _
  ring

#print axioms nearIdentity
#print axioms offset
#print axioms splitTop
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCorners2
