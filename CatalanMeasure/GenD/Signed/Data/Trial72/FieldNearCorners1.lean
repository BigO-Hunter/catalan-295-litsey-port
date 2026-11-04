module
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearLimit1
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


structure Covers : Prop where
  off0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ)
  top0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-11841522741 : ℚ) / 8589934592) : ℚ) : ℝ)
  jump0 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-107915881949 : ℚ) / 77309411328) : ℚ) : ℝ)
  off1 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ)
  top1 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-756905488599 : ℚ) / 549755813888) : ℚ) : ℝ)
  jump1 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ)
  off2 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ)
  top2 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1513810977579 : ℚ) / 1099511627776) : ℚ) : ℝ)
  jump2 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ)
  off3 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ)
  top3 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1491915739711 : ℚ) / 1099511627776) : ℚ) : ℝ)
  jump3 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ)
  off4 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ)
  top4 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1491915739351 : ℚ) / 1099511627776) : ℚ) : ℝ)
  jump4 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ)

private theorem kappa0 : nearK T1.trial ((0 : ℚ) / 1) ((0 : ℚ) / 1) ≤ ((((3593107125 : ℚ) / 8589934592) : ℚ) : ℝ) :=
  offset ((0 : ℚ) / 1) ((0 : ℚ) / 1) ((3593107125 : ℚ) / 8589934592) (by decide +kernel)

theorem off0 (c : Covers) : ∀ y ∈ Ico (98749/1000000 : ℝ) (999/1000),
    Generic.nearLim dc72 AssemblyBindings.X1 ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ) y ≤ ((((-316571149 : ℚ) / 536870912) : ℚ) : ℝ) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h := c.off0 y
    (by norm_num [Set.mem_Icc]; exact ⟨hy.1, hy.2.le⟩)
  rw [nearIdentity ((0 : ℚ) / 1) ((0 : ℚ) / 1) hy01, if_neg (by linarith [hy.2] : ¬ (1-1/1024:ℝ) < y)]
  have hk := kappa0
  push_cast at h hk ⊢
  linarith only [h, hk]

theorem top0 (c : Covers) : ∀ y ∈ Ico (999/1000 : ℝ) 1,
    Generic.nearLim dc72 AssemblyBindings.X1 ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ) y ≤
      ((((-64440747 : ℚ) / 67108864) : ℚ) : ℝ) + (5/11 * ((((0 : ℚ) / 1) : ℚ) : ℝ)) * (-Real.log (1-y^2)) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hs := splitTop ((0 : ℚ) / 1) ((0 : ℚ) / 1) (by decide +kernel) (y := y) ⟨by linarith [hy.1], hy.2⟩
  rw [nearIdentity ((0 : ℚ) / 1) ((0 : ℚ) / 1) hy01, hs]
  have hk := kappa0
  have hcs : (AssemblyBindings.X1.CSP : ℝ) / 72 = ((((5 : ℚ) / 288) : ℚ) : ℝ) := by
    change ((T1.params.CSP : ℚ) : ℝ) / 72 = _
    norm_num [T1.params]
  rw [hcs]
  rcases le_or_gt y (1 - 1/1024 : ℝ) with hj | hj
  · have h := c.top0 y
      (by norm_num [Set.mem_Icc]; exact ⟨hy.1, by linarith⟩)
    rw [if_neg (not_lt.mpr hj)]
    push_cast at h hk ⊢
    linarith only [h, hk]
  · have h := c.jump0 y
      (by norm_num [Set.mem_Icc]; exact ⟨by linarith, hy.2.le⟩)
    rw [if_pos hj]
    push_cast at h hk ⊢
    linarith only [h, hk]
#print axioms off0
#print axioms top0

private theorem kappa1 : nearK T1.trial ((1 : ℚ) / 200) ((0 : ℚ) / 1) ≤ ((((230911510231 : ℚ) / 549755813888) : ℚ) : ℝ) :=
  offset ((1 : ℚ) / 200) ((0 : ℚ) / 1) ((230911510231 : ℚ) / 549755813888) (by decide +kernel)

theorem off1 (c : Covers) : ∀ y ∈ Ico (98749/1000000 : ℝ) (999/1000),
    Generic.nearLim dc72 AssemblyBindings.X1 ((((1 : ℚ) / 200) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ) y ≤ ((((-630013205 : ℚ) / 1073741824) : ℚ) : ℝ) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h := c.off1 y
    (by norm_num [Set.mem_Icc]; exact ⟨hy.1, hy.2.le⟩)
  rw [nearIdentity ((1 : ℚ) / 200) ((0 : ℚ) / 1) hy01, if_neg (by linarith [hy.2] : ¬ (1-1/1024:ℝ) < y)]
  have hk := kappa1
  push_cast at h hk ⊢
  linarith only [h, hk]

theorem top1 (c : Covers) : ∀ y ∈ Ico (999/1000 : ℝ) 1,
    Generic.nearLim dc72 AssemblyBindings.X1 ((((1 : ℚ) / 200) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ) y ≤
      ((((-1027331989 : ℚ) / 1073741824) : ℚ) : ℝ) + (5/11 * ((((0 : ℚ) / 1) : ℚ) : ℝ)) * (-Real.log (1-y^2)) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hs := splitTop ((1 : ℚ) / 200) ((0 : ℚ) / 1) (by decide +kernel) (y := y) ⟨by linarith [hy.1], hy.2⟩
  rw [nearIdentity ((1 : ℚ) / 200) ((0 : ℚ) / 1) hy01, hs]
  have hk := kappa1
  have hcs : (AssemblyBindings.X1.CSP : ℝ) / 72 = ((((5 : ℚ) / 288) : ℚ) : ℝ) := by
    change ((T1.params.CSP : ℚ) : ℝ) / 72 = _
    norm_num [T1.params]
  rw [hcs]
  rcases le_or_gt y (1 - 1/1024 : ℝ) with hj | hj
  · have h := c.top1 y
      (by norm_num [Set.mem_Icc]; exact ⟨hy.1, by linarith⟩)
    rw [if_neg (not_lt.mpr hj)]
    push_cast at h hk ⊢
    linarith only [h, hk]
  · have h := c.jump1 y
      (by norm_num [Set.mem_Icc]; exact ⟨by linarith, hy.2.le⟩)
    rw [if_pos hj]
    push_cast at h hk ⊢
    linarith only [h, hk]
#print axioms off1
#print axioms top1

private theorem kappa2 : nearK T1.trial ((1 : ℚ) / 200) ((1 : ℚ) / 200) ≤ ((((472302217003 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  offset ((1 : ℚ) / 200) ((1 : ℚ) / 200) ((472302217003 : ℚ) / 1099511627776) (by decide +kernel)

theorem off2 (c : Covers) : ∀ y ∈ Ico (98749/1000000 : ℝ) (999/1000),
    Generic.nearLim dc72 AssemblyBindings.X1 ((((1 : ℚ) / 200) : ℚ) : ℝ) ((((1 : ℚ) / 200) : ℚ) : ℝ) y ≤ ((((-618669125 : ℚ) / 1073741824) : ℚ) : ℝ) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h := c.off2 y
    (by norm_num [Set.mem_Icc]; exact ⟨hy.1, hy.2.le⟩)
  rw [nearIdentity ((1 : ℚ) / 200) ((1 : ℚ) / 200) hy01, if_neg (by linarith [hy.2] : ¬ (1-1/1024:ℝ) < y)]
  have hk := kappa2
  push_cast at h hk ⊢
  linarith only [h, hk]

theorem top2 (c : Covers) : ∀ y ∈ Ico (999/1000 : ℝ) 1,
    Generic.nearLim dc72 AssemblyBindings.X1 ((((1 : ℚ) / 200) : ℚ) : ℝ) ((((1 : ℚ) / 200) : ℚ) : ℝ) y ≤
      ((((-1017098399 : ℚ) / 1073741824) : ℚ) : ℝ) + (5/11 * ((((1 : ℚ) / 200) : ℚ) : ℝ)) * (-Real.log (1-y^2)) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hs := splitTop ((1 : ℚ) / 200) ((1 : ℚ) / 200) (by decide +kernel) (y := y) ⟨by linarith [hy.1], hy.2⟩
  rw [nearIdentity ((1 : ℚ) / 200) ((1 : ℚ) / 200) hy01, hs]
  have hk := kappa2
  have hcs : (AssemblyBindings.X1.CSP : ℝ) / 72 = ((((5 : ℚ) / 288) : ℚ) : ℝ) := by
    change ((T1.params.CSP : ℚ) : ℝ) / 72 = _
    norm_num [T1.params]
  rw [hcs]
  rcases le_or_gt y (1 - 1/1024 : ℝ) with hj | hj
  · have h := c.top2 y
      (by norm_num [Set.mem_Icc]; exact ⟨hy.1, by linarith⟩)
    rw [if_neg (not_lt.mpr hj)]
    push_cast at h hk ⊢
    linarith only [h, hk]
  · have h := c.jump2 y
      (by norm_num [Set.mem_Icc]; exact ⟨by linarith, hy.2.le⟩)
    rw [if_pos hj]
    push_cast at h hk ⊢
    linarith only [h, hk]
#print axioms off2
#print axioms top2

private theorem kappa3 : nearK T1.trial ((1 : ℚ) / 16) ((0 : ℚ) / 1) ≤ ((((483734067775 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  offset ((1 : ℚ) / 16) ((0 : ℚ) / 1) ((483734067775 : ℚ) / 1099511627776) (by decide +kernel)

theorem off3 (c : Covers) : ∀ y ∈ Ico (98749/1000000 : ℝ) (999/1000),
    Generic.nearLim dc72 AssemblyBindings.X1 ((((1 : ℚ) / 16) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ) y ≤ ((((-593984413 : ℚ) / 1073741824) : ℚ) : ℝ) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h := c.off3 y
    (by norm_num [Set.mem_Icc]; exact ⟨hy.1, hy.2.le⟩)
  rw [nearIdentity ((1 : ℚ) / 16) ((0 : ℚ) / 1) hy01, if_neg (by linarith [hy.2] : ¬ (1-1/1024:ℝ) < y)]
  have hk := kappa3
  push_cast at h hk ⊢
  linarith only [h, hk]

theorem top3 (c : Covers) : ∀ y ∈ Ico (999/1000 : ℝ) 1,
    Generic.nearLim dc72 AssemblyBindings.X1 ((((1 : ℚ) / 16) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ) y ≤
      ((((-492276207 : ℚ) / 536870912) : ℚ) : ℝ) + (5/11 * ((((0 : ℚ) / 1) : ℚ) : ℝ)) * (-Real.log (1-y^2)) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hs := splitTop ((1 : ℚ) / 16) ((0 : ℚ) / 1) (by decide +kernel) (y := y) ⟨by linarith [hy.1], hy.2⟩
  rw [nearIdentity ((1 : ℚ) / 16) ((0 : ℚ) / 1) hy01, hs]
  have hk := kappa3
  have hcs : (AssemblyBindings.X1.CSP : ℝ) / 72 = ((((5 : ℚ) / 288) : ℚ) : ℝ) := by
    change ((T1.params.CSP : ℚ) : ℝ) / 72 = _
    norm_num [T1.params]
  rw [hcs]
  rcases le_or_gt y (1 - 1/1024 : ℝ) with hj | hj
  · have h := c.top3 y
      (by norm_num [Set.mem_Icc]; exact ⟨hy.1, by linarith⟩)
    rw [if_neg (not_lt.mpr hj)]
    push_cast at h hk ⊢
    linarith only [h, hk]
  · have h := c.jump3 y
      (by norm_num [Set.mem_Icc]; exact ⟨by linarith, hy.2.le⟩)
    rw [if_pos hj]
    push_cast at h hk ⊢
    linarith only [h, hk]
#print axioms off3
#print axioms top3

private theorem kappa4 : nearK T1.trial ((1 : ℚ) / 16) ((1 : ℚ) / 16) ≤ ((((614724024535 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  offset ((1 : ℚ) / 16) ((1 : ℚ) / 16) ((614724024535 : ℚ) / 1099511627776) (by decide +kernel)

theorem off4 (c : Covers) : ∀ y ∈ Ico (98749/1000000 : ℝ) (999/1000),
    Generic.nearLim dc72 AssemblyBindings.X1 ((((1 : ℚ) / 16) : ℚ) : ℝ) ((((1 : ℚ) / 16) : ℚ) : ℝ) y ≤ ((((-225764819 : ℚ) / 536870912) : ℚ) : ℝ) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h := c.off4 y
    (by norm_num [Set.mem_Icc]; exact ⟨hy.1, hy.2.le⟩)
  rw [nearIdentity ((1 : ℚ) / 16) ((1 : ℚ) / 16) hy01, if_neg (by linarith [hy.2] : ¬ (1-1/1024:ℝ) < y)]
  have hk := kappa4
  push_cast at h hk ⊢
  linarith only [h, hk]

theorem top4 (c : Covers) : ∀ y ∈ Ico (999/1000 : ℝ) 1,
    Generic.nearLim dc72 AssemblyBindings.X1 ((((1 : ℚ) / 16) : ℚ) : ℝ) ((((1 : ℚ) / 16) : ℚ) : ℝ) y ≤
      ((((-428316267 : ℚ) / 536870912) : ℚ) : ℝ) + (5/11 * ((((1 : ℚ) / 16) : ℚ) : ℝ)) * (-Real.log (1-y^2)) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hs := splitTop ((1 : ℚ) / 16) ((1 : ℚ) / 16) (by decide +kernel) (y := y) ⟨by linarith [hy.1], hy.2⟩
  rw [nearIdentity ((1 : ℚ) / 16) ((1 : ℚ) / 16) hy01, hs]
  have hk := kappa4
  have hcs : (AssemblyBindings.X1.CSP : ℝ) / 72 = ((((5 : ℚ) / 288) : ℚ) : ℝ) := by
    change ((T1.params.CSP : ℚ) : ℝ) / 72 = _
    norm_num [T1.params]
  rw [hcs]
  rcases le_or_gt y (1 - 1/1024 : ℝ) with hj | hj
  · have h := c.top4 y
      (by norm_num [Set.mem_Icc]; exact ⟨hy.1, by linarith⟩)
    rw [if_neg (not_lt.mpr hj)]
    push_cast at h hk ⊢
    linarith only [h, hk]
  · have h := c.jump4 y
      (by norm_num [Set.mem_Icc]; exact ⟨by linarith, hy.2.le⟩)
    rw [if_pos hj]
    push_cast at h hk ⊢
    linarith only [h, hk]
#print axioms off4
#print axioms top4
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCorners1
