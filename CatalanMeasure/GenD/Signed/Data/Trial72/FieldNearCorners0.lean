module
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearLimit0
public import CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCorners0
open Set CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
open AssemblyBindings
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000


structure Covers : Prop where
  off0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ)
  top0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-751264128269 : ℚ) / 549755813888) : ℚ) : ℝ)
  jump0 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-6847276500341 : ℚ) / 4947802324992) : ℚ) : ℝ)
  off1 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ)
  top1 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-187578040361 : ℚ) / 137438953472) : ℚ) : ℝ)
  jump1 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ)
  off2 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ)
  top2 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1500624323269 : ℚ) / 1099511627776) : ℚ) : ℝ)
  jump2 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ)

private theorem kappa0 : nearK T0.trial ((0 : ℚ) / 1) ((0 : ℚ) / 1) ≤ ((((221658151693 : ℚ) / 549755813888) : ℚ) : ℝ) :=
  offset ((0 : ℚ) / 1) ((0 : ℚ) / 1) ((221658151693 : ℚ) / 549755813888) (by decide +kernel)

theorem off0 (c : Covers) : ∀ y ∈ Ico (98749/1000000 : ℝ) (999/1000),
    Generic.nearLim dc72 AssemblyBindings.X0 ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ) y ≤ ((((-158556287 : ℚ) / 268435456) : ℚ) : ℝ) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h := c.off0 y
    (by norm_num [Set.mem_Icc]; exact ⟨hy.1, hy.2.le⟩)
  rw [nearIdentity ((0 : ℚ) / 1) ((0 : ℚ) / 1) hy01, if_neg (by linarith [hy.2] : ¬ (1-1/1024:ℝ) < y)]
  have hk := kappa0
  push_cast at h hk ⊢
  linarith only [h, hk]

theorem top0 (c : Covers) : ∀ y ∈ Ico (999/1000 : ℝ) 1,
    Generic.nearLim dc72 AssemblyBindings.X0 ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ) y ≤
      ((((-1034386673 : ℚ) / 1073741824) : ℚ) : ℝ) + (5/11 * ((((0 : ℚ) / 1) : ℚ) : ℝ)) * (-Real.log (1-y^2)) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hs := splitTop ((0 : ℚ) / 1) ((0 : ℚ) / 1) (by decide +kernel) (y := y) ⟨by linarith [hy.1], hy.2⟩
  rw [nearIdentity ((0 : ℚ) / 1) ((0 : ℚ) / 1) hy01, hs]
  have hk := kappa0
  have hcs : (AssemblyBindings.X0.CSP : ℝ) / 72 = ((((5 : ℚ) / 288) : ℚ) : ℝ) := by
    change ((T0.params.CSP : ℚ) : ℝ) / 72 = _
    norm_num [T0.params]
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

private theorem kappa1 : nearK T0.trial ((1 : ℚ) / 200) ((0 : ℚ) / 1) ≤ ((((55652701481 : ℚ) / 137438953472) : ℚ) : ℝ) :=
  offset ((1 : ℚ) / 200) ((0 : ℚ) / 1) ((55652701481 : ℚ) / 137438953472) (by decide +kernel)

theorem off1 (c : Covers) : ∀ y ∈ Ico (98749/1000000 : ℝ) (999/1000),
    Generic.nearLim dc72 AssemblyBindings.X0 ((((1 : ℚ) / 200) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ) y ≤ ((((-157774281 : ℚ) / 268435456) : ℚ) : ℝ) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h := c.off1 y
    (by norm_num [Set.mem_Icc]; exact ⟨hy.1, hy.2.le⟩)
  rw [nearIdentity ((1 : ℚ) / 200) ((0 : ℚ) / 1) hy01, if_neg (by linarith [hy.2] : ¬ (1-1/1024:ℝ) < y)]
  have hk := kappa1
  push_cast at h hk ⊢
  linarith only [h, hk]

theorem top1 (c : Covers) : ∀ y ∈ Ico (999/1000 : ℝ) 1,
    Generic.nearLim dc72 AssemblyBindings.X0 ((((1 : ℚ) / 200) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ) y ≤
      ((((-515333355 : ℚ) / 536870912) : ℚ) : ℝ) + (5/11 * ((((0 : ℚ) / 1) : ℚ) : ℝ)) * (-Real.log (1-y^2)) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hs := splitTop ((1 : ℚ) / 200) ((0 : ℚ) / 1) (by decide +kernel) (y := y) ⟨by linarith [hy.1], hy.2⟩
  rw [nearIdentity ((1 : ℚ) / 200) ((0 : ℚ) / 1) hy01, hs]
  have hk := kappa1
  have hcs : (AssemblyBindings.X0.CSP : ℝ) / 72 = ((((5 : ℚ) / 288) : ℚ) : ℝ) := by
    change ((T0.params.CSP : ℚ) : ℝ) / 72 = _
    norm_num [T0.params]
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

private theorem kappa2 : nearK T0.trial ((1 : ℚ) / 200) ((1 : ℚ) / 200) ≤ ((((455700808389 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  offset ((1 : ℚ) / 200) ((1 : ℚ) / 200) ((455700808389 : ℚ) / 1099511627776) (by decide +kernel)

theorem off2 (c : Covers) : ∀ y ∈ Ico (98749/1000000 : ℝ) (999/1000),
    Generic.nearLim dc72 AssemblyBindings.X0 ((((1 : ℚ) / 200) : ℚ) : ℝ) ((((1 : ℚ) / 200) : ℚ) : ℝ) y ≤ ((((-154938851 : ℚ) / 268435456) : ℚ) : ℝ) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h := c.off2 y
    (by norm_num [Set.mem_Icc]; exact ⟨hy.1, hy.2.le⟩)
  rw [nearIdentity ((1 : ℚ) / 200) ((1 : ℚ) / 200) hy01, if_neg (by linarith [hy.2] : ¬ (1-1/1024:ℝ) < y)]
  have hk := kappa2
  push_cast at h hk ⊢
  linarith only [h, hk]

theorem top2 (c : Covers) : ∀ y ∈ Ico (999/1000 : ℝ) 1,
    Generic.nearLim dc72 AssemblyBindings.X0 ((((1 : ℚ) / 200) : ℚ) : ℝ) ((((1 : ℚ) / 200) : ℚ) : ℝ) y ≤
      ((((-31888535 : ℚ) / 33554432) : ℚ) : ℝ) + (5/11 * ((((1 : ℚ) / 200) : ℚ) : ℝ)) * (-Real.log (1-y^2)) := by
  intro y hy
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hs := splitTop ((1 : ℚ) / 200) ((1 : ℚ) / 200) (by decide +kernel) (y := y) ⟨by linarith [hy.1], hy.2⟩
  rw [nearIdentity ((1 : ℚ) / 200) ((1 : ℚ) / 200) hy01, hs]
  have hk := kappa2
  have hcs : (AssemblyBindings.X0.CSP : ℝ) / 72 = ((((5 : ℚ) / 288) : ℚ) : ℝ) := by
    change ((T0.params.CSP : ℚ) : ℝ) / 72 = _
    norm_num [T0.params]
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
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCorners0
