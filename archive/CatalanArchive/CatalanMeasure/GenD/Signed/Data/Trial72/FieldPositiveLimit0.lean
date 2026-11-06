module
public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldPositiveLimit0
open Set CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

abbrev terms : List LTerm := dilTermsS T0.trial.qT T0.trial.qTn

theorem spIdentity (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) :
    fPosLim AssemblyBindings.X0.T.form (rfLim dc72.toParameters) ((dc72.sp : ℝ) / dc72.n0)
      (Consts.bSeq AssemblyBindings.X0.bs) AssemblyBindings.X0.bs.length ((AssemblyBindings.X0.CSP : ℝ) / dc72.n0) (dc72.thetaL : ℝ) y =
      fieldTower T0.spFq (poleF T0.spFq.poles) 0 y + lfieldTower terms 0 y + spK T0.trial +
        ((AssemblyBindings.X0.CSP : ℝ) / dc72.n0) * (if 1 - (dc72.thetaL : ℝ) < y then 1 else 0) := by
  have h := T0.hidSP (csL := (AssemblyBindings.X0.CSP : ℝ) / dc72.n0) (θL := (dc72.thetaL : ℝ)) (ne_of_gt hy.1)
  have hr : rfLim dc72.toParameters = rfQ (3/8) (1/9) (97/72) := by
    rw [rfLim_eq]
    norm_num [dc72]
  have hσ : (dc72.sp : ℝ) / dc72.n0 = ((5/18 : ℚ) : ℝ) := by norm_num [dc72_n0, dc72]
  rw [hr, hσ]
  exact h

theorem spmIdentity (a : ℚ) (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) :
    Generic.posLim dc72 AssemblyBindings.X0 y + (11/8:ℝ) * (a : ℝ) * (-Real.log (1-y^2)) =
      fieldTower (T0.spmAt a) (poleF (T0.spmAt a).poles) 0 y + lfieldTower terms 0 y + spmK T0.trial +
        ((AssemblyBindings.X0.CSP : ℝ) / dc72.n0) * (if 1 - (dc72.thetaL : ℝ) < y then 1 else 0) := by
  have h := T0.spmIdentityAt a (csL := (AssemblyBindings.X0.CSP : ℝ) / dc72.n0) (θL := (dc72.thetaL : ℝ)) hy
  have hr : (fun z : ℝ => -(((dc72.n0 : ℝ) - dc72.g0) / dc72.n0) * Real.log (1 + z^2)) =
      rmQ (11/12) := by
    funext z
    simp only [rmQ, dc72_n0, dc72_g0, Nat.cast_ofNat]
    push_cast
    ring
  have hσ : (dc72.sp : ℝ) / dc72.n0 = ((5/18 : ℚ) : ℝ) := by norm_num [dc72_n0, dc72]
  unfold Generic.posLim
  rw [hr, hσ]
  have hrc : ((11/8 : ℚ) : ℝ) = (11/8 : ℝ) := by norm_num
  rw [hrc] at h
  exact h

private theorem enclosures :
    Encl (cSv T0.trial) (ivOf (some (219958300254890109,319))) ∧
    Encl (cTp T0.trial) (ivOf (some (-374182068496652202,281))) ∧
    Encl (cSa T0.trial) (ivOf (some (2781564582940640,40))) := by
  have ev : encS T0.trial.v.tail = some (219958300254890109,319) := KappaBasics.sV_checked
  have ep : encT T0.trial.p.tail = some (-374182068496652202,281) := KappaBasics.tP_checked
  have ea : encS T0.trial.a.tail = some (2781564582940640,40) := KappaBasics.sA0_checked
  have hv := encl_sConst T0.trial.v.tail
  have hp := encl_tConst T0.trial.p.tail
  have ha := encl_sConst T0.trial.a.tail
  rw [ev] at hv
  rw [ep] at hp
  rw [ea] at ha
  exact ⟨hv, hp, ha⟩

theorem spOffset : spK T0.trial ≤ ((((7021280931583 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  obtain ⟨hv,hp,ha⟩ := enclosures
  exact sp_le (η := T0.trial.η) (Sup := T0.trial.Sup) (B := ((7021280931583 : ℚ) / 1099511627776)) hv hp ha (by decide +kernel)

theorem spmOffset : spmK T0.trial ≤ ((((2619484754487 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  obtain ⟨_,hp,ha⟩ := enclosures
  exact spm_le (η := T0.trial.η) (Sup := T0.trial.Sup) (B := ((2619484754487 : ℚ) / 549755813888)) hp ha (by decide +kernel)

#print axioms spIdentity
#print axioms spmIdentity
#print axioms spOffset
#print axioms spmOffset
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldPositiveLimit0
