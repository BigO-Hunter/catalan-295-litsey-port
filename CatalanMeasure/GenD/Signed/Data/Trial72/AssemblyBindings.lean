module
public import CatalanMeasure.GenD.Signed.Data.Trial72.T0Binding
public import CatalanMeasure.GenD.Signed.Data.Trial72.T0FieldBinding
public import CatalanMeasure.GenD.Signed.Data.Trial72.T1Binding
public import CatalanMeasure.GenD.Signed.Data.Trial72.T1FieldBinding
public import CatalanMeasure.GenD.Signed.Data.Trial72.T2Binding
public import CatalanMeasure.GenD.Signed.Data.Trial72.T2FieldBinding
public import CatalanMeasure.GenD.Signed.Data.Trial72.SheetBindings
public import CatalanMeasure.GenD.Signed.Data.Assembly.RowsCell
public import CatalanMeasure.GenD.Signed.Data.Assembly.Near
public import CatalanMeasure.GenD.Signed.Data.Assembly.Link
public import CatalanMeasure.GenD.Signed.Davis.Tail130Bounds
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Assembly CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.Parametric CatalanMeasure.GenD.Analytic OAI.InternalCatalan
open Davis.ScalarInstance72 SheetBindings ReferenceData
noncomputable section
def toAssembly (X : Core.FamPar) : FamPar := ⟨X.T, X.bs, X.CSP, X.Cb⟩
theorem famD_eq (X : Core.FamPar) (N : ℕ) :
    Generic.famD dc72 (toAssembly X) N = Core.famD dc72 X N := rfl
def X0 : FamPar := toAssembly T0.params
def X1 : FamPar := toAssembly T1.params
def X2 : FamPar := toAssembly T2.params
abbrev XA : Fin 2 → FamPar := ![X0,X1]
abbrev XB : Fin 2 → FamPar := ![X1,X2]
abbrev DA : Fin 2 → ℕ → SignedData := ![T0.D,T1.D]
abbrev DB : Fin 2 → ℕ → SignedData := ![T1.D,T2.D]
theorem hDA (i : Fin 2) (N : ℕ) : DA i N = Generic.famD dc72 (XA i) N := by
  fin_cases i <;> rfl
theorem hDB (i : Fin 2) (N : ℕ) : DB i N = Generic.famD dc72 (XB i) N := by
  fin_cases i <;> rfl

abbrev geometry72 := Davis.Tail130Bounds.geometry72
/-- This record prevents a legacy trial family from satisfying the near factory
by accident. All endpoint objects are the hash-pinned Trial72 family above. -/
structure InputsMatch (I : Generic.InputsAsym dc72 geometry72) : Prop where
  hXA : I.XA = XA
  hXB : I.XB = XB
  htarget : I.target = target72
  hcost : I.cost = cost72
  halpha : I.α1 = 1/16
  hlo : I.lo = ![0,1/200]
  hhi : I.hi = ![1/200,1/16]
  heps : I.epsSplit = ![1/10,1/10]

theorem matched_DA (I : Generic.InputsAsym dc72 geometry72) (h : InputsMatch I) (i : Fin 2) (N : ℕ) :
    I.DA i N = DA i N := by rw [I.hDA,h.hXA]; exact (hDA i N).symm
theorem matched_DB (I : Generic.InputsAsym dc72 geometry72) (h : InputsMatch I) (i : Fin 2) (N : ℕ) :
    I.DB i N = DB i N := by rw [I.hDB,h.hXB]; exact (hDB i N).symm

theorem hnear (I : Generic.InputsAsym dc72 geometry72) (h : InputsMatch I)
    (R : Generic.RowsAsym dc72 geometry72 I)
    {targetOld costOld MX MY normCap fieldCap residual nearCap δ e : ℝ}
    (Cref : SecondTrialCertificate 0 targetOld costOld MX MY normCap fieldCap residual nearCap)
    (Bref : SecondDecayBounds MX MY residual nearCap)
    (hδ : 0 < δ) (he : e ∈ Ioo (0:ℝ) (1/8))
    (hec : e*(4*(∑' j,|secondP j|)+4*(∑' j,|secondV j|)+|secondP 1|+20)<δ/2)
    (L : LinkCert (Generic.phase2Asym dc72 geometry72 I R) dc72.toParameters
      targetOld residual nearCap costOld G72 (nearReference Cref Bref) δ e I.target (72*cost72)) :
    FreeNearBound dc72.toParameters G72 (NodeSub Davis.tau72) target72 (72*cost72) (1/16) := by
  have hc : I.cost*(dc72.n0:ℝ) ≤ 72*cost72 := by rw [h.hcost,dc72_n0]; ring_nf
  simpa only [h.htarget,h.halpha] using
    Generic.hnear_asym dc72 geometry72 I R (nearReference Cref Bref) hδ he hec hc L

end
end CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings

namespace CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
noncomputable section
theorem hok0 : ∀ C : ℝ, ((X0.Cb:ℚ):ℝ) ≤ C → X0.T.DataOK C := fun C h => T0.dataOK h
theorem hRt0 : X0.T.R.tail = [] := rfl
abbrev rowSN0 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowSN_cell dc72 X0 hok0 hRt0
abbrev rowSC0 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowSC_cell dc72 X0 hok0
abbrev rowSP0 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowSP_cell dc72 X0 hok0 hRt0
abbrev rowSM0 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowNeg_cell dc72 X0 hok0 hRt0
abbrev rowSPM0 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowPos_cell dc72 X0 hok0 hRt0
abbrev rowSPMTop0 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowPosTop_cell dc72 X0 hok0 hRt0
abbrev rowNear0 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowNear_cell dc72 X0 hok0 hRt0
abbrev rowNearTop0 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowNearTop_cell dc72 X0 hok0 hRt0
theorem hok1 : ∀ C : ℝ, ((X1.Cb:ℚ):ℝ) ≤ C → X1.T.DataOK C := fun C h => T1.dataOK h
theorem hRt1 : X1.T.R.tail = [] := rfl
abbrev rowSN1 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowSN_cell dc72 X1 hok1 hRt1
abbrev rowSC1 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowSC_cell dc72 X1 hok1
abbrev rowSP1 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowSP_cell dc72 X1 hok1 hRt1
abbrev rowSM1 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowNeg_cell dc72 X1 hok1 hRt1
abbrev rowSPM1 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowPos_cell dc72 X1 hok1 hRt1
abbrev rowSPMTop1 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowPosTop_cell dc72 X1 hok1 hRt1
abbrev rowNear1 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowNear_cell dc72 X1 hok1 hRt1
abbrev rowNearTop1 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowNearTop_cell dc72 X1 hok1 hRt1
theorem hok2 : ∀ C : ℝ, ((X2.Cb:ℚ):ℝ) ≤ C → X2.T.DataOK C := fun C h => T2.dataOK h
theorem hRt2 : X2.T.R.tail = [] := rfl
abbrev rowSN2 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowSN_cell dc72 X2 hok2 hRt2
abbrev rowSC2 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowSC_cell dc72 X2 hok2
abbrev rowSP2 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowSP_cell dc72 X2 hok2 hRt2
abbrev rowSM2 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowNeg_cell dc72 X2 hok2 hRt2
abbrev rowSPM2 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowPos_cell dc72 X2 hok2 hRt2
abbrev rowSPMTop2 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowPosTop_cell dc72 X2 hok2 hRt2
abbrev rowNear2 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowNear_cell dc72 X2 hok2 hRt2
abbrev rowNearTop2 := CatalanMeasure.GenD.Signed.Data.Assembly.Generic.rowNearTop_cell dc72 X2 hok2 hRt2
end
end CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings

namespace CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Assembly
noncomputable section

theorem scIdentity0 (x : ℝ) :
    cfLim dc72.toParameters x + 2 * X0.T.form.v.Tform x =
      fieldTower T0.scFq (poleF T0.scFq.poles) 0 x + scK T0.trial := by
  simpa [cfLim_eq, X0, toAssembly, T0.params, dc72] using T0.hidSC x
theorem snIdentity0 (x : ℝ) :
    fNegLim X0.T.form (rfLim dc72.toParameters) x =
      fieldTower T0.snFq (poleF T0.snFq.poles) 0 x + snK T0.trial := by
  simpa [rfLim_eq, X0, toAssembly, T0.params, dc72] using T0.hidSN x
theorem smIdentity0 (x : ℝ) :
    fNegMLim X0.T.form (fun y => -(((dc72.n0:ℝ)-dc72.g0)/dc72.n0)*Real.log (1+y^2)) x =
      fieldTower T0.smFq (poleF T0.smFq.poles) 0 x + smK T0.trial := by
  simpa [rmQ, X0, toAssembly, T0.params, dc72] using T0.hidSM x

theorem boundSC0 (Fc : FieldQ) (hpl : T0.scFq.plogs = Fc.plogs) (hpo : T0.scFq.poles = Fc.poles)
    {δ : ℚ} (hδ : l1Q T0.scFq.poly Fc.poly ≤ δ) {T TR c lo : ℝ}
    (hsup : ∀ x ∈ Ioo (0:ℝ) 1, fieldTower Fc (poleF Fc.poles) 0 x ≤ T)
    (hlo0 : 0 < lo) (hlo1 : lo < 1)
    (hend : ∀ x ∈ Icc lo 1, x ≠ 1 → fieldTower Fc (poleF Fc.poles) 0 x ≤ TR+c*Real.log |x-1|)
    (hc : 0 < c) (hcmp : TR+c*Real.log (1-lo) ≤ T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0:ℝ) 1,
      (T0.D N).fCol x ≤ T+δ+scK T0.trial+ε := by
  simpa only [T0.D, X0, toAssembly] using
    Generic.rowSC_cell dc72 X0 hok0 T0.scFq Fc (scIdentity0) hpl hpo hδ
      hsup hlo0 hlo1 hend hc hcmp

theorem boundSN0 (Fc : FieldQ) (hpl : T0.snFq.plogs = Fc.plogs) (hpo : T0.snFq.poles = Fc.poles)
    {δ : ℚ} (hδ : l1Q T0.snFq.poly Fc.poly ≤ δ) {T TR c lo : ℝ}
    (hsup : ∀ x ∈ Ioo (-1:ℝ) 0, fieldTower Fc (poleF Fc.poles) 0 x ≤ T)
    (hlo0 : -1 < lo) (hlo1 : lo < 0)
    (hend : ∀ x ∈ Icc lo 0, x ≠ 0 → fieldTower Fc (poleF Fc.poles) 0 x ≤ TR+c*Real.log |x-0|)
    (hc : 0 < c) (hcmp : TR+c*Real.log (-lo) ≤ T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1:ℝ) 0,
      (T0.D N).fNeg x ≤ T+δ+snK T0.trial+ε := by
  simpa only [T0.D, X0, toAssembly] using
    Generic.rowSN_cell dc72 X0 hok0 hRt0 T0.snFq Fc (snIdentity0) hpl hpo hδ
      hsup hlo0 hlo1 hend hc hcmp

theorem boundSM0 (Fc : FieldQ) (hpl : T0.smFq.plogs = Fc.plogs) (hpo : T0.smFq.poles = Fc.poles)
    {δ : ℚ} (hδ : l1Q T0.smFq.poly Fc.poly ≤ δ) {T : ℝ}
    (hsup : ∀ x ∈ Ioc (-1:ℝ) (-(19501/100000:ℝ)), fieldTower Fc (poleF Fc.poles) 0 x ≤ T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1:ℝ) 0, x ≤ -(19501/100000:ℝ) →
      (T0.D N).fNegM (CatalanMeasure.Parametric.groupedMarkedField dc72.toParameters N) x ≤
        T+δ+smK T0.trial+ε := by
  simpa only [T0.D, X0, toAssembly] using
    Generic.rowNeg_cell dc72 X0 hok0 hRt0 T0.smFq Fc (smIdentity0) hpl hpo hδ
      (by norm_num : (-1:ℝ)< -(19501/100000:ℝ)) (by norm_num : -(19501/100000:ℝ)<0) hsup

theorem scIdentity1 (x : ℝ) :
    cfLim dc72.toParameters x + 2 * X1.T.form.v.Tform x =
      fieldTower T1.scFq (poleF T1.scFq.poles) 0 x + scK T1.trial := by
  simpa [cfLim_eq, X1, toAssembly, T1.params, dc72] using T1.hidSC x
theorem snIdentity1 (x : ℝ) :
    fNegLim X1.T.form (rfLim dc72.toParameters) x =
      fieldTower T1.snFq (poleF T1.snFq.poles) 0 x + snK T1.trial := by
  simpa [rfLim_eq, X1, toAssembly, T1.params, dc72] using T1.hidSN x
theorem smIdentity1 (x : ℝ) :
    fNegMLim X1.T.form (fun y => -(((dc72.n0:ℝ)-dc72.g0)/dc72.n0)*Real.log (1+y^2)) x =
      fieldTower T1.smFq (poleF T1.smFq.poles) 0 x + smK T1.trial := by
  simpa [rmQ, X1, toAssembly, T1.params, dc72] using T1.hidSM x

theorem boundSC1 (Fc : FieldQ) (hpl : T1.scFq.plogs = Fc.plogs) (hpo : T1.scFq.poles = Fc.poles)
    {δ : ℚ} (hδ : l1Q T1.scFq.poly Fc.poly ≤ δ) {T TR c lo : ℝ}
    (hsup : ∀ x ∈ Ioo (0:ℝ) 1, fieldTower Fc (poleF Fc.poles) 0 x ≤ T)
    (hlo0 : 0 < lo) (hlo1 : lo < 1)
    (hend : ∀ x ∈ Icc lo 1, x ≠ 1 → fieldTower Fc (poleF Fc.poles) 0 x ≤ TR+c*Real.log |x-1|)
    (hc : 0 < c) (hcmp : TR+c*Real.log (1-lo) ≤ T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0:ℝ) 1,
      (T1.D N).fCol x ≤ T+δ+scK T1.trial+ε := by
  simpa only [T1.D, X1, toAssembly] using
    Generic.rowSC_cell dc72 X1 hok1 T1.scFq Fc (scIdentity1) hpl hpo hδ
      hsup hlo0 hlo1 hend hc hcmp

theorem boundSN1 (Fc : FieldQ) (hpl : T1.snFq.plogs = Fc.plogs) (hpo : T1.snFq.poles = Fc.poles)
    {δ : ℚ} (hδ : l1Q T1.snFq.poly Fc.poly ≤ δ) {T TR c lo : ℝ}
    (hsup : ∀ x ∈ Ioo (-1:ℝ) 0, fieldTower Fc (poleF Fc.poles) 0 x ≤ T)
    (hlo0 : -1 < lo) (hlo1 : lo < 0)
    (hend : ∀ x ∈ Icc lo 0, x ≠ 0 → fieldTower Fc (poleF Fc.poles) 0 x ≤ TR+c*Real.log |x-0|)
    (hc : 0 < c) (hcmp : TR+c*Real.log (-lo) ≤ T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1:ℝ) 0,
      (T1.D N).fNeg x ≤ T+δ+snK T1.trial+ε := by
  simpa only [T1.D, X1, toAssembly] using
    Generic.rowSN_cell dc72 X1 hok1 hRt1 T1.snFq Fc (snIdentity1) hpl hpo hδ
      hsup hlo0 hlo1 hend hc hcmp

theorem boundSM1 (Fc : FieldQ) (hpl : T1.smFq.plogs = Fc.plogs) (hpo : T1.smFq.poles = Fc.poles)
    {δ : ℚ} (hδ : l1Q T1.smFq.poly Fc.poly ≤ δ) {T : ℝ}
    (hsup : ∀ x ∈ Ioc (-1:ℝ) (-(19501/100000:ℝ)), fieldTower Fc (poleF Fc.poles) 0 x ≤ T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1:ℝ) 0, x ≤ -(19501/100000:ℝ) →
      (T1.D N).fNegM (CatalanMeasure.Parametric.groupedMarkedField dc72.toParameters N) x ≤
        T+δ+smK T1.trial+ε := by
  simpa only [T1.D, X1, toAssembly] using
    Generic.rowNeg_cell dc72 X1 hok1 hRt1 T1.smFq Fc (smIdentity1) hpl hpo hδ
      (by norm_num : (-1:ℝ)< -(19501/100000:ℝ)) (by norm_num : -(19501/100000:ℝ)<0) hsup

theorem scIdentity2 (x : ℝ) :
    cfLim dc72.toParameters x + 2 * X2.T.form.v.Tform x =
      fieldTower T2.scFq (poleF T2.scFq.poles) 0 x + scK T2.trial := by
  simpa [cfLim_eq, X2, toAssembly, T2.params, dc72] using T2.hidSC x
theorem snIdentity2 (x : ℝ) :
    fNegLim X2.T.form (rfLim dc72.toParameters) x =
      fieldTower T2.snFq (poleF T2.snFq.poles) 0 x + snK T2.trial := by
  simpa [rfLim_eq, X2, toAssembly, T2.params, dc72] using T2.hidSN x
theorem smIdentity2 (x : ℝ) :
    fNegMLim X2.T.form (fun y => -(((dc72.n0:ℝ)-dc72.g0)/dc72.n0)*Real.log (1+y^2)) x =
      fieldTower T2.smFq (poleF T2.smFq.poles) 0 x + smK T2.trial := by
  simpa [rmQ, X2, toAssembly, T2.params, dc72] using T2.hidSM x

theorem boundSC2 (Fc : FieldQ) (hpl : T2.scFq.plogs = Fc.plogs) (hpo : T2.scFq.poles = Fc.poles)
    {δ : ℚ} (hδ : l1Q T2.scFq.poly Fc.poly ≤ δ) {T TR c lo : ℝ}
    (hsup : ∀ x ∈ Ioo (0:ℝ) 1, fieldTower Fc (poleF Fc.poles) 0 x ≤ T)
    (hlo0 : 0 < lo) (hlo1 : lo < 1)
    (hend : ∀ x ∈ Icc lo 1, x ≠ 1 → fieldTower Fc (poleF Fc.poles) 0 x ≤ TR+c*Real.log |x-1|)
    (hc : 0 < c) (hcmp : TR+c*Real.log (1-lo) ≤ T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0:ℝ) 1,
      (T2.D N).fCol x ≤ T+δ+scK T2.trial+ε := by
  simpa only [T2.D, X2, toAssembly] using
    Generic.rowSC_cell dc72 X2 hok2 T2.scFq Fc (scIdentity2) hpl hpo hδ
      hsup hlo0 hlo1 hend hc hcmp

theorem boundSN2 (Fc : FieldQ) (hpl : T2.snFq.plogs = Fc.plogs) (hpo : T2.snFq.poles = Fc.poles)
    {δ : ℚ} (hδ : l1Q T2.snFq.poly Fc.poly ≤ δ) {T TR c lo : ℝ}
    (hsup : ∀ x ∈ Ioo (-1:ℝ) 0, fieldTower Fc (poleF Fc.poles) 0 x ≤ T)
    (hlo0 : -1 < lo) (hlo1 : lo < 0)
    (hend : ∀ x ∈ Icc lo 0, x ≠ 0 → fieldTower Fc (poleF Fc.poles) 0 x ≤ TR+c*Real.log |x-0|)
    (hc : 0 < c) (hcmp : TR+c*Real.log (-lo) ≤ T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1:ℝ) 0,
      (T2.D N).fNeg x ≤ T+δ+snK T2.trial+ε := by
  simpa only [T2.D, X2, toAssembly] using
    Generic.rowSN_cell dc72 X2 hok2 hRt2 T2.snFq Fc (snIdentity2) hpl hpo hδ
      hsup hlo0 hlo1 hend hc hcmp

theorem boundSM2 (Fc : FieldQ) (hpl : T2.smFq.plogs = Fc.plogs) (hpo : T2.smFq.poles = Fc.poles)
    {δ : ℚ} (hδ : l1Q T2.smFq.poly Fc.poly ≤ δ) {T : ℝ}
    (hsup : ∀ x ∈ Ioc (-1:ℝ) (-(19501/100000:ℝ)), fieldTower Fc (poleF Fc.poles) 0 x ≤ T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1:ℝ) 0, x ≤ -(19501/100000:ℝ) →
      (T2.D N).fNegM (CatalanMeasure.Parametric.groupedMarkedField dc72.toParameters N) x ≤
        T+δ+smK T2.trial+ε := by
  simpa only [T2.D, X2, toAssembly] using
    Generic.rowNeg_cell dc72 X2 hok2 hRt2 T2.smFq Fc (smIdentity2) hpl hpo hδ
      (by norm_num : (-1:ℝ)< -(19501/100000:ℝ)) (by norm_num : -(19501/100000:ℝ)<0) hsup
end
end CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings

namespace CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
open Filter Set CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly
noncomputable section
theorem spikeEnv0 {S0 : ℝ}
    (hfr : ∀ x ∈ Icc (-1:ℝ) 1, frLim T0.trial.form x ≤ S0)
    (hgap : S0 < T0.trial.Sup) :
    ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (T0.D N)) := by
  simpa only [T0.D, X0, toAssembly] using
    Generic.famD_spikeEnv dc72 X0 hok0 hRt0 hfr hgap
theorem spikeEnv1 {S0 : ℝ}
    (hfr : ∀ x ∈ Icc (-1:ℝ) 1, frLim T1.trial.form x ≤ S0)
    (hgap : S0 < T1.trial.Sup) :
    ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (T1.D N)) := by
  simpa only [T1.D, X1, toAssembly] using
    Generic.famD_spikeEnv dc72 X1 hok1 hRt1 hfr hgap
theorem spikeEnv2 {S0 : ℝ}
    (hfr : ∀ x ∈ Icc (-1:ℝ) 1, frLim T2.trial.form x ≤ S0)
    (hgap : S0 < T2.trial.Sup) :
    ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (T2.D N)) := by
  simpa only [T2.D, X2, toAssembly] using
    Generic.famD_spikeEnv dc72 X2 hok2 hRt2 hfr hgap
end
end CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyBindings
