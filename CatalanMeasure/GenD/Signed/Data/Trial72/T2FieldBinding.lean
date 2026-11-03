module
public import CatalanMeasure.GenD.Signed.Data.Trial72.T2Fields
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed.Data.Trial72.T2
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert CatalanMeasure.Cert
noncomputable section
/-! The emitted nearFq/spmFq are at the trial's own alpha. Off-diagonal
threshold corners require these parameterized fields on the SAME frozen trial. -/
def nearAt (a b : ℚ) : FieldQ := nearFQ trial (rnFQ (11/12) (5/6)) aS rS bS (5/18) a b
def spmAt (a : ℚ) : FieldQ := spmFQ trial (rmFQ (11/12)) pT aS rS bS rr (5/18) (11/8) a
theorem nearIdentityAt (a b : ℚ) {csL θL x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    fNearMSLim trial.form (rnQ (11/12) (5/6)) a b ((5/18:ℚ):ℝ)
      (fQ bsL) bsL.length csL θL x =
      fieldTower (nearAt a b) (poleFn (nearAt a b).poles) 0 x +
        lfieldTower (scaleL (-1) (reflL (dilTermsS trial.qF trial.qFn))) 0 x +
        nearK trial a b + csL * (if 1-θL < x then 1 else 0) :=
  hid_near trial (fun y => (fval_rn _ _ y).symm) aS_eq rS_eq bS_eq rfl har rfl hx
theorem spmIdentityAt (a : ℚ) {csL θL x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    fPosMSLim trial.form (rmQ (11/12)) ((5/18:ℚ):ℝ) (fQ bsL) bsL.length csL θL x +
      ((11/8:ℚ):ℝ)*(a:ℝ)*(-Real.log (1-x^2)) =
      fieldTower (spmAt a) (poleFn (spmAt a).poles) 0 x +
        lfieldTower (dilTermsS trial.qT trial.qTn) 0 x + spmK trial +
        csL * (if 1-θL < x then 1 else 0) :=
  hid_spm trial (fun y => (fval_rm _ y).symm) pT_eq aS_eq rS_eq bS_eq rr_eq rfl har rfl hx
end
end CatalanMeasure.GenD.Signed.Data.Trial72.T2
