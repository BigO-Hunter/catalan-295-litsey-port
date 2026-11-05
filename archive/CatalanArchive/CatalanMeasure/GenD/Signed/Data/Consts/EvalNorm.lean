module

public import CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.NormV
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.NormP

@[expose] public section

/-! D58 compatibility: the generic exact rational norm engine is in EvalNormCore. -/
namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalNorm
open CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.TaylorCell (vecAdd)
export CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore (
  tseqE fQE fQE_supp summable_add_fin normSq_add_fin qSq qTailRec qDot hornQ crossH qCross qCrossRec qCrossRec_eq sum_qCrossRec qCross_eq qSq_eq_sum qTailRec_eq_sum qDot_eq_sum trialSeqS_nil_eq summable_tail trialSeqS_succ trialSeqS_eq_add summable_trialSeqS getD_map_div perturb_seq normChkP norm_perturb_le_of_total norm_perturb_le_of_bounds norm_perturb_le vecAdd_nil_left norm_tail_of_bounds norm_tail_le
)

/-! ### 7. The Cert590 caps -/

/-- `‖v‖² ≤ Bf` for `v = v₅₉₀ + dv`. -/
theorem norm_v_le {dl : List ℚ} {Bf : ℚ}
    (h : normChkP CatalanMeasure.GenD.D58.Cert590.Vc dl CatalanMeasure.GenD.D58.Cert590.V
      CatalanMeasure.GenD.D58.Cert590.NV Bf = true) :
    barrierTrialNormSq (tseqE (fQE (vecAdd (CatalanMeasure.GenD.D58.Cert590.Vc.map
      (fun n : ℤ => (n : ℚ) / 2 ^ 40)) dl)) (CatalanMeasure.GenD.D58.Cert590.V.map TailQ.toC))
      ≤ (Bf : ℝ) :=
  norm_perturb_le CatalanMeasure.GenD.D58.Cert590.normV_le h

theorem norm_p_le {dl : List ℚ} {Bf : ℚ}
    (h : normChkP CatalanMeasure.GenD.D58.Cert590.Pc dl CatalanMeasure.GenD.D58.Cert590.P
      CatalanMeasure.GenD.D58.Cert590.NP Bf = true) :
    barrierTrialNormSq (tseqE (fQE (vecAdd (CatalanMeasure.GenD.D58.Cert590.Pc.map
      (fun n : ℤ => (n : ℚ) / 2 ^ 40)) dl)) (CatalanMeasure.GenD.D58.Cert590.P.map TailQ.toC))
      ≤ (Bf : ℝ) :=
  norm_perturb_le CatalanMeasure.GenD.D58.Cert590.normP_le h

end CatalanMeasure.GenD.Signed.Data.Consts.EvalNorm
