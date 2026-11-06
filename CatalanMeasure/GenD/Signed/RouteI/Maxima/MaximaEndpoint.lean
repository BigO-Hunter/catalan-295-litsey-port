module
public import CatalanMeasure.Cert.Cover
public import CatalanMeasure.CellCert.FieldsS
public import OAI.NumberTheory.Catalan.Energy.BarrierGlobalMaxReduction
-- Source-bound shared L125 body SHA256 4b17b8d6fc1f0f02813616007421f0a09cbb04a860af18e7faf6b63275c276f2
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: estimated <=149 K R4 reserve, generic+instance consumption unmeasured

set_option Elab.async false
set_option maxHeartbeats 800000
set_option profiler true
set_option profiler.threshold 0
open Set Filter CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open scoped Topology
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.EndpointLimits
noncomputable section

theorem row_endpoint_contract
    {alpha beta gamma : ℝ} {u v : ℕ → ℝ}
    (hu : Summable (fun k => |u k|)) (hv : Summable (fun k => |v k|))
    (ha : 0 < alpha) (hb : 0 < beta) :
    ContinuousOn (rowFieldG alpha beta gamma u v) (Ico (-1 : ℝ) 0) ∧
    ContinuousOn (rowFieldG alpha beta gamma u v) (Ioo (0 : ℝ) 1) ∧
    Tendsto (rowFieldG alpha beta gamma u v) (𝓝[<] 0) atBot ∧
    Tendsto (rowFieldG alpha beta gamma u v) (𝓝[>] 0) atBot ∧
    Tendsto (rowFieldG alpha beta gamma u v) (𝓝[<] 1) atBot := by
  have hr := rowRegG_continuousOn gamma hu hv
  have hz : ContinuousAt
      (fun x : ℝ => beta * Real.log (1-x) + rowRegG gamma u v x) 0 := by
    have hl : ContinuousAt (fun x : ℝ => Real.log (1-x)) 0 :=
      (continuousAt_const.sub continuousAt_id).log (by norm_num)
    exact (hl.const_mul beta).add (continuousOn_continuousAt_zero hr)
  have heq0 : rowFieldG alpha beta gamma u v =
      fun x => alpha * Real.log |x| + (beta * Real.log (1-x) + rowRegG gamma u v x) := by
    funext x; unfold rowFieldG; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hc := rowFieldGP_continuousOn alpha beta gamma false false hu hv
      (S := Ico (-1 : ℝ) 0)
      (by intro y hy; exact ⟨hy.1, by linarith [hy.2]⟩)
      (Or.inr (by simp)) (Or.inr (by norm_num))
    simpa only [rowFieldGP_false] using hc
  · have hc := rowFieldGP_continuousOn alpha beta gamma false false hu hv
      (S := Ioo (0 : ℝ) 1)
      (by intro y hy; exact ⟨by linarith [hy.1], hy.2.le⟩)
      (Or.inr (by simp)) (Or.inr (by simp))
    simpa only [rowFieldGP_false] using hc
  · have hl : Tendsto (fun x : ℝ => alpha * Real.log |x|) (𝓝[<] 0) atBot := by
      simpa only [Real.log_abs] using
        (Tendsto.const_mul_atBot ha Real.tendsto_log_nhdsLT_zero)
    rw [heq0]
    exact atBot_add_finite hl (hz.tendsto.mono_left nhdsWithin_le_nhds)
  · have hl : Tendsto (fun x : ℝ => alpha * Real.log |x|) (𝓝[>] 0) atBot := by
      simpa only [Real.log_abs] using
        (Tendsto.const_mul_atBot ha Real.tendsto_log_nhdsGT_zero)
    rw [heq0]
    exact atBot_add_finite hl (hz.tendsto.mono_left nhdsWithin_le_nhds)
  · have heq : rowFieldG alpha beta gamma u v =
        fun x => beta * Real.log (1-x) +
          (alpha * Real.log |x| + rowRegG gamma u v x) := by
      funext x; unfold rowFieldG; ring
    rw [heq]
    have hl := Tendsto.const_mul_atBot hb log_one_sub_tendsto
    have hc : ContinuousAt (fun x : ℝ => Real.log |x|) 1 := by
      simpa only [Real.log_abs] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0))
    have ht := ((hc.tendsto.mono_left nhdsWithin_le_nhds).const_mul alpha).add
      (continuousOn_tendsto_one_left hr)
    exact atBot_add_finite hl ht

theorem col_endpoint_contract {b q : ℝ} {v : ℕ → ℝ}
    (hv : Summable (fun k => |v k|)) (hb : 0<b) (hq : 0<q) :
    ContinuousOn (colFieldG b q v) (Ioo (0 : ℝ) 1) ∧
    Tendsto (colFieldG b q v) (𝓝[>] 0) atBot ∧
    Tendsto (colFieldG b q v) (𝓝[<] 1) atBot := by
  have hr := colRegG_continuousOn hv
  refine ⟨?_, ?_, ?_⟩
  · have hc := colFieldGP_continuousOn b q false false hv
      (S := Ioo (0 : ℝ) 1)
      (by intro y hy; exact ⟨by linarith [hy.1], hy.2.le⟩)
      (Or.inr (by simp)) (Or.inr (by simp))
    simpa only [colFieldGP_false] using hc
  · have hl := Tendsto.const_mul_atBot hb Real.tendsto_log_nhdsGT_zero
    have hc : ContinuousAt (fun x : ℝ => q*Real.log (1-x)+colRegG v x) 0 := by
      have hlog : ContinuousAt (fun x : ℝ => Real.log (1-x)) 0 :=
        (continuousAt_const.sub continuousAt_id).log (by norm_num)
      exact (hlog.const_mul q).add (continuousOn_continuousAt_zero hr)
    have heq : colFieldG b q v = fun x => b*Real.log x+(q*Real.log (1-x)+colRegG v x) := by
      funext x; unfold colFieldG; ring
    rw [heq]
    exact atBot_add_finite hl (hc.tendsto.mono_left nhdsWithin_le_nhds)
  · have hl := Tendsto.const_mul_atBot hq log_one_sub_tendsto
    have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1)
    have ht := (hlog.const_mul b).add (continuousOn_tendsto_one_left hr)
    have heq : colFieldG b q v = fun x => q*Real.log (1-x)+(b*Real.log x+colRegG v x) := by
      funext x; unfold colFieldG; ring
    rw [heq]
    exact atBot_add_finite hl ht
#print axioms row_endpoint_contract
#print axioms col_endpoint_contract
end
end CatalanMeasure.GenD.Signed.RouteI.Maxima.EndpointLimits


-- Draft body to be appended to the source-bound L125 endpoint implementation
-- in the ONE full-consumer pilot. Not a separately submitted build.
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.Endpoints
open CatalanMeasure.CellCert Set Filter
open scoped Topology

theorem row_original_endpoints (R : RowWeights) (Pc Vc : List Int) (P V : List TailQ)
    (hP : tailsInDisk P = true) (hV : tailsInDisk V = true)
    (ha : (0 : Real) < R.alpha) (hb : (0 : Real) < R.beta) :
    let F := rowFieldSP R Pc Vc P V false false
    ContinuousOn F (Ico (-1 : Real) 0) ∧
    ContinuousOn F (Ioo (0 : Real) 1) ∧
    Tendsto F (𝓝[<] 0) atBot ∧ Tendsto F (𝓝[>] 0) atBot ∧
    Tendsto F (𝓝[<] 1) atBot := by
  simpa only [rowFieldSP_false, rowFieldS] using
    (CatalanMeasure.GenD.Signed.RouteI.Maxima.EndpointLimits.row_endpoint_contract
      (gamma := (R.gamma : Real))
      (trialSeqS_summable (cs := Pc) hP).1
      (trialSeqS_summable (cs := Vc) hV).1 ha hb)

theorem col_original_endpoints (C : ColumnWeights) (Vc : List Int) (V : List TailQ)
    (hV : tailsInDisk V = true)
    (hb : (0 : Real) < C.b) (hq : (0 : Real) < C.q) :
    let F := colFieldSP C Vc V false false
    ContinuousOn F (Ioo (0 : Real) 1) ∧
    Tendsto F (𝓝[>] 0) atBot ∧ Tendsto F (𝓝[<] 1) atBot := by
  simpa only [colFieldSP_false, colFieldS] using
    (CatalanMeasure.GenD.Signed.RouteI.Maxima.EndpointLimits.col_endpoint_contract
      (trialSeqS_summable (cs := Vc) hV).1 hb hq)

#print axioms row_original_endpoints
#print axioms col_original_endpoints
end CatalanMeasure.GenD.Signed.RouteI.Maxima.Endpoints

namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.Endpoints
open CatalanMeasure.CellCert Set Filter
open OAI.InternalCatalan.GlobalMaxReduction
open scoped Topology

theorem le_on_Icc_of_maxima {F : Real → Real} {a b M : Real}
    (hc : ContinuousOn F (Icc a b)) (ha : F a ≤ M) (hb : F b ≤ M)
    (hm : ∀ z ∈ Ioo a b, IsLocalMax F z → deriv F z = 0 → F z ≤ M) :
    ∀ x ∈ Icc a b, F x ≤ M := by
  intro x hx
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨x,hx⟩ hc
  have hcap : F z ≤ M := by
    by_cases hza : z = a
    · simpa only [hza] using ha
    by_cases hzb : z = b
    · simpa only [hzb] using hb
    have hi : z ∈ Ioo a b :=
      ⟨lt_of_le_of_ne hz.1 (Ne.symm hza), lt_of_le_of_ne hz.2 hzb⟩
    have hl : IsLocalMax F z := hmax.isLocalMax (Icc_mem_nhds hi.1 hi.2)
    exact hm z hi hl hl.deriv_eq_zero
  exact (hmax hx).trans hcap

theorem le_on_Ioo_of_maxima {F : Real → Real} {a b M : Real}
    (hc : ContinuousOn F (Ioo a b))
    (hl : Tendsto F (𝓝[>] a) atBot) (hr : Tendsto F (𝓝[<] b) atBot)
    (hm : ∀ z ∈ Ioo a b, IsLocalMax F z → deriv F z = 0 → F z ≤ M) :
    ∀ x ∈ Ioo a b, F x ≤ M := by
  intro x hx
  obtain ⟨l, hlx, hlM⟩ := exists_left_cutoff (M := M) hl hx.1
  obtain ⟨r, hxr, hrM⟩ := exists_right_cutoff (M := M) hr hx.2
  have hs : Icc l r ⊆ Ioo a b := by
    intro z hz
    exact ⟨hlx.1.trans_le hz.1, hz.2.trans_lt hxr.2⟩
  exact le_on_Icc_of_maxima (hc.mono hs) hlM hrM
    (fun z hz hmax hd => hm z (hs ⟨hz.1.le,hz.2.le⟩) hmax hd)
    x ⟨hlx.2.le,hxr.1.le⟩

theorem le_on_Ico_of_maxima {F : Real → Real} {a b M : Real}
    (hc : ContinuousOn F (Ico a b)) (ha : F a ≤ M)
    (hr : Tendsto F (𝓝[<] b) atBot)
    (hm : ∀ z ∈ Ioo a b, IsLocalMax F z → deriv F z = 0 → F z ≤ M) :
    ∀ x ∈ Ico a b, F x ≤ M := by
  intro x hx
  obtain ⟨r, hxr, hrM⟩ := exists_right_cutoff (M := M) hr hx.2
  have hs : Icc a r ⊆ Ico a b := by
    intro z hz
    exact ⟨hz.1,hz.2.trans_lt hxr.2⟩
  exact le_on_Icc_of_maxima (hc.mono hs) ha hrM
    (fun z hz hmax hd => hm z ⟨hz.1,hz.2.trans hxr.2⟩ hmax hd)
    x ⟨hx.1,hxr.1.le⟩

theorem row_original_cap (R : RowWeights) (Pc Vc : List Int) (P V : List TailQ)
    (hP : tailsInDisk P = true) (hV : tailsInDisk V = true)
    (ha : (0 : Real) < R.alpha) (hb : (0 : Real) < R.beta) (M : Real)
    (hboundary : rowFieldSP R Pc Vc P V false false (-1) ≤ M)
    (hmax : ∀ z ∈ Ioo (-1 : Real) 0 ∪ Ioo 0 1,
      IsLocalMax (rowFieldSP R Pc Vc P V false false) z →
      deriv (rowFieldSP R Pc Vc P V false false) z = 0 →
      rowFieldSP R Pc Vc P V false false z ≤ M) :
    ∀ x ∈ Ico (-1 : Real) 0 ∪ Ioo 0 1,
      rowFieldSP R Pc Vc P V false false x ≤ M := by
  obtain ⟨hcL,hcR,h0L,h0R,h1L⟩ := row_original_endpoints R Pc Vc P V hP hV ha hb
  intro x hx
  rcases hx with hx | hx
  · exact le_on_Ico_of_maxima hcL hboundary h0L
      (fun z hz hm hd => hmax z (Or.inl hz) hm hd) x hx
  · exact le_on_Ioo_of_maxima hcR h0R h1L
      (fun z hz hm hd => hmax z (Or.inr hz) hm hd) x hx

theorem col_original_cap (C : ColumnWeights) (Vc : List Int) (V : List TailQ)
    (hV : tailsInDisk V = true) (hb : (0 : Real) < C.b) (hq : (0 : Real) < C.q)
    (M : Real)
    (hmax : ∀ z ∈ Ioo (0 : Real) 1,
      IsLocalMax (colFieldSP C Vc V false false) z →
      deriv (colFieldSP C Vc V false false) z = 0 →
      colFieldSP C Vc V false false z ≤ M) :
    ∀ x ∈ Ioo (0 : Real) 1, colFieldSP C Vc V false false x ≤ M := by
  obtain ⟨hc,h0,h1⟩ := col_original_endpoints C Vc V hV hb hq
  exact le_on_Ioo_of_maxima hc h0 h1 hmax

#print axioms row_original_cap
#print axioms col_original_cap
end CatalanMeasure.GenD.Signed.RouteI.Maxima.Endpoints
