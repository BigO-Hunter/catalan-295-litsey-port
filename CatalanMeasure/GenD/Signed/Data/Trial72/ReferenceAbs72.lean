module
public import CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceData
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeA
public import CatalanMeasure.GenD.Signed.Data.Consts.SumAbs
public import CatalanMeasure.GenD.Signed.Interp
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceAbs72
open CatalanMeasure.Signed CatalanMeasure.Signed.Consts CatalanMeasure.Signed.FieldForm
open CatalanMeasure.Cert CatalanMeasure.CellCert
open ReferenceData
noncomputable section

private theorem absolute_sum (fa : List ℚ) (tl : List TailQ) (rho : List ℚ)
    (h : radOK tl rho = true) :
    ∑' j : ℕ, |tseq (bSeq fa) (tl.map TailQ.toC) j| ≤
      (absq fa : ℝ) + (radBound [] tl rho : ℝ) := by
  unfold radOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  let L := tl.zip rho
  have hL : ∀ p ∈ L, 0 ≤ p.2 ∧ p.2 < 1 ∧ p.1.zr*p.1.zr + p.1.zi*p.1.zi ≤ p.2*p.2 :=
    fun p hp => by simpa using hall p hp
  have h1 : L.map Prod.fst = tl := List.map_fst_zip (by omega)
  have h2 : L.map Prod.snd = rho := List.map_snd_zip (by omega)
  have hM := hasSum_rad_geom L hL
  have hcast := radBound_cast [] L
  rw [h1, h2] at hcast
  simp at hcast
  rw [← hcast] at hM
  have hF := (tsum_abs_bSeq fa)
  have hsF : Summable (fun j : ℕ => |bSeq fa (j+1)|) := by
    refine summable_of_ne_finset_zero (s := Finset.range fa.length) fun j hj => ?_
    have hk : fa.length ≤ j := by simpa using hj
    rw [bSeq_succ, getD_zero_of_le fa hk]
    simp
  have hsF0 := (summable_nat_add_iff 1).mp hsF
  rw [hsF0.tsum_eq_zero_add] at hF
  simp [bSeq] at hF
  have hm := hsF.hasSum.add hM
  have hle : ∀ j : ℕ, |tseq (bSeq fa) (tl.map TailQ.toC) (j+1)| ≤
      |bSeq fa (j+1)| + (L.map fun p => (((|p.1.rr| + |p.1.ri| : ℚ)) : ℝ) *
        ((p.2 : ℚ) : ℝ) ^ (j+1)).sum := by
    intro j
    have ht := tail_term_le_rad L hL (j+1)
    rw [h1] at ht
    rw [tseq, if_neg (Nat.succ_ne_zero j)]
    exact (abs_add_le _ _).trans (add_le_add_left ht _)
  have hs := Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle hm.summable
  have hs0 := (summable_nat_add_iff 1).mp hs
  rw [hs0.tsum_eq_zero_add]
  simp only [tseq, if_pos rfl, abs_zero, zero_add]
  have hb := hasSum_le hle hs.hasSum hm
  rw [← hs.hasSum.tsum_eq, hF] at hb
  exact hb

private def rhoP : List ℚ := (raw_ints% [800000000000, 800000000000, 900000000000, 900000000000, 950000000000, 950000000000, 970000000000, 970000000000, 980000000000, 980000000000, 990000000000, 990000000000, 995000000000, 995000000000, 997000000000, 997000000000, 999000000000, 999000000000, 999300000000, 999300000000, 999700000000, 999700000000, 999900000000, 999900000000, 999930000000, 999930000000, 999970000000, 999970000000, 999990000000, 999990000000, 999993000000, 999993000000, 999997000000, 999997000000, 989920814600, 989933632267, 989945747456, 989957167540, 989967899427, 989977949572, 989987323987, 989996028248, 990004067510, 990011446514, 990018169591, 990024240673, 990029663301, 990034440624, 990038575413, 990042070057, 990044926573, 990047146607, 990048731434, 990049681967, 990049998750, 990049681967, 990048731434, 990047146607, 990044926573, 990042070057, 990038575413, 990034440624, 990029663301, 990024240673, 990018169591, 990011446514, 990004067510, 989996028248, 989987323987, 989977949572, 989967899427, 989957167540, 989945747456, 989933632267, 989920814600]).map fun n => (n : ℚ) / 1000000000000
private theorem radP : radOK secondPData.tail rhoP = true := by decide +kernel
private theorem scalarP : absq secondPData.f + radBound [] secondPData.tail rhoP ≤ (1032 : ℚ) := by
  decide +kernel
theorem sumP : (∑' j, |secondP j|) ≤ (1032 : ℝ) := by
  have h := absolute_sum secondPData.f secondPData.tail rhoP radP
  have hs : (absq secondPData.f : ℝ) + (radBound [] secondPData.tail rhoP : ℝ) ≤ 1032 := by
    exact_mod_cast scalarP
  exact h.trans hs

private def rhoV : List ℚ := (raw_ints% [800000000000, 800000000000, 900000000000, 900000000000, 950000000000, 950000000000, 970000000000, 970000000000, 980000000000, 980000000000, 990000000000, 990000000000, 995000000000, 995000000000, 997000000000, 997000000000, 999000000000, 999000000000, 999300000000, 999300000000, 999700000000, 999700000000, 999900000000, 999900000000, 999930000000, 999930000000, 999970000000, 999970000000, 999990000000, 999990000000, 999993000000, 999993000000, 999997000000, 999997000000, 989920814600, 989933632267, 989945747456, 989957167540, 989967899427, 989977949572, 989987323987, 989996028248, 990004067510, 990011446514, 990018169591, 990024240673, 990029663301, 990034440624, 990038575413, 990042070057, 990044926573, 990047146607, 990048731434, 990049681967, 990049998750, 990049681967, 990048731434, 990047146607, 990044926573, 990042070057, 990038575413, 990034440624, 990029663301, 990024240673, 990018169591, 990011446514, 990004067510, 989996028248, 989987323987, 989977949572, 989967899427, 989957167540, 989945747456, 989933632267, 989920814600]).map fun n => (n : ℚ) / 1000000000000
private theorem radV : radOK secondVData.tail rhoV = true := by decide +kernel
private theorem scalarV : absq secondVData.f + radBound [] secondVData.tail rhoV ≤ (5544 : ℚ) := by
  decide +kernel
theorem sumV : (∑' j, |secondV j|) ≤ (5544 : ℝ) := by
  have h := absolute_sum secondVData.f secondVData.tail rhoV radV
  have hs : (absq secondVData.f : ℝ) + (radBound [] secondVData.tail rhoV : ℝ) ≤ 5544 := by
    exact_mod_cast scalarV
  exact h.trans hs

theorem hec :
    (1/1073741824 : ℝ)*(4*(∑' j, |secondP j|)+4*(∑' j, |secondV j|)+|secondP 1|+20) <
      (13/100000 : ℝ)/2 := by
  have hP := sumP
  have hV := sumV
  have h1 : |secondP 1| ≤ 1032 := (abs_le_tsum_abs secondP_summable 1).trans sumP
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceAbs72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceAbs72.hec
