module

public import CatalanMeasure.GenD.Analytic.PsiSelector
public import CatalanMeasure.GenD.Signed.LogEval

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Davis.S1Selector
open CatalanMeasure.GenD.Analytic
noncomputable section

def scalarOK (lo hi U Ψ : ℚ) : Bool :=
  match LogEval.logQ 12 (3/5) with
  | none => false
  | some (v,e) =>
    let a := 12 - 72*hi
    let contour := a*v + |a| * e + (24330011831893/549755813888 : ℚ)
    if lo ≤ 1/2 then
      match LogEval.logQ 12 2 with
      | none => false
      | some (v2,e2) => decide (contour ≤ U ∧ U+72*(v2+e2) ≤ Ψ)
    else
      match LogEval.logQ 12 lo, LogEval.logQ 12 (1-lo) with
      | some (v1,e1), some (v2,e2) =>
        decide (contour ≤ U ∧ U+72*(lo*(e1-v1)+(1-lo)*(e2-v2)) ≤ Ψ)
      | _, _ => false

theorem mul_logQ_upper {q v e : ℚ} {n : ℕ} (hlog : LogEval.logQ n q = some (v,e)) (a : ℚ) :
    (a : ℝ) * Real.log (q : ℝ) ≤ ((a*v+|a| *e : ℚ) : ℝ) := by
  obtain ⟨_, he⟩ := LogEval.logQ_spec hlog
  unfold LogEval.Enc at he
  have ht : (a : ℝ) * (Real.log (q : ℝ) - (v : ℝ)) ≤ |(a : ℝ)| * (e : ℝ) := by
    calc
      _ ≤ |(a : ℝ) * (Real.log (q : ℝ) - (v : ℝ))| := le_abs_self _
      _ = |(a : ℝ)| * |Real.log (q : ℝ) - (v : ℝ)| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left he (abs_nonneg _)
  push_cast
  nlinarith

theorem scalarOK_spec {lo hi U Ψ : ℚ} (hlo : 0 ≤ lo) (hlh : lo ≤ hi) (hhi : hi ≤ 1)
    (h : scalarOK lo hi U Ψ = true) :
    (12 - 72 * (hi : ℝ)) * Real.log (3/5) + (24330011831893/549755813888 : ℝ) ≤ (U : ℝ) ∧
      (U : ℝ) + 72 * binomRate (lo : ℝ) ≤ (Ψ : ℝ) := by
  cases hlog : LogEval.logQ 12 (3/5) with
  | none => simp [scalarOK, hlog] at h
  | some ve =>
    obtain ⟨v,e⟩ := ve
    have hcontour := mul_logQ_upper hlog (12-72*hi)
    push_cast at hcontour
    simp only [scalarOK, hlog] at h
    by_cases hhalf : lo ≤ 1/2
    · simp only [if_pos hhalf] at h
      cases h2 : LogEval.logQ 12 2 with
      | none => simp [h2] at h
      | some ve2 =>
        obtain ⟨v2,e2⟩ := ve2
        simp only [h2] at h
        have hf := of_decide_eq_true h
        have hf1 : (((12-72*hi)*v+|12-72*hi| *e+(24330011831893/549755813888 : ℚ) : ℚ) : ℝ) ≤ U := by
          exact_mod_cast hf.1
        have hf2 : (U : ℝ)+72*((v2 : ℝ)+e2) ≤ Ψ := by exact_mod_cast hf.2
        have hlog2 := mul_logQ_upper h2 1
        norm_num only [Rat.cast_one, Rat.cast_ofNat, one_mul] at hlog2
        push_cast at hf1 hlog2
        constructor
        · linarith
        · have hb := binomRate_le_log_two (lo : ℝ)
          linarith
    · simp only [if_neg hhalf] at h
      cases h1 : LogEval.logQ 12 lo with
      | none => simp [h1] at h
      | some ve1 =>
        obtain ⟨v1,e1⟩ := ve1
        cases h2 : LogEval.logQ 12 (1-lo) with
        | none => simp [h1,h2] at h
        | some ve2 =>
          obtain ⟨v2,e2⟩ := ve2
          simp only [h1,h2] at h
          have hf := of_decide_eq_true h
          have hf1 : (((12-72*hi)*v+|12-72*hi| *e+(24330011831893/549755813888 : ℚ) : ℚ) : ℝ) ≤ U := by
            exact_mod_cast hf.1
          have hf2 : (U : ℝ)+72*((lo : ℝ)*((e1 : ℝ)-v1)+(1-(lo : ℝ))*((e2 : ℝ)-v2)) ≤ Ψ := by
            exact_mod_cast hf.2
          obtain ⟨_, E1⟩ := LogEval.logQ_spec h1
          obtain ⟨_, E2⟩ := LogEval.logQ_spec h2
          unfold LogEval.Enc at E1 E2
          have hlower1 : -Real.log (lo : ℝ) ≤ (e1 : ℝ)-v1 := by
            have ht := (abs_le.mp E1).1
            linarith
          have hlower2 : -Real.log (1-(lo : ℝ)) ≤ (e2 : ℝ)-v2 := by
            push_cast at E2
            have ht := (abs_le.mp E2).1
            linarith
          have hloR : (0 : ℝ) ≤ lo := by exact_mod_cast hlo
          have hlo1 : (lo : ℝ) ≤ 1 := by exact_mod_cast hlh.trans hhi
          have hH : Real.binEntropy (lo : ℝ) ≤
              (lo : ℝ)*((e1 : ℝ)-v1)+(1-(lo : ℝ))*((e2 : ℝ)-v2) := by
            rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
            simp only [Real.negMulLog]
            nlinarith [mul_le_mul_of_nonneg_left hlower1 hloR,
              mul_le_mul_of_nonneg_left hlower2 (sub_nonneg.mpr hlo1)]
          have hhalfR : 1 ≤ 2 * (lo : ℝ) := by
            have ht : (1 : ℚ) ≤ 2*lo := by linarith [not_le.mp hhalf]
            exact_mod_cast ht
          have hbin : binomRate (lo : ℝ) = Real.binEntropy (lo : ℝ) := by
            unfold binomRate
            rw [if_pos hhalfR]
          push_cast at hf1
          constructor
          · linarith
          · rw [hbin]
            linarith

end
end CatalanMeasure.GenD.Signed.Davis.S1Selector
#print axioms CatalanMeasure.GenD.Signed.Davis.S1Selector.mul_logQ_upper
#print axioms CatalanMeasure.GenD.Signed.Davis.S1Selector.scalarOK_spec
