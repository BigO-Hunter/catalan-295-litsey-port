module
public import CatalanMeasure.GenD.Analytic.FirstGlue
public import CatalanMeasure.GenD.Analytic.WeightedAtom
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed.Data.Trial72.EndpointAdapters
open Set Filter CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.CellCert
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
open scoped Topology BigOperators
noncomputable section
/-! Endpoint-budget versions of the field-to-trial adapters. Physical row/column/
marked/near proofs are copied unchanged from FirstGlue/Glue; only the public
budget type is the existing End type (without a(1-a)log2). Thus no old stronger
budget is smuggled in as an extra producer obligation. No fixed-design data. -/
def firstEnd_of_fields {P : Parameters} (hP : Admissible P)
    {target cost normCap fieldCap : ℝ}
    (p v : ℕ → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hp : Summable (fun k => |p k|)) (hv : Summable (fun k => |v k|))
    (α β γ c b q : ℝ) (hα : α = ((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0)
    (hβ : β = 2 * (P.h0 : ℝ) / P.n0)
    (hγ : γ = ((P.n0 : ℝ) + P.b0 + P.q0 + P.g0 + P.h0) / P.n0 - 1 / 2)
    (hc : c = 2 * (P.g0 : ℝ) / P.n0)
    (hb : b = (P.b0 : ℝ) / P.n0) (hq : q = (P.q0 : ℝ) / P.n0)
    (MX MY : ℝ)
    (norm_le : barrierTrialNormSq p + barrierTrialNormSq v / 2 ≤ normCap)
    (field_sum : MX + MY = fieldCap)
    (row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, firstRowFieldG α β γ lam c p v x ≤ MX)
    (column_sup : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG b q v s ≤ MY)
    (budget : ∀ a : ℝ,
      (-gC0 P + gC1 P * a - a ^ 2) * Real.log 2 +
        normCap + (1 - a) * fieldCap +
        a * (2 * lam * ((P.g0 : ℝ) / P.n0)) ≤
          -target + Real.log 2 / 2 + cost * a) :
    FirstTrialBoundsEnd P target cost where
  p := p
  v := v
  lambda := lam
  MX := MX
  MY := MY
  normCap := normCap
  fieldCap := fieldCap
  lambda_nonneg := hlam
  p_summable := hp
  v_summable := hv
  norm_le := norm_le
  field_sum := field_sum
  row := by
    intro ε hε
    have hα0 : 0 ≤ α := by
      rw [hα]; have := n0_pos hP; positivity
    have hβ0 : 0 < β := by
      rw [hβ]; have := n0_pos hP; have : (0 : ℝ) < P.h0 := by exact_mod_cast hP.2.2.2.1
      positivity
    have hh := firstRowFieldG_corrected_eventually (α := α) (β := β) (γ := γ) (lam := lam)
      (c := c) hp hv hα0 hβ0 (a := 3 / 2) (b := 1 / 2) (by norm_num) (by norm_num) row_sup
      (fun N : ℕ => 1 / ((P.n0 : ℝ) * N))
      (fun N => by have := n0_pos hP; positivity) (invScale_tendsto hP) hε
    filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hc' hN x hx
    have hb' := hc' x hx
    have hid := physical_one_row_identity hP hN lam p v x
    rw [← hα, ← hβ, ← hγ, ← hc] at hid
    linarith only [hb', hid]
  column := by
    intro ε hε
    have hq0 : 0 < q := by
      rw [hq]; have := n0_pos hP; have : (0 : ℝ) < P.q0 := by exact_mod_cast hP.2.2.1
      positivity
    have hb0 : 0 ≤ b := by
      rw [hb]; have := n0_pos hP; positivity
    have hh := colFieldG_corrected_eventually (b := b) (q := q) hv hb0 hq0 column_sup
      (fun N : ℕ => 1 / ((P.n0 : ℝ) * N))
      (fun N => by have := n0_pos hP; positivity) (invScale_tendsto hP) hε
    filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hc' hN s hs
    rw [physical_column_identity_gen hP hN]
    have hb' := hc' s hs
    unfold colFieldG colRegG at hb'
    rw [hb, hq] at hb'
    simp only [zero_mul, add_zero]
    linarith only [hb']
  budget := budget

def secondEnd_of_fields {P : Parameters} (hP : Admissible P)
    {α1 target residual cost normCap fieldCap : ℝ} {G : ℝ → Prop}
    (u v : ℕ → ℝ) (hu : Summable (fun k => |u k|)) (hv : Summable (fun k => |v k|))
    (α β γ b q : ℝ) (hα : α = ((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0)
    (hβ : β = 2 * (P.h0 : ℝ) / P.n0)
    (hγ : γ = ((P.n0 : ℝ) + P.b0 + P.q0 + P.g0 + P.h0) / P.n0)
    (hb : b = (P.b0 : ℝ) / P.n0) (hq : q = (P.q0 : ℝ) / P.n0)
    (MX MY nearCap : ℝ)
    (near_sup : ∀ y ∈ Ioo (0 : ℝ) 1,
      -gRes P * Real.log (1 + y ^ 2) + (((P.n0 : ℝ) - 2 * P.g0 - 1) / P.n0) * Real.log y -
        u 1 * y ≤ nearCap)
    (norm_le : 2 * barrierTrialNormSq u + barrierTrialNormSq v / 2 ≤ normCap)
    (field_sum : MX + MY = fieldCap)
    (row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, rowFieldG α β γ u v x ≤ MX)
    (column_sup : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG b q v s ≤ MY)
    (residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, G x → resFieldGen (gRes P) u x ≤ residual)
    (budget : ∀ {a t : ℝ}, α1 ≤ a → 0 ≤ a → 0 ≤ t →
      (-gC0 P + gC1 P * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
        normCap + (1 - a) * fieldCap +
        (a - t) * residual + t * nearCap ≤
          -target + Real.log 2 / 2 + cost * a) :
    SecondTrialBoundsEnd P α1 target residual nearCap cost G where
  p := u
  v := v
  MX := MX
  MY := MY
  normCap := normCap
  fieldCap := fieldCap
  p_summable := hu
  v_summable := hv
  norm_le := norm_le
  field_sum := field_sum
  row := by
    intro ε hε
    have hα0 : 0 ≤ α := by
      rw [hα]; have := n0_pos hP; positivity
    have hβ0 : 0 < β := by
      rw [hβ]; have := n0_pos hP; have : (0 : ℝ) < P.h0 := by exact_mod_cast hP.2.2.2.1
      positivity
    have hh := rowFieldG_corrected_eventually (α := α) (β := β) (γ := γ) hu hv hα0 hβ0
      (a := 2) (b := 1 / 2) (by norm_num) (by norm_num) row_sup
      (fun N : ℕ => 1 / ((P.n0 : ℝ) * N))
      (fun N => by have := n0_pos hP; positivity) (invScale_tendsto hP) hε
    filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hc hN x hx
    rw [physical_free_row_identity, param_row_field_eq hP hN]
    have hb' := hc x hx
    rw [rowFieldG_eq, hα, hβ, hγ] at hb'
    linarith only [hb']
  column := by
    intro ε hε
    have hq0 : 0 < q := by
      rw [hq]; have := n0_pos hP; have : (0 : ℝ) < P.q0 := by exact_mod_cast hP.2.2.1
      positivity
    have hb0 : 0 ≤ b := by
      rw [hb]; have := n0_pos hP; positivity
    have hh := colFieldG_corrected_eventually (b := b) (q := q) hv hb0 hq0 column_sup
      (fun N : ℕ => 1 / ((P.n0 : ℝ) * N))
      (fun N => by have := n0_pos hP; positivity) (invScale_tendsto hP) hε
    filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hc hN s hs
    rw [physical_column_identity_gen hP hN]
    have hb' := hc s hs
    unfold colFieldG colRegG at hb'
    rw [hb, hq] at hb'
    simp only [zero_mul, add_zero]
    linarith only [hb']
  marked := by
    intro N hN x hx hgap
    have hn : (0 : ℝ) < P.n N := by exact_mod_cast n_pos hP hN
    have hsq : x ^ 2 ≤ 1 := by nlinarith only [hx.1, hx.2]
    have hlog : Real.log (1 + x ^ 2) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) (by linarith only [hsq])
    have hcorr := div_le_div_of_nonneg_right hlog hn.le
    have hb' := residual_sup x hx hgap
    unfold resFieldGen at hb'
    rw [grouped_marked_field_identity hP hN]
    linarith only [hb', hcorr]
  near := by
    intro N hN y hy
    have hn : (0 : ℝ) < P.n N := by exact_mod_cast n_pos hP hN
    have hsq : y ^ 2 ≤ 1 := by nlinarith only [hy.1, hy.2]
    have hlog : Real.log (1 + y ^ 2) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) (by linarith only [hsq])
    have hcorr := div_le_div_of_nonneg_right hlog hn.le
    have hb' := near_sup y hy
    have hcoef := near_coeff_ge hP hN
    have hly : Real.log y ≤ 0 := Real.log_nonpos hy.1.le hy.2.le
    have hm := mul_le_mul_of_nonpos_right hcoef hly
    unfold groupedNearField
    rw [grouped_marked_field_identity hP hN, abs_of_pos hy.1]
    linarith only [hb', hcorr, hm]
  budget := budget
end
end CatalanMeasure.GenD.Signed.Data.Trial72.EndpointAdapters

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EndpointAdapters.firstEnd_of_fields
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EndpointAdapters.secondEnd_of_fields
