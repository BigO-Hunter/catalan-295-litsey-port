module

public import CatalanMeasure.GenD.Signed.LogEval

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.AdaptiveAnchor
open CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.Cert (qabs)

def series (n : ℕ) (y : ℚ) : ℚ × ℚ :=
  let w := (y - 1) / (y + 1)
  (2 * w * CatalanMeasure.WLog.serH (w ^ 2) n 1,
    2 * w ^ (2 * n + 1) / (1 - w ^ 2))

theorem series_sound (n : ℕ) (y : ℚ) (hy : 1 ≤ y) :
    |Real.log (y : ℝ) - ((series n y).1 : ℝ)| ≤ ((series n y).2 : ℝ) := by
  have h : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  let w : ℝ := ((y : ℝ) - 1) / ((y : ℝ) + 1)
  have hd : (0 : ℝ) < (y : ℝ) + 1 := by linarith
  have h0 : 0 ≤ w := div_nonneg (by linarith) hd.le
  have h1 : w < 1 := (div_lt_one hd).2 (by linarith)
  have hr : (1 + w) / (1 - w) = (y : ℝ) := by
    apply (div_eq_iff (by linarith : 1 - w ≠ 0)).2
    dsimp [w]
    field_simp
    <;> ring
  have ht := CatalanMeasure.WLog.atanh_tail h0 h1 n
  rw [hr] at ht
  simpa only [series, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div, Rat.cast_pow,
    Rat.cast_sub, Rat.cast_add, Rat.cast_one, CatalanMeasure.WLog.serH_spec, w] using ht

def anchor (n : ℕ) (q : ℚ) : Option (ℚ × ℚ) := do
  let (m, y) ← findExpY (qabs q)
  let a := series n 2
  let b := series n y
  return ((m : ℚ) * a.1 + b.1, |(m : ℚ)| * a.2 + b.2)

theorem anchor_sound {n : ℕ} {q v e : ℚ} (h : anchor n q = some (v,e)) :
    |Real.log |(q : ℝ)| - (v : ℝ)| ≤ (e : ℝ) := by
  unfold anchor at h
  cases he : findExpY (qabs q) with
  | none => simp [he] at h
  | some p =>
    rcases p with ⟨m,y⟩
    simp only [he, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    obtain ⟨hy, h1, _⟩ := findExpY_spec he
    have h1r : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast h1
    have hy' : |(q : ℝ)| = (2 : ℝ)^m * (y : ℝ) := by
      have hp : (2 : ℝ)^m ≠ 0 := by positivity
      have hq : ((qabs q : ℚ) : ℝ) = |(q : ℝ)| := by
        unfold qabs
        split_ifs with hh
        · push_cast
          rw [abs_of_neg (by exact_mod_cast hh)]
        · rw [abs_of_nonneg (by exact_mod_cast (not_lt.mp hh))]
      have hs : ((qabs q : ℚ) : ℝ) / (2 : ℝ)^m = (y : ℝ) := by
        rw [hy, Rat.cast_div, Rat.cast_zpow] <;> norm_num
      rw [hq, div_eq_iff hp] at hs
      rw [mul_comm]
      exact hs
    rw [hy', Real.log_mul (by positivity) (by linarith), Real.log_zpow]
    push_cast
    have hb := series_sound n y h1
    have ha := series_sound n 2 (by norm_num)
    norm_num at ha
    calc
      _ = |(m : ℝ) * (Real.log 2 - ((series n 2).1 : ℝ)) +
          (Real.log (y : ℝ) - ((series n y).1 : ℝ))| := by congr 1 <;> ring
      _ ≤ _ := (abs_add_le _ _).trans (by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left ha (abs_nonneg _)) hb)

#print axioms series_sound
#print axioms anchor_sound

end CatalanMeasure.GenD.Signed.Data.Cells.D72.AdaptiveAnchor
