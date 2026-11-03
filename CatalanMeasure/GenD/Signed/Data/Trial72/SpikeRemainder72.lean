module
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeCount
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeRemainder72
open CatalanMeasure.Signed CatalanMeasure.Signed.Consts Filter
noncomputable section

/-- The frozen real root stays fixed within a q-piece, so the two remainder
coefficients involving it are real constants. Bound the scaled remainder
uniformly in the count and number of marked rows. -/
theorem uniform (bs : List ℚ) (ρ W : ℝ) (hW : 0 ≤ W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (l : ℝ) (s m : ℕ), 0 ≤ l → l ≤ 2 → 0 < s →
      (m : ℝ)/s ≤ W → costRem (fun k => l * bSeq bs k) s m ρ ≤ K := by
  let a : ℝ := S2q bs
  let b : ℝ := S1q bs
  let c : ℝ := ∑' k : ℕ, bSeq bs (k+1) * poisSeq ρ (k+1)
  let d : ℝ := barrierTrialS (bSeq bs) (-ρ)
  let e : ℝ := 2*ρ^2/(1-ρ^2)
  let B : ℝ := 4*|a|+8*|b|+8*|c|+8*|d|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨|Real.log 2|+(1+W)*B+W*|e|, by positivity, ?_⟩
  intro l s m hl h1 hs hw
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  let w : ℝ := (m : ℝ)/s
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hwW : w ≤ W := hw
  let C : ℝ := -(l^2)*a+2*l^2*b-4*l*c+4*l*d
  have hls : l^2 ≤ 4 := by nlinarith [mul_nonneg hl (sub_nonneg.mpr h1)]
  have ha := mul_le_mul (neg_le_abs a) hls (sq_nonneg l) (abs_nonneg a)
  have hb := mul_le_mul (le_abs_self b) hls (sq_nonneg l) (abs_nonneg b)
  have hc := mul_le_mul (neg_le_abs c) h1 hl (abs_nonneg c)
  have hd := mul_le_mul (le_abs_self d) h1 hl (abs_nonneg d)
  have hCB : C ≤ B := by dsimp [C,B]; linarith
  have h0 := mul_le_mul hCB (show 1+w ≤ 1+W by linarith) (show 0 ≤ 1+w by linarith) hB
  have hE := mul_le_mul (le_abs_self e) hwW hw0 (abs_nonneg e)
  have hsp : (∑' k : ℕ, (l*bSeq bs (k+1))*poisSeq ρ (k+1)) = l*c := by
    dsimp [c]
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by ring
  have hcost : costRem (fun k => l*bSeq bs k) s m ρ =
      Real.log 2 + C*(1+w) + e*w := by
    unfold costRem
    beta_reduce
    rw [tsum_lam_S2, tsum_lam_S1, hsp, barrierTrialS_smul]
    dsimp [C, w, a, b, d, e]
    have hs' : (s : ℝ) ≠ 0 := hsR.ne'
    rw [show ((s : ℝ)+m)/s = 1+(m : ℝ)/s by field_simp [hs'] <;> ring]
    rw [show 2*((s : ℝ)+m)/s = 2*(1+(m : ℝ)/s) by field_simp [hs'] <;> ring]
    rw [show 4*((s : ℝ)+m)/s = 4*(1+(m : ℝ)/s) by field_simp [hs'] <;> ring]
    ring
  rw [hcost]
  linarith [le_abs_self (Real.log 2)]

/-- A uniform constant is paid by any positive linear slack in the per-N
budget. This is the actual hfin inequality, with no sign assumption on K. -/
theorem absorb {δ K C : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (B : ℝ), B ≤ (C-δ)*N →
      2*(m : ℝ)*B + (m : ℝ)*K ≤ 2*(m : ℝ)*C*N := by
  obtain ⟨n, hn⟩ := exists_nat_ge (K/(2*δ))
  filter_upwards [eventually_ge_atTop n] with N hN m B hB
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hN
  have hK := (div_le_iff₀ (show 0 < 2*δ by positivity)).mp (hn.trans hnN)
  have hm := mul_le_mul_of_nonneg_left (show 2*B + K ≤ 2*C*N by nlinarith) (Nat.cast_nonneg (α := ℝ) m)
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeRemainder72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeRemainder72.uniform
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeRemainder72.absorb
