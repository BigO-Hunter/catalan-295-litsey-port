module
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldPositiveLimit2

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPm2
open Set Filter CatalanMeasure.Signed CatalanMeasure.GenD.Analytic
open CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

private theorem selfDistance (p : List ℚ) : l1Q p p ≤ 0 := by
  induction p with
  | nil => simp [l1Q]
  | cons a p ih => simpa [l1Q, qAbs] using ih

private theorem hTheta : (dc72.thetaL : ℝ) = 1/1024 := by norm_num [dc72]

private theorem hCost : ((AssemblyBindings.X2.CSP : ℝ) / dc72.n0) = ((((5 : ℚ) / 288) : ℚ) : ℝ) := by
  change ((T2.params.CSP : ℚ) : ℝ) / dc72.n0 = _
  norm_num [T2.params, dc72_n0]

private theorem hCost0 : (0 : ℝ) ≤ AssemblyBindings.X2.CSP := by
  change (0:ℝ) ≤ ((T2.params.CSP : ℚ) : ℝ)
  norm_num [T2.params]

theorem topOf
    (before : ∀ y ∈ Icc (999/1000 : ℝ) (1023/1024), fieldTower (T2.spmAt (0 : ℚ)) (poleF (T2.spmAt (0 : ℚ)).poles) 0 y + lfieldTower FieldPositiveLimit2.terms 0 y ≤ ((((-3144710066661 : ℚ) / 549755813888) : ℚ) : ℝ))
    (after : ∀ y ∈ Ico (1023/1024 : ℝ) 1, fieldTower (T2.spmAt (0 : ℚ)) (poleF (T2.spmAt (0 : ℚ)).poles) 0 y + lfieldTower FieldPositiveLimit2.terms 0 y ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ y ∈ Ioo (0 : ℝ) 1, (999/1000 : ℝ) ≤ y →
      (T2.D N).fPosMS (groupedMarkedField dc72.toParameters N) y ≤ ((((-505452203 : ℚ) / 536870912) : ℚ) : ℝ) + ε := by
  have hk := FieldPositiveLimit2.spmOffset
  have b1 : ((((-3144710066661 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2627127010789 : ℚ) / 549755813888) : ℚ) : ℝ) ≤ ((((-505452203 : ℚ) / 536870912) : ℚ) : ℝ) := by norm_num
  have b2 : ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) + ((((2627127010789 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((5 : ℚ) / 288) : ℚ) : ℝ) ≤ ((((-505452203 : ℚ) / 536870912) : ℚ) : ℝ) := by norm_num
  have hFt (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) := FieldPositiveLimit2.spmIdentity 0 y hy
  exact Generic.rowPosTop_cell dc72 AssemblyBindings.X2 AssemblyBindings.hok2 AssemblyBindings.hRt2
    (T2.spmAt 0) (T2.spmAt 0) (T2.spmAt 0) FieldPositiveLimit2.terms (K := spmK T2.trial)
    (fun y hy => by simpa only [Rat.cast_zero, mul_zero, zero_mul, add_zero] using hFt y hy)
    hCost0 rfl rfl (δ1 := 0) (selfDistance _) rfl rfl (δ2 := 0) (selfDistance _)
    (xc := (999/1000:ℝ)) (m := (1023/1024:ℝ))
    (T1 := ((((-3144710066661 : ℚ) / 549755813888) : ℚ) : ℝ)) (T2 := ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ)) (S := ((((-505452203 : ℚ) / 536870912) : ℚ) : ℝ))
    (by norm_num) (by norm_num) (by rw [hTheta]; norm_num)
    before after
    (by simp only [Rat.cast_zero, add_zero]; linarith only [hk,b1])
    (by simp only [Rat.cast_zero, add_zero,hCost]; linarith only [hk,b2])
#print axioms topOf

theorem offWideOf (lower : ∀ y ∈ Icc (98749/1000000 : ℝ) (999/1000), fieldTower (T2.spmAt ((1 : ℚ) / 200)) (poleF (T2.spmAt ((1 : ℚ) / 200)).poles) 0 y + lfieldTower FieldPositiveLimit2.terms 0 y ≤ ((((-2879621665765 : ℚ) / 549755813888) : ℚ) : ℝ)) (upper : ∀ y ∈ Icc (98749/1000000 : ℝ) (999/1000), fieldTower (T2.spmAt ((1 : ℚ) / 16)) (poleF (T2.spmAt ((1 : ℚ) / 16)).poles) 0 y + lfieldTower FieldPositiveLimit2.terms 0 y ≤ ((((-2863106845669 : ℚ) / 549755813888) : ℚ) : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (1/200 : ℝ) (1/16), ∀ y ∈ Ioo (0 : ℝ) 1,
      (98749/1000000 : ℝ) ≤ y → y < (999/1000 : ℝ) →
      (T2.D N).fPosMR (groupedMarkedField dc72.toParameters N) (11/8) α y ≤
        chord (1/200) (1/16) ((((-493153623 : ℚ) / 1073741824) : ℚ) : ℝ) ((((-460898115 : ℚ) / 1073741824) : ℚ) : ℝ) α + ε := by
  have key := Generic.rowPos_cell dc72 AssemblyBindings.X2 AssemblyBindings.hok2 AssemblyBindings.hRt2
    (rc := (11/8:ℝ)) (by norm_num) (α₁ := ((((1 : ℚ) / 200) : ℚ) : ℝ)) (α₂ := ((((1 : ℚ) / 16) : ℚ) : ℝ))
    (by norm_num) (by norm_num) (T2.spmAt ((1 : ℚ) / 200)) (T2.spmAt ((1 : ℚ) / 16))
    (T2.spmAt ((1 : ℚ) / 200)) (T2.spmAt ((1 : ℚ) / 16)) FieldPositiveLimit2.terms
    (K := spmK T2.trial) (FieldPositiveLimit2.spmIdentity ((1 : ℚ) / 200)) (FieldPositiveLimit2.spmIdentity ((1 : ℚ) / 16))
    rfl rfl (δ₁ := 0) (selfDistance _) rfl rfl (δ₂ := 0) (selfDistance _)
    (g := (98749/1000000:ℝ)) (xc := (999/1000:ℝ)) (T₁ := ((((-2879621665765 : ℚ) / 549755813888) : ℚ) : ℝ)) (T₂ := ((((-2863106845669 : ℚ) / 549755813888) : ℚ) : ℝ))
    (by norm_num) (by norm_num) (by rw [hTheta]; norm_num) lower upper
  intro ε hε
  filter_upwards [key ε hε] with N hN α hα y hy hg hxc
  have ha : α ∈ Icc ((((1 : ℚ) / 200) : ℚ) : ℝ) ((((1 : ℚ) / 16) : ℚ) : ℝ) := by norm_num at hα ⊢; exact hα
  have h := hN α ha y hy hg hxc
  change (T2.D N).fPosMR (groupedMarkedField dc72.toParameters N) (11/8) α y ≤ _ at h
  simp only [Rat.cast_zero, add_zero] at h
  have hl : ((((-2879621665765 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2627127010789 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-493153623 : ℚ) / 1073741824) : ℚ) : ℝ) := by norm_num
  have hu : ((((-2863106845669 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2627127010789 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-460898115 : ℚ) / 1073741824) : ℚ) : ℝ) := by norm_num
  have hp : (0:ℝ) < 1/16-1/200 := by norm_num
  have h0 : 0 ≤ (α-1/200)/(1/16-1/200) := div_nonneg (sub_nonneg.mpr hα.1) hp.le
  have h1 : (α-1/200)/(1/16-1/200) ≤ 1 := (div_le_iff₀ hp).mpr (by linarith [hα.2])
  rw [← hl, ← hu]
  unfold chord interpL
  rw [min_eq_right h1, max_eq_right h0]
  have hk := FieldPositiveLimit2.spmOffset
  push_cast at h
  linarith only [h,hk]
#print axioms offWideOf
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPm2
