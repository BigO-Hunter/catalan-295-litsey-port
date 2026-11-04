module
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldPositiveLimit0

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPm0
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

private theorem hCost : ((AssemblyBindings.X0.CSP : ℝ) / dc72.n0) = ((((5 : ℚ) / 288) : ℚ) : ℝ) := by
  change ((T0.params.CSP : ℚ) : ℝ) / dc72.n0 = _
  norm_num [T0.params, dc72_n0]

private theorem hCost0 : (0 : ℝ) ≤ AssemblyBindings.X0.CSP := by
  change (0:ℝ) ≤ ((T0.params.CSP : ℚ) : ℝ)
  norm_num [T0.params]

theorem topOf
    (before : ∀ y ∈ Icc (999/1000 : ℝ) (1023/1024), fieldTower (T0.spmAt (0 : ℚ)) (poleF (T0.spmAt (0 : ℚ)).poles) 0 y + lfieldTower FieldPositiveLimit0.terms 0 y ≤ ((((-3151596717623 : ℚ) / 549755813888) : ℚ) : ℝ))
    (after : ∀ y ∈ Ico (1023/1024 : ℝ) 1, fieldTower (T0.spmAt (0 : ℚ)) (poleF (T0.spmAt (0 : ℚ)).poles) 0 y + lfieldTower FieldPositiveLimit0.terms 0 y ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ y ∈ Ioo (0 : ℝ) 1, (999/1000 : ℝ) ≤ y →
      (T0.D N).fPosMS (groupedMarkedField dc72.toParameters N) y ≤ ((((-519640589 : ℚ) / 536870912) : ℚ) : ℝ) + ε := by
  have hk := FieldPositiveLimit0.spmOffset
  have b1 : ((((-3151596717623 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2619484754487 : ℚ) / 549755813888) : ℚ) : ℝ) ≤ ((((-519640589 : ℚ) / 536870912) : ℚ) : ℝ) := by norm_num
  have b2 : ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) + ((((2619484754487 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((5 : ℚ) / 288) : ℚ) : ℝ) ≤ ((((-519640589 : ℚ) / 536870912) : ℚ) : ℝ) := by norm_num
  have hFt (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) := FieldPositiveLimit0.spmIdentity 0 y hy
  exact Generic.rowPosTop_cell dc72 AssemblyBindings.X0 AssemblyBindings.hok0 AssemblyBindings.hRt0
    (T0.spmAt 0) (T0.spmAt 0) (T0.spmAt 0) FieldPositiveLimit0.terms (K := spmK T0.trial)
    (fun y hy => by simpa only [Rat.cast_zero, mul_zero, zero_mul, add_zero] using hFt y hy)
    hCost0 rfl rfl (δ1 := 0) (selfDistance _) rfl rfl (δ2 := 0) (selfDistance _)
    (xc := (999/1000:ℝ)) (m := (1023/1024:ℝ))
    (T1 := ((((-3151596717623 : ℚ) / 549755813888) : ℚ) : ℝ)) (T2 := ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ)) (S := ((((-519640589 : ℚ) / 536870912) : ℚ) : ℝ))
    (by norm_num) (by norm_num) (by rw [hTheta]; norm_num)
    before after
    (by simp only [Rat.cast_zero, add_zero]; linarith only [hk,b1])
    (by simp only [Rat.cast_zero, add_zero,hCost]; linarith only [hk,b2])
#print axioms topOf

theorem offSmallOf (upper : ∀ y ∈ Icc (98749/1000000 : ℝ) (999/1000), fieldTower (T0.spmAt ((1 : ℚ) / 200)) (poleF (T0.spmAt ((1 : ℚ) / 200)).poles) 0 y + lfieldTower FieldPositiveLimit0.terms 0 y ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ≤ (1/200 : ℝ), ∀ y ∈ Ioo (0 : ℝ) 1,
      (98749/1000000 : ℝ) ≤ y → y < (999/1000 : ℝ) →
      (T0.D N).fPosMR (groupedMarkedField dc72.toParameters N) (11/8) α y ≤ ((((-256471011 : ℚ) / 536870912) : ℚ) : ℝ)+ε := by
  have key := Generic.rowPosHi_cell dc72 AssemblyBindings.X0 AssemblyBindings.hok0 AssemblyBindings.hRt0
    (rc := (11/8:ℝ)) (by norm_num) (α₂ := ((((1 : ℚ) / 200) : ℚ) : ℝ))
    (T0.spmAt ((1 : ℚ) / 200)) (T0.spmAt ((1 : ℚ) / 200)) FieldPositiveLimit0.terms
    (K := spmK T0.trial) (FieldPositiveLimit0.spmIdentity ((1 : ℚ) / 200))
    rfl rfl (δ := 0) (selfDistance _) (g := (98749/1000000:ℝ)) (xc := (999/1000:ℝ))
    (T := ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ)) (by norm_num) (by norm_num) (by rw [hTheta]; norm_num) upper
  intro ε hε
  filter_upwards [key ε hε] with N hN α hα y hy hg hxc
  have ha : α ≤ ((((1 : ℚ) / 200) : ℚ) : ℝ) := by norm_num; exact hα
  have h := hN α ha y hy hg hxc
  change (T0.D N).fPosMR (groupedMarkedField dc72.toParameters N) (11/8) α y ≤ _ at h
  simp only [Rat.cast_zero, add_zero] at h
  have hk := FieldPositiveLimit0.spmOffset
  have hc : ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2619484754487 : ℚ) / 549755813888) : ℚ) : ℝ) ≤ ((((-256471011 : ℚ) / 536870912) : ℚ) : ℝ) := by norm_num
  linarith only [h,hk,hc]
#print axioms offSmallOf
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPm0
