module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Endpoints
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldPositiveLimit1

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSP1
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly
open CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Endpoints
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

abbrev S : ℚ := ((-936093947 : ℚ) / 536870912)
private abbrev K : ℚ := ((3518941170099 : ℚ) / 549755813888)
private abbrev C : ℚ := ((5 : ℚ) / 288)

private theorem selfDistance (p : List ℚ) : l1Q p p ≤ 0 := by
  induction p with
  | nil => simp [l1Q]
  | cons a p ih => simpa [l1Q, qAbs] using ih

theorem eventualOf
    (before : ∀ y ∈ Ioc (ceSignedSpT1End00Hi : ℝ) (1023/1024 : ℝ),
      fieldTower T1.spFq (poleF T1.spFq.poles) 0 y + lfieldTower terms 0 y ≤ (ceSignedSpT1ZeroCap : ℝ))
    (after : ∀ y ∈ Ico (1023/1024 : ℝ) 1,
      fieldTower T1.spFq (poleF T1.spFq.poles) 0 y + lfieldTower terms 0 y ≤ (ceSignedSpT1End01Target : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ y ∈ Ioo (0 : ℝ) 1, (T1.D N).fPosS y ≤ (S : ℝ)+ε := by
  have cs : ((AssemblyBindings.X1.CSP : ℝ) / dc72.n0) = (C : ℝ) := by
    change ((T1.params.CSP : ℚ) : ℝ) / dc72.n0 = _
    norm_num [T1.params, dc72_n0, C]
  have b0 : ceSignedSpT1ZeroCap + K ≤ S := by decide +kernel
  have b1 : ceSignedSpT1End01Target + K + C ≤ S := by decide +kernel
  have b0R := (Rat.cast_le (K := ℝ)).mpr b0
  have b1R := (Rat.cast_le (K := ℝ)).mpr b1
  have koff := FieldPositiveLimit1.spOffset
  change spK T1.trial ≤ (K : ℝ) at koff
  have hlow := lowCap
  have hhigh := highCap
  simp only [Rat.cast_add] at b0R b1R
  have hr0 : 0 < ceSignedSpT1End00Hi := by decide +kernel
  have hr1 : ceSignedSpT1End00Hi < (1/8 : ℚ) := by decide +kernel
  have hhi0 : (1023/1024 : ℚ) < ceSignedSpT1End01Lo := by decide +kernel
  have hr1R : (ceSignedSpT1End00Hi : ℝ) < 1/8 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using (Rat.cast_lt (K := ℝ)).mpr hr1
  have hhi0R : (1023/1024 : ℝ) < (ceSignedSpT1End01Lo : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using (Rat.cast_lt (K := ℝ)).mpr hhi0
  have hhi1 : ceSignedSpT1End01Lo < 1 := by decide +kernel
  have c0 : 0 < zeroC := by decide +kernel
  have c1 : 0 < oneC := by decide +kernel
  exact Generic.rowSP_cell dc72 AssemblyBindings.X1 AssemblyBindings.hok1 AssemblyBindings.hRt1
    T1.spFq T1.spFq T1.spFq terms (K := spK T1.trial) FieldPositiveLimit1.spIdentity
    (by change (0:ℝ) ≤ ((T1.params.CSP : ℚ):ℝ); norm_num [T1.params])
    rfl rfl (δ2 := 0) (selfDistance _) rfl rfl (δ3 := 0) (selfDistance _)
    (h0 := (ceSignedSpT1End00Hi : ℝ)) (m1 := (1/8 : ℝ)) (j := (1023/1024 : ℝ)) (lo1 := (ceSignedSpT1End01Lo : ℝ))
    (TR0 := ((ceSignedSpT1End00TR + ceSignedSpT1End00U + zeroE : ℚ) : ℝ)) (c0 := (zeroC : ℝ))
    (T1 := (ceSignedSpT1ZeroCap : ℝ)) (T2 := (ceSignedSpT1ZeroCap : ℝ)) (T3 := (ceSignedSpT1End01Target : ℝ))
    (TR4 := ((ceSignedSpT1End01TR + ceSignedSpT1End01U : ℚ) : ℝ)) (c4 := (oneC : ℝ)) (S := (S : ℝ))
    (by exact_mod_cast hr0) hr1R (by norm_num) (by norm_num [dc72])
    hhi0R (by exact_mod_cast hhi1)
    lowLog (by exact_mod_cast c0)
    (fun y hy => before y ⟨hy.1, hy.2.le.trans (by norm_num)⟩)
    (fun y hy => before y ⟨hr1R.trans_le hy.1, hy.2⟩)
    after highLog (by exact_mod_cast c1)
    (by simp only [Rat.cast_zero, add_zero]; linarith only [hlow,koff,b0R])
    (by linarith only [koff,b0R])
    (by simp only [Rat.cast_zero, add_zero]; linarith only [koff,b0R])
    (by simp only [Rat.cast_zero, add_zero,cs]; linarith only [koff,b1R])
    (by simp only [Rat.cast_zero, add_zero,cs]; linarith only [hhigh,koff,b1R])
#print axioms eventualOf
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSP1
