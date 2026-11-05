module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core031
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core039
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core046
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell032 : ∀ y ∈ Icc ((((-34085934202849 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((-16493748158449 : ℚ) / 17592186044416) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P031Lo : ℝ) (ceSignedSnEntryT0P031Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P031Lo, ceSignedSnEntryT0P031Hi, SignedSnEntryT0Core031Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P031Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core031Literal.q2] at h ⊢
  exact h

private theorem cell033 : ∀ y ∈ Icc ((((-16493748158449 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((-7697655136249 : ℚ) / 8796093022208) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P032Lo : ℝ) (ceSignedSnEntryT0P032Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P032Lo, ceSignedSnEntryT0P032Hi, SignedSnEntryT0Core032Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P032Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core032Literal.q2] at h ⊢
  exact h

private theorem cell034 : ∀ y ∈ Icc ((((-7697655136249 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((-3299608625149 : ℚ) / 4398046511104) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P033Lo : ℝ) (ceSignedSnEntryT0P033Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P033Lo, ceSignedSnEntryT0P033Hi, SignedSnEntryT0Core033Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P033Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core033Literal.q2] at h ⊢
  exact h

private theorem cell035 : ∀ y ∈ Icc ((((-3299608625149 : ℚ) / 4398046511104) : ℚ) : ℝ) ((((-20904679571437 : ℚ) / 35184372088832) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P034Lo : ℝ) (ceSignedSnEntryT0P034Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P034Lo, ceSignedSnEntryT0P034Hi, SignedSnEntryT0Core034Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P034Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core034Literal.q2] at h ⊢
  exact h

private theorem cell036 : ∀ y ∈ Icc ((((-20904679571437 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((-7706245070841 : ℚ) / 17592186044416) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P035Lo : ℝ) (ceSignedSnEntryT0P035Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P035Lo, ceSignedSnEntryT0P035Hi, SignedSnEntryT0Core035Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P035Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core035Literal.q2] at h ⊢
  exact h

private theorem cell037 : ∀ y ∈ Icc ((((-7706245070841 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((-5509369298939 : ℚ) / 17592186044416) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P036Lo : ℝ) (ceSignedSnEntryT0P036Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P036Lo, ceSignedSnEntryT0P036Hi, SignedSnEntryT0Core036Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P036Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core036Literal.q2] at h ⊢
  exact h

private theorem cell038 : ∀ y ∈ Icc ((((-5509369298939 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((-9920300711927 : ℚ) / 35184372088832) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P037Lo : ℝ) (ceSignedSnEntryT0P037Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P037Lo, ceSignedSnEntryT0P037Hi, SignedSnEntryT0Core037Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P037Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core037Literal.q2] at h ⊢
  exact h

private theorem cell039 : ∀ y ∈ Icc ((((-9920300711927 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((-1102732853247 : ℚ) / 4398046511104) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P038Lo : ℝ) (ceSignedSnEntryT0P038Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P038Lo, ceSignedSnEntryT0P038Hi, SignedSnEntryT0Core038Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P038Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core038Literal.q2] at h ⊢
  exact h

private theorem cell040 : ∀ y ∈ Icc ((((-1102732853247 : ℚ) / 4398046511104) : ℚ) : ℝ) ((((-14348411994099 : ℚ) / 70368744177664) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P039Lo : ℝ) (ceSignedSnEntryT0P039Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P039Lo, ceSignedSnEntryT0P039Hi, SignedSnEntryT0Core039Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P039Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core039Literal.q2] at h ⊢
  exact h

private theorem cell041 : ∀ y ∈ Icc ((((-14348411994099 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((-3312493527037 : ℚ) / 17592186044416) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P040Lo : ℝ) (ceSignedSnEntryT0P040Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P040Lo, ceSignedSnEntryT0P040Hi, SignedSnEntryT0Core040Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P040Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core040Literal.q2] at h ⊢
  exact h

private theorem cell042 : ∀ y ∈ Icc ((((-3312493527037 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((-12151536222197 : ℚ) / 70368744177664) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P041Lo : ℝ) (ceSignedSnEntryT0P041Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P041Lo, ceSignedSnEntryT0P041Hi, SignedSnEntryT0Core041Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P041Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core041Literal.q2] at h ⊢
  exact h

private theorem cell043 : ∀ y ∈ Icc ((((-12151536222197 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((-47507707002837 : ℚ) / 281474976710656) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P042Lo : ℝ) (ceSignedSnEntryT0P042Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P042Lo, ceSignedSnEntryT0P042Hi, SignedSnEntryT0Core042Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P042Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core042Literal.q2] at h ⊢
  exact h

private theorem cell044 : ∀ y ∈ Icc ((((-47507707002837 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((-23204634558443 : ℚ) / 140737488355328) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P043Lo : ℝ) (ceSignedSnEntryT0P043Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P043Lo, ceSignedSnEntryT0P043Hi, SignedSnEntryT0Core043Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P043Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core043Literal.q2] at h ⊢
  exact h

private theorem cell045 : ∀ y ∈ Icc ((((-23204634558443 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((-5526549168123 : ℚ) / 35184372088832) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P044Lo : ℝ) (ceSignedSnEntryT0P044Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P044Lo, ceSignedSnEntryT0P044Hi, SignedSnEntryT0Core044Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P044Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core044Literal.q2] at h ⊢
  exact h

private theorem cell046 : ∀ y ∈ Icc ((((-5526549168123 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((-21007758786541 : ℚ) / 140737488355328) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P045Lo : ℝ) (ceSignedSnEntryT0P045Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P045Lo, ceSignedSnEntryT0P045Hi, SignedSnEntryT0Core045Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P045Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core045Literal.q2] at h ⊢
  exact h

private theorem cell047 : ∀ y ∈ Icc ((((-21007758786541 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((-9954660450295 : ℚ) / 70368744177664) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P046Lo : ℝ) (ceSignedSnEntryT0P046Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P046Lo, ceSignedSnEntryT0P046Hi, SignedSnEntryT0Core046Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P046Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core046Literal.q2] at h ⊢
  exact h

theorem cover002 : ∀ y ∈ Icc ((((-34085934202849 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((-9954660450295 : ℚ) / 70368744177664) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell032 cell033) (cover_union cell034 cell035)) (cover_union (cover_union cell036 cell037) (cover_union cell038 cell039))) (cover_union (cover_union (cover_union cell040 cell041) (cover_union cell042 cell043)) (cover_union (cover_union cell044 cell045) (cover_union cell046 cell047))))
#print axioms cover002
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover
