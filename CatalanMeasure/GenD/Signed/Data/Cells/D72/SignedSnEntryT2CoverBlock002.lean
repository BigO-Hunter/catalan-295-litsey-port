module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core031
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core039
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core046
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell032 : ∀ y ∈ Icc ((((-5348147640125229 : ℚ) / 5497558138880000) : ℚ) : ℝ) ((((-332925205197561 : ℚ) / 343597383680000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P031Lo : ℝ) (ceSignedSnEntryT2P031Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P031Lo, ceSignedSnEntryT2P031Hi, SignedSnEntryT2Core031Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P031Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core031Literal.q2] at h ⊢
  exact h

private theorem cell033 : ∀ y ∈ Icc ((((-332925205197561 : ℚ) / 343597383680000) : ℚ) : ℝ) ((((-528411456923247 : ℚ) / 549755813888000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P032Lo : ℝ) (ceSignedSnEntryT2P032Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P032Lo, ceSignedSnEntryT2P032Hi, SignedSnEntryT2Core032Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P032Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core032Literal.q2] at h ⊢
  exact h

private theorem cell034 : ∀ y ∈ Icc ((((-528411456923247 : ℚ) / 549755813888000) : ℚ) : ℝ) ((((-5262770212268217 : ℚ) / 5497558138880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P033Lo : ℝ) (ceSignedSnEntryT2P033Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P033Lo, ceSignedSnEntryT2P033Hi, SignedSnEntryT2Core033Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P033Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core033Literal.q2] at h ⊢
  exact h

private theorem cell035 : ∀ y ∈ Icc ((((-5262770212268217 : ℚ) / 5497558138880000) : ℚ) : ℝ) ((((-2599368570687729 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P034Lo : ℝ) (ceSignedSnEntryT2P034Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P034Lo, ceSignedSnEntryT2P034Hi, SignedSnEntryT2Core034Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P034Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core034Literal.q2] at h ⊢
  exact h

private theorem cell036 : ∀ y ∈ Icc ((((-2599368570687729 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-1035478556882241 : ℚ) / 1099511627776000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P035Lo : ℝ) (ceSignedSnEntryT2P035Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P035Lo, ceSignedSnEntryT2P035Hi, SignedSnEntryT2Core035Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P035Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core035Literal.q2] at h ⊢
  exact h

private theorem cell037 : ∀ y ∈ Icc ((((-1035478556882241 : ℚ) / 1099511627776000) : ℚ) : ℝ) ((((-5092015356554193 : ℚ) / 5497558138880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P036Lo : ℝ) (ceSignedSnEntryT2P036Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P036Lo, ceSignedSnEntryT2P036Hi, SignedSnEntryT2Core036Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P036Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core036Literal.q2] at h ⊢
  exact h

private theorem cell038 : ∀ y ∈ Icc ((((-5092015356554193 : ℚ) / 5497558138880000) : ℚ) : ℝ) ((((-253533549979497 : ℚ) / 274877906944000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P037Lo : ℝ) (ceSignedSnEntryT2P037Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P037Lo, ceSignedSnEntryT2P037Hi, SignedSnEntryT2Core037Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P037Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core037Literal.q2] at h ⊢
  exact h

private theorem cell039 : ∀ y ∈ Icc ((((-253533549979497 : ℚ) / 274877906944000) : ℚ) : ℝ) ((((-77895212058327 : ℚ) / 85899345920000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P038Lo : ℝ) (ceSignedSnEntryT2P038Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P038Lo, ceSignedSnEntryT2P038Hi, SignedSnEntryT2Core038Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P038Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core038Literal.q2] at h ⊢
  exact h

private theorem cell040 : ∀ y ∈ Icc ((((-77895212058327 : ℚ) / 85899345920000) : ℚ) : ℝ) ((((-2471302428902211 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P039Lo : ℝ) (ceSignedSnEntryT2P039Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P039Lo, ceSignedSnEntryT2P039Hi, SignedSnEntryT2Core039Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P039Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core039Literal.q2] at h ⊢
  exact h

private theorem cell041 : ∀ y ∈ Icc ((((-2471302428902211 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-485722742994741 : ℚ) / 549755813888000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P040Lo : ℝ) (ceSignedSnEntryT2P040Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P040Lo, ceSignedSnEntryT2P040Hi, SignedSnEntryT2Core040Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P040Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core040Literal.q2] at h ⊢
  exact h

private theorem cell042 : ∀ y ∈ Icc ((((-485722742994741 : ℚ) / 549755813888000) : ℚ) : ℝ) ((((-601817339502363 : ℚ) / 687194767360000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P041Lo : ℝ) (ceSignedSnEntryT2P041Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P041Lo, ceSignedSnEntryT2P041Hi, SignedSnEntryT2Core041Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P041Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core041Literal.q2] at h ⊢
  exact h

private theorem cell043 : ∀ y ∈ Icc ((((-601817339502363 : ℚ) / 687194767360000) : ℚ) : ℝ) ((((-1182290322040473 : ℚ) / 1374389534720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P042Lo : ℝ) (ceSignedSnEntryT2P042Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P042Lo, ceSignedSnEntryT2P042Hi, SignedSnEntryT2Core042Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P042Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core042Literal.q2] at h ⊢
  exact h

private theorem cell044 : ∀ y ∈ Icc ((((-1182290322040473 : ℚ) / 1374389534720000) : ℚ) : ℝ) ((((-2343236287116693 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P043Lo : ℝ) (ceSignedSnEntryT2P043Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P043Lo, ceSignedSnEntryT2P043Hi, SignedSnEntryT2Core043Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P043Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core043Literal.q2] at h ⊢
  exact h

private theorem cell045 : ∀ y ∈ Icc ((((-2343236287116693 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-88606805813247 : ℚ) / 109951162777600) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P044Lo : ℝ) (ceSignedSnEntryT2P044Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P044Lo, ceSignedSnEntryT2P044Hi, SignedSnEntryT2Core044Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P044Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core044Literal.q2] at h ⊢
  exact h

private theorem cell046 : ∀ y ∈ Icc ((((-88606805813247 : ℚ) / 109951162777600) : ℚ) : ℝ) ((((-1096912894183461 : ℚ) / 1374389534720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P045Lo : ℝ) (ceSignedSnEntryT2P045Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P045Lo, ceSignedSnEntryT2P045Hi, SignedSnEntryT2Core045Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P045Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core045Literal.q2] at h ⊢
  exact h

private theorem cell047 : ∀ y ∈ Icc ((((-1096912894183461 : ℚ) / 1374389534720000) : ℚ) : ℝ) ((((-134446067152401 : ℚ) / 171798691840000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P046Lo : ℝ) (ceSignedSnEntryT2P046Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P046Lo, ceSignedSnEntryT2P046Hi, SignedSnEntryT2Core046Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P046Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core046Literal.q2] at h ⊢
  exact h

theorem cover002 : ∀ y ∈ Icc ((((-5348147640125229 : ℚ) / 5497558138880000) : ℚ) : ℝ) ((((-134446067152401 : ℚ) / 171798691840000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell032 cell033) (cover_union cell034 cell035)) (cover_union (cover_union cell036 cell037) (cover_union cell038 cell039))) (cover_union (cover_union (cover_union cell040 cell041) (cover_union cell042 cell043)) (cover_union (cover_union cell044 cell045) (cover_union cell046 cell047))))
#print axioms cover002
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
