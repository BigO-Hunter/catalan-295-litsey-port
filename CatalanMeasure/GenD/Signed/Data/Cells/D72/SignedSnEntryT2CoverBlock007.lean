module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core110
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core111
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core112
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core113
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core114
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core115
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core116
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core117
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core118
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core119
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core120
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core121
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core122
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core123
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core124
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core125
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell112 : ∀ y ∈ Icc ((((-323119 : ℚ) / 2048000) : ℚ) : ℝ) ((((-391223 : ℚ) / 2560000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P110Lo : ℝ) (ceSignedSnEntryT2P110Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P110Lo, ceSignedSnEntryT2P110Hi, SignedSnEntryT2Core110Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P110Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core110Literal.q2] at h ⊢
  exact h

private theorem cell113 : ∀ y ∈ Icc ((((-391223 : ℚ) / 2560000) : ℚ) : ℝ) ((((-187161 : ℚ) / 1280000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P111Lo : ℝ) (ceSignedSnEntryT2P111Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P111Lo, ceSignedSnEntryT2P111Hi, SignedSnEntryT2Core111Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P111Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core111Literal.q2] at h ⊢
  exact h

private theorem cell114 : ∀ y ∈ Icc ((((-187161 : ℚ) / 1280000) : ℚ) : ℝ) ((((-357421 : ℚ) / 2560000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P112Lo : ℝ) (ceSignedSnEntryT2P112Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P112Lo, ceSignedSnEntryT2P112Hi, SignedSnEntryT2Core112Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P112Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core112Literal.q2] at h ⊢
  exact h

private theorem cell115 : ∀ y ∈ Icc ((((-357421 : ℚ) / 2560000) : ℚ) : ℝ) ((((-8513 : ℚ) / 64000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P113Lo : ℝ) (ceSignedSnEntryT2P113Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P113Lo, ceSignedSnEntryT2P113Hi, SignedSnEntryT2Core113Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P113Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core113Literal.q2] at h ⊢
  exact h

private theorem cell116 : ∀ y ∈ Icc ((((-8513 : ℚ) / 64000) : ℚ) : ℝ) ((((-664139 : ℚ) / 5120000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P114Lo : ℝ) (ceSignedSnEntryT2P114Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P114Lo, ceSignedSnEntryT2P114Hi, SignedSnEntryT2Core114Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P114Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core114Literal.q2] at h ⊢
  exact h

private theorem cell117 : ∀ y ∈ Icc ((((-664139 : ℚ) / 5120000) : ℚ) : ℝ) ((((-2605853 : ℚ) / 20480000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P115Lo : ℝ) (ceSignedSnEntryT2P115Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P115Lo, ceSignedSnEntryT2P115Hi, SignedSnEntryT2Core115Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P115Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core115Literal.q2] at h ⊢
  exact h

private theorem cell118 : ∀ y ∈ Icc ((((-2605853 : ℚ) / 20480000) : ℚ) : ℝ) ((((-323619 : ℚ) / 2560000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P116Lo : ℝ) (ceSignedSnEntryT2P116Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P116Lo, ceSignedSnEntryT2P116Hi, SignedSnEntryT2Core116Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P116Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core116Literal.q2] at h ⊢
  exact h

private theorem cell119 : ∀ y ∈ Icc ((((-323619 : ℚ) / 2560000) : ℚ) : ℝ) ((((-5161003 : ℚ) / 40960000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P117Lo : ℝ) (ceSignedSnEntryT2P117Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P117Lo, ceSignedSnEntryT2P117Hi, SignedSnEntryT2Core117Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P117Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core117Literal.q2] at h ⊢
  exact h

private theorem cell120 : ∀ y ∈ Icc ((((-5161003 : ℚ) / 40960000) : ℚ) : ℝ) ((((-10271303 : ℚ) / 81920000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P118Lo : ℝ) (ceSignedSnEntryT2P118Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P118Lo, ceSignedSnEntryT2P118Hi, SignedSnEntryT2Core118Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P118Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core118Literal.q2] at h ⊢
  exact h

private theorem cell121 : ∀ y ∈ Icc ((((-10271303 : ℚ) / 81920000) : ℚ) : ℝ) ((((-51103 : ℚ) / 409600) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P119Lo : ℝ) (ceSignedSnEntryT2P119Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P119Lo, ceSignedSnEntryT2P119Hi, SignedSnEntryT2Core119Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P119Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core119Literal.q2] at h ⊢
  exact h

private theorem cell122 : ∀ y ∈ Icc ((((-51103 : ℚ) / 409600) : ℚ) : ℝ) ((((-630337 : ℚ) / 5120000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P120Lo : ℝ) (ceSignedSnEntryT2P120Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P120Lo, ceSignedSnEntryT2P120Hi, SignedSnEntryT2Core120Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P120Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core120Literal.q2] at h ⊢
  exact h

private theorem cell123 : ∀ y ∈ Icc ((((-630337 : ℚ) / 5120000) : ℚ) : ℝ) ((((-153359 : ℚ) / 1280000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P121Lo : ℝ) (ceSignedSnEntryT2P121Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P121Lo, ceSignedSnEntryT2P121Hi, SignedSnEntryT2Core121Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P121Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core121Literal.q2] at h ⊢
  exact h

private theorem cell124 : ∀ y ∈ Icc ((((-153359 : ℚ) / 1280000) : ℚ) : ℝ) ((((-289817 : ℚ) / 2560000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P122Lo : ℝ) (ceSignedSnEntryT2P122Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P122Lo, ceSignedSnEntryT2P122Hi, SignedSnEntryT2Core122Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P122Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core122Literal.q2] at h ⊢
  exact h

private theorem cell125 : ∀ y ∈ Icc ((((-289817 : ℚ) / 2560000) : ℚ) : ℝ) ((((-68229 : ℚ) / 640000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P123Lo : ℝ) (ceSignedSnEntryT2P123Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P123Lo, ceSignedSnEntryT2P123Hi, SignedSnEntryT2Core123Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P123Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core123Literal.q2] at h ⊢
  exact h

private theorem cell126 : ∀ y ∈ Icc ((((-68229 : ℚ) / 640000) : ℚ) : ℝ) ((((-51203 : ℚ) / 512000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P124Lo : ℝ) (ceSignedSnEntryT2P124Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P124Lo, ceSignedSnEntryT2P124Hi, SignedSnEntryT2Core124Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P124Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core124Literal.q2] at h ⊢
  exact h

private theorem cell127 : ∀ y ∈ Icc ((((-51203 : ℚ) / 512000) : ℚ) : ℝ) ((((-119557 : ℚ) / 1280000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P125Lo : ℝ) (ceSignedSnEntryT2P125Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P125Lo, ceSignedSnEntryT2P125Hi, SignedSnEntryT2Core125Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P125Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core125Literal.q2] at h ⊢
  exact h

theorem cover007 : ∀ y ∈ Icc ((((-323119 : ℚ) / 2048000) : ℚ) : ℝ) ((((-119557 : ℚ) / 1280000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell112 cell113) (cover_union cell114 cell115)) (cover_union (cover_union cell116 cell117) (cover_union cell118 cell119))) (cover_union (cover_union (cover_union cell120 cell121) (cover_union cell122 cell123)) (cover_union (cover_union cell124 cell125) (cover_union cell126 cell127))))
#print axioms cover007
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
