module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core126
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core127
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core128
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core129
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core130
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core131
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core132
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core133
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core134
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core135
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core136
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core137
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core138
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core139
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2End02
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell128 : ∀ y ∈ Icc ((((-119557 : ℚ) / 1280000) : ℚ) : ℝ) ((((-222213 : ℚ) / 2560000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P126Lo : ℝ) (ceSignedSnEntryT2P126Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P126Lo, ceSignedSnEntryT2P126Hi, SignedSnEntryT2Core126Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P126Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core126Literal.q2] at h ⊢
  exact h

private theorem cell129 : ∀ y ∈ Icc ((((-222213 : ℚ) / 2560000) : ℚ) : ℝ) ((((-401 : ℚ) / 5000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P127Lo : ℝ) (ceSignedSnEntryT2P127Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P127Lo, ceSignedSnEntryT2P127Hi, SignedSnEntryT2Core127Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P127Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core127Literal.q2] at h ⊢
  exact h

private theorem cell130 : ∀ y ∈ Icc ((((-401 : ℚ) / 5000) : ℚ) : ℝ) ((((-188411 : ℚ) / 2560000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P128Lo : ℝ) (ceSignedSnEntryT2P128Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P128Lo, ceSignedSnEntryT2P128Hi, SignedSnEntryT2Core128Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P128Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core128Literal.q2] at h ⊢
  exact h

private theorem cell131 : ∀ y ∈ Icc ((((-188411 : ℚ) / 2560000) : ℚ) : ℝ) ((((-17151 : ℚ) / 256000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P129Lo : ℝ) (ceSignedSnEntryT2P129Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P129Lo, ceSignedSnEntryT2P129Hi, SignedSnEntryT2Core129Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P129Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core129Literal.q2] at h ⊢
  exact h

private theorem cell132 : ∀ y ∈ Icc ((((-17151 : ℚ) / 256000) : ℚ) : ℝ) ((((-154609 : ℚ) / 2560000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P130Lo : ℝ) (ceSignedSnEntryT2P130Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P130Lo, ceSignedSnEntryT2P130Hi, SignedSnEntryT2Core130Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P130Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core130Literal.q2] at h ⊢
  exact h

private theorem cell133 : ∀ y ∈ Icc ((((-154609 : ℚ) / 2560000) : ℚ) : ℝ) ((((-34427 : ℚ) / 640000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P131Lo : ℝ) (ceSignedSnEntryT2P131Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P131Lo, ceSignedSnEntryT2P131Hi, SignedSnEntryT2Core131Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P131Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core131Literal.q2] at h ⊢
  exact h

private theorem cell134 : ∀ y ∈ Icc ((((-34427 : ℚ) / 640000) : ℚ) : ℝ) ((((-120807 : ℚ) / 2560000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P132Lo : ℝ) (ceSignedSnEntryT2P132Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P132Lo, ceSignedSnEntryT2P132Hi, SignedSnEntryT2Core132Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P132Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core132Literal.q2] at h ⊢
  exact h

private theorem cell135 : ∀ y ∈ Icc ((((-120807 : ℚ) / 2560000) : ℚ) : ℝ) ((((-51953 : ℚ) / 1280000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P133Lo : ℝ) (ceSignedSnEntryT2P133Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P133Lo, ceSignedSnEntryT2P133Hi, SignedSnEntryT2Core133Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P133Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core133Literal.q2] at h ⊢
  exact h

private theorem cell136 : ∀ y ∈ Icc ((((-51953 : ℚ) / 1280000) : ℚ) : ℝ) ((((-17401 : ℚ) / 512000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P134Lo : ℝ) (ceSignedSnEntryT2P134Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P134Lo, ceSignedSnEntryT2P134Hi, SignedSnEntryT2Core134Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P134Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core134Literal.q2] at h ⊢
  exact h

private theorem cell137 : ∀ y ∈ Icc ((((-17401 : ℚ) / 512000) : ℚ) : ℝ) ((((-8763 : ℚ) / 320000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P135Lo : ℝ) (ceSignedSnEntryT2P135Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P135Lo, ceSignedSnEntryT2P135Hi, SignedSnEntryT2Core135Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P135Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core135Literal.q2] at h ⊢
  exact h

private theorem cell138 : ∀ y ∈ Icc ((((-8763 : ℚ) / 320000) : ℚ) : ℝ) ((((-53203 : ℚ) / 2560000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P136Lo : ℝ) (ceSignedSnEntryT2P136Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P136Lo, ceSignedSnEntryT2P136Hi, SignedSnEntryT2Core136Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P136Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core136Literal.q2] at h ⊢
  exact h

private theorem cell139 : ∀ y ∈ Icc ((((-53203 : ℚ) / 2560000) : ℚ) : ℝ) ((((-18151 : ℚ) / 1280000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P137Lo : ℝ) (ceSignedSnEntryT2P137Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P137Lo, ceSignedSnEntryT2P137Hi, SignedSnEntryT2Core137Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P137Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core137Literal.q2] at h ⊢
  exact h

private theorem cell140 : ∀ y ∈ Icc ((((-18151 : ℚ) / 1280000) : ℚ) : ℝ) ((((-19401 : ℚ) / 2560000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P138Lo : ℝ) (ceSignedSnEntryT2P138Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P138Lo, ceSignedSnEntryT2P138Hi, SignedSnEntryT2Core138Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P138Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core138Literal.q2] at h ⊢
  exact h

private theorem cell141 : ∀ y ∈ Icc ((((-19401 : ℚ) / 2560000) : ℚ) : ℝ) ((((-1 : ℚ) / 1024) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P139Lo : ℝ) (ceSignedSnEntryT2P139Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P139Lo, ceSignedSnEntryT2P139Hi, SignedSnEntryT2Core139Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P139Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core139Literal.q2] at h ⊢
  exact h

theorem endIdentity142 : fieldNFCheck ceSignedSnEntryT2E02FullFq ceSignedSnEntryT2Fq = true := by decide +kernel
    
private theorem cell142 : ∀ y ∈ Icc ((((-1 : ℚ) / 1024) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2E02Lo : ℝ) (ceSignedSnEntryT2E02Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2E02Lo, ceSignedSnEntryT2E02Hi, SignedSnEntryT2End02Literal.q2, ceSignedSnEntryT2E02EndLiteral.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2E02Bound y hx (by norm_num [ceSignedSnEntryT2E02Site, ceSignedSnEntryT2E02EndLiteral.q2]; exact ne_of_lt hd.2)
  rw [fieldNFCheck_sound endIdentity142 y] at h
  simp only [ceSignedSnEntryT2E02FullTs, lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2End02Literal.q2, ceSignedSnEntryT2E02Target, ceSignedSnEntryT2E02EndLiteral.q2] at h ⊢
  exact h

theorem cover008 : ∀ y ∈ Icc ((((-119557 : ℚ) / 1280000) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union cell128 (cover_union cell129 cell130)) (cover_union (cover_union cell131 cell132) (cover_union cell133 cell134))) (cover_union (cover_union (cover_union cell135 cell136) (cover_union cell137 cell138)) (cover_union (cover_union cell139 cell140) (cover_union cell141 cell142))))
#print axioms cover008
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
