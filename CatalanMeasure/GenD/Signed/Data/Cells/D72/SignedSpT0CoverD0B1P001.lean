module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0039
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0046
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0047
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0048
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0049
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverD0B1P001L016 : ∀ x ∈ Icc ((((17013 : ℚ) / 57344) : ℚ) : ℝ) ((((4477 : ℚ) / 14336) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0034Lo : ℝ) (ceSignedSpT0P0034Hi : ℝ) := by
    norm_num [ceSignedSpT0P0034Lo, ceSignedSpT0P0034Hi, SignedSpT0P0034Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0034Bound x h'
  norm_num [SignedSpT0P0034Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P001L017 : ∀ x ∈ Icc ((((4477 : ℚ) / 14336) : ℚ) : ℝ) ((((1407 : ℚ) / 4096) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0035Lo : ℝ) (ceSignedSpT0P0035Hi : ℝ) := by
    norm_num [ceSignedSpT0P0035Lo, ceSignedSpT0P0035Hi, SignedSpT0P0035Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0035Bound x h'
  norm_num [SignedSpT0P0035Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P001L018 : ∀ x ∈ Icc ((((1407 : ℚ) / 4096) : ℚ) : ℝ) ((((1343 : ℚ) / 3584) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0036Lo : ℝ) (ceSignedSpT0P0036Hi : ℝ) := by
    norm_num [ceSignedSpT0P0036Lo, ceSignedSpT0P0036Hi, SignedSpT0P0036Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0036Bound x h'
  norm_num [SignedSpT0P0036Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P001L019 : ∀ x ∈ Icc ((((1343 : ℚ) / 3584) : ℚ) : ℝ) ((((11639 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0037Lo : ℝ) (ceSignedSpT0P0037Hi : ℝ) := by
    norm_num [ceSignedSpT0P0037Lo, ceSignedSpT0P0037Hi, SignedSpT0P0037Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0037Bound x h'
  norm_num [SignedSpT0P0037Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P001L020 : ∀ x ∈ Icc ((((11639 : ℚ) / 28672) : ℚ) : ℝ) ((((6267 : ℚ) / 14336) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0038Lo : ℝ) (ceSignedSpT0P0038Hi : ℝ) := by
    norm_num [ceSignedSpT0P0038Lo, ceSignedSpT0P0038Hi, SignedSpT0P0038Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0038Bound x h'
  norm_num [SignedSpT0P0038Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P001L021 : ∀ x ∈ Icc ((((6267 : ℚ) / 14336) : ℚ) : ℝ) ((((13429 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0039Lo : ℝ) (ceSignedSpT0P0039Hi : ℝ) := by
    norm_num [ceSignedSpT0P0039Lo, ceSignedSpT0P0039Hi, SignedSpT0P0039Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0039Bound x h'
  norm_num [SignedSpT0P0039Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P001L022 : ∀ x ∈ Icc ((((13429 : ℚ) / 28672) : ℚ) : ℝ) ((((15219 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0040Lo : ℝ) (ceSignedSpT0P0040Hi : ℝ) := by
    norm_num [ceSignedSpT0P0040Lo, ceSignedSpT0P0040Hi, SignedSpT0P0040Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0040Bound x h'
  norm_num [SignedSpT0P0040Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P001L023 : ∀ x ∈ Icc ((((15219 : ℚ) / 28672) : ℚ) : ℝ) ((((17009 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0041Lo : ℝ) (ceSignedSpT0P0041Hi : ℝ) := by
    norm_num [ceSignedSpT0P0041Lo, ceSignedSpT0P0041Hi, SignedSpT0P0041Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0041Bound x h'
  norm_num [SignedSpT0P0041Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P001L024 : ∀ x ∈ Icc ((((17009 : ℚ) / 28672) : ℚ) : ℝ) ((((18799 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0042Lo : ℝ) (ceSignedSpT0P0042Hi : ℝ) := by
    norm_num [ceSignedSpT0P0042Lo, ceSignedSpT0P0042Hi, SignedSpT0P0042Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0042Bound x h'
  norm_num [SignedSpT0P0042Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P001L025 : ∀ x ∈ Icc ((((18799 : ℚ) / 28672) : ℚ) : ℝ) ((((9847 : ℚ) / 14336) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0043Lo : ℝ) (ceSignedSpT0P0043Hi : ℝ) := by
    norm_num [ceSignedSpT0P0043Lo, ceSignedSpT0P0043Hi, SignedSpT0P0043Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0043Bound x h'
  norm_num [SignedSpT0P0043Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P001L026 : ∀ x ∈ Icc ((((9847 : ℚ) / 14336) : ℚ) : ℝ) ((((20589 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0044Lo : ℝ) (ceSignedSpT0P0044Hi : ℝ) := by
    norm_num [ceSignedSpT0P0044Lo, ceSignedSpT0P0044Hi, SignedSpT0P0044Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0044Bound x h'
  norm_num [SignedSpT0P0044Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P001L027 : ∀ x ∈ Icc ((((20589 : ℚ) / 28672) : ℚ) : ℝ) ((((5371 : ℚ) / 7168) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0045Lo : ℝ) (ceSignedSpT0P0045Hi : ℝ) := by
    norm_num [ceSignedSpT0P0045Lo, ceSignedSpT0P0045Hi, SignedSpT0P0045Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0045Bound x h'
  norm_num [SignedSpT0P0045Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P001L028 : ∀ x ∈ Icc ((((5371 : ℚ) / 7168) : ℚ) : ℝ) ((((3197 : ℚ) / 4096) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0046Lo : ℝ) (ceSignedSpT0P0046Hi : ℝ) := by
    norm_num [ceSignedSpT0P0046Lo, ceSignedSpT0P0046Hi, SignedSpT0P0046Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0046Bound x h'
  norm_num [SignedSpT0P0046Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P001L029 : ∀ x ∈ Icc ((((3197 : ℚ) / 4096) : ℚ) : ℝ) ((((11637 : ℚ) / 14336) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0047Lo : ℝ) (ceSignedSpT0P0047Hi : ℝ) := by
    norm_num [ceSignedSpT0P0047Lo, ceSignedSpT0P0047Hi, SignedSpT0P0047Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0047Bound x h'
  norm_num [SignedSpT0P0047Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P001L030 : ∀ x ∈ Icc ((((11637 : ℚ) / 14336) : ℚ) : ℝ) ((((24169 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0048Lo : ℝ) (ceSignedSpT0P0048Hi : ℝ) := by
    norm_num [ceSignedSpT0P0048Lo, ceSignedSpT0P0048Hi, SignedSpT0P0048Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0048Bound x h'
  norm_num [SignedSpT0P0048Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P001L031 : ∀ x ∈ Icc ((((24169 : ℚ) / 28672) : ℚ) : ℝ) ((((49233 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0049Lo : ℝ) (ceSignedSpT0P0049Hi : ℝ) := by
    norm_num [ceSignedSpT0P0049Lo, ceSignedSpT0P0049Hi, SignedSpT0P0049Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0049Bound x h'
  norm_num [SignedSpT0P0049Literal.q2] at h ⊢
  exact h

theorem SignedSpT0CoverD0B1P001 : ∀ x ∈ Icc ((((17013 : ℚ) / 57344) : ℚ) : ℝ) ((((49233 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT0CoverD0B1P001L016 SignedSpT0CoverD0B1P001L017) (cover_union SignedSpT0CoverD0B1P001L018 SignedSpT0CoverD0B1P001L019)) (cover_union (cover_union SignedSpT0CoverD0B1P001L020 SignedSpT0CoverD0B1P001L021) (cover_union SignedSpT0CoverD0B1P001L022 SignedSpT0CoverD0B1P001L023))) (cover_union (cover_union (cover_union SignedSpT0CoverD0B1P001L024 SignedSpT0CoverD0B1P001L025) (cover_union SignedSpT0CoverD0B1P001L026 SignedSpT0CoverD0B1P001L027)) (cover_union (cover_union SignedSpT0CoverD0B1P001L028 SignedSpT0CoverD0B1P001L029) (cover_union SignedSpT0CoverD0B1P001L030 SignedSpT0CoverD0B1P001L031))))
#print axioms SignedSpT0CoverD0B1P001

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
