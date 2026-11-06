module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0039
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0046
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0047
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmRT1116CoverD0B0P002L032 : ∀ x ∈ Icc ((((1996849 : ℚ) / 2900000) : ℚ) : ℝ) ((((20868741 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0032Lo : ℝ) (ceSignedSpmRT1116P0032Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0032Lo, ceSignedSpmRT1116P0032Hi, SignedSpmRT1116P0032Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0032Bound x h'
  norm_num [SignedSpmRT1116P0032Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P002L033 : ∀ x ∈ Icc ((((20868741 : ℚ) / 29000000) : ℚ) : ℝ) ((((680281 : ℚ) / 906250) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0033Lo : ℝ) (ceSignedSpmRT1116P0033Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0033Lo, ceSignedSpmRT1116P0033Hi, SignedSpmRT1116P0033Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0033Bound x h'
  norm_num [SignedSpmRT1116P0033Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P002L034 : ∀ x ∈ Icc ((((680281 : ℚ) / 906250) : ℚ) : ℝ) ((((22669243 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0034Lo : ℝ) (ceSignedSpmRT1116P0034Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0034Lo, ceSignedSpmRT1116P0034Hi, SignedSpmRT1116P0034Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0034Bound x h'
  norm_num [SignedSpmRT1116P0034Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P002L035 : ∀ x ∈ Icc ((((22669243 : ℚ) / 29000000) : ℚ) : ℝ) ((((11784747 : ℚ) / 14500000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0035Lo : ℝ) (ceSignedSpmRT1116P0035Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0035Lo, ceSignedSpmRT1116P0035Hi, SignedSpmRT1116P0035Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0035Bound x h'
  norm_num [SignedSpmRT1116P0035Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P002L036 : ∀ x ∈ Icc ((((11784747 : ℚ) / 14500000) : ℚ) : ℝ) ((((4893949 : ℚ) / 5800000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0036Lo : ℝ) (ceSignedSpmRT1116P0036Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0036Lo, ceSignedSpmRT1116P0036Hi, SignedSpmRT1116P0036Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0036Bound x h'
  norm_num [SignedSpmRT1116P0036Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P002L037 : ∀ x ∈ Icc ((((4893949 : ℚ) / 5800000) : ℚ) : ℝ) ((((49839741 : ℚ) / 58000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0037Lo : ℝ) (ceSignedSpmRT1116P0037Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0037Lo, ceSignedSpmRT1116P0037Hi, SignedSpmRT1116P0037Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0037Bound x h'
  norm_num [SignedSpmRT1116P0037Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P002L038 : ∀ x ∈ Icc ((((49839741 : ℚ) / 58000000) : ℚ) : ℝ) ((((6342499 : ℚ) / 7250000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0038Lo : ℝ) (ceSignedSpmRT1116P0038Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0038Lo, ceSignedSpmRT1116P0038Hi, SignedSpmRT1116P0038Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0038Bound x h'
  norm_num [SignedSpmRT1116P0038Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P002L039 : ∀ x ∈ Icc ((((6342499 : ℚ) / 7250000) : ℚ) : ℝ) ((((51640243 : ℚ) / 58000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0039Lo : ℝ) (ceSignedSpmRT1116P0039Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0039Lo, ceSignedSpmRT1116P0039Hi, SignedSpmRT1116P0039Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0039Bound x h'
  norm_num [SignedSpmRT1116P0039Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P002L040 : ∀ x ∈ Icc ((((51640243 : ℚ) / 58000000) : ℚ) : ℝ) ((((26270247 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0040Lo : ℝ) (ceSignedSpmRT1116P0040Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0040Lo, ceSignedSpmRT1116P0040Hi, SignedSpmRT1116P0040Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0040Bound x h'
  norm_num [SignedSpmRT1116P0040Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P002L041 : ∀ x ∈ Icc ((((26270247 : ℚ) / 29000000) : ℚ) : ℝ) ((((10688149 : ℚ) / 11600000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0041Lo : ℝ) (ceSignedSpmRT1116P0041Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0041Lo, ceSignedSpmRT1116P0041Hi, SignedSpmRT1116P0041Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0041Bound x h'
  norm_num [SignedSpmRT1116P0041Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P002L042 : ∀ x ∈ Icc ((((10688149 : ℚ) / 11600000) : ℚ) : ℝ) ((((107781741 : ℚ) / 116000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0042Lo : ℝ) (ceSignedSpmRT1116P0042Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0042Lo, ceSignedSpmRT1116P0042Hi, SignedSpmRT1116P0042Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0042Bound x h'
  norm_num [SignedSpmRT1116P0042Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P002L043 : ∀ x ∈ Icc ((((107781741 : ℚ) / 116000000) : ℚ) : ℝ) ((((13585249 : ℚ) / 14500000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0043Lo : ℝ) (ceSignedSpmRT1116P0043Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0043Lo, ceSignedSpmRT1116P0043Hi, SignedSpmRT1116P0043Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0043Bound x h'
  norm_num [SignedSpmRT1116P0043Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P002L044 : ∀ x ∈ Icc ((((13585249 : ℚ) / 14500000) : ℚ) : ℝ) ((((109582243 : ℚ) / 116000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0044Lo : ℝ) (ceSignedSpmRT1116P0044Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0044Lo, ceSignedSpmRT1116P0044Hi, SignedSpmRT1116P0044Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0044Bound x h'
  norm_num [SignedSpmRT1116P0044Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P002L045 : ∀ x ∈ Icc ((((109582243 : ℚ) / 116000000) : ℚ) : ℝ) ((((55241247 : ℚ) / 58000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0045Lo : ℝ) (ceSignedSpmRT1116P0045Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0045Lo, ceSignedSpmRT1116P0045Hi, SignedSpmRT1116P0045Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0045Bound x h'
  norm_num [SignedSpmRT1116P0045Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P002L046 : ∀ x ∈ Icc ((((55241247 : ℚ) / 58000000) : ℚ) : ℝ) ((((22276549 : ℚ) / 23200000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0046Lo : ℝ) (ceSignedSpmRT1116P0046Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0046Lo, ceSignedSpmRT1116P0046Hi, SignedSpmRT1116P0046Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0046Bound x h'
  norm_num [SignedSpmRT1116P0046Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P002L047 : ∀ x ∈ Icc ((((22276549 : ℚ) / 23200000) : ℚ) : ℝ) ((((223665741 : ℚ) / 232000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0047Lo : ℝ) (ceSignedSpmRT1116P0047Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0047Lo, ceSignedSpmRT1116P0047Hi, SignedSpmRT1116P0047Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0047Bound x h'
  norm_num [SignedSpmRT1116P0047Literal.q2] at h ⊢
  exact h

theorem SignedSpmRT1116CoverD0B0P002 : ∀ x ∈ Icc ((((1996849 : ℚ) / 2900000) : ℚ) : ℝ) ((((223665741 : ℚ) / 232000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmRT1116CoverD0B0P002L032 SignedSpmRT1116CoverD0B0P002L033) (cover_union SignedSpmRT1116CoverD0B0P002L034 SignedSpmRT1116CoverD0B0P002L035)) (cover_union (cover_union SignedSpmRT1116CoverD0B0P002L036 SignedSpmRT1116CoverD0B0P002L037) (cover_union SignedSpmRT1116CoverD0B0P002L038 SignedSpmRT1116CoverD0B0P002L039))) (cover_union (cover_union (cover_union SignedSpmRT1116CoverD0B0P002L040 SignedSpmRT1116CoverD0B0P002L041) (cover_union SignedSpmRT1116CoverD0B0P002L042 SignedSpmRT1116CoverD0B0P002L043)) (cover_union (cover_union SignedSpmRT1116CoverD0B0P002L044 SignedSpmRT1116CoverD0B0P002L045) (cover_union SignedSpmRT1116CoverD0B0P002L046 SignedSpmRT1116CoverD0B0P002L047))))
#print axioms SignedSpmRT1116CoverD0B0P002

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Cover
