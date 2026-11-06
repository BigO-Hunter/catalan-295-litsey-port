module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0039
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0046
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200P0047
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmRT11200CoverD0B0P002L032 : ∀ x ∈ Icc ((((1996849 : ℚ) / 2900000) : ℚ) : ℝ) ((((20868741 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0032Lo : ℝ) (ceSignedSpmRT11200P0032Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0032Lo, ceSignedSpmRT11200P0032Hi, SignedSpmRT11200P0032Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0032Bound x h'
  norm_num [SignedSpmRT11200P0032Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT11200CoverD0B0P002L033 : ∀ x ∈ Icc ((((20868741 : ℚ) / 29000000) : ℚ) : ℝ) ((((680281 : ℚ) / 906250) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0033Lo : ℝ) (ceSignedSpmRT11200P0033Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0033Lo, ceSignedSpmRT11200P0033Hi, SignedSpmRT11200P0033Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0033Bound x h'
  norm_num [SignedSpmRT11200P0033Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT11200CoverD0B0P002L034 : ∀ x ∈ Icc ((((680281 : ℚ) / 906250) : ℚ) : ℝ) ((((22669243 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0034Lo : ℝ) (ceSignedSpmRT11200P0034Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0034Lo, ceSignedSpmRT11200P0034Hi, SignedSpmRT11200P0034Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0034Bound x h'
  norm_num [SignedSpmRT11200P0034Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT11200CoverD0B0P002L035 : ∀ x ∈ Icc ((((22669243 : ℚ) / 29000000) : ℚ) : ℝ) ((((11784747 : ℚ) / 14500000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0035Lo : ℝ) (ceSignedSpmRT11200P0035Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0035Lo, ceSignedSpmRT11200P0035Hi, SignedSpmRT11200P0035Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0035Bound x h'
  norm_num [SignedSpmRT11200P0035Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT11200CoverD0B0P002L036 : ∀ x ∈ Icc ((((11784747 : ℚ) / 14500000) : ℚ) : ℝ) ((((4893949 : ℚ) / 5800000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0036Lo : ℝ) (ceSignedSpmRT11200P0036Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0036Lo, ceSignedSpmRT11200P0036Hi, SignedSpmRT11200P0036Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0036Bound x h'
  norm_num [SignedSpmRT11200P0036Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT11200CoverD0B0P002L037 : ∀ x ∈ Icc ((((4893949 : ℚ) / 5800000) : ℚ) : ℝ) ((((49839741 : ℚ) / 58000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0037Lo : ℝ) (ceSignedSpmRT11200P0037Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0037Lo, ceSignedSpmRT11200P0037Hi, SignedSpmRT11200P0037Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0037Bound x h'
  norm_num [SignedSpmRT11200P0037Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT11200CoverD0B0P002L038 : ∀ x ∈ Icc ((((49839741 : ℚ) / 58000000) : ℚ) : ℝ) ((((6342499 : ℚ) / 7250000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0038Lo : ℝ) (ceSignedSpmRT11200P0038Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0038Lo, ceSignedSpmRT11200P0038Hi, SignedSpmRT11200P0038Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0038Bound x h'
  norm_num [SignedSpmRT11200P0038Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT11200CoverD0B0P002L039 : ∀ x ∈ Icc ((((6342499 : ℚ) / 7250000) : ℚ) : ℝ) ((((51640243 : ℚ) / 58000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0039Lo : ℝ) (ceSignedSpmRT11200P0039Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0039Lo, ceSignedSpmRT11200P0039Hi, SignedSpmRT11200P0039Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0039Bound x h'
  norm_num [SignedSpmRT11200P0039Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT11200CoverD0B0P002L040 : ∀ x ∈ Icc ((((51640243 : ℚ) / 58000000) : ℚ) : ℝ) ((((26270247 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0040Lo : ℝ) (ceSignedSpmRT11200P0040Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0040Lo, ceSignedSpmRT11200P0040Hi, SignedSpmRT11200P0040Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0040Bound x h'
  norm_num [SignedSpmRT11200P0040Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT11200CoverD0B0P002L041 : ∀ x ∈ Icc ((((26270247 : ℚ) / 29000000) : ℚ) : ℝ) ((((10688149 : ℚ) / 11600000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0041Lo : ℝ) (ceSignedSpmRT11200P0041Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0041Lo, ceSignedSpmRT11200P0041Hi, SignedSpmRT11200P0041Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0041Bound x h'
  norm_num [SignedSpmRT11200P0041Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT11200CoverD0B0P002L042 : ∀ x ∈ Icc ((((10688149 : ℚ) / 11600000) : ℚ) : ℝ) ((((107781741 : ℚ) / 116000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0042Lo : ℝ) (ceSignedSpmRT11200P0042Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0042Lo, ceSignedSpmRT11200P0042Hi, SignedSpmRT11200P0042Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0042Bound x h'
  norm_num [SignedSpmRT11200P0042Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT11200CoverD0B0P002L043 : ∀ x ∈ Icc ((((107781741 : ℚ) / 116000000) : ℚ) : ℝ) ((((13585249 : ℚ) / 14500000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0043Lo : ℝ) (ceSignedSpmRT11200P0043Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0043Lo, ceSignedSpmRT11200P0043Hi, SignedSpmRT11200P0043Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0043Bound x h'
  norm_num [SignedSpmRT11200P0043Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT11200CoverD0B0P002L044 : ∀ x ∈ Icc ((((13585249 : ℚ) / 14500000) : ℚ) : ℝ) ((((109582243 : ℚ) / 116000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0044Lo : ℝ) (ceSignedSpmRT11200P0044Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0044Lo, ceSignedSpmRT11200P0044Hi, SignedSpmRT11200P0044Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0044Bound x h'
  norm_num [SignedSpmRT11200P0044Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT11200CoverD0B0P002L045 : ∀ x ∈ Icc ((((109582243 : ℚ) / 116000000) : ℚ) : ℝ) ((((55241247 : ℚ) / 58000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0045Lo : ℝ) (ceSignedSpmRT11200P0045Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0045Lo, ceSignedSpmRT11200P0045Hi, SignedSpmRT11200P0045Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0045Bound x h'
  norm_num [SignedSpmRT11200P0045Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT11200CoverD0B0P002L046 : ∀ x ∈ Icc ((((55241247 : ℚ) / 58000000) : ℚ) : ℝ) ((((22276549 : ℚ) / 23200000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0046Lo : ℝ) (ceSignedSpmRT11200P0046Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0046Lo, ceSignedSpmRT11200P0046Hi, SignedSpmRT11200P0046Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0046Bound x h'
  norm_num [SignedSpmRT11200P0046Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT11200CoverD0B0P002L047 : ∀ x ∈ Icc ((((22276549 : ℚ) / 23200000) : ℚ) : ℝ) ((((223665741 : ℚ) / 232000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT11200P0047Lo : ℝ) (ceSignedSpmRT11200P0047Hi : ℝ) := by
    norm_num [ceSignedSpmRT11200P0047Lo, ceSignedSpmRT11200P0047Hi, SignedSpmRT11200P0047Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT11200P0047Bound x h'
  norm_num [SignedSpmRT11200P0047Literal.q2] at h ⊢
  exact h

theorem SignedSpmRT11200CoverD0B0P002 : ∀ x ∈ Icc ((((1996849 : ℚ) / 2900000) : ℚ) : ℝ) ((((223665741 : ℚ) / 232000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT11200Fq (poleF ceSignedSpmRT11200Fq.poles) 0 x + lfieldTower ceSignedSpmRT11200Ts 0 x ≤ ((((-5779228294357 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmRT11200CoverD0B0P002L032 SignedSpmRT11200CoverD0B0P002L033) (cover_union SignedSpmRT11200CoverD0B0P002L034 SignedSpmRT11200CoverD0B0P002L035)) (cover_union (cover_union SignedSpmRT11200CoverD0B0P002L036 SignedSpmRT11200CoverD0B0P002L037) (cover_union SignedSpmRT11200CoverD0B0P002L038 SignedSpmRT11200CoverD0B0P002L039))) (cover_union (cover_union (cover_union SignedSpmRT11200CoverD0B0P002L040 SignedSpmRT11200CoverD0B0P002L041) (cover_union SignedSpmRT11200CoverD0B0P002L042 SignedSpmRT11200CoverD0B0P002L043)) (cover_union (cover_union SignedSpmRT11200CoverD0B0P002L044 SignedSpmRT11200CoverD0B0P002L045) (cover_union SignedSpmRT11200CoverD0B0P002L046 SignedSpmRT11200CoverD0B0P002L047))))
#print axioms SignedSpmRT11200CoverD0B0P002

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200Cover
