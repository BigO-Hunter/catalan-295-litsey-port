module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0039
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0046
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0047
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0048
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT0CoverD1B0P002L032 : ∀ x ∈ Icc ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((562944584711685 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0033Lo : ℝ) (ceSignedSpmTopT0P0033Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0033Lo, ceSignedSpmTopT0P0033Hi, SignedSpmTopT0P0033Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0033Bound x h'
  norm_num [SignedSpmTopT0P0033Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P002L033 : ∀ x ∈ Icc ((((562944584711685 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((1125890243165193 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0034Lo : ℝ) (ceSignedSpmTopT0P0034Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0034Lo, ceSignedSpmTopT0P0034Hi, SignedSpmTopT0P0034Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0034Bound x h'
  norm_num [SignedSpmTopT0P0034Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P002L034 : ∀ x ∈ Icc ((((1125890243165193 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((140736414613377 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0035Lo : ℝ) (ceSignedSpmTopT0P0035Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0035Lo, ceSignedSpmTopT0P0035Hi, SignedSpmTopT0P0035Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0035Bound x h'
  norm_num [SignedSpmTopT0P0035Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P002L035 : ∀ x ∈ Icc ((((140736414613377 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((1125892390648839 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0036Lo : ℝ) (ceSignedSpmTopT0P0036Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0036Lo, ceSignedSpmTopT0P0036Hi, SignedSpmTopT0P0036Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0036Bound x h'
  norm_num [SignedSpmTopT0P0036Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P002L036 : ∀ x ∈ Icc ((((1125892390648839 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((562946732195331 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0037Lo : ℝ) (ceSignedSpmTopT0P0037Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0037Lo, ceSignedSpmTopT0P0037Hi, SignedSpmTopT0P0037Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0037Bound x h'
  norm_num [SignedSpmTopT0P0037Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P002L037 : ∀ x ∈ Icc ((((562946732195331 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((1125894538132485 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0038Lo : ℝ) (ceSignedSpmTopT0P0038Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0038Lo, ceSignedSpmTopT0P0038Hi, SignedSpmTopT0P0038Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0038Bound x h'
  norm_num [SignedSpmTopT0P0038Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P002L038 : ∀ x ∈ Icc ((((1125894538132485 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((2251790150006793 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0039Lo : ℝ) (ceSignedSpmTopT0P0039Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0039Lo, ceSignedSpmTopT0P0039Hi, SignedSpmTopT0P0039Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0039Bound x h'
  norm_num [SignedSpmTopT0P0039Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P002L039 : ∀ x ∈ Icc ((((2251790150006793 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((281473902968577 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0040Lo : ℝ) (ceSignedSpmTopT0P0040Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0040Lo, ceSignedSpmTopT0P0040Hi, SignedSpmTopT0P0040Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0040Bound x h'
  norm_num [SignedSpmTopT0P0040Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P002L040 : ∀ x ∈ Icc ((((281473902968577 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((2251792297490439 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0041Lo : ℝ) (ceSignedSpmTopT0P0041Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0041Lo, ceSignedSpmTopT0P0041Hi, SignedSpmTopT0P0041Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0041Bound x h'
  norm_num [SignedSpmTopT0P0041Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P002L041 : ∀ x ∈ Icc ((((2251792297490439 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((1125896685616131 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0042Lo : ℝ) (ceSignedSpmTopT0P0042Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0042Lo, ceSignedSpmTopT0P0042Hi, SignedSpmTopT0P0042Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0042Bound x h'
  norm_num [SignedSpmTopT0P0042Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P002L042 : ∀ x ∈ Icc ((((1125896685616131 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((2251794444974085 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0043Lo : ℝ) (ceSignedSpmTopT0P0043Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0043Lo, ceSignedSpmTopT0P0043Hi, SignedSpmTopT0P0043Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0043Bound x h'
  norm_num [SignedSpmTopT0P0043Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P002L043 : ∀ x ∈ Icc ((((2251794444974085 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((4503589963689993 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0044Lo : ℝ) (ceSignedSpmTopT0P0044Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0044Lo, ceSignedSpmTopT0P0044Hi, SignedSpmTopT0P0044Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0044Bound x h'
  norm_num [SignedSpmTopT0P0044Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P002L044 : ∀ x ∈ Icc ((((4503589963689993 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((562948879678977 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0045Lo : ℝ) (ceSignedSpmTopT0P0045Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0045Lo, ceSignedSpmTopT0P0045Hi, SignedSpmTopT0P0045Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0045Bound x h'
  norm_num [SignedSpmTopT0P0045Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P002L045 : ∀ x ∈ Icc ((((562948879678977 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((4503592111173639 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0046Lo : ℝ) (ceSignedSpmTopT0P0046Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0046Lo, ceSignedSpmTopT0P0046Hi, SignedSpmTopT0P0046Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0046Bound x h'
  norm_num [SignedSpmTopT0P0046Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P002L046 : ∀ x ∈ Icc ((((4503592111173639 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((2251796592457731 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0047Lo : ℝ) (ceSignedSpmTopT0P0047Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0047Lo, ceSignedSpmTopT0P0047Hi, SignedSpmTopT0P0047Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0047Bound x h'
  norm_num [SignedSpmTopT0P0047Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P002L047 : ∀ x ∈ Icc ((((2251796592457731 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0048Lo : ℝ) (ceSignedSpmTopT0P0048Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0048Lo, ceSignedSpmTopT0P0048Hi, SignedSpmTopT0P0048Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0048Bound x h'
  norm_num [SignedSpmTopT0P0048Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT0CoverD1B0P002 : ∀ x ∈ Icc ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT0CoverD1B0P002L032 SignedSpmTopT0CoverD1B0P002L033) (cover_union SignedSpmTopT0CoverD1B0P002L034 SignedSpmTopT0CoverD1B0P002L035)) (cover_union (cover_union SignedSpmTopT0CoverD1B0P002L036 SignedSpmTopT0CoverD1B0P002L037) (cover_union SignedSpmTopT0CoverD1B0P002L038 SignedSpmTopT0CoverD1B0P002L039))) (cover_union (cover_union (cover_union SignedSpmTopT0CoverD1B0P002L040 SignedSpmTopT0CoverD1B0P002L041) (cover_union SignedSpmTopT0CoverD1B0P002L042 SignedSpmTopT0CoverD1B0P002L043)) (cover_union (cover_union SignedSpmTopT0CoverD1B0P002L044 SignedSpmTopT0CoverD1B0P002L045) (cover_union SignedSpmTopT0CoverD1B0P002L046 SignedSpmTopT0CoverD1B0P002L047))))
#print axioms SignedSpmTopT0CoverD1B0P002

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover
