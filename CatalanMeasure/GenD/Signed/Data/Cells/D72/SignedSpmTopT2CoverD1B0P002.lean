module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0039
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0046
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0047
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0048
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT2CoverD1B0P002L032 : ∀ x ∈ Icc ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((562944584711685 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0033Lo : ℝ) (ceSignedSpmTopT2P0033Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0033Lo, ceSignedSpmTopT2P0033Hi, SignedSpmTopT2P0033Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0033Bound x h'
  norm_num [SignedSpmTopT2P0033Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P002L033 : ∀ x ∈ Icc ((((562944584711685 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((1125890243165193 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0034Lo : ℝ) (ceSignedSpmTopT2P0034Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0034Lo, ceSignedSpmTopT2P0034Hi, SignedSpmTopT2P0034Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0034Bound x h'
  norm_num [SignedSpmTopT2P0034Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P002L034 : ∀ x ∈ Icc ((((1125890243165193 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((140736414613377 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0035Lo : ℝ) (ceSignedSpmTopT2P0035Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0035Lo, ceSignedSpmTopT2P0035Hi, SignedSpmTopT2P0035Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0035Bound x h'
  norm_num [SignedSpmTopT2P0035Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P002L035 : ∀ x ∈ Icc ((((140736414613377 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((1125892390648839 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0036Lo : ℝ) (ceSignedSpmTopT2P0036Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0036Lo, ceSignedSpmTopT2P0036Hi, SignedSpmTopT2P0036Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0036Bound x h'
  norm_num [SignedSpmTopT2P0036Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P002L036 : ∀ x ∈ Icc ((((1125892390648839 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((562946732195331 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0037Lo : ℝ) (ceSignedSpmTopT2P0037Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0037Lo, ceSignedSpmTopT2P0037Hi, SignedSpmTopT2P0037Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0037Bound x h'
  norm_num [SignedSpmTopT2P0037Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P002L037 : ∀ x ∈ Icc ((((562946732195331 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((1125894538132485 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0038Lo : ℝ) (ceSignedSpmTopT2P0038Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0038Lo, ceSignedSpmTopT2P0038Hi, SignedSpmTopT2P0038Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0038Bound x h'
  norm_num [SignedSpmTopT2P0038Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P002L038 : ∀ x ∈ Icc ((((1125894538132485 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((2251790150006793 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0039Lo : ℝ) (ceSignedSpmTopT2P0039Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0039Lo, ceSignedSpmTopT2P0039Hi, SignedSpmTopT2P0039Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0039Bound x h'
  norm_num [SignedSpmTopT2P0039Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P002L039 : ∀ x ∈ Icc ((((2251790150006793 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((281473902968577 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0040Lo : ℝ) (ceSignedSpmTopT2P0040Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0040Lo, ceSignedSpmTopT2P0040Hi, SignedSpmTopT2P0040Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0040Bound x h'
  norm_num [SignedSpmTopT2P0040Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P002L040 : ∀ x ∈ Icc ((((281473902968577 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((2251792297490439 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0041Lo : ℝ) (ceSignedSpmTopT2P0041Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0041Lo, ceSignedSpmTopT2P0041Hi, SignedSpmTopT2P0041Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0041Bound x h'
  norm_num [SignedSpmTopT2P0041Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P002L041 : ∀ x ∈ Icc ((((2251792297490439 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((1125896685616131 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0042Lo : ℝ) (ceSignedSpmTopT2P0042Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0042Lo, ceSignedSpmTopT2P0042Hi, SignedSpmTopT2P0042Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0042Bound x h'
  norm_num [SignedSpmTopT2P0042Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P002L042 : ∀ x ∈ Icc ((((1125896685616131 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((2251794444974085 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0043Lo : ℝ) (ceSignedSpmTopT2P0043Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0043Lo, ceSignedSpmTopT2P0043Hi, SignedSpmTopT2P0043Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0043Bound x h'
  norm_num [SignedSpmTopT2P0043Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P002L043 : ∀ x ∈ Icc ((((2251794444974085 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((4503589963689993 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0044Lo : ℝ) (ceSignedSpmTopT2P0044Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0044Lo, ceSignedSpmTopT2P0044Hi, SignedSpmTopT2P0044Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0044Bound x h'
  norm_num [SignedSpmTopT2P0044Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P002L044 : ∀ x ∈ Icc ((((4503589963689993 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((562948879678977 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0045Lo : ℝ) (ceSignedSpmTopT2P0045Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0045Lo, ceSignedSpmTopT2P0045Hi, SignedSpmTopT2P0045Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0045Bound x h'
  norm_num [SignedSpmTopT2P0045Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P002L045 : ∀ x ∈ Icc ((((562948879678977 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((4503592111173639 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0046Lo : ℝ) (ceSignedSpmTopT2P0046Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0046Lo, ceSignedSpmTopT2P0046Hi, SignedSpmTopT2P0046Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0046Bound x h'
  norm_num [SignedSpmTopT2P0046Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P002L046 : ∀ x ∈ Icc ((((4503592111173639 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((2251796592457731 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0047Lo : ℝ) (ceSignedSpmTopT2P0047Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0047Lo, ceSignedSpmTopT2P0047Hi, SignedSpmTopT2P0047Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0047Bound x h'
  norm_num [SignedSpmTopT2P0047Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P002L047 : ∀ x ∈ Icc ((((2251796592457731 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0048Lo : ℝ) (ceSignedSpmTopT2P0048Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0048Lo, ceSignedSpmTopT2P0048Hi, SignedSpmTopT2P0048Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0048Bound x h'
  norm_num [SignedSpmTopT2P0048Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT2CoverD1B0P002 : ∀ x ∈ Icc ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT2CoverD1B0P002L032 SignedSpmTopT2CoverD1B0P002L033) (cover_union SignedSpmTopT2CoverD1B0P002L034 SignedSpmTopT2CoverD1B0P002L035)) (cover_union (cover_union SignedSpmTopT2CoverD1B0P002L036 SignedSpmTopT2CoverD1B0P002L037) (cover_union SignedSpmTopT2CoverD1B0P002L038 SignedSpmTopT2CoverD1B0P002L039))) (cover_union (cover_union (cover_union SignedSpmTopT2CoverD1B0P002L040 SignedSpmTopT2CoverD1B0P002L041) (cover_union SignedSpmTopT2CoverD1B0P002L042 SignedSpmTopT2CoverD1B0P002L043)) (cover_union (cover_union SignedSpmTopT2CoverD1B0P002L044 SignedSpmTopT2CoverD1B0P002L045) (cover_union SignedSpmTopT2CoverD1B0P002L046 SignedSpmTopT2CoverD1B0P002L047))))
#print axioms SignedSpmTopT2CoverD1B0P002

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover
