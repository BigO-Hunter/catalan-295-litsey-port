module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0120
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0121
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0122
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0123
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0124
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0125
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0126
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0127
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0128
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0129
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0130
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0131
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0132
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0133
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0134
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0135
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverD1B0P002L032 : ∀ x ∈ Icc ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((562944584711685 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0120Lo : ℝ) (ceSignedSpT0P0120Hi : ℝ) := by
    norm_num [ceSignedSpT0P0120Lo, ceSignedSpT0P0120Hi, SignedSpT0P0120Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0120Bound x h'
  norm_num [SignedSpT0P0120Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P002L033 : ∀ x ∈ Icc ((((562944584711685 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((1125890243165193 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0121Lo : ℝ) (ceSignedSpT0P0121Hi : ℝ) := by
    norm_num [ceSignedSpT0P0121Lo, ceSignedSpT0P0121Hi, SignedSpT0P0121Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0121Bound x h'
  norm_num [SignedSpT0P0121Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P002L034 : ∀ x ∈ Icc ((((1125890243165193 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((140736414613377 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0122Lo : ℝ) (ceSignedSpT0P0122Hi : ℝ) := by
    norm_num [ceSignedSpT0P0122Lo, ceSignedSpT0P0122Hi, SignedSpT0P0122Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0122Bound x h'
  norm_num [SignedSpT0P0122Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P002L035 : ∀ x ∈ Icc ((((140736414613377 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((1125892390648839 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0123Lo : ℝ) (ceSignedSpT0P0123Hi : ℝ) := by
    norm_num [ceSignedSpT0P0123Lo, ceSignedSpT0P0123Hi, SignedSpT0P0123Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0123Bound x h'
  norm_num [SignedSpT0P0123Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P002L036 : ∀ x ∈ Icc ((((1125892390648839 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((562946732195331 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0124Lo : ℝ) (ceSignedSpT0P0124Hi : ℝ) := by
    norm_num [ceSignedSpT0P0124Lo, ceSignedSpT0P0124Hi, SignedSpT0P0124Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0124Bound x h'
  norm_num [SignedSpT0P0124Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P002L037 : ∀ x ∈ Icc ((((562946732195331 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((1125894538132485 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0125Lo : ℝ) (ceSignedSpT0P0125Hi : ℝ) := by
    norm_num [ceSignedSpT0P0125Lo, ceSignedSpT0P0125Hi, SignedSpT0P0125Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0125Bound x h'
  norm_num [SignedSpT0P0125Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P002L038 : ∀ x ∈ Icc ((((1125894538132485 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((2251790150006793 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0126Lo : ℝ) (ceSignedSpT0P0126Hi : ℝ) := by
    norm_num [ceSignedSpT0P0126Lo, ceSignedSpT0P0126Hi, SignedSpT0P0126Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0126Bound x h'
  norm_num [SignedSpT0P0126Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P002L039 : ∀ x ∈ Icc ((((2251790150006793 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((281473902968577 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0127Lo : ℝ) (ceSignedSpT0P0127Hi : ℝ) := by
    norm_num [ceSignedSpT0P0127Lo, ceSignedSpT0P0127Hi, SignedSpT0P0127Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0127Bound x h'
  norm_num [SignedSpT0P0127Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P002L040 : ∀ x ∈ Icc ((((281473902968577 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((2251792297490439 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0128Lo : ℝ) (ceSignedSpT0P0128Hi : ℝ) := by
    norm_num [ceSignedSpT0P0128Lo, ceSignedSpT0P0128Hi, SignedSpT0P0128Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0128Bound x h'
  norm_num [SignedSpT0P0128Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P002L041 : ∀ x ∈ Icc ((((2251792297490439 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((1125896685616131 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0129Lo : ℝ) (ceSignedSpT0P0129Hi : ℝ) := by
    norm_num [ceSignedSpT0P0129Lo, ceSignedSpT0P0129Hi, SignedSpT0P0129Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0129Bound x h'
  norm_num [SignedSpT0P0129Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P002L042 : ∀ x ∈ Icc ((((1125896685616131 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((2251794444974085 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0130Lo : ℝ) (ceSignedSpT0P0130Hi : ℝ) := by
    norm_num [ceSignedSpT0P0130Lo, ceSignedSpT0P0130Hi, SignedSpT0P0130Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0130Bound x h'
  norm_num [SignedSpT0P0130Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P002L043 : ∀ x ∈ Icc ((((2251794444974085 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((4503589963689993 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0131Lo : ℝ) (ceSignedSpT0P0131Hi : ℝ) := by
    norm_num [ceSignedSpT0P0131Lo, ceSignedSpT0P0131Hi, SignedSpT0P0131Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0131Bound x h'
  norm_num [SignedSpT0P0131Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P002L044 : ∀ x ∈ Icc ((((4503589963689993 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((562948879678977 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0132Lo : ℝ) (ceSignedSpT0P0132Hi : ℝ) := by
    norm_num [ceSignedSpT0P0132Lo, ceSignedSpT0P0132Hi, SignedSpT0P0132Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0132Bound x h'
  norm_num [SignedSpT0P0132Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P002L045 : ∀ x ∈ Icc ((((562948879678977 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((4503592111173639 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0133Lo : ℝ) (ceSignedSpT0P0133Hi : ℝ) := by
    norm_num [ceSignedSpT0P0133Lo, ceSignedSpT0P0133Hi, SignedSpT0P0133Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0133Bound x h'
  norm_num [SignedSpT0P0133Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P002L046 : ∀ x ∈ Icc ((((4503592111173639 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((2251796592457731 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0134Lo : ℝ) (ceSignedSpT0P0134Hi : ℝ) := by
    norm_num [ceSignedSpT0P0134Lo, ceSignedSpT0P0134Hi, SignedSpT0P0134Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0134Bound x h'
  norm_num [SignedSpT0P0134Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P002L047 : ∀ x ∈ Icc ((((2251796592457731 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0135Lo : ℝ) (ceSignedSpT0P0135Hi : ℝ) := by
    norm_num [ceSignedSpT0P0135Lo, ceSignedSpT0P0135Hi, SignedSpT0P0135Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0135Bound x h'
  norm_num [SignedSpT0P0135Literal.q2] at h ⊢
  exact h

theorem SignedSpT0CoverD1B0P002 : ∀ x ∈ Icc ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT0CoverD1B0P002L032 SignedSpT0CoverD1B0P002L033) (cover_union SignedSpT0CoverD1B0P002L034 SignedSpT0CoverD1B0P002L035)) (cover_union (cover_union SignedSpT0CoverD1B0P002L036 SignedSpT0CoverD1B0P002L037) (cover_union SignedSpT0CoverD1B0P002L038 SignedSpT0CoverD1B0P002L039))) (cover_union (cover_union (cover_union SignedSpT0CoverD1B0P002L040 SignedSpT0CoverD1B0P002L041) (cover_union SignedSpT0CoverD1B0P002L042 SignedSpT0CoverD1B0P002L043)) (cover_union (cover_union SignedSpT0CoverD1B0P002L044 SignedSpT0CoverD1B0P002L045) (cover_union SignedSpT0CoverD1B0P002L046 SignedSpT0CoverD1B0P002L047))))
#print axioms SignedSpT0CoverD1B0P002

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
