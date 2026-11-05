module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0122
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0123
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0124
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0125
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0126
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0127
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0128
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0129
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0130
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0131
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0132
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0133
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0134
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0135
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0136
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0137
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT2CoverD1B0P002L032 : ∀ x ∈ Icc ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((562944584711685 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0122Lo : ℝ) (ceSignedSpT2P0122Hi : ℝ) := by
    norm_num [ceSignedSpT2P0122Lo, ceSignedSpT2P0122Hi, SignedSpT2P0122Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0122Bound x h'
  norm_num [SignedSpT2P0122Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P002L033 : ∀ x ∈ Icc ((((562944584711685 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((1125890243165193 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0123Lo : ℝ) (ceSignedSpT2P0123Hi : ℝ) := by
    norm_num [ceSignedSpT2P0123Lo, ceSignedSpT2P0123Hi, SignedSpT2P0123Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0123Bound x h'
  norm_num [SignedSpT2P0123Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P002L034 : ∀ x ∈ Icc ((((1125890243165193 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((140736414613377 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0124Lo : ℝ) (ceSignedSpT2P0124Hi : ℝ) := by
    norm_num [ceSignedSpT2P0124Lo, ceSignedSpT2P0124Hi, SignedSpT2P0124Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0124Bound x h'
  norm_num [SignedSpT2P0124Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P002L035 : ∀ x ∈ Icc ((((140736414613377 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((1125892390648839 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0125Lo : ℝ) (ceSignedSpT2P0125Hi : ℝ) := by
    norm_num [ceSignedSpT2P0125Lo, ceSignedSpT2P0125Hi, SignedSpT2P0125Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0125Bound x h'
  norm_num [SignedSpT2P0125Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P002L036 : ∀ x ∈ Icc ((((1125892390648839 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((562946732195331 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0126Lo : ℝ) (ceSignedSpT2P0126Hi : ℝ) := by
    norm_num [ceSignedSpT2P0126Lo, ceSignedSpT2P0126Hi, SignedSpT2P0126Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0126Bound x h'
  norm_num [SignedSpT2P0126Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P002L037 : ∀ x ∈ Icc ((((562946732195331 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((1125894538132485 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0127Lo : ℝ) (ceSignedSpT2P0127Hi : ℝ) := by
    norm_num [ceSignedSpT2P0127Lo, ceSignedSpT2P0127Hi, SignedSpT2P0127Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0127Bound x h'
  norm_num [SignedSpT2P0127Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P002L038 : ∀ x ∈ Icc ((((1125894538132485 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((2251790150006793 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0128Lo : ℝ) (ceSignedSpT2P0128Hi : ℝ) := by
    norm_num [ceSignedSpT2P0128Lo, ceSignedSpT2P0128Hi, SignedSpT2P0128Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0128Bound x h'
  norm_num [SignedSpT2P0128Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P002L039 : ∀ x ∈ Icc ((((2251790150006793 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((281473902968577 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0129Lo : ℝ) (ceSignedSpT2P0129Hi : ℝ) := by
    norm_num [ceSignedSpT2P0129Lo, ceSignedSpT2P0129Hi, SignedSpT2P0129Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0129Bound x h'
  norm_num [SignedSpT2P0129Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P002L040 : ∀ x ∈ Icc ((((281473902968577 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((2251792297490439 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0130Lo : ℝ) (ceSignedSpT2P0130Hi : ℝ) := by
    norm_num [ceSignedSpT2P0130Lo, ceSignedSpT2P0130Hi, SignedSpT2P0130Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0130Bound x h'
  norm_num [SignedSpT2P0130Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P002L041 : ∀ x ∈ Icc ((((2251792297490439 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((1125896685616131 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0131Lo : ℝ) (ceSignedSpT2P0131Hi : ℝ) := by
    norm_num [ceSignedSpT2P0131Lo, ceSignedSpT2P0131Hi, SignedSpT2P0131Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0131Bound x h'
  norm_num [SignedSpT2P0131Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P002L042 : ∀ x ∈ Icc ((((1125896685616131 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((2251794444974085 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0132Lo : ℝ) (ceSignedSpT2P0132Hi : ℝ) := by
    norm_num [ceSignedSpT2P0132Lo, ceSignedSpT2P0132Hi, SignedSpT2P0132Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0132Bound x h'
  norm_num [SignedSpT2P0132Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P002L043 : ∀ x ∈ Icc ((((2251794444974085 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((4503589963689993 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0133Lo : ℝ) (ceSignedSpT2P0133Hi : ℝ) := by
    norm_num [ceSignedSpT2P0133Lo, ceSignedSpT2P0133Hi, SignedSpT2P0133Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0133Bound x h'
  norm_num [SignedSpT2P0133Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P002L044 : ∀ x ∈ Icc ((((4503589963689993 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((562948879678977 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0134Lo : ℝ) (ceSignedSpT2P0134Hi : ℝ) := by
    norm_num [ceSignedSpT2P0134Lo, ceSignedSpT2P0134Hi, SignedSpT2P0134Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0134Bound x h'
  norm_num [SignedSpT2P0134Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P002L045 : ∀ x ∈ Icc ((((562948879678977 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((4503592111173639 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0135Lo : ℝ) (ceSignedSpT2P0135Hi : ℝ) := by
    norm_num [ceSignedSpT2P0135Lo, ceSignedSpT2P0135Hi, SignedSpT2P0135Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0135Bound x h'
  norm_num [SignedSpT2P0135Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P002L046 : ∀ x ∈ Icc ((((4503592111173639 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((2251796592457731 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0136Lo : ℝ) (ceSignedSpT2P0136Hi : ℝ) := by
    norm_num [ceSignedSpT2P0136Lo, ceSignedSpT2P0136Hi, SignedSpT2P0136Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0136Bound x h'
  norm_num [SignedSpT2P0136Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P002L047 : ∀ x ∈ Icc ((((2251796592457731 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0137Lo : ℝ) (ceSignedSpT2P0137Hi : ℝ) := by
    norm_num [ceSignedSpT2P0137Lo, ceSignedSpT2P0137Hi, SignedSpT2P0137Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0137Bound x h'
  norm_num [SignedSpT2P0137Literal.q2] at h ⊢
  exact h

theorem SignedSpT2CoverD1B0P002 : ∀ x ∈ Icc ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P002L032 SignedSpT2CoverD1B0P002L033) (cover_union SignedSpT2CoverD1B0P002L034 SignedSpT2CoverD1B0P002L035)) (cover_union (cover_union SignedSpT2CoverD1B0P002L036 SignedSpT2CoverD1B0P002L037) (cover_union SignedSpT2CoverD1B0P002L038 SignedSpT2CoverD1B0P002L039))) (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P002L040 SignedSpT2CoverD1B0P002L041) (cover_union SignedSpT2CoverD1B0P002L042 SignedSpT2CoverD1B0P002L043)) (cover_union (cover_union SignedSpT2CoverD1B0P002L044 SignedSpT2CoverD1B0P002L045) (cover_union SignedSpT2CoverD1B0P002L046 SignedSpT2CoverD1B0P002L047))))
#print axioms SignedSpT2CoverD1B0P002

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
