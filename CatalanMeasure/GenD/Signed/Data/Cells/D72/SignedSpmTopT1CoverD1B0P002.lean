module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0039
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0046
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0047
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0048
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT1CoverD1B0P002L032 : ∀ x ∈ Icc ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((562944584711685 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0033Lo : ℝ) (ceSignedSpmTopT1P0033Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0033Lo, ceSignedSpmTopT1P0033Hi, SignedSpmTopT1P0033Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0033Bound x h'
  norm_num [SignedSpmTopT1P0033Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P002L033 : ∀ x ∈ Icc ((((562944584711685 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((1125890243165193 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0034Lo : ℝ) (ceSignedSpmTopT1P0034Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0034Lo, ceSignedSpmTopT1P0034Hi, SignedSpmTopT1P0034Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0034Bound x h'
  norm_num [SignedSpmTopT1P0034Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P002L034 : ∀ x ∈ Icc ((((1125890243165193 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((140736414613377 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0035Lo : ℝ) (ceSignedSpmTopT1P0035Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0035Lo, ceSignedSpmTopT1P0035Hi, SignedSpmTopT1P0035Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0035Bound x h'
  norm_num [SignedSpmTopT1P0035Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P002L035 : ∀ x ∈ Icc ((((140736414613377 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((1125892390648839 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0036Lo : ℝ) (ceSignedSpmTopT1P0036Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0036Lo, ceSignedSpmTopT1P0036Hi, SignedSpmTopT1P0036Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0036Bound x h'
  norm_num [SignedSpmTopT1P0036Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P002L036 : ∀ x ∈ Icc ((((1125892390648839 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((562946732195331 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0037Lo : ℝ) (ceSignedSpmTopT1P0037Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0037Lo, ceSignedSpmTopT1P0037Hi, SignedSpmTopT1P0037Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0037Bound x h'
  norm_num [SignedSpmTopT1P0037Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P002L037 : ∀ x ∈ Icc ((((562946732195331 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((1125894538132485 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0038Lo : ℝ) (ceSignedSpmTopT1P0038Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0038Lo, ceSignedSpmTopT1P0038Hi, SignedSpmTopT1P0038Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0038Bound x h'
  norm_num [SignedSpmTopT1P0038Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P002L038 : ∀ x ∈ Icc ((((1125894538132485 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((2251790150006793 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0039Lo : ℝ) (ceSignedSpmTopT1P0039Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0039Lo, ceSignedSpmTopT1P0039Hi, SignedSpmTopT1P0039Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0039Bound x h'
  norm_num [SignedSpmTopT1P0039Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P002L039 : ∀ x ∈ Icc ((((2251790150006793 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((281473902968577 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0040Lo : ℝ) (ceSignedSpmTopT1P0040Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0040Lo, ceSignedSpmTopT1P0040Hi, SignedSpmTopT1P0040Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0040Bound x h'
  norm_num [SignedSpmTopT1P0040Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P002L040 : ∀ x ∈ Icc ((((281473902968577 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((2251792297490439 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0041Lo : ℝ) (ceSignedSpmTopT1P0041Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0041Lo, ceSignedSpmTopT1P0041Hi, SignedSpmTopT1P0041Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0041Bound x h'
  norm_num [SignedSpmTopT1P0041Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P002L041 : ∀ x ∈ Icc ((((2251792297490439 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((1125896685616131 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0042Lo : ℝ) (ceSignedSpmTopT1P0042Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0042Lo, ceSignedSpmTopT1P0042Hi, SignedSpmTopT1P0042Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0042Bound x h'
  norm_num [SignedSpmTopT1P0042Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P002L042 : ∀ x ∈ Icc ((((1125896685616131 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((2251794444974085 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0043Lo : ℝ) (ceSignedSpmTopT1P0043Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0043Lo, ceSignedSpmTopT1P0043Hi, SignedSpmTopT1P0043Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0043Bound x h'
  norm_num [SignedSpmTopT1P0043Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P002L043 : ∀ x ∈ Icc ((((2251794444974085 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((4503589963689993 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0044Lo : ℝ) (ceSignedSpmTopT1P0044Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0044Lo, ceSignedSpmTopT1P0044Hi, SignedSpmTopT1P0044Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0044Bound x h'
  norm_num [SignedSpmTopT1P0044Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P002L044 : ∀ x ∈ Icc ((((4503589963689993 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((562948879678977 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0045Lo : ℝ) (ceSignedSpmTopT1P0045Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0045Lo, ceSignedSpmTopT1P0045Hi, SignedSpmTopT1P0045Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0045Bound x h'
  norm_num [SignedSpmTopT1P0045Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P002L045 : ∀ x ∈ Icc ((((562948879678977 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((4503592111173639 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0046Lo : ℝ) (ceSignedSpmTopT1P0046Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0046Lo, ceSignedSpmTopT1P0046Hi, SignedSpmTopT1P0046Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0046Bound x h'
  norm_num [SignedSpmTopT1P0046Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P002L046 : ∀ x ∈ Icc ((((4503592111173639 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((2251796592457731 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0047Lo : ℝ) (ceSignedSpmTopT1P0047Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0047Lo, ceSignedSpmTopT1P0047Hi, SignedSpmTopT1P0047Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0047Bound x h'
  norm_num [SignedSpmTopT1P0047Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P002L047 : ∀ x ∈ Icc ((((2251796592457731 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0048Lo : ℝ) (ceSignedSpmTopT1P0048Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0048Lo, ceSignedSpmTopT1P0048Hi, SignedSpmTopT1P0048Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0048Bound x h'
  norm_num [SignedSpmTopT1P0048Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT1CoverD1B0P002 : ∀ x ∈ Icc ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT1CoverD1B0P002L032 SignedSpmTopT1CoverD1B0P002L033) (cover_union SignedSpmTopT1CoverD1B0P002L034 SignedSpmTopT1CoverD1B0P002L035)) (cover_union (cover_union SignedSpmTopT1CoverD1B0P002L036 SignedSpmTopT1CoverD1B0P002L037) (cover_union SignedSpmTopT1CoverD1B0P002L038 SignedSpmTopT1CoverD1B0P002L039))) (cover_union (cover_union (cover_union SignedSpmTopT1CoverD1B0P002L040 SignedSpmTopT1CoverD1B0P002L041) (cover_union SignedSpmTopT1CoverD1B0P002L042 SignedSpmTopT1CoverD1B0P002L043)) (cover_union (cover_union SignedSpmTopT1CoverD1B0P002L044 SignedSpmTopT1CoverD1B0P002L045) (cover_union SignedSpmTopT1CoverD1B0P002L046 SignedSpmTopT1CoverD1B0P002L047))))
#print axioms SignedSpmTopT1CoverD1B0P002

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover
