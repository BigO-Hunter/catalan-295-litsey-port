module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0184
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0185
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0186
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0187
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0188
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0189
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0190
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0191
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0192
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0193
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0194
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0195
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0196
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0197
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0198
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0199
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT1CoverD1B0P006L096 : ∀ x ∈ Icc ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((2305843005990371331 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0184Lo : ℝ) (ceSignedSpT1P0184Hi : ℝ) := by
    norm_num [ceSignedSpT1P0184Lo, ceSignedSpT1P0184Hi, SignedSpT1P0184Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0184Bound x h'
  norm_num [SignedSpT1P0184Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P006L097 : ∀ x ∈ Icc ((((2305843005990371331 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((4611686013054484485 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0185Lo : ℝ) (ceSignedSpT1P0185Hi : ℝ) := by
    norm_num [ceSignedSpT1P0185Lo, ceSignedSpT1P0185Hi, SignedSpT1P0185Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0185Bound x h'
  norm_num [SignedSpT1P0185Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P006L098 : ∀ x ∈ Icc ((((4611686013054484485 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((9223372027182710793 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0186Lo : ℝ) (ceSignedSpT1P0186Hi : ℝ) := by
    norm_num [ceSignedSpT1P0186Lo, ceSignedSpT1P0186Hi, SignedSpT1P0186Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0186Bound x h'
  norm_num [SignedSpT1P0186Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P006L099 : ∀ x ∈ Icc ((((9223372027182710793 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((1152921503532056577 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0187Lo : ℝ) (ceSignedSpT1P0187Hi : ℝ) := by
    norm_num [ceSignedSpT1P0187Lo, ceSignedSpT1P0187Hi, SignedSpT1P0187Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0187Bound x h'
  norm_num [SignedSpT1P0187Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P006L100 : ∀ x ∈ Icc ((((1152921503532056577 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((9223372029330194439 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0188Lo : ℝ) (ceSignedSpT1P0188Hi : ℝ) := by
    norm_num [ceSignedSpT1P0188Lo, ceSignedSpT1P0188Hi, SignedSpT1P0188Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0188Bound x h'
  norm_num [SignedSpT1P0188Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P006L101 : ∀ x ∈ Icc ((((9223372029330194439 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((4611686015201968131 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0189Lo : ℝ) (ceSignedSpT1P0189Hi : ℝ) := by
    norm_num [ceSignedSpT1P0189Lo, ceSignedSpT1P0189Hi, SignedSpT1P0189Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0189Bound x h'
  norm_num [SignedSpT1P0189Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P006L102 : ∀ x ∈ Icc ((((4611686015201968131 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((9223372031477678085 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0190Lo : ℝ) (ceSignedSpT1P0190Hi : ℝ) := by
    norm_num [ceSignedSpT1P0190Lo, ceSignedSpT1P0190Hi, SignedSpT1P0190Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0190Bound x h'
  norm_num [SignedSpT1P0190Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P006L103 : ∀ x ∈ Icc ((((9223372031477678085 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((18446744064029097993 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0191Lo : ℝ) (ceSignedSpT1P0191Hi : ℝ) := by
    norm_num [ceSignedSpT1P0191Lo, ceSignedSpT1P0191Hi, SignedSpT1P0191Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0191Bound x h'
  norm_num [SignedSpT1P0191Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P006L104 : ∀ x ∈ Icc ((((18446744064029097993 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((2305843008137854977 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0192Lo : ℝ) (ceSignedSpT1P0192Hi : ℝ) := by
    norm_num [ceSignedSpT1P0192Lo, ceSignedSpT1P0192Hi, SignedSpT1P0192Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0192Bound x h'
  norm_num [SignedSpT1P0192Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P006L105 : ∀ x ∈ Icc ((((2305843008137854977 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((18446744066176581639 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0193Lo : ℝ) (ceSignedSpT1P0193Hi : ℝ) := by
    norm_num [ceSignedSpT1P0193Lo, ceSignedSpT1P0193Hi, SignedSpT1P0193Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0193Bound x h'
  norm_num [SignedSpT1P0193Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P006L106 : ∀ x ∈ Icc ((((18446744066176581639 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((9223372033625161731 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0194Lo : ℝ) (ceSignedSpT1P0194Hi : ℝ) := by
    norm_num [ceSignedSpT1P0194Lo, ceSignedSpT1P0194Hi, SignedSpT1P0194Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0194Bound x h'
  norm_num [SignedSpT1P0194Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P006L107 : ∀ x ∈ Icc ((((9223372033625161731 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((18446744068324065285 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0195Lo : ℝ) (ceSignedSpT1P0195Hi : ℝ) := by
    norm_num [ceSignedSpT1P0195Lo, ceSignedSpT1P0195Hi, SignedSpT1P0195Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0195Bound x h'
  norm_num [SignedSpT1P0195Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P006L108 : ∀ x ∈ Icc ((((18446744068324065285 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((36893488137721872393 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0196Lo : ℝ) (ceSignedSpT1P0196Hi : ℝ) := by
    norm_num [ceSignedSpT1P0196Lo, ceSignedSpT1P0196Hi, SignedSpT1P0196Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0196Bound x h'
  norm_num [SignedSpT1P0196Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P006L109 : ∀ x ∈ Icc ((((36893488137721872393 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((4611686017349451777 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0197Lo : ℝ) (ceSignedSpT1P0197Hi : ℝ) := by
    norm_num [ceSignedSpT1P0197Lo, ceSignedSpT1P0197Hi, SignedSpT1P0197Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0197Bound x h'
  norm_num [SignedSpT1P0197Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P006L110 : ∀ x ∈ Icc ((((4611686017349451777 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((36893488139869356039 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0198Lo : ℝ) (ceSignedSpT1P0198Hi : ℝ) := by
    norm_num [ceSignedSpT1P0198Lo, ceSignedSpT1P0198Hi, SignedSpT1P0198Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0198Bound x h'
  norm_num [SignedSpT1P0198Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P006L111 : ∀ x ∈ Icc ((((36893488139869356039 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0199Lo : ℝ) (ceSignedSpT1P0199Hi : ℝ) := by
    norm_num [ceSignedSpT1P0199Lo, ceSignedSpT1P0199Hi, SignedSpT1P0199Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0199Bound x h'
  norm_num [SignedSpT1P0199Literal.q2] at h ⊢
  exact h

theorem SignedSpT1CoverD1B0P006 : ∀ x ∈ Icc ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT1CoverD1B0P006L096 SignedSpT1CoverD1B0P006L097) (cover_union SignedSpT1CoverD1B0P006L098 SignedSpT1CoverD1B0P006L099)) (cover_union (cover_union SignedSpT1CoverD1B0P006L100 SignedSpT1CoverD1B0P006L101) (cover_union SignedSpT1CoverD1B0P006L102 SignedSpT1CoverD1B0P006L103))) (cover_union (cover_union (cover_union SignedSpT1CoverD1B0P006L104 SignedSpT1CoverD1B0P006L105) (cover_union SignedSpT1CoverD1B0P006L106 SignedSpT1CoverD1B0P006L107)) (cover_union (cover_union SignedSpT1CoverD1B0P006L108 SignedSpT1CoverD1B0P006L109) (cover_union SignedSpT1CoverD1B0P006L110 SignedSpT1CoverD1B0P006L111))))
#print axioms SignedSpT1CoverD1B0P006

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
