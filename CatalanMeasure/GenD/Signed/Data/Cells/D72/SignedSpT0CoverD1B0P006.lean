module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0184
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0185
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0186
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0187
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0188
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0189
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0190
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0191
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0192
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0193
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0194
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0195
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0196
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0197
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0198
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0199
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverD1B0P006L096 : ∀ x ∈ Icc ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((2305843005990371331 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0184Lo : ℝ) (ceSignedSpT0P0184Hi : ℝ) := by
    norm_num [ceSignedSpT0P0184Lo, ceSignedSpT0P0184Hi, SignedSpT0P0184Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0184Bound x h'
  norm_num [SignedSpT0P0184Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P006L097 : ∀ x ∈ Icc ((((2305843005990371331 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((4611686013054484485 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0185Lo : ℝ) (ceSignedSpT0P0185Hi : ℝ) := by
    norm_num [ceSignedSpT0P0185Lo, ceSignedSpT0P0185Hi, SignedSpT0P0185Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0185Bound x h'
  norm_num [SignedSpT0P0185Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P006L098 : ∀ x ∈ Icc ((((4611686013054484485 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((9223372027182710793 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0186Lo : ℝ) (ceSignedSpT0P0186Hi : ℝ) := by
    norm_num [ceSignedSpT0P0186Lo, ceSignedSpT0P0186Hi, SignedSpT0P0186Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0186Bound x h'
  norm_num [SignedSpT0P0186Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P006L099 : ∀ x ∈ Icc ((((9223372027182710793 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((1152921503532056577 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0187Lo : ℝ) (ceSignedSpT0P0187Hi : ℝ) := by
    norm_num [ceSignedSpT0P0187Lo, ceSignedSpT0P0187Hi, SignedSpT0P0187Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0187Bound x h'
  norm_num [SignedSpT0P0187Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P006L100 : ∀ x ∈ Icc ((((1152921503532056577 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((9223372029330194439 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0188Lo : ℝ) (ceSignedSpT0P0188Hi : ℝ) := by
    norm_num [ceSignedSpT0P0188Lo, ceSignedSpT0P0188Hi, SignedSpT0P0188Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0188Bound x h'
  norm_num [SignedSpT0P0188Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P006L101 : ∀ x ∈ Icc ((((9223372029330194439 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((4611686015201968131 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0189Lo : ℝ) (ceSignedSpT0P0189Hi : ℝ) := by
    norm_num [ceSignedSpT0P0189Lo, ceSignedSpT0P0189Hi, SignedSpT0P0189Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0189Bound x h'
  norm_num [SignedSpT0P0189Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P006L102 : ∀ x ∈ Icc ((((4611686015201968131 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((9223372031477678085 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0190Lo : ℝ) (ceSignedSpT0P0190Hi : ℝ) := by
    norm_num [ceSignedSpT0P0190Lo, ceSignedSpT0P0190Hi, SignedSpT0P0190Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0190Bound x h'
  norm_num [SignedSpT0P0190Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P006L103 : ∀ x ∈ Icc ((((9223372031477678085 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((18446744064029097993 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0191Lo : ℝ) (ceSignedSpT0P0191Hi : ℝ) := by
    norm_num [ceSignedSpT0P0191Lo, ceSignedSpT0P0191Hi, SignedSpT0P0191Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0191Bound x h'
  norm_num [SignedSpT0P0191Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P006L104 : ∀ x ∈ Icc ((((18446744064029097993 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((2305843008137854977 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0192Lo : ℝ) (ceSignedSpT0P0192Hi : ℝ) := by
    norm_num [ceSignedSpT0P0192Lo, ceSignedSpT0P0192Hi, SignedSpT0P0192Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0192Bound x h'
  norm_num [SignedSpT0P0192Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P006L105 : ∀ x ∈ Icc ((((2305843008137854977 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((18446744066176581639 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0193Lo : ℝ) (ceSignedSpT0P0193Hi : ℝ) := by
    norm_num [ceSignedSpT0P0193Lo, ceSignedSpT0P0193Hi, SignedSpT0P0193Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0193Bound x h'
  norm_num [SignedSpT0P0193Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P006L106 : ∀ x ∈ Icc ((((18446744066176581639 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((9223372033625161731 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0194Lo : ℝ) (ceSignedSpT0P0194Hi : ℝ) := by
    norm_num [ceSignedSpT0P0194Lo, ceSignedSpT0P0194Hi, SignedSpT0P0194Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0194Bound x h'
  norm_num [SignedSpT0P0194Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P006L107 : ∀ x ∈ Icc ((((9223372033625161731 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((18446744068324065285 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0195Lo : ℝ) (ceSignedSpT0P0195Hi : ℝ) := by
    norm_num [ceSignedSpT0P0195Lo, ceSignedSpT0P0195Hi, SignedSpT0P0195Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0195Bound x h'
  norm_num [SignedSpT0P0195Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P006L108 : ∀ x ∈ Icc ((((18446744068324065285 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((36893488137721872393 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0196Lo : ℝ) (ceSignedSpT0P0196Hi : ℝ) := by
    norm_num [ceSignedSpT0P0196Lo, ceSignedSpT0P0196Hi, SignedSpT0P0196Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0196Bound x h'
  norm_num [SignedSpT0P0196Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P006L109 : ∀ x ∈ Icc ((((36893488137721872393 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((4611686017349451777 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0197Lo : ℝ) (ceSignedSpT0P0197Hi : ℝ) := by
    norm_num [ceSignedSpT0P0197Lo, ceSignedSpT0P0197Hi, SignedSpT0P0197Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0197Bound x h'
  norm_num [SignedSpT0P0197Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P006L110 : ∀ x ∈ Icc ((((4611686017349451777 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((36893488139869356039 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0198Lo : ℝ) (ceSignedSpT0P0198Hi : ℝ) := by
    norm_num [ceSignedSpT0P0198Lo, ceSignedSpT0P0198Hi, SignedSpT0P0198Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0198Bound x h'
  norm_num [SignedSpT0P0198Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P006L111 : ∀ x ∈ Icc ((((36893488139869356039 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0199Lo : ℝ) (ceSignedSpT0P0199Hi : ℝ) := by
    norm_num [ceSignedSpT0P0199Lo, ceSignedSpT0P0199Hi, SignedSpT0P0199Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0199Bound x h'
  norm_num [SignedSpT0P0199Literal.q2] at h ⊢
  exact h

theorem SignedSpT0CoverD1B0P006 : ∀ x ∈ Icc ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT0CoverD1B0P006L096 SignedSpT0CoverD1B0P006L097) (cover_union SignedSpT0CoverD1B0P006L098 SignedSpT0CoverD1B0P006L099)) (cover_union (cover_union SignedSpT0CoverD1B0P006L100 SignedSpT0CoverD1B0P006L101) (cover_union SignedSpT0CoverD1B0P006L102 SignedSpT0CoverD1B0P006L103))) (cover_union (cover_union (cover_union SignedSpT0CoverD1B0P006L104 SignedSpT0CoverD1B0P006L105) (cover_union SignedSpT0CoverD1B0P006L106 SignedSpT0CoverD1B0P006L107)) (cover_union (cover_union SignedSpT0CoverD1B0P006L108 SignedSpT0CoverD1B0P006L109) (cover_union SignedSpT0CoverD1B0P006L110 SignedSpT0CoverD1B0P006L111))))
#print axioms SignedSpT0CoverD1B0P006

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
