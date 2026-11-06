module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0097
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0098
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0099
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0100
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0101
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0102
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0103
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0104
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0105
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0106
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0107
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0108
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0109
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0110
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0111
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0112
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT1CoverD1B0P006L096 : ∀ x ∈ Icc ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((2305843005990371331 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0097Lo : ℝ) (ceSignedSpmTopT1P0097Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0097Lo, ceSignedSpmTopT1P0097Hi, SignedSpmTopT1P0097Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0097Bound x h'
  norm_num [SignedSpmTopT1P0097Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P006L097 : ∀ x ∈ Icc ((((2305843005990371331 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((4611686013054484485 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0098Lo : ℝ) (ceSignedSpmTopT1P0098Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0098Lo, ceSignedSpmTopT1P0098Hi, SignedSpmTopT1P0098Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0098Bound x h'
  norm_num [SignedSpmTopT1P0098Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P006L098 : ∀ x ∈ Icc ((((4611686013054484485 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((9223372027182710793 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0099Lo : ℝ) (ceSignedSpmTopT1P0099Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0099Lo, ceSignedSpmTopT1P0099Hi, SignedSpmTopT1P0099Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0099Bound x h'
  norm_num [SignedSpmTopT1P0099Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P006L099 : ∀ x ∈ Icc ((((9223372027182710793 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((1152921503532056577 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0100Lo : ℝ) (ceSignedSpmTopT1P0100Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0100Lo, ceSignedSpmTopT1P0100Hi, SignedSpmTopT1P0100Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0100Bound x h'
  norm_num [SignedSpmTopT1P0100Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P006L100 : ∀ x ∈ Icc ((((1152921503532056577 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((9223372029330194439 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0101Lo : ℝ) (ceSignedSpmTopT1P0101Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0101Lo, ceSignedSpmTopT1P0101Hi, SignedSpmTopT1P0101Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0101Bound x h'
  norm_num [SignedSpmTopT1P0101Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P006L101 : ∀ x ∈ Icc ((((9223372029330194439 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((4611686015201968131 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0102Lo : ℝ) (ceSignedSpmTopT1P0102Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0102Lo, ceSignedSpmTopT1P0102Hi, SignedSpmTopT1P0102Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0102Bound x h'
  norm_num [SignedSpmTopT1P0102Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P006L102 : ∀ x ∈ Icc ((((4611686015201968131 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((9223372031477678085 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0103Lo : ℝ) (ceSignedSpmTopT1P0103Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0103Lo, ceSignedSpmTopT1P0103Hi, SignedSpmTopT1P0103Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0103Bound x h'
  norm_num [SignedSpmTopT1P0103Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P006L103 : ∀ x ∈ Icc ((((9223372031477678085 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((18446744064029097993 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0104Lo : ℝ) (ceSignedSpmTopT1P0104Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0104Lo, ceSignedSpmTopT1P0104Hi, SignedSpmTopT1P0104Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0104Bound x h'
  norm_num [SignedSpmTopT1P0104Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P006L104 : ∀ x ∈ Icc ((((18446744064029097993 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((2305843008137854977 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0105Lo : ℝ) (ceSignedSpmTopT1P0105Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0105Lo, ceSignedSpmTopT1P0105Hi, SignedSpmTopT1P0105Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0105Bound x h'
  norm_num [SignedSpmTopT1P0105Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P006L105 : ∀ x ∈ Icc ((((2305843008137854977 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((18446744066176581639 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0106Lo : ℝ) (ceSignedSpmTopT1P0106Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0106Lo, ceSignedSpmTopT1P0106Hi, SignedSpmTopT1P0106Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0106Bound x h'
  norm_num [SignedSpmTopT1P0106Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P006L106 : ∀ x ∈ Icc ((((18446744066176581639 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((9223372033625161731 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0107Lo : ℝ) (ceSignedSpmTopT1P0107Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0107Lo, ceSignedSpmTopT1P0107Hi, SignedSpmTopT1P0107Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0107Bound x h'
  norm_num [SignedSpmTopT1P0107Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P006L107 : ∀ x ∈ Icc ((((9223372033625161731 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((18446744068324065285 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0108Lo : ℝ) (ceSignedSpmTopT1P0108Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0108Lo, ceSignedSpmTopT1P0108Hi, SignedSpmTopT1P0108Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0108Bound x h'
  norm_num [SignedSpmTopT1P0108Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P006L108 : ∀ x ∈ Icc ((((18446744068324065285 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((36893488137721872393 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0109Lo : ℝ) (ceSignedSpmTopT1P0109Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0109Lo, ceSignedSpmTopT1P0109Hi, SignedSpmTopT1P0109Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0109Bound x h'
  norm_num [SignedSpmTopT1P0109Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P006L109 : ∀ x ∈ Icc ((((36893488137721872393 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((4611686017349451777 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0110Lo : ℝ) (ceSignedSpmTopT1P0110Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0110Lo, ceSignedSpmTopT1P0110Hi, SignedSpmTopT1P0110Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0110Bound x h'
  norm_num [SignedSpmTopT1P0110Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P006L110 : ∀ x ∈ Icc ((((4611686017349451777 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((36893488139869356039 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0111Lo : ℝ) (ceSignedSpmTopT1P0111Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0111Lo, ceSignedSpmTopT1P0111Hi, SignedSpmTopT1P0111Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0111Bound x h'
  norm_num [SignedSpmTopT1P0111Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P006L111 : ∀ x ∈ Icc ((((36893488139869356039 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0112Lo : ℝ) (ceSignedSpmTopT1P0112Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0112Lo, ceSignedSpmTopT1P0112Hi, SignedSpmTopT1P0112Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0112Bound x h'
  norm_num [SignedSpmTopT1P0112Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT1CoverD1B0P006 : ∀ x ∈ Icc ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT1CoverD1B0P006L096 SignedSpmTopT1CoverD1B0P006L097) (cover_union SignedSpmTopT1CoverD1B0P006L098 SignedSpmTopT1CoverD1B0P006L099)) (cover_union (cover_union SignedSpmTopT1CoverD1B0P006L100 SignedSpmTopT1CoverD1B0P006L101) (cover_union SignedSpmTopT1CoverD1B0P006L102 SignedSpmTopT1CoverD1B0P006L103))) (cover_union (cover_union (cover_union SignedSpmTopT1CoverD1B0P006L104 SignedSpmTopT1CoverD1B0P006L105) (cover_union SignedSpmTopT1CoverD1B0P006L106 SignedSpmTopT1CoverD1B0P006L107)) (cover_union (cover_union SignedSpmTopT1CoverD1B0P006L108 SignedSpmTopT1CoverD1B0P006L109) (cover_union SignedSpmTopT1CoverD1B0P006L110 SignedSpmTopT1CoverD1B0P006L111))))
#print axioms SignedSpmTopT1CoverD1B0P006

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover
