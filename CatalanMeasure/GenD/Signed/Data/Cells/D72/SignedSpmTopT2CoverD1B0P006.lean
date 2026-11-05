module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0097
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0098
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0099
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0100
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0101
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0102
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0103
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0104
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0105
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0106
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0107
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0108
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0109
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0110
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0111
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0112
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT2CoverD1B0P006L096 : ∀ x ∈ Icc ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((2305843005990371331 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0097Lo : ℝ) (ceSignedSpmTopT2P0097Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0097Lo, ceSignedSpmTopT2P0097Hi, SignedSpmTopT2P0097Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0097Bound x h'
  norm_num [SignedSpmTopT2P0097Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P006L097 : ∀ x ∈ Icc ((((2305843005990371331 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((4611686013054484485 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0098Lo : ℝ) (ceSignedSpmTopT2P0098Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0098Lo, ceSignedSpmTopT2P0098Hi, SignedSpmTopT2P0098Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0098Bound x h'
  norm_num [SignedSpmTopT2P0098Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P006L098 : ∀ x ∈ Icc ((((4611686013054484485 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((9223372027182710793 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0099Lo : ℝ) (ceSignedSpmTopT2P0099Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0099Lo, ceSignedSpmTopT2P0099Hi, SignedSpmTopT2P0099Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0099Bound x h'
  norm_num [SignedSpmTopT2P0099Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P006L099 : ∀ x ∈ Icc ((((9223372027182710793 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((1152921503532056577 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0100Lo : ℝ) (ceSignedSpmTopT2P0100Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0100Lo, ceSignedSpmTopT2P0100Hi, SignedSpmTopT2P0100Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0100Bound x h'
  norm_num [SignedSpmTopT2P0100Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P006L100 : ∀ x ∈ Icc ((((1152921503532056577 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((9223372029330194439 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0101Lo : ℝ) (ceSignedSpmTopT2P0101Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0101Lo, ceSignedSpmTopT2P0101Hi, SignedSpmTopT2P0101Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0101Bound x h'
  norm_num [SignedSpmTopT2P0101Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P006L101 : ∀ x ∈ Icc ((((9223372029330194439 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((4611686015201968131 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0102Lo : ℝ) (ceSignedSpmTopT2P0102Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0102Lo, ceSignedSpmTopT2P0102Hi, SignedSpmTopT2P0102Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0102Bound x h'
  norm_num [SignedSpmTopT2P0102Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P006L102 : ∀ x ∈ Icc ((((4611686015201968131 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((9223372031477678085 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0103Lo : ℝ) (ceSignedSpmTopT2P0103Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0103Lo, ceSignedSpmTopT2P0103Hi, SignedSpmTopT2P0103Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0103Bound x h'
  norm_num [SignedSpmTopT2P0103Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P006L103 : ∀ x ∈ Icc ((((9223372031477678085 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((18446744064029097993 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0104Lo : ℝ) (ceSignedSpmTopT2P0104Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0104Lo, ceSignedSpmTopT2P0104Hi, SignedSpmTopT2P0104Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0104Bound x h'
  norm_num [SignedSpmTopT2P0104Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P006L104 : ∀ x ∈ Icc ((((18446744064029097993 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((2305843008137854977 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0105Lo : ℝ) (ceSignedSpmTopT2P0105Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0105Lo, ceSignedSpmTopT2P0105Hi, SignedSpmTopT2P0105Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0105Bound x h'
  norm_num [SignedSpmTopT2P0105Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P006L105 : ∀ x ∈ Icc ((((2305843008137854977 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((18446744066176581639 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0106Lo : ℝ) (ceSignedSpmTopT2P0106Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0106Lo, ceSignedSpmTopT2P0106Hi, SignedSpmTopT2P0106Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0106Bound x h'
  norm_num [SignedSpmTopT2P0106Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P006L106 : ∀ x ∈ Icc ((((18446744066176581639 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((9223372033625161731 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0107Lo : ℝ) (ceSignedSpmTopT2P0107Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0107Lo, ceSignedSpmTopT2P0107Hi, SignedSpmTopT2P0107Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0107Bound x h'
  norm_num [SignedSpmTopT2P0107Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P006L107 : ∀ x ∈ Icc ((((9223372033625161731 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((18446744068324065285 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0108Lo : ℝ) (ceSignedSpmTopT2P0108Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0108Lo, ceSignedSpmTopT2P0108Hi, SignedSpmTopT2P0108Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0108Bound x h'
  norm_num [SignedSpmTopT2P0108Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P006L108 : ∀ x ∈ Icc ((((18446744068324065285 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((36893488137721872393 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0109Lo : ℝ) (ceSignedSpmTopT2P0109Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0109Lo, ceSignedSpmTopT2P0109Hi, SignedSpmTopT2P0109Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0109Bound x h'
  norm_num [SignedSpmTopT2P0109Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P006L109 : ∀ x ∈ Icc ((((36893488137721872393 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((4611686017349451777 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0110Lo : ℝ) (ceSignedSpmTopT2P0110Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0110Lo, ceSignedSpmTopT2P0110Hi, SignedSpmTopT2P0110Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0110Bound x h'
  norm_num [SignedSpmTopT2P0110Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P006L110 : ∀ x ∈ Icc ((((4611686017349451777 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((36893488139869356039 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0111Lo : ℝ) (ceSignedSpmTopT2P0111Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0111Lo, ceSignedSpmTopT2P0111Hi, SignedSpmTopT2P0111Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0111Bound x h'
  norm_num [SignedSpmTopT2P0111Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P006L111 : ∀ x ∈ Icc ((((36893488139869356039 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0112Lo : ℝ) (ceSignedSpmTopT2P0112Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0112Lo, ceSignedSpmTopT2P0112Hi, SignedSpmTopT2P0112Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0112Bound x h'
  norm_num [SignedSpmTopT2P0112Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT2CoverD1B0P006 : ∀ x ∈ Icc ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT2CoverD1B0P006L096 SignedSpmTopT2CoverD1B0P006L097) (cover_union SignedSpmTopT2CoverD1B0P006L098 SignedSpmTopT2CoverD1B0P006L099)) (cover_union (cover_union SignedSpmTopT2CoverD1B0P006L100 SignedSpmTopT2CoverD1B0P006L101) (cover_union SignedSpmTopT2CoverD1B0P006L102 SignedSpmTopT2CoverD1B0P006L103))) (cover_union (cover_union (cover_union SignedSpmTopT2CoverD1B0P006L104 SignedSpmTopT2CoverD1B0P006L105) (cover_union SignedSpmTopT2CoverD1B0P006L106 SignedSpmTopT2CoverD1B0P006L107)) (cover_union (cover_union SignedSpmTopT2CoverD1B0P006L108 SignedSpmTopT2CoverD1B0P006L109) (cover_union SignedSpmTopT2CoverD1B0P006L110 SignedSpmTopT2CoverD1B0P006L111))))
#print axioms SignedSpmTopT2CoverD1B0P006

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover
