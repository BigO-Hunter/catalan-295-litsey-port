module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0218
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0219
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0220
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0221
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0222
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0223
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0224
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0225
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0226
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0227
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0228
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0229
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0230
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0231
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0232
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0233
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT2CoverD1B0P008L128 : ∀ x ∈ Icc ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((590295810348505104393 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0218Lo : ℝ) (ceSignedSpT2P0218Hi : ℝ) := by
    norm_num [ceSignedSpT2P0218Lo, ceSignedSpT2P0218Hi, SignedSpT2P0218Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0218Bound x h'
  norm_num [SignedSpT2P0218Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P008L129 : ∀ x ∈ Icc ((((590295810348505104393 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((73786976293697355777 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0219Lo : ℝ) (ceSignedSpT2P0219Hi : ℝ) := by
    norm_num [ceSignedSpT2P0219Lo, ceSignedSpT2P0219Hi, SignedSpT2P0219Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0219Bound x h'
  norm_num [SignedSpT2P0219Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P008L130 : ∀ x ∈ Icc ((((73786976293697355777 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((590295810350652588039 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0220Lo : ℝ) (ceSignedSpT2P0220Hi : ℝ) := by
    norm_num [ceSignedSpT2P0220Lo, ceSignedSpT2P0220Hi, SignedSpT2P0220Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0220Bound x h'
  norm_num [SignedSpT2P0220Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P008L131 : ∀ x ∈ Icc ((((590295810350652588039 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((295147905175863164931 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0221Lo : ℝ) (ceSignedSpT2P0221Hi : ℝ) := by
    norm_num [ceSignedSpT2P0221Lo, ceSignedSpT2P0221Hi, SignedSpT2P0221Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0221Bound x h'
  norm_num [SignedSpT2P0221Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P008L132 : ∀ x ∈ Icc ((((295147905175863164931 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((590295810352800071685 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0222Lo : ℝ) (ceSignedSpT2P0222Hi : ℝ) := by
    norm_num [ceSignedSpT2P0222Lo, ceSignedSpT2P0222Hi, SignedSpT2P0222Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0222Bound x h'
  norm_num [SignedSpT2P0222Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P008L133 : ∀ x ∈ Icc ((((590295810352800071685 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((147573952588468453377 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0223Lo : ℝ) (ceSignedSpT2P0223Hi : ℝ) := by
    norm_num [ceSignedSpT2P0223Lo, ceSignedSpT2P0223Hi, SignedSpT2P0223Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0223Bound x h'
  norm_num [SignedSpT2P0223Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P008L134 : ∀ x ∈ Icc ((((147573952588468453377 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((1180591620708821368839 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0224Lo : ℝ) (ceSignedSpT2P0224Hi : ℝ) := by
    norm_num [ceSignedSpT2P0224Lo, ceSignedSpT2P0224Hi, SignedSpT2P0224Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0224Bound x h'
  norm_num [SignedSpT2P0224Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P008L135 : ∀ x ∈ Icc ((((1180591620708821368839 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((590295810354947555331 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0225Lo : ℝ) (ceSignedSpT2P0225Hi : ℝ) := by
    norm_num [ceSignedSpT2P0225Lo, ceSignedSpT2P0225Hi, SignedSpT2P0225Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0225Bound x h'
  norm_num [SignedSpT2P0225Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P008L136 : ∀ x ∈ Icc ((((590295810354947555331 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((1180591620710968852485 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0226Lo : ℝ) (ceSignedSpT2P0226Hi : ℝ) := by
    norm_num [ceSignedSpT2P0226Lo, ceSignedSpT2P0226Hi, SignedSpT2P0226Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0226Bound x h'
  norm_num [SignedSpT2P0226Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P008L137 : ∀ x ∈ Icc ((((1180591620710968852485 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((295147905178010648577 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0227Lo : ℝ) (ceSignedSpT2P0227Hi : ℝ) := by
    norm_num [ceSignedSpT2P0227Lo, ceSignedSpT2P0227Hi, SignedSpT2P0227Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0227Bound x h'
  norm_num [SignedSpT2P0227Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P008L138 : ∀ x ∈ Icc ((((295147905178010648577 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((2361183241425158930439 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0228Lo : ℝ) (ceSignedSpT2P0228Hi : ℝ) := by
    norm_num [ceSignedSpT2P0228Lo, ceSignedSpT2P0228Hi, SignedSpT2P0228Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0228Bound x h'
  norm_num [SignedSpT2P0228Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P008L139 : ∀ x ∈ Icc ((((2361183241425158930439 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((1180591620713116336131 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0229Lo : ℝ) (ceSignedSpT2P0229Hi : ℝ) := by
    norm_num [ceSignedSpT2P0229Lo, ceSignedSpT2P0229Hi, SignedSpT2P0229Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0229Bound x h'
  norm_num [SignedSpT2P0229Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P008L140 : ∀ x ∈ Icc ((((1180591620713116336131 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((2361183241427306414085 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0230Lo : ℝ) (ceSignedSpT2P0230Hi : ℝ) := by
    norm_num [ceSignedSpT2P0230Lo, ceSignedSpT2P0230Hi, SignedSpT2P0230Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0230Bound x h'
  norm_num [SignedSpT2P0230Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P008L141 : ∀ x ∈ Icc ((((2361183241427306414085 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((590295810357095038977 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0231Lo : ℝ) (ceSignedSpT2P0231Hi : ℝ) := by
    norm_num [ceSignedSpT2P0231Lo, ceSignedSpT2P0231Hi, SignedSpT2P0231Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0231Bound x h'
  norm_num [SignedSpT2P0231Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P008L142 : ∀ x ∈ Icc ((((590295810357095038977 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((2361183241429453897731 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0232Lo : ℝ) (ceSignedSpT2P0232Hi : ℝ) := by
    norm_num [ceSignedSpT2P0232Lo, ceSignedSpT2P0232Hi, SignedSpT2P0232Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0232Bound x h'
  norm_num [SignedSpT2P0232Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P008L143 : ∀ x ∈ Icc ((((2361183241429453897731 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0233Lo : ℝ) (ceSignedSpT2P0233Hi : ℝ) := by
    norm_num [ceSignedSpT2P0233Lo, ceSignedSpT2P0233Hi, SignedSpT2P0233Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0233Bound x h'
  norm_num [SignedSpT2P0233Literal.q2] at h ⊢
  exact h

theorem SignedSpT2CoverD1B0P008 : ∀ x ∈ Icc ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P008L128 SignedSpT2CoverD1B0P008L129) (cover_union SignedSpT2CoverD1B0P008L130 SignedSpT2CoverD1B0P008L131)) (cover_union (cover_union SignedSpT2CoverD1B0P008L132 SignedSpT2CoverD1B0P008L133) (cover_union SignedSpT2CoverD1B0P008L134 SignedSpT2CoverD1B0P008L135))) (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P008L136 SignedSpT2CoverD1B0P008L137) (cover_union SignedSpT2CoverD1B0P008L138 SignedSpT2CoverD1B0P008L139)) (cover_union (cover_union SignedSpT2CoverD1B0P008L140 SignedSpT2CoverD1B0P008L141) (cover_union SignedSpT2CoverD1B0P008L142 SignedSpT2CoverD1B0P008L143))))
#print axioms SignedSpT2CoverD1B0P008

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
