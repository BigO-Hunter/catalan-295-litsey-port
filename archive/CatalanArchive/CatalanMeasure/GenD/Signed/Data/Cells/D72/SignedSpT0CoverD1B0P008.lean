module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0216
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0217
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0218
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0219
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0220
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0221
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0222
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0223
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0224
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0225
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0226
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0227
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0228
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0229
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0230
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0231
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverD1B0P008L128 : ∀ x ∈ Icc ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((590295810348505104393 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0216Lo : ℝ) (ceSignedSpT0P0216Hi : ℝ) := by
    norm_num [ceSignedSpT0P0216Lo, ceSignedSpT0P0216Hi, SignedSpT0P0216Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0216Bound x h'
  norm_num [SignedSpT0P0216Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P008L129 : ∀ x ∈ Icc ((((590295810348505104393 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((73786976293697355777 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0217Lo : ℝ) (ceSignedSpT0P0217Hi : ℝ) := by
    norm_num [ceSignedSpT0P0217Lo, ceSignedSpT0P0217Hi, SignedSpT0P0217Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0217Bound x h'
  norm_num [SignedSpT0P0217Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P008L130 : ∀ x ∈ Icc ((((73786976293697355777 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((590295810350652588039 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0218Lo : ℝ) (ceSignedSpT0P0218Hi : ℝ) := by
    norm_num [ceSignedSpT0P0218Lo, ceSignedSpT0P0218Hi, SignedSpT0P0218Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0218Bound x h'
  norm_num [SignedSpT0P0218Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P008L131 : ∀ x ∈ Icc ((((590295810350652588039 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((295147905175863164931 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0219Lo : ℝ) (ceSignedSpT0P0219Hi : ℝ) := by
    norm_num [ceSignedSpT0P0219Lo, ceSignedSpT0P0219Hi, SignedSpT0P0219Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0219Bound x h'
  norm_num [SignedSpT0P0219Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P008L132 : ∀ x ∈ Icc ((((295147905175863164931 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((590295810352800071685 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0220Lo : ℝ) (ceSignedSpT0P0220Hi : ℝ) := by
    norm_num [ceSignedSpT0P0220Lo, ceSignedSpT0P0220Hi, SignedSpT0P0220Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0220Bound x h'
  norm_num [SignedSpT0P0220Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P008L133 : ∀ x ∈ Icc ((((590295810352800071685 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((147573952588468453377 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0221Lo : ℝ) (ceSignedSpT0P0221Hi : ℝ) := by
    norm_num [ceSignedSpT0P0221Lo, ceSignedSpT0P0221Hi, SignedSpT0P0221Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0221Bound x h'
  norm_num [SignedSpT0P0221Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P008L134 : ∀ x ∈ Icc ((((147573952588468453377 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((1180591620708821368839 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0222Lo : ℝ) (ceSignedSpT0P0222Hi : ℝ) := by
    norm_num [ceSignedSpT0P0222Lo, ceSignedSpT0P0222Hi, SignedSpT0P0222Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0222Bound x h'
  norm_num [SignedSpT0P0222Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P008L135 : ∀ x ∈ Icc ((((1180591620708821368839 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((590295810354947555331 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0223Lo : ℝ) (ceSignedSpT0P0223Hi : ℝ) := by
    norm_num [ceSignedSpT0P0223Lo, ceSignedSpT0P0223Hi, SignedSpT0P0223Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0223Bound x h'
  norm_num [SignedSpT0P0223Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P008L136 : ∀ x ∈ Icc ((((590295810354947555331 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((1180591620710968852485 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0224Lo : ℝ) (ceSignedSpT0P0224Hi : ℝ) := by
    norm_num [ceSignedSpT0P0224Lo, ceSignedSpT0P0224Hi, SignedSpT0P0224Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0224Bound x h'
  norm_num [SignedSpT0P0224Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P008L137 : ∀ x ∈ Icc ((((1180591620710968852485 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((295147905178010648577 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0225Lo : ℝ) (ceSignedSpT0P0225Hi : ℝ) := by
    norm_num [ceSignedSpT0P0225Lo, ceSignedSpT0P0225Hi, SignedSpT0P0225Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0225Bound x h'
  norm_num [SignedSpT0P0225Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P008L138 : ∀ x ∈ Icc ((((295147905178010648577 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((2361183241425158930439 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0226Lo : ℝ) (ceSignedSpT0P0226Hi : ℝ) := by
    norm_num [ceSignedSpT0P0226Lo, ceSignedSpT0P0226Hi, SignedSpT0P0226Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0226Bound x h'
  norm_num [SignedSpT0P0226Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P008L139 : ∀ x ∈ Icc ((((2361183241425158930439 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((1180591620713116336131 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0227Lo : ℝ) (ceSignedSpT0P0227Hi : ℝ) := by
    norm_num [ceSignedSpT0P0227Lo, ceSignedSpT0P0227Hi, SignedSpT0P0227Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0227Bound x h'
  norm_num [SignedSpT0P0227Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P008L140 : ∀ x ∈ Icc ((((1180591620713116336131 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((2361183241427306414085 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0228Lo : ℝ) (ceSignedSpT0P0228Hi : ℝ) := by
    norm_num [ceSignedSpT0P0228Lo, ceSignedSpT0P0228Hi, SignedSpT0P0228Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0228Bound x h'
  norm_num [SignedSpT0P0228Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P008L141 : ∀ x ∈ Icc ((((2361183241427306414085 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((590295810357095038977 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0229Lo : ℝ) (ceSignedSpT0P0229Hi : ℝ) := by
    norm_num [ceSignedSpT0P0229Lo, ceSignedSpT0P0229Hi, SignedSpT0P0229Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0229Bound x h'
  norm_num [SignedSpT0P0229Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P008L142 : ∀ x ∈ Icc ((((590295810357095038977 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((2361183241429453897731 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0230Lo : ℝ) (ceSignedSpT0P0230Hi : ℝ) := by
    norm_num [ceSignedSpT0P0230Lo, ceSignedSpT0P0230Hi, SignedSpT0P0230Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0230Bound x h'
  norm_num [SignedSpT0P0230Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P008L143 : ∀ x ∈ Icc ((((2361183241429453897731 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0231Lo : ℝ) (ceSignedSpT0P0231Hi : ℝ) := by
    norm_num [ceSignedSpT0P0231Lo, ceSignedSpT0P0231Hi, SignedSpT0P0231Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0231Bound x h'
  norm_num [SignedSpT0P0231Literal.q2] at h ⊢
  exact h

theorem SignedSpT0CoverD1B0P008 : ∀ x ∈ Icc ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT0CoverD1B0P008L128 SignedSpT0CoverD1B0P008L129) (cover_union SignedSpT0CoverD1B0P008L130 SignedSpT0CoverD1B0P008L131)) (cover_union (cover_union SignedSpT0CoverD1B0P008L132 SignedSpT0CoverD1B0P008L133) (cover_union SignedSpT0CoverD1B0P008L134 SignedSpT0CoverD1B0P008L135))) (cover_union (cover_union (cover_union SignedSpT0CoverD1B0P008L136 SignedSpT0CoverD1B0P008L137) (cover_union SignedSpT0CoverD1B0P008L138 SignedSpT0CoverD1B0P008L139)) (cover_union (cover_union SignedSpT0CoverD1B0P008L140 SignedSpT0CoverD1B0P008L141) (cover_union SignedSpT0CoverD1B0P008L142 SignedSpT0CoverD1B0P008L143))))
#print axioms SignedSpT0CoverD1B0P008

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
