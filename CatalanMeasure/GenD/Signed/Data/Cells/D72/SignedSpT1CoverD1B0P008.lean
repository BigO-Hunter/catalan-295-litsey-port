module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0216
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0217
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0218
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0219
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0220
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0221
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0222
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0223
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0224
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0225
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0226
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0227
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0228
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0229
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0230
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0231
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT1CoverD1B0P008L128 : ∀ x ∈ Icc ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((590295810348505104393 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0216Lo : ℝ) (ceSignedSpT1P0216Hi : ℝ) := by
    norm_num [ceSignedSpT1P0216Lo, ceSignedSpT1P0216Hi, SignedSpT1P0216Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0216Bound x h'
  norm_num [SignedSpT1P0216Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P008L129 : ∀ x ∈ Icc ((((590295810348505104393 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((73786976293697355777 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0217Lo : ℝ) (ceSignedSpT1P0217Hi : ℝ) := by
    norm_num [ceSignedSpT1P0217Lo, ceSignedSpT1P0217Hi, SignedSpT1P0217Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0217Bound x h'
  norm_num [SignedSpT1P0217Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P008L130 : ∀ x ∈ Icc ((((73786976293697355777 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((590295810350652588039 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0218Lo : ℝ) (ceSignedSpT1P0218Hi : ℝ) := by
    norm_num [ceSignedSpT1P0218Lo, ceSignedSpT1P0218Hi, SignedSpT1P0218Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0218Bound x h'
  norm_num [SignedSpT1P0218Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P008L131 : ∀ x ∈ Icc ((((590295810350652588039 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((295147905175863164931 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0219Lo : ℝ) (ceSignedSpT1P0219Hi : ℝ) := by
    norm_num [ceSignedSpT1P0219Lo, ceSignedSpT1P0219Hi, SignedSpT1P0219Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0219Bound x h'
  norm_num [SignedSpT1P0219Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P008L132 : ∀ x ∈ Icc ((((295147905175863164931 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((590295810352800071685 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0220Lo : ℝ) (ceSignedSpT1P0220Hi : ℝ) := by
    norm_num [ceSignedSpT1P0220Lo, ceSignedSpT1P0220Hi, SignedSpT1P0220Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0220Bound x h'
  norm_num [SignedSpT1P0220Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P008L133 : ∀ x ∈ Icc ((((590295810352800071685 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((147573952588468453377 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0221Lo : ℝ) (ceSignedSpT1P0221Hi : ℝ) := by
    norm_num [ceSignedSpT1P0221Lo, ceSignedSpT1P0221Hi, SignedSpT1P0221Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0221Bound x h'
  norm_num [SignedSpT1P0221Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P008L134 : ∀ x ∈ Icc ((((147573952588468453377 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((1180591620708821368839 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0222Lo : ℝ) (ceSignedSpT1P0222Hi : ℝ) := by
    norm_num [ceSignedSpT1P0222Lo, ceSignedSpT1P0222Hi, SignedSpT1P0222Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0222Bound x h'
  norm_num [SignedSpT1P0222Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P008L135 : ∀ x ∈ Icc ((((1180591620708821368839 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((590295810354947555331 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0223Lo : ℝ) (ceSignedSpT1P0223Hi : ℝ) := by
    norm_num [ceSignedSpT1P0223Lo, ceSignedSpT1P0223Hi, SignedSpT1P0223Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0223Bound x h'
  norm_num [SignedSpT1P0223Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P008L136 : ∀ x ∈ Icc ((((590295810354947555331 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((1180591620710968852485 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0224Lo : ℝ) (ceSignedSpT1P0224Hi : ℝ) := by
    norm_num [ceSignedSpT1P0224Lo, ceSignedSpT1P0224Hi, SignedSpT1P0224Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0224Bound x h'
  norm_num [SignedSpT1P0224Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P008L137 : ∀ x ∈ Icc ((((1180591620710968852485 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((295147905178010648577 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0225Lo : ℝ) (ceSignedSpT1P0225Hi : ℝ) := by
    norm_num [ceSignedSpT1P0225Lo, ceSignedSpT1P0225Hi, SignedSpT1P0225Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0225Bound x h'
  norm_num [SignedSpT1P0225Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P008L138 : ∀ x ∈ Icc ((((295147905178010648577 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((2361183241425158930439 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0226Lo : ℝ) (ceSignedSpT1P0226Hi : ℝ) := by
    norm_num [ceSignedSpT1P0226Lo, ceSignedSpT1P0226Hi, SignedSpT1P0226Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0226Bound x h'
  norm_num [SignedSpT1P0226Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P008L139 : ∀ x ∈ Icc ((((2361183241425158930439 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((1180591620713116336131 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0227Lo : ℝ) (ceSignedSpT1P0227Hi : ℝ) := by
    norm_num [ceSignedSpT1P0227Lo, ceSignedSpT1P0227Hi, SignedSpT1P0227Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0227Bound x h'
  norm_num [SignedSpT1P0227Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P008L140 : ∀ x ∈ Icc ((((1180591620713116336131 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((2361183241427306414085 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0228Lo : ℝ) (ceSignedSpT1P0228Hi : ℝ) := by
    norm_num [ceSignedSpT1P0228Lo, ceSignedSpT1P0228Hi, SignedSpT1P0228Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0228Bound x h'
  norm_num [SignedSpT1P0228Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P008L141 : ∀ x ∈ Icc ((((2361183241427306414085 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((590295810357095038977 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0229Lo : ℝ) (ceSignedSpT1P0229Hi : ℝ) := by
    norm_num [ceSignedSpT1P0229Lo, ceSignedSpT1P0229Hi, SignedSpT1P0229Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0229Bound x h'
  norm_num [SignedSpT1P0229Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P008L142 : ∀ x ∈ Icc ((((590295810357095038977 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((2361183241429453897731 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0230Lo : ℝ) (ceSignedSpT1P0230Hi : ℝ) := by
    norm_num [ceSignedSpT1P0230Lo, ceSignedSpT1P0230Hi, SignedSpT1P0230Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0230Bound x h'
  norm_num [SignedSpT1P0230Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P008L143 : ∀ x ∈ Icc ((((2361183241429453897731 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0231Lo : ℝ) (ceSignedSpT1P0231Hi : ℝ) := by
    norm_num [ceSignedSpT1P0231Lo, ceSignedSpT1P0231Hi, SignedSpT1P0231Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0231Bound x h'
  norm_num [SignedSpT1P0231Literal.q2] at h ⊢
  exact h

theorem SignedSpT1CoverD1B0P008 : ∀ x ∈ Icc ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT1CoverD1B0P008L128 SignedSpT1CoverD1B0P008L129) (cover_union SignedSpT1CoverD1B0P008L130 SignedSpT1CoverD1B0P008L131)) (cover_union (cover_union SignedSpT1CoverD1B0P008L132 SignedSpT1CoverD1B0P008L133) (cover_union SignedSpT1CoverD1B0P008L134 SignedSpT1CoverD1B0P008L135))) (cover_union (cover_union (cover_union SignedSpT1CoverD1B0P008L136 SignedSpT1CoverD1B0P008L137) (cover_union SignedSpT1CoverD1B0P008L138 SignedSpT1CoverD1B0P008L139)) (cover_union (cover_union SignedSpT1CoverD1B0P008L140 SignedSpT1CoverD1B0P008L141) (cover_union SignedSpT1CoverD1B0P008L142 SignedSpT1CoverD1B0P008L143))))
#print axioms SignedSpT1CoverD1B0P008

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
