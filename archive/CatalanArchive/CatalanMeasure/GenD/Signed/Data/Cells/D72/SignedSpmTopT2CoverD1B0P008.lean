module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0129
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0130
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0131
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0132
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0133
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0134
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0135
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0136
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0137
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0138
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0139
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0140
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0141
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0142
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0143
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0144
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT2CoverD1B0P008L128 : ∀ x ∈ Icc ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((590295810348505104393 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0129Lo : ℝ) (ceSignedSpmTopT2P0129Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0129Lo, ceSignedSpmTopT2P0129Hi, SignedSpmTopT2P0129Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0129Bound x h'
  norm_num [SignedSpmTopT2P0129Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P008L129 : ∀ x ∈ Icc ((((590295810348505104393 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((73786976293697355777 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0130Lo : ℝ) (ceSignedSpmTopT2P0130Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0130Lo, ceSignedSpmTopT2P0130Hi, SignedSpmTopT2P0130Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0130Bound x h'
  norm_num [SignedSpmTopT2P0130Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P008L130 : ∀ x ∈ Icc ((((73786976293697355777 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((590295810350652588039 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0131Lo : ℝ) (ceSignedSpmTopT2P0131Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0131Lo, ceSignedSpmTopT2P0131Hi, SignedSpmTopT2P0131Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0131Bound x h'
  norm_num [SignedSpmTopT2P0131Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P008L131 : ∀ x ∈ Icc ((((590295810350652588039 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((295147905175863164931 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0132Lo : ℝ) (ceSignedSpmTopT2P0132Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0132Lo, ceSignedSpmTopT2P0132Hi, SignedSpmTopT2P0132Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0132Bound x h'
  norm_num [SignedSpmTopT2P0132Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P008L132 : ∀ x ∈ Icc ((((295147905175863164931 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((590295810352800071685 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0133Lo : ℝ) (ceSignedSpmTopT2P0133Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0133Lo, ceSignedSpmTopT2P0133Hi, SignedSpmTopT2P0133Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0133Bound x h'
  norm_num [SignedSpmTopT2P0133Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P008L133 : ∀ x ∈ Icc ((((590295810352800071685 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((147573952588468453377 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0134Lo : ℝ) (ceSignedSpmTopT2P0134Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0134Lo, ceSignedSpmTopT2P0134Hi, SignedSpmTopT2P0134Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0134Bound x h'
  norm_num [SignedSpmTopT2P0134Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P008L134 : ∀ x ∈ Icc ((((147573952588468453377 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((1180591620708821368839 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0135Lo : ℝ) (ceSignedSpmTopT2P0135Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0135Lo, ceSignedSpmTopT2P0135Hi, SignedSpmTopT2P0135Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0135Bound x h'
  norm_num [SignedSpmTopT2P0135Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P008L135 : ∀ x ∈ Icc ((((1180591620708821368839 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((590295810354947555331 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0136Lo : ℝ) (ceSignedSpmTopT2P0136Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0136Lo, ceSignedSpmTopT2P0136Hi, SignedSpmTopT2P0136Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0136Bound x h'
  norm_num [SignedSpmTopT2P0136Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P008L136 : ∀ x ∈ Icc ((((590295810354947555331 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((1180591620710968852485 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0137Lo : ℝ) (ceSignedSpmTopT2P0137Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0137Lo, ceSignedSpmTopT2P0137Hi, SignedSpmTopT2P0137Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0137Bound x h'
  norm_num [SignedSpmTopT2P0137Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P008L137 : ∀ x ∈ Icc ((((1180591620710968852485 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((295147905178010648577 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0138Lo : ℝ) (ceSignedSpmTopT2P0138Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0138Lo, ceSignedSpmTopT2P0138Hi, SignedSpmTopT2P0138Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0138Bound x h'
  norm_num [SignedSpmTopT2P0138Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P008L138 : ∀ x ∈ Icc ((((295147905178010648577 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((2361183241425158930439 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0139Lo : ℝ) (ceSignedSpmTopT2P0139Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0139Lo, ceSignedSpmTopT2P0139Hi, SignedSpmTopT2P0139Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0139Bound x h'
  norm_num [SignedSpmTopT2P0139Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P008L139 : ∀ x ∈ Icc ((((2361183241425158930439 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((1180591620713116336131 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0140Lo : ℝ) (ceSignedSpmTopT2P0140Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0140Lo, ceSignedSpmTopT2P0140Hi, SignedSpmTopT2P0140Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0140Bound x h'
  norm_num [SignedSpmTopT2P0140Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P008L140 : ∀ x ∈ Icc ((((1180591620713116336131 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((2361183241427306414085 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0141Lo : ℝ) (ceSignedSpmTopT2P0141Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0141Lo, ceSignedSpmTopT2P0141Hi, SignedSpmTopT2P0141Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0141Bound x h'
  norm_num [SignedSpmTopT2P0141Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P008L141 : ∀ x ∈ Icc ((((2361183241427306414085 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((590295810357095038977 : ℚ) / 590295810358705651712) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0142Lo : ℝ) (ceSignedSpmTopT2P0142Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0142Lo, ceSignedSpmTopT2P0142Hi, SignedSpmTopT2P0142Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0142Bound x h'
  norm_num [SignedSpmTopT2P0142Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P008L142 : ∀ x ∈ Icc ((((590295810357095038977 : ℚ) / 590295810358705651712) : ℚ) : ℝ) ((((2361183241429453897731 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0143Lo : ℝ) (ceSignedSpmTopT2P0143Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0143Lo, ceSignedSpmTopT2P0143Hi, SignedSpmTopT2P0143Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0143Bound x h'
  norm_num [SignedSpmTopT2P0143Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P008L143 : ∀ x ∈ Icc ((((2361183241429453897731 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0144Lo : ℝ) (ceSignedSpmTopT2P0144Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0144Lo, ceSignedSpmTopT2P0144Hi, SignedSpmTopT2P0144Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0144Bound x h'
  norm_num [SignedSpmTopT2P0144Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT2CoverD1B0P008 : ∀ x ∈ Icc ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT2CoverD1B0P008L128 SignedSpmTopT2CoverD1B0P008L129) (cover_union SignedSpmTopT2CoverD1B0P008L130 SignedSpmTopT2CoverD1B0P008L131)) (cover_union (cover_union SignedSpmTopT2CoverD1B0P008L132 SignedSpmTopT2CoverD1B0P008L133) (cover_union SignedSpmTopT2CoverD1B0P008L134 SignedSpmTopT2CoverD1B0P008L135))) (cover_union (cover_union (cover_union SignedSpmTopT2CoverD1B0P008L136 SignedSpmTopT2CoverD1B0P008L137) (cover_union SignedSpmTopT2CoverD1B0P008L138 SignedSpmTopT2CoverD1B0P008L139)) (cover_union (cover_union SignedSpmTopT2CoverD1B0P008L140 SignedSpmTopT2CoverD1B0P008L141) (cover_union SignedSpmTopT2CoverD1B0P008L142 SignedSpmTopT2CoverD1B0P008L143))))
#print axioms SignedSpmTopT2CoverD1B0P008

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover
