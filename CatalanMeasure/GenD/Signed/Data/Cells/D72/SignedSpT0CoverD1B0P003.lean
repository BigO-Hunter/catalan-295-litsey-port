module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0136
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0137
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0138
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0139
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0140
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0141
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0142
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0143
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0144
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0145
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0146
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0147
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0148
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0149
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0150
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0151
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverD1B0P003L048 : ∀ x ∈ Icc ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((9007189591056393 : ℚ) / 9007199254740992) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0136Lo : ℝ) (ceSignedSpT0P0136Hi : ℝ) := by
    norm_num [ceSignedSpT0P0136Lo, ceSignedSpT0P0136Hi, SignedSpT0P0136Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0136Bound x h'
  norm_num [SignedSpT0P0136Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P003L049 : ∀ x ∈ Icc ((((9007189591056393 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((1125898833099777 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0137Lo : ℝ) (ceSignedSpT0P0137Hi : ℝ) := by
    norm_num [ceSignedSpT0P0137Lo, ceSignedSpT0P0137Hi, SignedSpT0P0137Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0137Bound x h'
  norm_num [SignedSpT0P0137Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P003L050 : ∀ x ∈ Icc ((((1125898833099777 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((9007191738540039 : ℚ) / 9007199254740992) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0138Lo : ℝ) (ceSignedSpT0P0138Hi : ℝ) := by
    norm_num [ceSignedSpT0P0138Lo, ceSignedSpT0P0138Hi, SignedSpT0P0138Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0138Bound x h'
  norm_num [SignedSpT0P0138Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P003L051 : ∀ x ∈ Icc ((((9007191738540039 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((4503596406140931 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0139Lo : ℝ) (ceSignedSpT0P0139Hi : ℝ) := by
    norm_num [ceSignedSpT0P0139Lo, ceSignedSpT0P0139Hi, SignedSpT0P0139Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0139Bound x h'
  norm_num [SignedSpT0P0139Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P003L052 : ∀ x ∈ Icc ((((4503596406140931 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((9007193886023685 : ℚ) / 9007199254740992) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0140Lo : ℝ) (ceSignedSpT0P0140Hi : ℝ) := by
    norm_num [ceSignedSpT0P0140Lo, ceSignedSpT0P0140Hi, SignedSpT0P0140Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0140Bound x h'
  norm_num [SignedSpT0P0140Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P003L053 : ∀ x ∈ Icc ((((9007193886023685 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((18014388845789193 : ℚ) / 18014398509481984) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0141Lo : ℝ) (ceSignedSpT0P0141Hi : ℝ) := by
    norm_num [ceSignedSpT0P0141Lo, ceSignedSpT0P0141Hi, SignedSpT0P0141Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0141Bound x h'
  norm_num [SignedSpT0P0141Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P003L054 : ∀ x ∈ Icc ((((18014388845789193 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((2251798739941377 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0142Lo : ℝ) (ceSignedSpT0P0142Hi : ℝ) := by
    norm_num [ceSignedSpT0P0142Lo, ceSignedSpT0P0142Hi, SignedSpT0P0142Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0142Bound x h'
  norm_num [SignedSpT0P0142Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P003L055 : ∀ x ∈ Icc ((((2251798739941377 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((18014390993272839 : ℚ) / 18014398509481984) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0143Lo : ℝ) (ceSignedSpT0P0143Hi : ℝ) := by
    norm_num [ceSignedSpT0P0143Lo, ceSignedSpT0P0143Hi, SignedSpT0P0143Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0143Bound x h'
  norm_num [SignedSpT0P0143Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P003L056 : ∀ x ∈ Icc ((((18014390993272839 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((9007196033507331 : ℚ) / 9007199254740992) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0144Lo : ℝ) (ceSignedSpT0P0144Hi : ℝ) := by
    norm_num [ceSignedSpT0P0144Lo, ceSignedSpT0P0144Hi, SignedSpT0P0144Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0144Bound x h'
  norm_num [SignedSpT0P0144Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P003L057 : ∀ x ∈ Icc ((((9007196033507331 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((18014393140756485 : ℚ) / 18014398509481984) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0145Lo : ℝ) (ceSignedSpT0P0145Hi : ℝ) := by
    norm_num [ceSignedSpT0P0145Lo, ceSignedSpT0P0145Hi, SignedSpT0P0145Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0145Bound x h'
  norm_num [SignedSpT0P0145Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P003L058 : ∀ x ∈ Icc ((((18014393140756485 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((36028787355254793 : ℚ) / 36028797018963968) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0146Lo : ℝ) (ceSignedSpT0P0146Hi : ℝ) := by
    norm_num [ceSignedSpT0P0146Lo, ceSignedSpT0P0146Hi, SignedSpT0P0146Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0146Bound x h'
  norm_num [SignedSpT0P0146Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P003L059 : ∀ x ∈ Icc ((((36028787355254793 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((4503598553624577 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0147Lo : ℝ) (ceSignedSpT0P0147Hi : ℝ) := by
    norm_num [ceSignedSpT0P0147Lo, ceSignedSpT0P0147Hi, SignedSpT0P0147Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0147Bound x h'
  norm_num [SignedSpT0P0147Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P003L060 : ∀ x ∈ Icc ((((4503598553624577 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((36028789502738439 : ℚ) / 36028797018963968) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0148Lo : ℝ) (ceSignedSpT0P0148Hi : ℝ) := by
    norm_num [ceSignedSpT0P0148Lo, ceSignedSpT0P0148Hi, SignedSpT0P0148Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0148Bound x h'
  norm_num [SignedSpT0P0148Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P003L061 : ∀ x ∈ Icc ((((36028789502738439 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((18014395288240131 : ℚ) / 18014398509481984) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0149Lo : ℝ) (ceSignedSpT0P0149Hi : ℝ) := by
    norm_num [ceSignedSpT0P0149Lo, ceSignedSpT0P0149Hi, SignedSpT0P0149Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0149Bound x h'
  norm_num [SignedSpT0P0149Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P003L062 : ∀ x ∈ Icc ((((18014395288240131 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((36028791650222085 : ℚ) / 36028797018963968) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0150Lo : ℝ) (ceSignedSpT0P0150Hi : ℝ) := by
    norm_num [ceSignedSpT0P0150Lo, ceSignedSpT0P0150Hi, SignedSpT0P0150Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0150Bound x h'
  norm_num [SignedSpT0P0150Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P003L063 : ∀ x ∈ Icc ((((36028791650222085 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((72057584374185993 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0151Lo : ℝ) (ceSignedSpT0P0151Hi : ℝ) := by
    norm_num [ceSignedSpT0P0151Lo, ceSignedSpT0P0151Hi, SignedSpT0P0151Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0151Bound x h'
  norm_num [SignedSpT0P0151Literal.q2] at h ⊢
  exact h

theorem SignedSpT0CoverD1B0P003 : ∀ x ∈ Icc ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((72057584374185993 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT0CoverD1B0P003L048 SignedSpT0CoverD1B0P003L049) (cover_union SignedSpT0CoverD1B0P003L050 SignedSpT0CoverD1B0P003L051)) (cover_union (cover_union SignedSpT0CoverD1B0P003L052 SignedSpT0CoverD1B0P003L053) (cover_union SignedSpT0CoverD1B0P003L054 SignedSpT0CoverD1B0P003L055))) (cover_union (cover_union (cover_union SignedSpT0CoverD1B0P003L056 SignedSpT0CoverD1B0P003L057) (cover_union SignedSpT0CoverD1B0P003L058 SignedSpT0CoverD1B0P003L059)) (cover_union (cover_union SignedSpT0CoverD1B0P003L060 SignedSpT0CoverD1B0P003L061) (cover_union SignedSpT0CoverD1B0P003L062 SignedSpT0CoverD1B0P003L063))))
#print axioms SignedSpT0CoverD1B0P003

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
