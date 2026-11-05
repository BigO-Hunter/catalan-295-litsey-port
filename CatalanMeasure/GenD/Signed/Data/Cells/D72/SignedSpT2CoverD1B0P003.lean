module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0138
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0139
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0140
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0141
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0142
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0143
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0144
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0145
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0146
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0147
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0148
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0149
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0150
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0151
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0152
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0153
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT2CoverD1B0P003L048 : ∀ x ∈ Icc ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((9007189591056393 : ℚ) / 9007199254740992) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0138Lo : ℝ) (ceSignedSpT2P0138Hi : ℝ) := by
    norm_num [ceSignedSpT2P0138Lo, ceSignedSpT2P0138Hi, SignedSpT2P0138Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0138Bound x h'
  norm_num [SignedSpT2P0138Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P003L049 : ∀ x ∈ Icc ((((9007189591056393 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((1125898833099777 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0139Lo : ℝ) (ceSignedSpT2P0139Hi : ℝ) := by
    norm_num [ceSignedSpT2P0139Lo, ceSignedSpT2P0139Hi, SignedSpT2P0139Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0139Bound x h'
  norm_num [SignedSpT2P0139Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P003L050 : ∀ x ∈ Icc ((((1125898833099777 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((9007191738540039 : ℚ) / 9007199254740992) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0140Lo : ℝ) (ceSignedSpT2P0140Hi : ℝ) := by
    norm_num [ceSignedSpT2P0140Lo, ceSignedSpT2P0140Hi, SignedSpT2P0140Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0140Bound x h'
  norm_num [SignedSpT2P0140Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P003L051 : ∀ x ∈ Icc ((((9007191738540039 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((4503596406140931 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0141Lo : ℝ) (ceSignedSpT2P0141Hi : ℝ) := by
    norm_num [ceSignedSpT2P0141Lo, ceSignedSpT2P0141Hi, SignedSpT2P0141Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0141Bound x h'
  norm_num [SignedSpT2P0141Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P003L052 : ∀ x ∈ Icc ((((4503596406140931 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((9007193886023685 : ℚ) / 9007199254740992) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0142Lo : ℝ) (ceSignedSpT2P0142Hi : ℝ) := by
    norm_num [ceSignedSpT2P0142Lo, ceSignedSpT2P0142Hi, SignedSpT2P0142Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0142Bound x h'
  norm_num [SignedSpT2P0142Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P003L053 : ∀ x ∈ Icc ((((9007193886023685 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((18014388845789193 : ℚ) / 18014398509481984) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0143Lo : ℝ) (ceSignedSpT2P0143Hi : ℝ) := by
    norm_num [ceSignedSpT2P0143Lo, ceSignedSpT2P0143Hi, SignedSpT2P0143Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0143Bound x h'
  norm_num [SignedSpT2P0143Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P003L054 : ∀ x ∈ Icc ((((18014388845789193 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((2251798739941377 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0144Lo : ℝ) (ceSignedSpT2P0144Hi : ℝ) := by
    norm_num [ceSignedSpT2P0144Lo, ceSignedSpT2P0144Hi, SignedSpT2P0144Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0144Bound x h'
  norm_num [SignedSpT2P0144Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P003L055 : ∀ x ∈ Icc ((((2251798739941377 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((18014390993272839 : ℚ) / 18014398509481984) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0145Lo : ℝ) (ceSignedSpT2P0145Hi : ℝ) := by
    norm_num [ceSignedSpT2P0145Lo, ceSignedSpT2P0145Hi, SignedSpT2P0145Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0145Bound x h'
  norm_num [SignedSpT2P0145Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P003L056 : ∀ x ∈ Icc ((((18014390993272839 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((9007196033507331 : ℚ) / 9007199254740992) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0146Lo : ℝ) (ceSignedSpT2P0146Hi : ℝ) := by
    norm_num [ceSignedSpT2P0146Lo, ceSignedSpT2P0146Hi, SignedSpT2P0146Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0146Bound x h'
  norm_num [SignedSpT2P0146Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P003L057 : ∀ x ∈ Icc ((((9007196033507331 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((18014393140756485 : ℚ) / 18014398509481984) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0147Lo : ℝ) (ceSignedSpT2P0147Hi : ℝ) := by
    norm_num [ceSignedSpT2P0147Lo, ceSignedSpT2P0147Hi, SignedSpT2P0147Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0147Bound x h'
  norm_num [SignedSpT2P0147Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P003L058 : ∀ x ∈ Icc ((((18014393140756485 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((36028787355254793 : ℚ) / 36028797018963968) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0148Lo : ℝ) (ceSignedSpT2P0148Hi : ℝ) := by
    norm_num [ceSignedSpT2P0148Lo, ceSignedSpT2P0148Hi, SignedSpT2P0148Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0148Bound x h'
  norm_num [SignedSpT2P0148Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P003L059 : ∀ x ∈ Icc ((((36028787355254793 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((4503598553624577 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0149Lo : ℝ) (ceSignedSpT2P0149Hi : ℝ) := by
    norm_num [ceSignedSpT2P0149Lo, ceSignedSpT2P0149Hi, SignedSpT2P0149Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0149Bound x h'
  norm_num [SignedSpT2P0149Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P003L060 : ∀ x ∈ Icc ((((4503598553624577 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((36028789502738439 : ℚ) / 36028797018963968) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0150Lo : ℝ) (ceSignedSpT2P0150Hi : ℝ) := by
    norm_num [ceSignedSpT2P0150Lo, ceSignedSpT2P0150Hi, SignedSpT2P0150Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0150Bound x h'
  norm_num [SignedSpT2P0150Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P003L061 : ∀ x ∈ Icc ((((36028789502738439 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((18014395288240131 : ℚ) / 18014398509481984) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0151Lo : ℝ) (ceSignedSpT2P0151Hi : ℝ) := by
    norm_num [ceSignedSpT2P0151Lo, ceSignedSpT2P0151Hi, SignedSpT2P0151Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0151Bound x h'
  norm_num [SignedSpT2P0151Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P003L062 : ∀ x ∈ Icc ((((18014395288240131 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((36028791650222085 : ℚ) / 36028797018963968) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0152Lo : ℝ) (ceSignedSpT2P0152Hi : ℝ) := by
    norm_num [ceSignedSpT2P0152Lo, ceSignedSpT2P0152Hi, SignedSpT2P0152Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0152Bound x h'
  norm_num [SignedSpT2P0152Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P003L063 : ∀ x ∈ Icc ((((36028791650222085 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((72057584374185993 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0153Lo : ℝ) (ceSignedSpT2P0153Hi : ℝ) := by
    norm_num [ceSignedSpT2P0153Lo, ceSignedSpT2P0153Hi, SignedSpT2P0153Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0153Bound x h'
  norm_num [SignedSpT2P0153Literal.q2] at h ⊢
  exact h

theorem SignedSpT2CoverD1B0P003 : ∀ x ∈ Icc ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((72057584374185993 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P003L048 SignedSpT2CoverD1B0P003L049) (cover_union SignedSpT2CoverD1B0P003L050 SignedSpT2CoverD1B0P003L051)) (cover_union (cover_union SignedSpT2CoverD1B0P003L052 SignedSpT2CoverD1B0P003L053) (cover_union SignedSpT2CoverD1B0P003L054 SignedSpT2CoverD1B0P003L055))) (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P003L056 SignedSpT2CoverD1B0P003L057) (cover_union SignedSpT2CoverD1B0P003L058 SignedSpT2CoverD1B0P003L059)) (cover_union (cover_union SignedSpT2CoverD1B0P003L060 SignedSpT2CoverD1B0P003L061) (cover_union SignedSpT2CoverD1B0P003L062 SignedSpT2CoverD1B0P003L063))))
#print axioms SignedSpT2CoverD1B0P003

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
