module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0081
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0082
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0083
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0084
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0085
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0086
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0087
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0088
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0089
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0090
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0091
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0092
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0093
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0094
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0095
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0096
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT2CoverD1B0P005L080 : ∀ x ∈ Icc ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((576460744786706439 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0081Lo : ℝ) (ceSignedSpmTopT2P0081Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0081Lo, ceSignedSpmTopT2P0081Hi, SignedSpmTopT2P0081Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0081Bound x h'
  norm_num [SignedSpmTopT2P0081Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P005L081 : ∀ x ∈ Icc ((((576460744786706439 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((288230372930224131 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0082Lo : ℝ) (ceSignedSpmTopT2P0082Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0082Lo, ceSignedSpmTopT2P0082Hi, SignedSpmTopT2P0082Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0082Bound x h'
  norm_num [SignedSpmTopT2P0082Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P005L082 : ∀ x ∈ Icc ((((288230372930224131 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((576460746934190085 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0083Lo : ℝ) (ceSignedSpmTopT2P0083Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0083Lo, ceSignedSpmTopT2P0083Hi, SignedSpmTopT2P0083Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0083Bound x h'
  norm_num [SignedSpmTopT2P0083Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P005L083 : ∀ x ∈ Icc ((((576460746934190085 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((1152921494942121993 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0084Lo : ℝ) (ceSignedSpmTopT2P0084Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0084Lo, ceSignedSpmTopT2P0084Hi, SignedSpmTopT2P0084Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0084Bound x h'
  norm_num [SignedSpmTopT2P0084Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P005L084 : ∀ x ∈ Icc ((((1152921494942121993 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((144115187001982977 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0085Lo : ℝ) (ceSignedSpmTopT2P0085Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0085Lo, ceSignedSpmTopT2P0085Hi, SignedSpmTopT2P0085Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0085Bound x h'
  norm_num [SignedSpmTopT2P0085Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P005L085 : ∀ x ∈ Icc ((((144115187001982977 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((1152921497089605639 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0086Lo : ℝ) (ceSignedSpmTopT2P0086Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0086Lo, ceSignedSpmTopT2P0086Hi, SignedSpmTopT2P0086Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0086Bound x h'
  norm_num [SignedSpmTopT2P0086Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P005L086 : ∀ x ∈ Icc ((((1152921497089605639 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((576460749081673731 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0087Lo : ℝ) (ceSignedSpmTopT2P0087Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0087Lo, ceSignedSpmTopT2P0087Hi, SignedSpmTopT2P0087Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0087Bound x h'
  norm_num [SignedSpmTopT2P0087Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P005L087 : ∀ x ∈ Icc ((((576460749081673731 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((1152921499237089285 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0088Lo : ℝ) (ceSignedSpmTopT2P0088Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0088Lo, ceSignedSpmTopT2P0088Hi, SignedSpmTopT2P0088Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0088Bound x h'
  norm_num [SignedSpmTopT2P0088Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P005L088 : ∀ x ∈ Icc ((((1152921499237089285 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((2305842999547920393 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0089Lo : ℝ) (ceSignedSpmTopT2P0089Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0089Lo, ceSignedSpmTopT2P0089Hi, SignedSpmTopT2P0089Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0089Bound x h'
  norm_num [SignedSpmTopT2P0089Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P005L089 : ∀ x ∈ Icc ((((2305842999547920393 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((288230375077707777 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0090Lo : ℝ) (ceSignedSpmTopT2P0090Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0090Lo, ceSignedSpmTopT2P0090Hi, SignedSpmTopT2P0090Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0090Bound x h'
  norm_num [SignedSpmTopT2P0090Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P005L090 : ∀ x ∈ Icc ((((288230375077707777 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((2305843001695404039 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0091Lo : ℝ) (ceSignedSpmTopT2P0091Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0091Lo, ceSignedSpmTopT2P0091Hi, SignedSpmTopT2P0091Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0091Bound x h'
  norm_num [SignedSpmTopT2P0091Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P005L091 : ∀ x ∈ Icc ((((2305843001695404039 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((1152921501384572931 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0092Lo : ℝ) (ceSignedSpmTopT2P0092Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0092Lo, ceSignedSpmTopT2P0092Hi, SignedSpmTopT2P0092Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0092Bound x h'
  norm_num [SignedSpmTopT2P0092Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P005L092 : ∀ x ∈ Icc ((((1152921501384572931 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((2305843003842887685 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0093Lo : ℝ) (ceSignedSpmTopT2P0093Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0093Lo, ceSignedSpmTopT2P0093Hi, SignedSpmTopT2P0093Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0093Bound x h'
  norm_num [SignedSpmTopT2P0093Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P005L093 : ∀ x ∈ Icc ((((2305843003842887685 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((4611686008759517193 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0094Lo : ℝ) (ceSignedSpmTopT2P0094Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0094Lo, ceSignedSpmTopT2P0094Hi, SignedSpmTopT2P0094Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0094Bound x h'
  norm_num [SignedSpmTopT2P0094Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P005L094 : ∀ x ∈ Icc ((((4611686008759517193 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((576460751229157377 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0095Lo : ℝ) (ceSignedSpmTopT2P0095Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0095Lo, ceSignedSpmTopT2P0095Hi, SignedSpmTopT2P0095Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0095Bound x h'
  norm_num [SignedSpmTopT2P0095Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P005L095 : ∀ x ∈ Icc ((((576460751229157377 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0096Lo : ℝ) (ceSignedSpmTopT2P0096Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0096Lo, ceSignedSpmTopT2P0096Hi, SignedSpmTopT2P0096Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0096Bound x h'
  norm_num [SignedSpmTopT2P0096Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT2CoverD1B0P005 : ∀ x ∈ Icc ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT2CoverD1B0P005L080 SignedSpmTopT2CoverD1B0P005L081) (cover_union SignedSpmTopT2CoverD1B0P005L082 SignedSpmTopT2CoverD1B0P005L083)) (cover_union (cover_union SignedSpmTopT2CoverD1B0P005L084 SignedSpmTopT2CoverD1B0P005L085) (cover_union SignedSpmTopT2CoverD1B0P005L086 SignedSpmTopT2CoverD1B0P005L087))) (cover_union (cover_union (cover_union SignedSpmTopT2CoverD1B0P005L088 SignedSpmTopT2CoverD1B0P005L089) (cover_union SignedSpmTopT2CoverD1B0P005L090 SignedSpmTopT2CoverD1B0P005L091)) (cover_union (cover_union SignedSpmTopT2CoverD1B0P005L092 SignedSpmTopT2CoverD1B0P005L093) (cover_union SignedSpmTopT2CoverD1B0P005L094 SignedSpmTopT2CoverD1B0P005L095))))
#print axioms SignedSpmTopT2CoverD1B0P005

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover
