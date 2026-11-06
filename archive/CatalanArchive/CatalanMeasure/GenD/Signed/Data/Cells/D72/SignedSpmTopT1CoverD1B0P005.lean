module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0081
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0082
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0083
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0084
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0085
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0086
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0087
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0088
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0089
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0090
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0091
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0092
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0093
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0094
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0095
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0096
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT1CoverD1B0P005L080 : ∀ x ∈ Icc ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((576460744786706439 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0081Lo : ℝ) (ceSignedSpmTopT1P0081Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0081Lo, ceSignedSpmTopT1P0081Hi, SignedSpmTopT1P0081Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0081Bound x h'
  norm_num [SignedSpmTopT1P0081Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P005L081 : ∀ x ∈ Icc ((((576460744786706439 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((288230372930224131 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0082Lo : ℝ) (ceSignedSpmTopT1P0082Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0082Lo, ceSignedSpmTopT1P0082Hi, SignedSpmTopT1P0082Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0082Bound x h'
  norm_num [SignedSpmTopT1P0082Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P005L082 : ∀ x ∈ Icc ((((288230372930224131 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((576460746934190085 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0083Lo : ℝ) (ceSignedSpmTopT1P0083Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0083Lo, ceSignedSpmTopT1P0083Hi, SignedSpmTopT1P0083Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0083Bound x h'
  norm_num [SignedSpmTopT1P0083Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P005L083 : ∀ x ∈ Icc ((((576460746934190085 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((1152921494942121993 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0084Lo : ℝ) (ceSignedSpmTopT1P0084Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0084Lo, ceSignedSpmTopT1P0084Hi, SignedSpmTopT1P0084Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0084Bound x h'
  norm_num [SignedSpmTopT1P0084Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P005L084 : ∀ x ∈ Icc ((((1152921494942121993 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((144115187001982977 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0085Lo : ℝ) (ceSignedSpmTopT1P0085Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0085Lo, ceSignedSpmTopT1P0085Hi, SignedSpmTopT1P0085Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0085Bound x h'
  norm_num [SignedSpmTopT1P0085Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P005L085 : ∀ x ∈ Icc ((((144115187001982977 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((1152921497089605639 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0086Lo : ℝ) (ceSignedSpmTopT1P0086Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0086Lo, ceSignedSpmTopT1P0086Hi, SignedSpmTopT1P0086Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0086Bound x h'
  norm_num [SignedSpmTopT1P0086Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P005L086 : ∀ x ∈ Icc ((((1152921497089605639 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((576460749081673731 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0087Lo : ℝ) (ceSignedSpmTopT1P0087Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0087Lo, ceSignedSpmTopT1P0087Hi, SignedSpmTopT1P0087Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0087Bound x h'
  norm_num [SignedSpmTopT1P0087Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P005L087 : ∀ x ∈ Icc ((((576460749081673731 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((1152921499237089285 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0088Lo : ℝ) (ceSignedSpmTopT1P0088Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0088Lo, ceSignedSpmTopT1P0088Hi, SignedSpmTopT1P0088Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0088Bound x h'
  norm_num [SignedSpmTopT1P0088Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P005L088 : ∀ x ∈ Icc ((((1152921499237089285 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((2305842999547920393 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0089Lo : ℝ) (ceSignedSpmTopT1P0089Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0089Lo, ceSignedSpmTopT1P0089Hi, SignedSpmTopT1P0089Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0089Bound x h'
  norm_num [SignedSpmTopT1P0089Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P005L089 : ∀ x ∈ Icc ((((2305842999547920393 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((288230375077707777 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0090Lo : ℝ) (ceSignedSpmTopT1P0090Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0090Lo, ceSignedSpmTopT1P0090Hi, SignedSpmTopT1P0090Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0090Bound x h'
  norm_num [SignedSpmTopT1P0090Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P005L090 : ∀ x ∈ Icc ((((288230375077707777 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((2305843001695404039 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0091Lo : ℝ) (ceSignedSpmTopT1P0091Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0091Lo, ceSignedSpmTopT1P0091Hi, SignedSpmTopT1P0091Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0091Bound x h'
  norm_num [SignedSpmTopT1P0091Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P005L091 : ∀ x ∈ Icc ((((2305843001695404039 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((1152921501384572931 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0092Lo : ℝ) (ceSignedSpmTopT1P0092Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0092Lo, ceSignedSpmTopT1P0092Hi, SignedSpmTopT1P0092Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0092Bound x h'
  norm_num [SignedSpmTopT1P0092Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P005L092 : ∀ x ∈ Icc ((((1152921501384572931 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((2305843003842887685 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0093Lo : ℝ) (ceSignedSpmTopT1P0093Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0093Lo, ceSignedSpmTopT1P0093Hi, SignedSpmTopT1P0093Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0093Bound x h'
  norm_num [SignedSpmTopT1P0093Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P005L093 : ∀ x ∈ Icc ((((2305843003842887685 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((4611686008759517193 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0094Lo : ℝ) (ceSignedSpmTopT1P0094Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0094Lo, ceSignedSpmTopT1P0094Hi, SignedSpmTopT1P0094Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0094Bound x h'
  norm_num [SignedSpmTopT1P0094Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P005L094 : ∀ x ∈ Icc ((((4611686008759517193 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((576460751229157377 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0095Lo : ℝ) (ceSignedSpmTopT1P0095Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0095Lo, ceSignedSpmTopT1P0095Hi, SignedSpmTopT1P0095Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0095Bound x h'
  norm_num [SignedSpmTopT1P0095Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P005L095 : ∀ x ∈ Icc ((((576460751229157377 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0096Lo : ℝ) (ceSignedSpmTopT1P0096Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0096Lo, ceSignedSpmTopT1P0096Hi, SignedSpmTopT1P0096Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0096Bound x h'
  norm_num [SignedSpmTopT1P0096Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT1CoverD1B0P005 : ∀ x ∈ Icc ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT1CoverD1B0P005L080 SignedSpmTopT1CoverD1B0P005L081) (cover_union SignedSpmTopT1CoverD1B0P005L082 SignedSpmTopT1CoverD1B0P005L083)) (cover_union (cover_union SignedSpmTopT1CoverD1B0P005L084 SignedSpmTopT1CoverD1B0P005L085) (cover_union SignedSpmTopT1CoverD1B0P005L086 SignedSpmTopT1CoverD1B0P005L087))) (cover_union (cover_union (cover_union SignedSpmTopT1CoverD1B0P005L088 SignedSpmTopT1CoverD1B0P005L089) (cover_union SignedSpmTopT1CoverD1B0P005L090 SignedSpmTopT1CoverD1B0P005L091)) (cover_union (cover_union SignedSpmTopT1CoverD1B0P005L092 SignedSpmTopT1CoverD1B0P005L093) (cover_union SignedSpmTopT1CoverD1B0P005L094 SignedSpmTopT1CoverD1B0P005L095))))
#print axioms SignedSpmTopT1CoverD1B0P005

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover
