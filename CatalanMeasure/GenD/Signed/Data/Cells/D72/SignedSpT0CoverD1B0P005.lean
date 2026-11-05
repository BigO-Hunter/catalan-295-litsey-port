module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0168
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0169
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0170
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0171
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0172
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0173
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0174
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0175
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0176
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0177
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0178
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0179
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0180
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0181
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0182
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0183
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverD1B0P005L080 : ∀ x ∈ Icc ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((576460744786706439 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0168Lo : ℝ) (ceSignedSpT0P0168Hi : ℝ) := by
    norm_num [ceSignedSpT0P0168Lo, ceSignedSpT0P0168Hi, SignedSpT0P0168Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0168Bound x h'
  norm_num [SignedSpT0P0168Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P005L081 : ∀ x ∈ Icc ((((576460744786706439 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((288230372930224131 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0169Lo : ℝ) (ceSignedSpT0P0169Hi : ℝ) := by
    norm_num [ceSignedSpT0P0169Lo, ceSignedSpT0P0169Hi, SignedSpT0P0169Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0169Bound x h'
  norm_num [SignedSpT0P0169Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P005L082 : ∀ x ∈ Icc ((((288230372930224131 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((576460746934190085 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0170Lo : ℝ) (ceSignedSpT0P0170Hi : ℝ) := by
    norm_num [ceSignedSpT0P0170Lo, ceSignedSpT0P0170Hi, SignedSpT0P0170Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0170Bound x h'
  norm_num [SignedSpT0P0170Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P005L083 : ∀ x ∈ Icc ((((576460746934190085 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((1152921494942121993 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0171Lo : ℝ) (ceSignedSpT0P0171Hi : ℝ) := by
    norm_num [ceSignedSpT0P0171Lo, ceSignedSpT0P0171Hi, SignedSpT0P0171Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0171Bound x h'
  norm_num [SignedSpT0P0171Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P005L084 : ∀ x ∈ Icc ((((1152921494942121993 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((144115187001982977 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0172Lo : ℝ) (ceSignedSpT0P0172Hi : ℝ) := by
    norm_num [ceSignedSpT0P0172Lo, ceSignedSpT0P0172Hi, SignedSpT0P0172Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0172Bound x h'
  norm_num [SignedSpT0P0172Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P005L085 : ∀ x ∈ Icc ((((144115187001982977 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((1152921497089605639 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0173Lo : ℝ) (ceSignedSpT0P0173Hi : ℝ) := by
    norm_num [ceSignedSpT0P0173Lo, ceSignedSpT0P0173Hi, SignedSpT0P0173Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0173Bound x h'
  norm_num [SignedSpT0P0173Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P005L086 : ∀ x ∈ Icc ((((1152921497089605639 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((576460749081673731 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0174Lo : ℝ) (ceSignedSpT0P0174Hi : ℝ) := by
    norm_num [ceSignedSpT0P0174Lo, ceSignedSpT0P0174Hi, SignedSpT0P0174Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0174Bound x h'
  norm_num [SignedSpT0P0174Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P005L087 : ∀ x ∈ Icc ((((576460749081673731 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((1152921499237089285 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0175Lo : ℝ) (ceSignedSpT0P0175Hi : ℝ) := by
    norm_num [ceSignedSpT0P0175Lo, ceSignedSpT0P0175Hi, SignedSpT0P0175Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0175Bound x h'
  norm_num [SignedSpT0P0175Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P005L088 : ∀ x ∈ Icc ((((1152921499237089285 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((2305842999547920393 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0176Lo : ℝ) (ceSignedSpT0P0176Hi : ℝ) := by
    norm_num [ceSignedSpT0P0176Lo, ceSignedSpT0P0176Hi, SignedSpT0P0176Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0176Bound x h'
  norm_num [SignedSpT0P0176Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P005L089 : ∀ x ∈ Icc ((((2305842999547920393 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((288230375077707777 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0177Lo : ℝ) (ceSignedSpT0P0177Hi : ℝ) := by
    norm_num [ceSignedSpT0P0177Lo, ceSignedSpT0P0177Hi, SignedSpT0P0177Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0177Bound x h'
  norm_num [SignedSpT0P0177Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P005L090 : ∀ x ∈ Icc ((((288230375077707777 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((2305843001695404039 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0178Lo : ℝ) (ceSignedSpT0P0178Hi : ℝ) := by
    norm_num [ceSignedSpT0P0178Lo, ceSignedSpT0P0178Hi, SignedSpT0P0178Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0178Bound x h'
  norm_num [SignedSpT0P0178Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P005L091 : ∀ x ∈ Icc ((((2305843001695404039 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((1152921501384572931 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0179Lo : ℝ) (ceSignedSpT0P0179Hi : ℝ) := by
    norm_num [ceSignedSpT0P0179Lo, ceSignedSpT0P0179Hi, SignedSpT0P0179Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0179Bound x h'
  norm_num [SignedSpT0P0179Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P005L092 : ∀ x ∈ Icc ((((1152921501384572931 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((2305843003842887685 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0180Lo : ℝ) (ceSignedSpT0P0180Hi : ℝ) := by
    norm_num [ceSignedSpT0P0180Lo, ceSignedSpT0P0180Hi, SignedSpT0P0180Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0180Bound x h'
  norm_num [SignedSpT0P0180Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P005L093 : ∀ x ∈ Icc ((((2305843003842887685 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((4611686008759517193 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0181Lo : ℝ) (ceSignedSpT0P0181Hi : ℝ) := by
    norm_num [ceSignedSpT0P0181Lo, ceSignedSpT0P0181Hi, SignedSpT0P0181Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0181Bound x h'
  norm_num [SignedSpT0P0181Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P005L094 : ∀ x ∈ Icc ((((4611686008759517193 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((576460751229157377 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0182Lo : ℝ) (ceSignedSpT0P0182Hi : ℝ) := by
    norm_num [ceSignedSpT0P0182Lo, ceSignedSpT0P0182Hi, SignedSpT0P0182Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0182Bound x h'
  norm_num [SignedSpT0P0182Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P005L095 : ∀ x ∈ Icc ((((576460751229157377 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0183Lo : ℝ) (ceSignedSpT0P0183Hi : ℝ) := by
    norm_num [ceSignedSpT0P0183Lo, ceSignedSpT0P0183Hi, SignedSpT0P0183Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0183Bound x h'
  norm_num [SignedSpT0P0183Literal.q2] at h ⊢
  exact h

theorem SignedSpT0CoverD1B0P005 : ∀ x ∈ Icc ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT0CoverD1B0P005L080 SignedSpT0CoverD1B0P005L081) (cover_union SignedSpT0CoverD1B0P005L082 SignedSpT0CoverD1B0P005L083)) (cover_union (cover_union SignedSpT0CoverD1B0P005L084 SignedSpT0CoverD1B0P005L085) (cover_union SignedSpT0CoverD1B0P005L086 SignedSpT0CoverD1B0P005L087))) (cover_union (cover_union (cover_union SignedSpT0CoverD1B0P005L088 SignedSpT0CoverD1B0P005L089) (cover_union SignedSpT0CoverD1B0P005L090 SignedSpT0CoverD1B0P005L091)) (cover_union (cover_union SignedSpT0CoverD1B0P005L092 SignedSpT0CoverD1B0P005L093) (cover_union SignedSpT0CoverD1B0P005L094 SignedSpT0CoverD1B0P005L095))))
#print axioms SignedSpT0CoverD1B0P005

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
