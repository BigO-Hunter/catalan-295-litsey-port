module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0168
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0169
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0170
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0171
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0172
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0173
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0174
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0175
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0176
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0177
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0178
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0179
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0180
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0181
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0182
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0183
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT1CoverD1B0P005L080 : ∀ x ∈ Icc ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((576460744786706439 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0168Lo : ℝ) (ceSignedSpT1P0168Hi : ℝ) := by
    norm_num [ceSignedSpT1P0168Lo, ceSignedSpT1P0168Hi, SignedSpT1P0168Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0168Bound x h'
  norm_num [SignedSpT1P0168Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P005L081 : ∀ x ∈ Icc ((((576460744786706439 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((288230372930224131 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0169Lo : ℝ) (ceSignedSpT1P0169Hi : ℝ) := by
    norm_num [ceSignedSpT1P0169Lo, ceSignedSpT1P0169Hi, SignedSpT1P0169Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0169Bound x h'
  norm_num [SignedSpT1P0169Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P005L082 : ∀ x ∈ Icc ((((288230372930224131 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((576460746934190085 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0170Lo : ℝ) (ceSignedSpT1P0170Hi : ℝ) := by
    norm_num [ceSignedSpT1P0170Lo, ceSignedSpT1P0170Hi, SignedSpT1P0170Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0170Bound x h'
  norm_num [SignedSpT1P0170Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P005L083 : ∀ x ∈ Icc ((((576460746934190085 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((1152921494942121993 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0171Lo : ℝ) (ceSignedSpT1P0171Hi : ℝ) := by
    norm_num [ceSignedSpT1P0171Lo, ceSignedSpT1P0171Hi, SignedSpT1P0171Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0171Bound x h'
  norm_num [SignedSpT1P0171Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P005L084 : ∀ x ∈ Icc ((((1152921494942121993 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((144115187001982977 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0172Lo : ℝ) (ceSignedSpT1P0172Hi : ℝ) := by
    norm_num [ceSignedSpT1P0172Lo, ceSignedSpT1P0172Hi, SignedSpT1P0172Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0172Bound x h'
  norm_num [SignedSpT1P0172Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P005L085 : ∀ x ∈ Icc ((((144115187001982977 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((1152921497089605639 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0173Lo : ℝ) (ceSignedSpT1P0173Hi : ℝ) := by
    norm_num [ceSignedSpT1P0173Lo, ceSignedSpT1P0173Hi, SignedSpT1P0173Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0173Bound x h'
  norm_num [SignedSpT1P0173Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P005L086 : ∀ x ∈ Icc ((((1152921497089605639 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((576460749081673731 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0174Lo : ℝ) (ceSignedSpT1P0174Hi : ℝ) := by
    norm_num [ceSignedSpT1P0174Lo, ceSignedSpT1P0174Hi, SignedSpT1P0174Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0174Bound x h'
  norm_num [SignedSpT1P0174Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P005L087 : ∀ x ∈ Icc ((((576460749081673731 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((1152921499237089285 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0175Lo : ℝ) (ceSignedSpT1P0175Hi : ℝ) := by
    norm_num [ceSignedSpT1P0175Lo, ceSignedSpT1P0175Hi, SignedSpT1P0175Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0175Bound x h'
  norm_num [SignedSpT1P0175Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P005L088 : ∀ x ∈ Icc ((((1152921499237089285 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((2305842999547920393 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0176Lo : ℝ) (ceSignedSpT1P0176Hi : ℝ) := by
    norm_num [ceSignedSpT1P0176Lo, ceSignedSpT1P0176Hi, SignedSpT1P0176Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0176Bound x h'
  norm_num [SignedSpT1P0176Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P005L089 : ∀ x ∈ Icc ((((2305842999547920393 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((288230375077707777 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0177Lo : ℝ) (ceSignedSpT1P0177Hi : ℝ) := by
    norm_num [ceSignedSpT1P0177Lo, ceSignedSpT1P0177Hi, SignedSpT1P0177Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0177Bound x h'
  norm_num [SignedSpT1P0177Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P005L090 : ∀ x ∈ Icc ((((288230375077707777 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((2305843001695404039 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0178Lo : ℝ) (ceSignedSpT1P0178Hi : ℝ) := by
    norm_num [ceSignedSpT1P0178Lo, ceSignedSpT1P0178Hi, SignedSpT1P0178Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0178Bound x h'
  norm_num [SignedSpT1P0178Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P005L091 : ∀ x ∈ Icc ((((2305843001695404039 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((1152921501384572931 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0179Lo : ℝ) (ceSignedSpT1P0179Hi : ℝ) := by
    norm_num [ceSignedSpT1P0179Lo, ceSignedSpT1P0179Hi, SignedSpT1P0179Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0179Bound x h'
  norm_num [SignedSpT1P0179Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P005L092 : ∀ x ∈ Icc ((((1152921501384572931 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((2305843003842887685 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0180Lo : ℝ) (ceSignedSpT1P0180Hi : ℝ) := by
    norm_num [ceSignedSpT1P0180Lo, ceSignedSpT1P0180Hi, SignedSpT1P0180Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0180Bound x h'
  norm_num [SignedSpT1P0180Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P005L093 : ∀ x ∈ Icc ((((2305843003842887685 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((4611686008759517193 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0181Lo : ℝ) (ceSignedSpT1P0181Hi : ℝ) := by
    norm_num [ceSignedSpT1P0181Lo, ceSignedSpT1P0181Hi, SignedSpT1P0181Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0181Bound x h'
  norm_num [SignedSpT1P0181Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P005L094 : ∀ x ∈ Icc ((((4611686008759517193 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((576460751229157377 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0182Lo : ℝ) (ceSignedSpT1P0182Hi : ℝ) := by
    norm_num [ceSignedSpT1P0182Lo, ceSignedSpT1P0182Hi, SignedSpT1P0182Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0182Bound x h'
  norm_num [SignedSpT1P0182Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P005L095 : ∀ x ∈ Icc ((((576460751229157377 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0183Lo : ℝ) (ceSignedSpT1P0183Hi : ℝ) := by
    norm_num [ceSignedSpT1P0183Lo, ceSignedSpT1P0183Hi, SignedSpT1P0183Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0183Bound x h'
  norm_num [SignedSpT1P0183Literal.q2] at h ⊢
  exact h

theorem SignedSpT1CoverD1B0P005 : ∀ x ∈ Icc ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT1CoverD1B0P005L080 SignedSpT1CoverD1B0P005L081) (cover_union SignedSpT1CoverD1B0P005L082 SignedSpT1CoverD1B0P005L083)) (cover_union (cover_union SignedSpT1CoverD1B0P005L084 SignedSpT1CoverD1B0P005L085) (cover_union SignedSpT1CoverD1B0P005L086 SignedSpT1CoverD1B0P005L087))) (cover_union (cover_union (cover_union SignedSpT1CoverD1B0P005L088 SignedSpT1CoverD1B0P005L089) (cover_union SignedSpT1CoverD1B0P005L090 SignedSpT1CoverD1B0P005L091)) (cover_union (cover_union SignedSpT1CoverD1B0P005L092 SignedSpT1CoverD1B0P005L093) (cover_union SignedSpT1CoverD1B0P005L094 SignedSpT1CoverD1B0P005L095))))
#print axioms SignedSpT1CoverD1B0P005

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
