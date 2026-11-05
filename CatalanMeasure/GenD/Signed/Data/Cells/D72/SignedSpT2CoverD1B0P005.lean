module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0170
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0171
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0172
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0173
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0174
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0175
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0176
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0177
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0178
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0179
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0180
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0181
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0182
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0183
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0184
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0185
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT2CoverD1B0P005L080 : ∀ x ∈ Icc ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((576460744786706439 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0170Lo : ℝ) (ceSignedSpT2P0170Hi : ℝ) := by
    norm_num [ceSignedSpT2P0170Lo, ceSignedSpT2P0170Hi, SignedSpT2P0170Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0170Bound x h'
  norm_num [SignedSpT2P0170Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P005L081 : ∀ x ∈ Icc ((((576460744786706439 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((288230372930224131 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0171Lo : ℝ) (ceSignedSpT2P0171Hi : ℝ) := by
    norm_num [ceSignedSpT2P0171Lo, ceSignedSpT2P0171Hi, SignedSpT2P0171Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0171Bound x h'
  norm_num [SignedSpT2P0171Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P005L082 : ∀ x ∈ Icc ((((288230372930224131 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((576460746934190085 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0172Lo : ℝ) (ceSignedSpT2P0172Hi : ℝ) := by
    norm_num [ceSignedSpT2P0172Lo, ceSignedSpT2P0172Hi, SignedSpT2P0172Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0172Bound x h'
  norm_num [SignedSpT2P0172Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P005L083 : ∀ x ∈ Icc ((((576460746934190085 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((1152921494942121993 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0173Lo : ℝ) (ceSignedSpT2P0173Hi : ℝ) := by
    norm_num [ceSignedSpT2P0173Lo, ceSignedSpT2P0173Hi, SignedSpT2P0173Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0173Bound x h'
  norm_num [SignedSpT2P0173Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P005L084 : ∀ x ∈ Icc ((((1152921494942121993 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((144115187001982977 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0174Lo : ℝ) (ceSignedSpT2P0174Hi : ℝ) := by
    norm_num [ceSignedSpT2P0174Lo, ceSignedSpT2P0174Hi, SignedSpT2P0174Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0174Bound x h'
  norm_num [SignedSpT2P0174Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P005L085 : ∀ x ∈ Icc ((((144115187001982977 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((1152921497089605639 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0175Lo : ℝ) (ceSignedSpT2P0175Hi : ℝ) := by
    norm_num [ceSignedSpT2P0175Lo, ceSignedSpT2P0175Hi, SignedSpT2P0175Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0175Bound x h'
  norm_num [SignedSpT2P0175Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P005L086 : ∀ x ∈ Icc ((((1152921497089605639 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((576460749081673731 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0176Lo : ℝ) (ceSignedSpT2P0176Hi : ℝ) := by
    norm_num [ceSignedSpT2P0176Lo, ceSignedSpT2P0176Hi, SignedSpT2P0176Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0176Bound x h'
  norm_num [SignedSpT2P0176Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P005L087 : ∀ x ∈ Icc ((((576460749081673731 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((1152921499237089285 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0177Lo : ℝ) (ceSignedSpT2P0177Hi : ℝ) := by
    norm_num [ceSignedSpT2P0177Lo, ceSignedSpT2P0177Hi, SignedSpT2P0177Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0177Bound x h'
  norm_num [SignedSpT2P0177Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P005L088 : ∀ x ∈ Icc ((((1152921499237089285 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((2305842999547920393 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0178Lo : ℝ) (ceSignedSpT2P0178Hi : ℝ) := by
    norm_num [ceSignedSpT2P0178Lo, ceSignedSpT2P0178Hi, SignedSpT2P0178Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0178Bound x h'
  norm_num [SignedSpT2P0178Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P005L089 : ∀ x ∈ Icc ((((2305842999547920393 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((288230375077707777 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0179Lo : ℝ) (ceSignedSpT2P0179Hi : ℝ) := by
    norm_num [ceSignedSpT2P0179Lo, ceSignedSpT2P0179Hi, SignedSpT2P0179Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0179Bound x h'
  norm_num [SignedSpT2P0179Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P005L090 : ∀ x ∈ Icc ((((288230375077707777 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((2305843001695404039 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0180Lo : ℝ) (ceSignedSpT2P0180Hi : ℝ) := by
    norm_num [ceSignedSpT2P0180Lo, ceSignedSpT2P0180Hi, SignedSpT2P0180Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0180Bound x h'
  norm_num [SignedSpT2P0180Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P005L091 : ∀ x ∈ Icc ((((2305843001695404039 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((1152921501384572931 : ℚ) / 1152921504606846976) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0181Lo : ℝ) (ceSignedSpT2P0181Hi : ℝ) := by
    norm_num [ceSignedSpT2P0181Lo, ceSignedSpT2P0181Hi, SignedSpT2P0181Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0181Bound x h'
  norm_num [SignedSpT2P0181Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P005L092 : ∀ x ∈ Icc ((((1152921501384572931 : ℚ) / 1152921504606846976) : ℚ) : ℝ) ((((2305843003842887685 : ℚ) / 2305843009213693952) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0182Lo : ℝ) (ceSignedSpT2P0182Hi : ℝ) := by
    norm_num [ceSignedSpT2P0182Lo, ceSignedSpT2P0182Hi, SignedSpT2P0182Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0182Bound x h'
  norm_num [SignedSpT2P0182Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P005L093 : ∀ x ∈ Icc ((((2305843003842887685 : ℚ) / 2305843009213693952) : ℚ) : ℝ) ((((4611686008759517193 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0183Lo : ℝ) (ceSignedSpT2P0183Hi : ℝ) := by
    norm_num [ceSignedSpT2P0183Lo, ceSignedSpT2P0183Hi, SignedSpT2P0183Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0183Bound x h'
  norm_num [SignedSpT2P0183Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P005L094 : ∀ x ∈ Icc ((((4611686008759517193 : ℚ) / 4611686018427387904) : ℚ) : ℝ) ((((576460751229157377 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0184Lo : ℝ) (ceSignedSpT2P0184Hi : ℝ) := by
    norm_num [ceSignedSpT2P0184Lo, ceSignedSpT2P0184Hi, SignedSpT2P0184Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0184Bound x h'
  norm_num [SignedSpT2P0184Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P005L095 : ∀ x ∈ Icc ((((576460751229157377 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0185Lo : ℝ) (ceSignedSpT2P0185Hi : ℝ) := by
    norm_num [ceSignedSpT2P0185Lo, ceSignedSpT2P0185Hi, SignedSpT2P0185Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0185Bound x h'
  norm_num [SignedSpT2P0185Literal.q2] at h ⊢
  exact h

theorem SignedSpT2CoverD1B0P005 : ∀ x ∈ Icc ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((4611686010907000839 : ℚ) / 4611686018427387904) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P005L080 SignedSpT2CoverD1B0P005L081) (cover_union SignedSpT2CoverD1B0P005L082 SignedSpT2CoverD1B0P005L083)) (cover_union (cover_union SignedSpT2CoverD1B0P005L084 SignedSpT2CoverD1B0P005L085) (cover_union SignedSpT2CoverD1B0P005L086 SignedSpT2CoverD1B0P005L087))) (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P005L088 SignedSpT2CoverD1B0P005L089) (cover_union SignedSpT2CoverD1B0P005L090 SignedSpT2CoverD1B0P005L091)) (cover_union (cover_union SignedSpT2CoverD1B0P005L092 SignedSpT2CoverD1B0P005L093) (cover_union SignedSpT2CoverD1B0P005L094 SignedSpT2CoverD1B0P005L095))))
#print axioms SignedSpT2CoverD1B0P005

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
