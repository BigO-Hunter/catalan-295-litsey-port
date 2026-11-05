module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core063
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core064
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core065
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core066
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core067
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core068
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core069
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core070
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core071
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core072
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core073
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core074
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core075
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core076
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core077
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core078
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell064 : ∀ y ∈ Icc ((((-798091896683919 : ℚ) / 1374389534720000) : ℚ) : ℝ) ((((-314967887280717 : ℚ) / 549755813888000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P063Lo : ℝ) (ceSignedSnEntryT2P063Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P063Lo, ceSignedSnEntryT2P063Hi, SignedSnEntryT2Core063Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P063Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core063Literal.q2] at h ⊢
  exact h

private theorem cell065 : ∀ y ∈ Icc ((((-314967887280717 : ℚ) / 549755813888000) : ℚ) : ℝ) ((((-755403182755413 : ℚ) / 1374389534720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P064Lo : ℝ) (ceSignedSnEntryT2P064Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P064Lo, ceSignedSnEntryT2P064Hi, SignedSnEntryT2Core064Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P064Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core064Literal.q2] at h ⊢
  exact h

private theorem cell066 : ∀ y ∈ Icc ((((-755403182755413 : ℚ) / 1374389534720000) : ℚ) : ℝ) ((((-1489462008546573 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P065Lo : ℝ) (ceSignedSnEntryT2P065Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P065Lo, ceSignedSnEntryT2P065Hi, SignedSnEntryT2Core065Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P065Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core065Literal.q2] at h ⊢
  exact h

private theorem cell067 : ∀ y ∈ Icc ((((-1489462008546573 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-2957579660128893 : ℚ) / 5497558138880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P066Lo : ℝ) (ceSignedSnEntryT2P066Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P066Lo, ceSignedSnEntryT2P066Hi, SignedSnEntryT2Core066Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P066Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core066Literal.q2] at h ⊢
  exact h

private theorem cell068 : ∀ y ∈ Icc ((((-2957579660128893 : ℚ) / 5497558138880000) : ℚ) : ℝ) ((((-18351470644779 : ℚ) / 34359738368000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P067Lo : ℝ) (ceSignedSnEntryT2P067Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P067Lo, ceSignedSnEntryT2P067Hi, SignedSnEntryT2Core067Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P067Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core067Literal.q2] at h ⊢
  exact h

private theorem cell069 : ∀ y ∈ Icc ((((-18351470644779 : ℚ) / 34359738368000) : ℚ) : ℝ) ((((-345685055931327 : ℚ) / 687194767360000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P068Lo : ℝ) (ceSignedSnEntryT2P068Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P068Lo, ceSignedSnEntryT2P068Hi, SignedSnEntryT2Core068Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P068Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core068Literal.q2] at h ⊢
  exact h

private theorem cell070 : ∀ y ∈ Icc ((((-345685055931327 : ℚ) / 687194767360000) : ℚ) : ℝ) ((((-2744136090486363 : ℚ) / 5497558138880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P069Lo : ℝ) (ceSignedSnEntryT2P069Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P069Lo, ceSignedSnEntryT2P069Hi, SignedSnEntryT2Core069Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P069Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core069Literal.q2] at h ⊢
  exact h

private theorem cell071 : ∀ y ∈ Icc ((((-2744136090486363 : ℚ) / 5497558138880000) : ℚ) : ℝ) ((((-272279173352211 : ℚ) / 549755813888000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P070Lo : ℝ) (ceSignedSnEntryT2P070Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P070Lo, ceSignedSnEntryT2P070Hi, SignedSnEntryT2Core070Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P070Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core070Literal.q2] at h ⊢
  exact h

private theorem cell072 : ∀ y ∈ Icc ((((-272279173352211 : ℚ) / 549755813888000) : ℚ) : ℝ) ((((-670025754898401 : ℚ) / 1374389534720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P071Lo : ℝ) (ceSignedSnEntryT2P071Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P071Lo, ceSignedSnEntryT2P071Hi, SignedSnEntryT2Core071Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P071Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core071Literal.q2] at h ⊢
  exact h

private theorem cell073 : ∀ y ∈ Icc ((((-670025754898401 : ℚ) / 1374389534720000) : ℚ) : ℝ) ((((-162170349483537 : ℚ) / 343597383680000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P072Lo : ℝ) (ceSignedSnEntryT2P072Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P072Lo, ceSignedSnEntryT2P072Hi, SignedSnEntryT2Core072Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P072Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core072Literal.q2] at h ⊢
  exact h

private theorem cell074 : ∀ y ∈ Icc ((((-162170349483537 : ℚ) / 343597383680000) : ℚ) : ℝ) ((((-125467408193979 : ℚ) / 274877906944000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P073Lo : ℝ) (ceSignedSnEntryT2P073Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P073Lo, ceSignedSnEntryT2P073Hi, SignedSnEntryT2Core073Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P073Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core073Literal.q2] at h ⊢
  exact h

private theorem cell075 : ∀ y ∈ Icc ((((-125467408193979 : ℚ) / 274877906944000) : ℚ) : ℝ) ((((-1233329724975537 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P074Lo : ℝ) (ceSignedSnEntryT2P074Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P074Lo, ceSignedSnEntryT2P074Hi, SignedSnEntryT2Core074Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P074Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core074Literal.q2] at h ⊢
  exact h

private theorem cell076 : ∀ y ∈ Icc ((((-1233329724975537 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-302996342002821 : ℚ) / 687194767360000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P075Lo : ℝ) (ceSignedSnEntryT2P075Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P075Lo, ceSignedSnEntryT2P075Hi, SignedSnEntryT2Core075Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P075Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core075Literal.q2] at h ⊢
  exact h

private theorem cell077 : ∀ y ∈ Icc ((((-302996342002821 : ℚ) / 687194767360000) : ℚ) : ℝ) ((((-45918091884741 : ℚ) / 109951162777600) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P076Lo : ℝ) (ceSignedSnEntryT2P076Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P076Lo, ceSignedSnEntryT2P076Hi, SignedSnEntryT2Core076Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P076Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core076Literal.q2] at h ⊢
  exact h

private theorem cell078 : ∀ y ∈ Icc ((((-45918091884741 : ℚ) / 109951162777600) : ℚ) : ℝ) ((((-35206498129821 : ℚ) / 85899345920000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P077Lo : ℝ) (ceSignedSnEntryT2P077Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P077Lo, ceSignedSnEntryT2P077Hi, SignedSnEntryT2Core077Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P077Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core077Literal.q2] at h ⊢
  exact h

private theorem cell079 : ∀ y ∈ Icc ((((-35206498129821 : ℚ) / 85899345920000) : ℚ) : ℝ) ((((-2231871523344291 : ℚ) / 5497558138880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P078Lo : ℝ) (ceSignedSnEntryT2P078Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P078Lo, ceSignedSnEntryT2P078Hi, SignedSnEntryT2Core078Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P078Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core078Literal.q2] at h ⊢
  exact h

theorem cover004 : ∀ y ∈ Icc ((((-798091896683919 : ℚ) / 1374389534720000) : ℚ) : ℝ) ((((-2231871523344291 : ℚ) / 5497558138880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell064 cell065) (cover_union cell066 cell067)) (cover_union (cover_union cell068 cell069) (cover_union cell070 cell071))) (cover_union (cover_union (cover_union cell072 cell073) (cover_union cell074 cell075)) (cover_union (cover_union cell076 cell077) (cover_union cell078 cell079))))
#print axioms cover004
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
