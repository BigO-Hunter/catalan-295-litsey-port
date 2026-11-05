module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0End01
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverProbeD1B0P000L000Field : fieldNFCheck ceSignedSpT0End01FullFq ceSignedSpT0Fq = true := by decide +kernel
private theorem SignedSpT0CoverProbeD1B0P000L000Terms : laurentNF ceSignedSpT0End01FullTs = laurentNF ceSignedSpT0Ts := by decide +kernel

private theorem SignedSpT0CoverProbeD1B0P000L000 : ∀ x ∈ Icc ((((1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0End01Lo : ℝ) (ceSignedSpT0End01Hi : ℝ) := by
    norm_num [ceSignedSpT0End01Lo, ceSignedSpT0End01Hi, SignedSpT0End01Literal.q2, ceSignedSpT0End01EndLiteral.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0End01Bound x h' (by norm_num [ceSignedSpT0End01Site, ceSignedSpT0End01EndLiteral.q2]; exact ne_of_lt hd.2)
  rw [fieldNFCheck_sound SignedSpT0CoverProbeD1B0P000L000Field x, ← laurentNF_sound ceSignedSpT0End01FullTs x, SignedSpT0CoverProbeD1B0P000L000Terms, laurentNF_sound ceSignedSpT0Ts x] at h
  norm_num [SignedSpT0End01Literal.q2, ceSignedSpT0End01EndLiteral.q2, ceSignedSpT0End01Target] at h ⊢
  exact h

theorem SignedSpT0CoverProbeD1B0P000 : ∀ x ∈ Icc ((((1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  SignedSpT0CoverProbeD1B0P000L000
#print axioms SignedSpT0CoverProbeD1B0P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
