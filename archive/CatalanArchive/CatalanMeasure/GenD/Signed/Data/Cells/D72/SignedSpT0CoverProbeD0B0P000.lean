module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0001
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverProbeD0B0P000L000Field : fieldNFCheck ceSignedSpT0End00FullFq ceSignedSpT0ZeroPlain = true := by decide +kernel
private theorem SignedSpT0CoverProbeD0B0P000L000Terms : laurentNF ceSignedSpT0End00FullTs = laurentNF [] := by decide +kernel

private theorem SignedSpT0CoverProbeD0B0P000L000 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0End00Lo : ℝ) (ceSignedSpT0End00Hi : ℝ) := by
    norm_num [ceSignedSpT0End00Lo, ceSignedSpT0End00Hi, SignedSpT0End00Literal.q2, ceSignedSpT0End00EndLiteral.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0End00Bound x h' (by norm_num [ceSignedSpT0End00Site, ceSignedSpT0End00EndLiteral.q2]; exact ne_of_gt hd.1)
  rw [fieldNFCheck_sound SignedSpT0CoverProbeD0B0P000L000Field x, ← laurentNF_sound ceSignedSpT0End00FullTs x, SignedSpT0CoverProbeD0B0P000L000Terms, laurentNF_sound [] x] at h
  norm_num [SignedSpT0End00Literal.q2, ceSignedSpT0End00EndLiteral.q2, ceSignedSpT0End00Target] at h ⊢
  exact h

private theorem SignedSpT0CoverProbeD0B0P000L001 : ∀ x ∈ Icc ((((1 : ℚ) / 1024) : ℚ) : ℝ) ((((143 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0000Lo : ℝ) (ceSignedSpT0P0000Hi : ℝ) := by
    norm_num [ceSignedSpT0P0000Lo, ceSignedSpT0P0000Hi, SignedSpT0P0000Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0000Bound x h'
  norm_num [SignedSpT0P0000Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverProbeD0B0P000L002 : ∀ x ∈ Icc ((((143 : ℚ) / 16384) : ℚ) : ℝ) ((((135 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0001Lo : ℝ) (ceSignedSpT0P0001Hi : ℝ) := by
    norm_num [ceSignedSpT0P0001Lo, ceSignedSpT0P0001Hi, SignedSpT0P0001Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0001Bound x h'
  norm_num [SignedSpT0P0001Literal.q2] at h ⊢
  exact h

theorem SignedSpT0CoverProbeD0B0P000 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((135 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) :=
  (cover_union SignedSpT0CoverProbeD0B0P000L000 (cover_union SignedSpT0CoverProbeD0B0P000L001 SignedSpT0CoverProbeD0B0P000L002))
#print axioms SignedSpT0CoverProbeD0B0P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
