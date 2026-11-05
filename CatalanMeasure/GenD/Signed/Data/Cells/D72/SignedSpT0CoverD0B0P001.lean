module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0015
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0017
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverD0B0P001L016 : ∀ x ∈ Icc ((((3715 : ℚ) / 32768) : ℚ) : ℝ) ((((1921 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0015Lo : ℝ) (ceSignedSpT0P0015Hi : ℝ) := by
    norm_num [ceSignedSpT0P0015Lo, ceSignedSpT0P0015Hi, SignedSpT0P0015Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0015Bound x h'
  norm_num [SignedSpT0P0015Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P001L017 : ∀ x ∈ Icc ((((1921 : ℚ) / 16384) : ℚ) : ℝ) ((((3969 : ℚ) / 32768) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0016Lo : ℝ) (ceSignedSpT0P0016Hi : ℝ) := by
    norm_num [ceSignedSpT0P0016Lo, ceSignedSpT0P0016Hi, SignedSpT0P0016Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0016Bound x h'
  norm_num [SignedSpT0P0016Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P001L018 : ∀ x ∈ Icc ((((3969 : ℚ) / 32768) : ℚ) : ℝ) ((((1 : ℚ) / 8) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0017Lo : ℝ) (ceSignedSpT0P0017Hi : ℝ) := by
    norm_num [ceSignedSpT0P0017Lo, ceSignedSpT0P0017Hi, SignedSpT0P0017Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0017Bound x h'
  norm_num [SignedSpT0P0017Literal.q2] at h ⊢
  exact h

theorem SignedSpT0CoverD0B0P001 : ∀ x ∈ Icc ((((3715 : ℚ) / 32768) : ℚ) : ℝ) ((((1 : ℚ) / 8) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) :=
  (cover_union SignedSpT0CoverD0B0P001L016 (cover_union SignedSpT0CoverD0B0P001L017 SignedSpT0CoverD0B0P001L018))
#print axioms SignedSpT0CoverD0B0P001

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
