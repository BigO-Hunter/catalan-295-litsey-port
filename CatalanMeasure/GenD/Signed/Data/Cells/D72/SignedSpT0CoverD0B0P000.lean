module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0014
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverD0B0P000L000Field : fieldNFCheck ceSignedSpT0End00FullFq ceSignedSpT0ZeroPlain = true := by decide +kernel
private theorem SignedSpT0CoverD0B0P000L000Terms : laurentNF ceSignedSpT0End00FullTs = laurentNF [] := by decide +kernel

private theorem SignedSpT0CoverD0B0P000L000 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0End00Lo : ℝ) (ceSignedSpT0End00Hi : ℝ) := by
    norm_num [ceSignedSpT0End00Lo, ceSignedSpT0End00Hi, SignedSpT0End00Literal.q2, ceSignedSpT0End00EndLiteral.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0End00Bound x h' (by norm_num [ceSignedSpT0End00Site, ceSignedSpT0End00EndLiteral.q2]; exact ne_of_gt hd.1)
  rw [fieldNFCheck_sound SignedSpT0CoverD0B0P000L000Field x, ← laurentNF_sound ceSignedSpT0End00FullTs x, SignedSpT0CoverD0B0P000L000Terms, laurentNF_sound [] x] at h
  norm_num [SignedSpT0End00Literal.q2, ceSignedSpT0End00EndLiteral.q2, ceSignedSpT0End00Target] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P000L001 : ∀ x ∈ Icc ((((1 : ℚ) / 1024) : ℚ) : ℝ) ((((143 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0000Lo : ℝ) (ceSignedSpT0P0000Hi : ℝ) := by
    norm_num [ceSignedSpT0P0000Lo, ceSignedSpT0P0000Hi, SignedSpT0P0000Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0000Bound x h'
  norm_num [SignedSpT0P0000Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P000L002 : ∀ x ∈ Icc ((((143 : ℚ) / 16384) : ℚ) : ℝ) ((((135 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0001Lo : ℝ) (ceSignedSpT0P0001Hi : ℝ) := by
    norm_num [ceSignedSpT0P0001Lo, ceSignedSpT0P0001Hi, SignedSpT0P0001Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0001Bound x h'
  norm_num [SignedSpT0P0001Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P000L003 : ∀ x ∈ Icc ((((135 : ℚ) / 8192) : ℚ) : ℝ) ((((397 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0002Lo : ℝ) (ceSignedSpT0P0002Hi : ℝ) := by
    norm_num [ceSignedSpT0P0002Lo, ceSignedSpT0P0002Hi, SignedSpT0P0002Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0002Bound x h'
  norm_num [SignedSpT0P0002Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P000L004 : ∀ x ∈ Icc ((((397 : ℚ) / 16384) : ℚ) : ℝ) ((((131 : ℚ) / 4096) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0003Lo : ℝ) (ceSignedSpT0P0003Hi : ℝ) := by
    norm_num [ceSignedSpT0P0003Lo, ceSignedSpT0P0003Hi, SignedSpT0P0003Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0003Bound x h'
  norm_num [SignedSpT0P0003Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P000L005 : ∀ x ∈ Icc ((((131 : ℚ) / 4096) : ℚ) : ℝ) ((((651 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0004Lo : ℝ) (ceSignedSpT0P0004Hi : ℝ) := by
    norm_num [ceSignedSpT0P0004Lo, ceSignedSpT0P0004Hi, SignedSpT0P0004Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0004Bound x h'
  norm_num [SignedSpT0P0004Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P000L006 : ∀ x ∈ Icc ((((651 : ℚ) / 16384) : ℚ) : ℝ) ((((389 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0005Lo : ℝ) (ceSignedSpT0P0005Hi : ℝ) := by
    norm_num [ceSignedSpT0P0005Lo, ceSignedSpT0P0005Hi, SignedSpT0P0005Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0005Bound x h'
  norm_num [SignedSpT0P0005Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P000L007 : ∀ x ∈ Icc ((((389 : ℚ) / 8192) : ℚ) : ℝ) ((((905 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0006Lo : ℝ) (ceSignedSpT0P0006Hi : ℝ) := by
    norm_num [ceSignedSpT0P0006Lo, ceSignedSpT0P0006Hi, SignedSpT0P0006Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0006Bound x h'
  norm_num [SignedSpT0P0006Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P000L008 : ∀ x ∈ Icc ((((905 : ℚ) / 16384) : ℚ) : ℝ) ((((129 : ℚ) / 2048) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0007Lo : ℝ) (ceSignedSpT0P0007Hi : ℝ) := by
    norm_num [ceSignedSpT0P0007Lo, ceSignedSpT0P0007Hi, SignedSpT0P0007Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0007Bound x h'
  norm_num [SignedSpT0P0007Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P000L009 : ∀ x ∈ Icc ((((129 : ℚ) / 2048) : ℚ) : ℝ) ((((1159 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0008Lo : ℝ) (ceSignedSpT0P0008Hi : ℝ) := by
    norm_num [ceSignedSpT0P0008Lo, ceSignedSpT0P0008Hi, SignedSpT0P0008Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0008Bound x h'
  norm_num [SignedSpT0P0008Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P000L010 : ∀ x ∈ Icc ((((1159 : ℚ) / 16384) : ℚ) : ℝ) ((((643 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0009Lo : ℝ) (ceSignedSpT0P0009Hi : ℝ) := by
    norm_num [ceSignedSpT0P0009Lo, ceSignedSpT0P0009Hi, SignedSpT0P0009Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0009Bound x h'
  norm_num [SignedSpT0P0009Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P000L011 : ∀ x ∈ Icc ((((643 : ℚ) / 8192) : ℚ) : ℝ) ((((1413 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0010Lo : ℝ) (ceSignedSpT0P0010Hi : ℝ) := by
    norm_num [ceSignedSpT0P0010Lo, ceSignedSpT0P0010Hi, SignedSpT0P0010Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0010Bound x h'
  norm_num [SignedSpT0P0010Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P000L012 : ∀ x ∈ Icc ((((1413 : ℚ) / 16384) : ℚ) : ℝ) ((((385 : ℚ) / 4096) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0011Lo : ℝ) (ceSignedSpT0P0011Hi : ℝ) := by
    norm_num [ceSignedSpT0P0011Lo, ceSignedSpT0P0011Hi, SignedSpT0P0011Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0011Bound x h'
  norm_num [SignedSpT0P0011Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P000L013 : ∀ x ∈ Icc ((((385 : ℚ) / 4096) : ℚ) : ℝ) ((((1667 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0012Lo : ℝ) (ceSignedSpT0P0012Hi : ℝ) := by
    norm_num [ceSignedSpT0P0012Lo, ceSignedSpT0P0012Hi, SignedSpT0P0012Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0012Bound x h'
  norm_num [SignedSpT0P0012Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P000L014 : ∀ x ∈ Icc ((((1667 : ℚ) / 16384) : ℚ) : ℝ) ((((897 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0013Lo : ℝ) (ceSignedSpT0P0013Hi : ℝ) := by
    norm_num [ceSignedSpT0P0013Lo, ceSignedSpT0P0013Hi, SignedSpT0P0013Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0013Bound x h'
  norm_num [SignedSpT0P0013Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B0P000L015 : ∀ x ∈ Icc ((((897 : ℚ) / 8192) : ℚ) : ℝ) ((((3715 : ℚ) / 32768) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0014Lo : ℝ) (ceSignedSpT0P0014Hi : ℝ) := by
    norm_num [ceSignedSpT0P0014Lo, ceSignedSpT0P0014Hi, SignedSpT0P0014Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0014Bound x h'
  norm_num [SignedSpT0P0014Literal.q2] at h ⊢
  exact h

theorem SignedSpT0CoverD0B0P000 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((3715 : ℚ) / 32768) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT0CoverD0B0P000L000 SignedSpT0CoverD0B0P000L001) (cover_union SignedSpT0CoverD0B0P000L002 SignedSpT0CoverD0B0P000L003)) (cover_union (cover_union SignedSpT0CoverD0B0P000L004 SignedSpT0CoverD0B0P000L005) (cover_union SignedSpT0CoverD0B0P000L006 SignedSpT0CoverD0B0P000L007))) (cover_union (cover_union (cover_union SignedSpT0CoverD0B0P000L008 SignedSpT0CoverD0B0P000L009) (cover_union SignedSpT0CoverD0B0P000L010 SignedSpT0CoverD0B0P000L011)) (cover_union (cover_union SignedSpT0CoverD0B0P000L012 SignedSpT0CoverD0B0P000L013) (cover_union SignedSpT0CoverD0B0P000L014 SignedSpT0CoverD0B0P000L015))))
#print axioms SignedSpT0CoverD0B0P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
