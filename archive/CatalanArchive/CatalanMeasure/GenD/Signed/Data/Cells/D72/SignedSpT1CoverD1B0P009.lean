module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0232
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0233
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0234
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0235
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0236
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0237
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1End01
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT1CoverD1B0P009L144 : ∀ x ∈ Icc ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((1180591620715263819777 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0232Lo : ℝ) (ceSignedSpT1P0232Hi : ℝ) := by
    norm_num [ceSignedSpT1P0232Lo, ceSignedSpT1P0232Hi, SignedSpT1P0232Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0232Bound x h'
  norm_num [SignedSpT1P0232Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P009L145 : ∀ x ∈ Icc ((((1180591620715263819777 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((4722366482862129020931 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0233Lo : ℝ) (ceSignedSpT1P0233Hi : ℝ) := by
    norm_num [ceSignedSpT1P0233Lo, ceSignedSpT1P0233Hi, SignedSpT1P0233Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0233Bound x h'
  norm_num [SignedSpT1P0233Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P009L146 : ∀ x ∈ Icc ((((4722366482862129020931 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((2361183241431601381377 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0234Lo : ℝ) (ceSignedSpT1P0234Hi : ℝ) := by
    norm_num [ceSignedSpT1P0234Lo, ceSignedSpT1P0234Hi, SignedSpT1P0234Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0234Bound x h'
  norm_num [SignedSpT1P0234Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P009L147 : ∀ x ∈ Icc ((((2361183241431601381377 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((4722366482864276504577 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0235Lo : ℝ) (ceSignedSpT1P0235Hi : ℝ) := by
    norm_num [ceSignedSpT1P0235Lo, ceSignedSpT1P0235Hi, SignedSpT1P0235Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0235Bound x h'
  norm_num [SignedSpT1P0235Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P009L148 : ∀ x ∈ Icc ((((4722366482864276504577 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((9444732965729626750977 : ℚ) / 9444732965739290427392) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0236Lo : ℝ) (ceSignedSpT1P0236Hi : ℝ) := by
    norm_num [ceSignedSpT1P0236Lo, ceSignedSpT1P0236Hi, SignedSpT1P0236Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0236Bound x h'
  norm_num [SignedSpT1P0236Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P009L149 : ∀ x ∈ Icc ((((9444732965729626750977 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) ((((1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0237Lo : ℝ) (ceSignedSpT1P0237Hi : ℝ) := by
    norm_num [ceSignedSpT1P0237Lo, ceSignedSpT1P0237Hi, SignedSpT1P0237Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0237Bound x h'
  norm_num [SignedSpT1P0237Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P009L150Field : fieldNFCheck ceSignedSpT1End01FullFq ceSignedSpT1Fq = true := by decide +kernel
private theorem SignedSpT1CoverD1B0P009L150Terms : laurentNF ceSignedSpT1End01FullTs = laurentNF ceSignedSpT1Ts := by decide +kernel

private theorem SignedSpT1CoverD1B0P009L150 : ∀ x ∈ Icc ((((1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1End01Lo : ℝ) (ceSignedSpT1End01Hi : ℝ) := by
    norm_num [ceSignedSpT1End01Lo, ceSignedSpT1End01Hi, SignedSpT1End01Literal.q2, ceSignedSpT1End01EndLiteral.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1End01Bound x h' (by norm_num [ceSignedSpT1End01Site, ceSignedSpT1End01EndLiteral.q2]; exact ne_of_lt hd.2)
  rw [fieldNFCheck_sound SignedSpT1CoverD1B0P009L150Field x, ← laurentNF_sound ceSignedSpT1End01FullTs x, SignedSpT1CoverD1B0P009L150Terms, laurentNF_sound ceSignedSpT1Ts x] at h
  norm_num [SignedSpT1End01Literal.q2, ceSignedSpT1End01EndLiteral.q2, ceSignedSpT1End01Target] at h ⊢
  exact h

theorem SignedSpT1CoverD1B0P009 : ∀ x ∈ Icc ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union SignedSpT1CoverD1B0P009L144 (cover_union SignedSpT1CoverD1B0P009L145 SignedSpT1CoverD1B0P009L146)) (cover_union (cover_union SignedSpT1CoverD1B0P009L147 SignedSpT1CoverD1B0P009L148) (cover_union SignedSpT1CoverD1B0P009L149 SignedSpT1CoverD1B0P009L150)))
#print axioms SignedSpT1CoverD1B0P009

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
