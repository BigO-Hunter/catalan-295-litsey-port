module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0232
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0233
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0234
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0235
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0236
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0237
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0End01
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverD1B0P009L144 : ∀ x ∈ Icc ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((1180591620715263819777 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0232Lo : ℝ) (ceSignedSpT0P0232Hi : ℝ) := by
    norm_num [ceSignedSpT0P0232Lo, ceSignedSpT0P0232Hi, SignedSpT0P0232Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0232Bound x h'
  norm_num [SignedSpT0P0232Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P009L145 : ∀ x ∈ Icc ((((1180591620715263819777 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((4722366482862129020931 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0233Lo : ℝ) (ceSignedSpT0P0233Hi : ℝ) := by
    norm_num [ceSignedSpT0P0233Lo, ceSignedSpT0P0233Hi, SignedSpT0P0233Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0233Bound x h'
  norm_num [SignedSpT0P0233Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P009L146 : ∀ x ∈ Icc ((((4722366482862129020931 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((2361183241431601381377 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0234Lo : ℝ) (ceSignedSpT0P0234Hi : ℝ) := by
    norm_num [ceSignedSpT0P0234Lo, ceSignedSpT0P0234Hi, SignedSpT0P0234Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0234Bound x h'
  norm_num [SignedSpT0P0234Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P009L147 : ∀ x ∈ Icc ((((2361183241431601381377 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((4722366482864276504577 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0235Lo : ℝ) (ceSignedSpT0P0235Hi : ℝ) := by
    norm_num [ceSignedSpT0P0235Lo, ceSignedSpT0P0235Hi, SignedSpT0P0235Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0235Bound x h'
  norm_num [SignedSpT0P0235Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P009L148 : ∀ x ∈ Icc ((((4722366482864276504577 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((9444732965729626750977 : ℚ) / 9444732965739290427392) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0236Lo : ℝ) (ceSignedSpT0P0236Hi : ℝ) := by
    norm_num [ceSignedSpT0P0236Lo, ceSignedSpT0P0236Hi, SignedSpT0P0236Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0236Bound x h'
  norm_num [SignedSpT0P0236Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P009L149 : ∀ x ∈ Icc ((((9444732965729626750977 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) ((((1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0237Lo : ℝ) (ceSignedSpT0P0237Hi : ℝ) := by
    norm_num [ceSignedSpT0P0237Lo, ceSignedSpT0P0237Hi, SignedSpT0P0237Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0237Bound x h'
  norm_num [SignedSpT0P0237Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P009L150Field : fieldNFCheck ceSignedSpT0End01FullFq ceSignedSpT0Fq = true := by decide +kernel
private theorem SignedSpT0CoverD1B0P009L150Terms : laurentNF ceSignedSpT0End01FullTs = laurentNF ceSignedSpT0Ts := by decide +kernel

private theorem SignedSpT0CoverD1B0P009L150 : ∀ x ∈ Icc ((((1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0End01Lo : ℝ) (ceSignedSpT0End01Hi : ℝ) := by
    norm_num [ceSignedSpT0End01Lo, ceSignedSpT0End01Hi, SignedSpT0End01Literal.q2, ceSignedSpT0End01EndLiteral.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0End01Bound x h' (by norm_num [ceSignedSpT0End01Site, ceSignedSpT0End01EndLiteral.q2]; exact ne_of_lt hd.2)
  rw [fieldNFCheck_sound SignedSpT0CoverD1B0P009L150Field x, ← laurentNF_sound ceSignedSpT0End01FullTs x, SignedSpT0CoverD1B0P009L150Terms, laurentNF_sound ceSignedSpT0Ts x] at h
  norm_num [SignedSpT0End01Literal.q2, ceSignedSpT0End01EndLiteral.q2, ceSignedSpT0End01Target] at h ⊢
  exact h

theorem SignedSpT0CoverD1B0P009 : ∀ x ∈ Icc ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union SignedSpT0CoverD1B0P009L144 (cover_union SignedSpT0CoverD1B0P009L145 SignedSpT0CoverD1B0P009L146)) (cover_union (cover_union SignedSpT0CoverD1B0P009L147 SignedSpT0CoverD1B0P009L148) (cover_union SignedSpT0CoverD1B0P009L149 SignedSpT0CoverD1B0P009L150)))
#print axioms SignedSpT0CoverD1B0P009

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
