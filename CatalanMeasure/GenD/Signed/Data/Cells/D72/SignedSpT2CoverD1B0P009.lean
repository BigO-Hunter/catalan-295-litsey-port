module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0234
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0235
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0236
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0237
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0238
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0239
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2End01
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT2CoverD1B0P009L144 : ∀ x ∈ Icc ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((1180591620715263819777 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0234Lo : ℝ) (ceSignedSpT2P0234Hi : ℝ) := by
    norm_num [ceSignedSpT2P0234Lo, ceSignedSpT2P0234Hi, SignedSpT2P0234Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0234Bound x h'
  norm_num [SignedSpT2P0234Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P009L145 : ∀ x ∈ Icc ((((1180591620715263819777 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((4722366482862129020931 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0235Lo : ℝ) (ceSignedSpT2P0235Hi : ℝ) := by
    norm_num [ceSignedSpT2P0235Lo, ceSignedSpT2P0235Hi, SignedSpT2P0235Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0235Bound x h'
  norm_num [SignedSpT2P0235Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P009L146 : ∀ x ∈ Icc ((((4722366482862129020931 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((2361183241431601381377 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0236Lo : ℝ) (ceSignedSpT2P0236Hi : ℝ) := by
    norm_num [ceSignedSpT2P0236Lo, ceSignedSpT2P0236Hi, SignedSpT2P0236Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0236Bound x h'
  norm_num [SignedSpT2P0236Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P009L147 : ∀ x ∈ Icc ((((2361183241431601381377 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((4722366482864276504577 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0237Lo : ℝ) (ceSignedSpT2P0237Hi : ℝ) := by
    norm_num [ceSignedSpT2P0237Lo, ceSignedSpT2P0237Hi, SignedSpT2P0237Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0237Bound x h'
  norm_num [SignedSpT2P0237Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P009L148 : ∀ x ∈ Icc ((((4722366482864276504577 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((9444732965729626750977 : ℚ) / 9444732965739290427392) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0238Lo : ℝ) (ceSignedSpT2P0238Hi : ℝ) := by
    norm_num [ceSignedSpT2P0238Lo, ceSignedSpT2P0238Hi, SignedSpT2P0238Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0238Bound x h'
  norm_num [SignedSpT2P0238Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P009L149 : ∀ x ∈ Icc ((((9444732965729626750977 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) ((((1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0239Lo : ℝ) (ceSignedSpT2P0239Hi : ℝ) := by
    norm_num [ceSignedSpT2P0239Lo, ceSignedSpT2P0239Hi, SignedSpT2P0239Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0239Bound x h'
  norm_num [SignedSpT2P0239Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P009L150Field : fieldNFCheck ceSignedSpT2End01FullFq ceSignedSpT2Fq = true := by decide +kernel
private theorem SignedSpT2CoverD1B0P009L150Terms : laurentNF ceSignedSpT2End01FullTs = laurentNF ceSignedSpT2Ts := by decide +kernel

private theorem SignedSpT2CoverD1B0P009L150 : ∀ x ∈ Icc ((((1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2End01Lo : ℝ) (ceSignedSpT2End01Hi : ℝ) := by
    norm_num [ceSignedSpT2End01Lo, ceSignedSpT2End01Hi, SignedSpT2End01Literal.q2, ceSignedSpT2End01EndLiteral.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2End01Bound x h' (by norm_num [ceSignedSpT2End01Site, ceSignedSpT2End01EndLiteral.q2]; exact ne_of_lt hd.2)
  rw [fieldNFCheck_sound SignedSpT2CoverD1B0P009L150Field x, ← laurentNF_sound ceSignedSpT2End01FullTs x, SignedSpT2CoverD1B0P009L150Terms, laurentNF_sound ceSignedSpT2Ts x] at h
  norm_num [SignedSpT2End01Literal.q2, ceSignedSpT2End01EndLiteral.q2, ceSignedSpT2End01Target] at h ⊢
  exact h

theorem SignedSpT2CoverD1B0P009 : ∀ x ∈ Icc ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union SignedSpT2CoverD1B0P009L144 (cover_union SignedSpT2CoverD1B0P009L145 SignedSpT2CoverD1B0P009L146)) (cover_union (cover_union SignedSpT2CoverD1B0P009L147 SignedSpT2CoverD1B0P009L148) (cover_union SignedSpT2CoverD1B0P009L149 SignedSpT2CoverD1B0P009L150)))
#print axioms SignedSpT2CoverD1B0P009

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
