module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0145
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0146
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0147
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0148
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0149
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0150
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1End00
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT1CoverD1B0P009L144 : ∀ x ∈ Icc ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((1180591620715263819777 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0145Lo : ℝ) (ceSignedSpmTopT1P0145Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0145Lo, ceSignedSpmTopT1P0145Hi, SignedSpmTopT1P0145Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0145Bound x h'
  norm_num [SignedSpmTopT1P0145Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P009L145 : ∀ x ∈ Icc ((((1180591620715263819777 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((4722366482862129020931 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0146Lo : ℝ) (ceSignedSpmTopT1P0146Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0146Lo, ceSignedSpmTopT1P0146Hi, SignedSpmTopT1P0146Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0146Bound x h'
  norm_num [SignedSpmTopT1P0146Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P009L146 : ∀ x ∈ Icc ((((4722366482862129020931 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((2361183241431601381377 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0147Lo : ℝ) (ceSignedSpmTopT1P0147Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0147Lo, ceSignedSpmTopT1P0147Hi, SignedSpmTopT1P0147Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0147Bound x h'
  norm_num [SignedSpmTopT1P0147Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P009L147 : ∀ x ∈ Icc ((((2361183241431601381377 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((4722366482864276504577 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0148Lo : ℝ) (ceSignedSpmTopT1P0148Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0148Lo, ceSignedSpmTopT1P0148Hi, SignedSpmTopT1P0148Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0148Bound x h'
  norm_num [SignedSpmTopT1P0148Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P009L148 : ∀ x ∈ Icc ((((4722366482864276504577 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((9444732965729626750977 : ℚ) / 9444732965739290427392) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0149Lo : ℝ) (ceSignedSpmTopT1P0149Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0149Lo, ceSignedSpmTopT1P0149Hi, SignedSpmTopT1P0149Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0149Bound x h'
  norm_num [SignedSpmTopT1P0149Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P009L149 : ∀ x ∈ Icc ((((9444732965729626750977 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) ((((1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0150Lo : ℝ) (ceSignedSpmTopT1P0150Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0150Lo, ceSignedSpmTopT1P0150Hi, SignedSpmTopT1P0150Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0150Bound x h'
  norm_num [SignedSpmTopT1P0150Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P009L150Field : fieldNFCheck ceSignedSpmTopT1End00FullFq ceSignedSpmTopT1Fq = true := by decide +kernel
private theorem SignedSpmTopT1CoverD1B0P009L150Terms : laurentNF ceSignedSpmTopT1End00FullTs = laurentNF ceSignedSpmTopT1Ts := by decide +kernel

private theorem SignedSpmTopT1CoverD1B0P009L150 : ∀ x ∈ Icc ((((1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1End00Lo : ℝ) (ceSignedSpmTopT1End00Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1End00Lo, ceSignedSpmTopT1End00Hi, SignedSpmTopT1End00Literal.q2, ceSignedSpmTopT1End00EndLiteral.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1End00Bound x h' (by norm_num [ceSignedSpmTopT1End00Site, ceSignedSpmTopT1End00EndLiteral.q2]; exact ne_of_lt hd.2)
  rw [fieldNFCheck_sound SignedSpmTopT1CoverD1B0P009L150Field x, ← laurentNF_sound ceSignedSpmTopT1End00FullTs x, SignedSpmTopT1CoverD1B0P009L150Terms, laurentNF_sound ceSignedSpmTopT1Ts x] at h
  norm_num [SignedSpmTopT1End00Literal.q2, ceSignedSpmTopT1End00EndLiteral.q2, ceSignedSpmTopT1End00Target] at h ⊢
  exact h

theorem SignedSpmTopT1CoverD1B0P009 : ∀ x ∈ Icc ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union SignedSpmTopT1CoverD1B0P009L144 (cover_union SignedSpmTopT1CoverD1B0P009L145 SignedSpmTopT1CoverD1B0P009L146)) (cover_union (cover_union SignedSpmTopT1CoverD1B0P009L147 SignedSpmTopT1CoverD1B0P009L148) (cover_union SignedSpmTopT1CoverD1B0P009L149 SignedSpmTopT1CoverD1B0P009L150)))
#print axioms SignedSpmTopT1CoverD1B0P009

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover
