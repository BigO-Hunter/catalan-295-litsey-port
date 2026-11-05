module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0145
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0146
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0147
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0148
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0149
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0150
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0End00
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT0CoverD1B0P009L144 : ∀ x ∈ Icc ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((1180591620715263819777 : ℚ) / 1180591620717411303424) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0145Lo : ℝ) (ceSignedSpmTopT0P0145Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0145Lo, ceSignedSpmTopT0P0145Hi, SignedSpmTopT0P0145Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0145Bound x h'
  norm_num [SignedSpmTopT0P0145Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P009L145 : ∀ x ∈ Icc ((((1180591620715263819777 : ℚ) / 1180591620717411303424) : ℚ) : ℝ) ((((4722366482862129020931 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0146Lo : ℝ) (ceSignedSpmTopT0P0146Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0146Lo, ceSignedSpmTopT0P0146Hi, SignedSpmTopT0P0146Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0146Bound x h'
  norm_num [SignedSpmTopT0P0146Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P009L146 : ∀ x ∈ Icc ((((4722366482862129020931 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((2361183241431601381377 : ℚ) / 2361183241434822606848) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0147Lo : ℝ) (ceSignedSpmTopT0P0147Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0147Lo, ceSignedSpmTopT0P0147Hi, SignedSpmTopT0P0147Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0147Bound x h'
  norm_num [SignedSpmTopT0P0147Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P009L147 : ∀ x ∈ Icc ((((2361183241431601381377 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) ((((4722366482864276504577 : ℚ) / 4722366482869645213696) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0148Lo : ℝ) (ceSignedSpmTopT0P0148Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0148Lo, ceSignedSpmTopT0P0148Hi, SignedSpmTopT0P0148Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0148Bound x h'
  norm_num [SignedSpmTopT0P0148Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P009L148 : ∀ x ∈ Icc ((((4722366482864276504577 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((9444732965729626750977 : ℚ) / 9444732965739290427392) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0149Lo : ℝ) (ceSignedSpmTopT0P0149Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0149Lo, ceSignedSpmTopT0P0149Hi, SignedSpmTopT0P0149Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0149Bound x h'
  norm_num [SignedSpmTopT0P0149Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P009L149 : ∀ x ∈ Icc ((((9444732965729626750977 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) ((((1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0150Lo : ℝ) (ceSignedSpmTopT0P0150Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0150Lo, ceSignedSpmTopT0P0150Hi, SignedSpmTopT0P0150Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0150Bound x h'
  norm_num [SignedSpmTopT0P0150Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P009L150Field : fieldNFCheck ceSignedSpmTopT0End00FullFq ceSignedSpmTopT0Fq = true := by decide +kernel
private theorem SignedSpmTopT0CoverD1B0P009L150Terms : laurentNF ceSignedSpmTopT0End00FullTs = laurentNF ceSignedSpmTopT0Ts := by decide +kernel

private theorem SignedSpmTopT0CoverD1B0P009L150 : ∀ x ∈ Icc ((((1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0End00Lo : ℝ) (ceSignedSpmTopT0End00Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0End00Lo, ceSignedSpmTopT0End00Hi, SignedSpmTopT0End00Literal.q2, ceSignedSpmTopT0End00EndLiteral.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0End00Bound x h' (by norm_num [ceSignedSpmTopT0End00Site, ceSignedSpmTopT0End00EndLiteral.q2]; exact ne_of_lt hd.2)
  rw [fieldNFCheck_sound SignedSpmTopT0CoverD1B0P009L150Field x, ← laurentNF_sound ceSignedSpmTopT0End00FullTs x, SignedSpmTopT0CoverD1B0P009L150Terms, laurentNF_sound ceSignedSpmTopT0Ts x] at h
  norm_num [SignedSpmTopT0End00Literal.q2, ceSignedSpmTopT0End00EndLiteral.q2, ceSignedSpmTopT0End00Target] at h ⊢
  exact h

theorem SignedSpmTopT0CoverD1B0P009 : ∀ x ∈ Icc ((((4722366482859981537285 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union SignedSpmTopT0CoverD1B0P009L144 (cover_union SignedSpmTopT0CoverD1B0P009L145 SignedSpmTopT0CoverD1B0P009L146)) (cover_union (cover_union SignedSpmTopT0CoverD1B0P009L147 SignedSpmTopT0CoverD1B0P009L148) (cover_union SignedSpmTopT0CoverD1B0P009L149 SignedSpmTopT0CoverD1B0P009L150)))
#print axioms SignedSpmTopT0CoverD1B0P009

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover
