module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core047
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core048
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core049
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core050
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core051
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core052
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core053
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core054
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core055
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core056
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core057
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core058
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core059
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core060
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core061
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core062
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell048 : ∀ y ∈ Icc ((((-9954660450295 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((-18810883014639 : ℚ) / 140737488355328) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P047Lo : ℝ) (ceSignedSnEntryT0P047Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P047Lo, ceSignedSnEntryT0P047Hi, SignedSnEntryT0Core047Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P047Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core047Literal.q2] at h ⊢
  exact h

private theorem cell049 : ∀ y ∈ Icc ((((-18810883014639 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((-71948218400703 : ℚ) / 562949953421312) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P048Lo : ℝ) (ceSignedSnEntryT0P048Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P048Lo, ceSignedSnEntryT0P048Hi, SignedSnEntryT0Core048Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P048Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core048Literal.q2] at h ⊢
  exact h

private theorem cell050 : ∀ y ∈ Icc ((((-71948218400703 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((-69751342628801 : ℚ) / 562949953421312) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P049Lo : ℝ) (ceSignedSnEntryT0P049Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P049Lo, ceSignedSnEntryT0P049Hi, SignedSnEntryT0Core049Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P049Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core049Literal.q2] at h ⊢
  exact h

private theorem cell051 : ∀ y ∈ Icc ((((-69751342628801 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((-34326452371425 : ℚ) / 281474976710656) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P050Lo : ℝ) (ceSignedSnEntryT0P050Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P050Lo, ceSignedSnEntryT0P050Hi, SignedSnEntryT0Core050Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P050Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core050Literal.q2] at h ⊢
  exact h

private theorem cell052 : ∀ y ∈ Icc ((((-34326452371425 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((-16614007242737 : ℚ) / 140737488355328) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P051Lo : ℝ) (ceSignedSnEntryT0P051Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P051Lo, ceSignedSnEntryT0P051Hi, SignedSnEntryT0Core051Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P051Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core051Literal.q2] at h ⊢
  exact h

private theorem cell053 : ∀ y ∈ Icc ((((-16614007242737 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((-7757784678393 : ℚ) / 70368744177664) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P052Lo : ℝ) (ceSignedSnEntryT0P052Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P052Lo, ceSignedSnEntryT0P052Hi, SignedSnEntryT0Core052Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P052Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core052Literal.q2] at h ⊢
  exact h

private theorem cell054 : ∀ y ∈ Icc ((((-7757784678393 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((-14417131470835 : ℚ) / 140737488355328) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P053Lo : ℝ) (ceSignedSnEntryT0P053Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P053Lo, ceSignedSnEntryT0P053Hi, SignedSnEntryT0Core053Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P053Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core053Literal.q2] at h ⊢
  exact h

private theorem cell055 : ∀ y ∈ Icc ((((-14417131470835 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((-3329673396221 : ℚ) / 35184372088832) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P054Lo : ℝ) (ceSignedSnEntryT0P054Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P054Lo, ceSignedSnEntryT0P054Hi, SignedSnEntryT0Core054Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P054Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core054Literal.q2] at h ⊢
  exact h

private theorem cell056 : ∀ y ∈ Icc ((((-3329673396221 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((-12220255698933 : ℚ) / 140737488355328) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P055Lo : ℝ) (ceSignedSnEntryT0P055Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P055Lo, ceSignedSnEntryT0P055Hi, SignedSnEntryT0Core055Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P055Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core055Literal.q2] at h ⊢
  exact h

private theorem cell057 : ∀ y ∈ Icc ((((-12220255698933 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((-5560908906491 : ℚ) / 70368744177664) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P056Lo : ℝ) (ceSignedSnEntryT0P056Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P056Lo, ceSignedSnEntryT0P056Hi, SignedSnEntryT0Core056Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P056Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core056Literal.q2] at h ⊢
  exact h

private theorem cell058 : ∀ y ∈ Icc ((((-5560908906491 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((-10023379927031 : ℚ) / 140737488355328) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P057Lo : ℝ) (ceSignedSnEntryT0P057Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P057Lo, ceSignedSnEntryT0P057Hi, SignedSnEntryT0Core057Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P057Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core057Literal.q2] at h ⊢
  exact h

private theorem cell059 : ∀ y ∈ Icc ((((-10023379927031 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((-1115617755135 : ℚ) / 17592186044416) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P058Lo : ℝ) (ceSignedSnEntryT0P058Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P058Lo, ceSignedSnEntryT0P058Hi, SignedSnEntryT0Core058Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P058Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core058Literal.q2] at h ⊢
  exact h

private theorem cell060 : ∀ y ∈ Icc ((((-1115617755135 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((-7826504155129 : ℚ) / 140737488355328) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P059Lo : ℝ) (ceSignedSnEntryT0P059Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P059Lo, ceSignedSnEntryT0P059Hi, SignedSnEntryT0Core059Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P059Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core059Literal.q2] at h ⊢
  exact h

private theorem cell061 : ∀ y ∈ Icc ((((-7826504155129 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((-3364033134589 : ℚ) / 70368744177664) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P060Lo : ℝ) (ceSignedSnEntryT0P060Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P060Lo, ceSignedSnEntryT0P060Hi, SignedSnEntryT0Core060Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P060Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core060Literal.q2] at h ⊢
  exact h

private theorem cell062 : ∀ y ∈ Icc ((((-3364033134589 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((-5629628383227 : ℚ) / 140737488355328) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P061Lo : ℝ) (ceSignedSnEntryT0P061Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P061Lo, ceSignedSnEntryT0P061Hi, SignedSnEntryT0Core061Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P061Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core061Literal.q2] at h ⊢
  exact h

private theorem cell063 : ∀ y ∈ Icc ((((-5629628383227 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((-1132797624319 : ℚ) / 35184372088832) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P062Lo : ℝ) (ceSignedSnEntryT0P062Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P062Lo, ceSignedSnEntryT0P062Hi, SignedSnEntryT0Core062Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P062Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core062Literal.q2] at h ⊢
  exact h

theorem cover003 : ∀ y ∈ Icc ((((-9954660450295 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((-1132797624319 : ℚ) / 35184372088832) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell048 cell049) (cover_union cell050 cell051)) (cover_union (cover_union cell052 cell053) (cover_union cell054 cell055))) (cover_union (cover_union (cover_union cell056 cell057) (cover_union cell058 cell059)) (cover_union (cover_union cell060 cell061) (cover_union cell062 cell063))))
#print axioms cover003
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover
