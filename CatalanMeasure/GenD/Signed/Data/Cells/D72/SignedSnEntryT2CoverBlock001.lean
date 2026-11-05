module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core015
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core023
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core030
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell016 : ∀ y ∈ Icc ((((-1407353539195035747 : ℚ) / 1407374883553280000) : ℚ) : ℝ) ((((-703666097419035747 : ℚ) / 703687441776640000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P015Lo : ℝ) (ceSignedSnEntryT2P015Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P015Lo, ceSignedSnEntryT2P015Hi, SignedSnEntryT2Core015Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P015Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core015Literal.q2] at h ⊢
  exact h

private theorem cell017 : ∀ y ∈ Icc ((((-703666097419035747 : ℚ) / 703687441776640000) : ℚ) : ℝ) ((((-351822376531035747 : ℚ) / 351843720888320000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P016Lo : ℝ) (ceSignedSnEntryT2P016Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P016Lo, ceSignedSnEntryT2P016Hi, SignedSnEntryT2Core016Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P016Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core016Literal.q2] at h ⊢
  exact h

private theorem cell018 : ∀ y ∈ Icc ((((-351822376531035747 : ℚ) / 351843720888320000) : ℚ) : ℝ) ((((-175900516087035747 : ℚ) / 175921860444160000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P017Lo : ℝ) (ceSignedSnEntryT2P017Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P017Lo, ceSignedSnEntryT2P017Hi, SignedSnEntryT2Core017Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P017Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core017Literal.q2] at h ⊢
  exact h

private theorem cell019 : ∀ y ∈ Icc ((((-175900516087035747 : ℚ) / 175921860444160000) : ℚ) : ℝ) ((((-87939585865035747 : ℚ) / 87960930222080000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P018Lo : ℝ) (ceSignedSnEntryT2P018Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P018Lo, ceSignedSnEntryT2P018Hi, SignedSnEntryT2Core018Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P018Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core018Literal.q2] at h ⊢
  exact h

private theorem cell020 : ∀ y ∈ Icc ((((-87939585865035747 : ℚ) / 87960930222080000) : ℚ) : ℝ) ((((-175857827373107241 : ℚ) / 175921860444160000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P019Lo : ℝ) (ceSignedSnEntryT2P019Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P019Lo, ceSignedSnEntryT2P019Hi, SignedSnEntryT2Core019Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P019Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core019Literal.q2] at h ⊢
  exact h

private theorem cell021 : ∀ y ∈ Icc ((((-175857827373107241 : ℚ) / 175921860444160000) : ℚ) : ℝ) ((((-43959120754035747 : ℚ) / 43980465111040000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P020Lo : ℝ) (ceSignedSnEntryT2P020Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P020Lo, ceSignedSnEntryT2P020Hi, SignedSnEntryT2Core020Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P020Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core020Literal.q2] at h ⊢
  exact h

private theorem cell022 : ∀ y ∈ Icc ((((-43959120754035747 : ℚ) / 43980465111040000) : ℚ) : ℝ) ((((-87896897151107241 : ℚ) / 87960930222080000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P021Lo : ℝ) (ceSignedSnEntryT2P021Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P021Lo, ceSignedSnEntryT2P021Hi, SignedSnEntryT2Core021Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P021Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core021Literal.q2] at h ⊢
  exact h

private theorem cell023 : ∀ y ∈ Icc ((((-87896897151107241 : ℚ) / 87960930222080000) : ℚ) : ℝ) ((((-21968888198535747 : ℚ) / 21990232555520000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P022Lo : ℝ) (ceSignedSnEntryT2P022Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P022Lo, ceSignedSnEntryT2P022Hi, SignedSnEntryT2Core022Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P022Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core022Literal.q2] at h ⊢
  exact h

private theorem cell024 : ∀ y ∈ Icc ((((-21968888198535747 : ℚ) / 21990232555520000) : ℚ) : ℝ) ((((-43916432040107241 : ℚ) / 43980465111040000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P023Lo : ℝ) (ceSignedSnEntryT2P023Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P023Lo, ceSignedSnEntryT2P023Hi, SignedSnEntryT2Core023Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P023Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core023Literal.q2] at h ⊢
  exact h

private theorem cell025 : ∀ y ∈ Icc ((((-43916432040107241 : ℚ) / 43980465111040000) : ℚ) : ℝ) ((((-21926199484607241 : ℚ) / 21990232555520000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P024Lo : ℝ) (ceSignedSnEntryT2P024Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P024Lo, ceSignedSnEntryT2P024Hi, SignedSnEntryT2Core024Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P024Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core024Literal.q2] at h ⊢
  exact h

private theorem cell026 : ∀ y ∈ Icc ((((-21926199484607241 : ℚ) / 21990232555520000) : ℚ) : ℝ) ((((-43831054612250229 : ℚ) / 43980465111040000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P025Lo : ℝ) (ceSignedSnEntryT2P025Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P025Lo, ceSignedSnEntryT2P025Hi, SignedSnEntryT2Core025Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P025Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core025Literal.q2] at h ⊢
  exact h

private theorem cell027 : ∀ y ∈ Icc ((((-43831054612250229 : ℚ) / 43980465111040000) : ℚ) : ℝ) ((((-4376702154135747 : ℚ) / 4398046511104000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P026Lo : ℝ) (ceSignedSnEntryT2P026Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P026Lo, ceSignedSnEntryT2P026Hi, SignedSnEntryT2Core026Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P026Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core026Literal.q2] at h ⊢
  exact h

private theorem cell028 : ∀ y ∈ Icc ((((-4376702154135747 : ℚ) / 4398046511104000) : ℚ) : ℝ) ((((-2727434712473247 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P027Lo : ℝ) (ceSignedSnEntryT2P027Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P027Lo, ceSignedSnEntryT2P027Hi, SignedSnEntryT2Core027Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P027Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core027Literal.q2] at h ⊢
  exact h

private theorem cell029 : ∀ y ∈ Icc ((((-2727434712473247 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-5433525067982241 : ℚ) / 5497558138880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P028Lo : ℝ) (ceSignedSnEntryT2P028Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P028Lo, ceSignedSnEntryT2P028Hi, SignedSnEntryT2Core028Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P028Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core028Literal.q2] at h ⊢
  exact h

private theorem cell030 : ∀ y ∈ Icc ((((-5433525067982241 : ℚ) / 5497558138880000) : ℚ) : ℝ) ((((-2684745998544741 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P029Lo : ℝ) (ceSignedSnEntryT2P029Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P029Lo, ceSignedSnEntryT2P029Hi, SignedSnEntryT2Core029Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P029Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core029Literal.q2] at h ⊢
  exact h

private theorem cell031 : ∀ y ∈ Icc ((((-2684745998544741 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-5348147640125229 : ℚ) / 5497558138880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P030Lo : ℝ) (ceSignedSnEntryT2P030Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P030Lo, ceSignedSnEntryT2P030Hi, SignedSnEntryT2Core030Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P030Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core030Literal.q2] at h ⊢
  exact h

theorem cover001 : ∀ y ∈ Icc ((((-1407353539195035747 : ℚ) / 1407374883553280000) : ℚ) : ℝ) ((((-5348147640125229 : ℚ) / 5497558138880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell016 cell017) (cover_union cell018 cell019)) (cover_union (cover_union cell020 cell021) (cover_union cell022 cell023))) (cover_union (cover_union (cover_union cell024 cell025) (cover_union cell026 cell027)) (cover_union (cover_union cell028 cell029) (cover_union cell030 cell031))))
#print axioms cover001
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
