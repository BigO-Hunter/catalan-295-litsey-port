module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core015
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core023
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core030
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell016 : ∀ y ∈ Icc ((((-75997666826967405169 : ℚ) / 75998243711877120000) : ℚ) : ℝ) ((((-37998544971063405169 : ℚ) / 37999121855938560000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P015Lo : ℝ) (ceSignedSnEntryT1P015Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P015Lo, ceSignedSnEntryT1P015Hi, SignedSnEntryT1Core015Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P015Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core015Literal.q2] at h ⊢
  exact h

private theorem cell017 : ∀ y ∈ Icc ((((-37998544971063405169 : ℚ) / 37999121855938560000) : ℚ) : ℝ) ((((-18998984043111405169 : ℚ) / 18999560927969280000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P016Lo : ℝ) (ceSignedSnEntryT1P016Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P016Lo, ceSignedSnEntryT1P016Hi, SignedSnEntryT1Core016Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P016Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core016Literal.q2] at h ⊢
  exact h

private theorem cell018 : ∀ y ∈ Icc ((((-18998984043111405169 : ℚ) / 18999560927969280000) : ℚ) : ℝ) ((((-9499203579135405169 : ℚ) / 9499780463984640000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P017Lo : ℝ) (ceSignedSnEntryT1P017Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P017Lo, ceSignedSnEntryT1P017Hi, SignedSnEntryT1Core017Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P017Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core017Literal.q2] at h ⊢
  exact h

private theorem cell019 : ∀ y ∈ Icc ((((-9499203579135405169 : ℚ) / 9499780463984640000) : ℚ) : ℝ) ((((-4749313347147405169 : ℚ) / 4749890231992320000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P018Lo : ℝ) (ceSignedSnEntryT1P018Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P018Lo, ceSignedSnEntryT1P018Hi, SignedSnEntryT1Core018Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P018Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core018Literal.q2] at h ⊢
  exact h

private theorem cell020 : ∀ y ∈ Icc ((((-4749313347147405169 : ℚ) / 4749890231992320000) : ℚ) : ℝ) ((((-2374368231153405169 : ℚ) / 2374945115996160000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P019Lo : ℝ) (ceSignedSnEntryT1P019Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P019Lo, ceSignedSnEntryT1P019Hi, SignedSnEntryT1Core019Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P019Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core019Literal.q2] at h ⊢
  exact h

private theorem cell021 : ∀ y ∈ Icc ((((-2374368231153405169 : ℚ) / 2374945115996160000) : ℚ) : ℝ) ((((-1899379207954605169 : ℚ) / 1899956092796928000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P020Lo : ℝ) (ceSignedSnEntryT1P020Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P020Lo, ceSignedSnEntryT1P020Hi, SignedSnEntryT1Core020Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P020Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core020Literal.q2] at h ⊢
  exact h

private theorem cell022 : ∀ y ∈ Icc ((((-1899379207954605169 : ℚ) / 1899956092796928000) : ℚ) : ℝ) ((((-1582719859155405169 : ℚ) / 1583296743997440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P021Lo : ℝ) (ceSignedSnEntryT1P021Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P021Lo, ceSignedSnEntryT1P021Hi, SignedSnEntryT1Core021Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P021Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core021Literal.q2] at h ⊢
  exact h

private theorem cell023 : ∀ y ∈ Icc ((((-1582719859155405169 : ℚ) / 1583296743997440000) : ℚ) : ℝ) ((((-9495742270091836183 : ℚ) / 9499780463984640000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P022Lo : ℝ) (ceSignedSnEntryT1P022Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P022Lo, ceSignedSnEntryT1P022Hi, SignedSnEntryT1Core022Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P022Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core022Literal.q2] at h ⊢
  exact h

private theorem cell024 : ∀ y ∈ Icc ((((-9495742270091836183 : ℚ) / 9499780463984640000) : ℚ) : ℝ) ((((-1186895673156405169 : ℚ) / 1187472557998080000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P023Lo : ℝ) (ceSignedSnEntryT1P023Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P023Lo, ceSignedSnEntryT1P023Hi, SignedSnEntryT1Core023Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P023Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core023Literal.q2] at h ⊢
  exact h

private theorem cell025 : ∀ y ∈ Icc ((((-1186895673156405169 : ℚ) / 1187472557998080000) : ℚ) : ℝ) ((((-593159394157905169 : ℚ) / 593736278999040000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P024Lo : ℝ) (ceSignedSnEntryT1P024Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P024Lo, ceSignedSnEntryT1P024Hi, SignedSnEntryT1Core024Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P024Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core024Literal.q2] at h ⊢
  exact h

private theorem cell026 : ∀ y ∈ Icc ((((-593159394157905169 : ℚ) / 593736278999040000) : ℚ) : ℝ) ((((-395247301158405169 : ℚ) / 395824185999360000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P025Lo : ℝ) (ceSignedSnEntryT1P025Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P025Lo, ceSignedSnEntryT1P025Hi, SignedSnEntryT1Core025Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P025Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core025Literal.q2] at h ⊢
  exact h

private theorem cell027 : ∀ y ∈ Icc ((((-395247301158405169 : ℚ) / 395824185999360000) : ℚ) : ℝ) ((((-147857184909030169 : ℚ) / 148434069749760000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P026Lo : ℝ) (ceSignedSnEntryT1P026Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P026Lo, ceSignedSnEntryT1P026Hi, SignedSnEntryT1Core026Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P026Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core026Literal.q2] at h ⊢
  exact h

private theorem cell028 : ∀ y ∈ Icc ((((-147857184909030169 : ℚ) / 148434069749760000) : ℚ) : ℝ) ((((-73640150034217669 : ℚ) / 74217034874880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P027Lo : ℝ) (ceSignedSnEntryT1P027Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P027Lo, ceSignedSnEntryT1P027Hi, SignedSnEntryT1Core027Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P027Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core027Literal.q2] at h ⊢
  exact h

private theorem cell029 : ∀ y ∈ Icc ((((-73640150034217669 : ℚ) / 74217034874880000) : ℚ) : ℝ) ((((-36531632596811419 : ℚ) / 37108517437440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P028Lo : ℝ) (ceSignedSnEntryT1P028Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P028Lo, ceSignedSnEntryT1P028Hi, SignedSnEntryT1Core028Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P028Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core028Literal.q2] at h ⊢
  exact h

private theorem cell030 : ∀ y ∈ Icc ((((-36531632596811419 : ℚ) / 37108517437440000) : ℚ) : ℝ) ((((-8988686939054147 : ℚ) / 9277129359360000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P029Lo : ℝ) (ceSignedSnEntryT1P029Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P029Lo, ceSignedSnEntryT1P029Hi, SignedSnEntryT1Core029Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P029Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core029Literal.q2] at h ⊢
  exact h

private theorem cell031 : ∀ y ∈ Icc ((((-8988686939054147 : ℚ) / 9277129359360000) : ℚ) : ℝ) ((((-17400489037513463 : ℚ) / 18554258718720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P030Lo : ℝ) (ceSignedSnEntryT1P030Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P030Lo, ceSignedSnEntryT1P030Hi, SignedSnEntryT1Core030Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P030Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core030Literal.q2] at h ⊢
  exact h

theorem cover001 : ∀ y ∈ Icc ((((-75997666826967405169 : ℚ) / 75998243711877120000) : ℚ) : ℝ) ((((-17400489037513463 : ℚ) / 18554258718720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell016 cell017) (cover_union cell018 cell019)) (cover_union (cover_union cell020 cell021) (cover_union cell022 cell023))) (cover_union (cover_union (cover_union cell024 cell025) (cover_union cell026 cell027)) (cover_union (cover_union cell028 cell029) (cover_union cell030 cell031))))
#print axioms cover001
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Cover
