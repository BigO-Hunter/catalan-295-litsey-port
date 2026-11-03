module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearCorners002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearL0PrefixProduction
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction014
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction015
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers031
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers039
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers046
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers047
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers048
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers049
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers050
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open CatalanMeasure.GenD.Signed.Data.Trial
namespace D72.NearCornerCover002
theorem prefixField : fieldNFCheck D2L0PrefixFullFq D72.NearBinding002.literalField = true := by decide +kernel
theorem prefixTerms : laurentNF D2L0PrefixFullTs = laurentNF D72.NearBinding002.literalTerms := by decide +kernel
theorem envelope0 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((828367 : ℚ) / 8388608) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hxL : x ∈ Ioc (0 : ℝ) (D2L0PrefixHi : ℝ) := by
    rcases hx with ⟨hl,hu⟩
    constructor <;> norm_num [D2L0PrefixHi, D2L0PrefixEndLiteral.q2] at * <;> linarith
  have hb := D2L0PrefixBound x hxL
  rw [fieldNFCheck_sound prefixField x, ← laurentNF_sound D2L0PrefixFullTs x, prefixTerms, laurentNF_sound] at hb
  exact hb.trans (by norm_num [D2L0PrefixTarget, D2L0PrefixEndLiteral.q2])
theorem envelope1 (x : ℝ) (hx : x ∈ Icc ((((828367 : ℚ) / 8388608) : ℚ) : ℝ) ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hxL : x ∈ Ioc (0 : ℝ) (D2L0PrefixHi : ℝ) := by
    rcases hx with ⟨hl,hu⟩
    constructor <;> norm_num [D2L0PrefixHi, D2L0PrefixEndLiteral.q2] at * <;> linarith
  have hb := D2L0PrefixBound x hxL
  rw [fieldNFCheck_sound prefixField x, ← laurentNF_sound D2L0PrefixFullTs x, prefixTerms, laurentNF_sound] at hb
  exact hb.trans (by norm_num [D2L0PrefixTarget, D2L0PrefixEndLiteral.q2])
theorem envelope2 (x : ℝ) (hx : x ∈ Icc ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ) ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hxL : x ∈ Ioc (0 : ℝ) (D2L0PrefixHi : ℝ) := by
    rcases hx with ⟨hl,hu⟩
    constructor <;> norm_num [D2L0PrefixHi, D2L0PrefixEndLiteral.q2] at * <;> linarith
  have hb := D2L0PrefixBound x hxL
  rw [fieldNFCheck_sound prefixField x, ← laurentNF_sound D2L0PrefixFullTs x, prefixTerms, laurentNF_sound] at hb
  exact hb.trans (by norm_num [D2L0PrefixTarget, D2L0PrefixEndLiteral.q2])
theorem envelope3 (x : ℝ) (hx : x ∈ Icc ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ) ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hxL : x ∈ Ioc (0 : ℝ) (D2L0PrefixHi : ℝ) := by
    rcases hx with ⟨hl,hu⟩
    constructor <;> norm_num [D2L0PrefixHi, D2L0PrefixEndLiteral.q2] at * <;> linarith
  have hb := D2L0PrefixBound x hxL
  rw [fieldNFCheck_sound prefixField x, ← laurentNF_sound D2L0PrefixFullTs x, prefixTerms, laurentNF_sound] at hb
  exact hb.trans (by norm_num [D2L0PrefixTarget, D2L0PrefixEndLiteral.q2])
theorem envelope4 (x : ℝ) (hx : x ∈ Icc ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ) ((((313261 : ℚ) / 1048576) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction019P0Lo : ℝ) (d2NearProduction019P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction019P0Lo, d2NearProduction019P0Hi, d2NearProduction019P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction019P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction019P0Literal.q2])
theorem envelope5 (x : ℝ) (hx : x ∈ Icc ((((313261 : ℚ) / 1048576) : ℚ) : ℝ) ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction019P1Lo : ℝ) (d2NearProduction019P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction019P1Lo, d2NearProduction019P1Hi, d2NearProduction019P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction019P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction019P1Literal.q2])
theorem envelope6 (x : ℝ) (hx : x ∈ Icc ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ) ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction019P2Lo : ℝ) (d2NearProduction019P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction019P2Lo, d2NearProduction019P2Hi, d2NearProduction019P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction019P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction019P2Literal.q2])
theorem envelope7 (x : ℝ) (hx : x ∈ Icc ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ) ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction013P0Lo : ℝ) (d2NearProduction013P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction013P0Lo, d2NearProduction013P0Hi, d2NearProduction013P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction013P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction013P0Literal.q2])
theorem envelope8 (x : ℝ) (hx : x ∈ Icc ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ) ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction013P1Lo : ℝ) (d2NearProduction013P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction013P1Lo, d2NearProduction013P1Hi, d2NearProduction013P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction013P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction013P1Literal.q2])
theorem envelope9 (x : ℝ) (hx : x ∈ Icc ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ) ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction013P2Lo : ℝ) (d2NearProduction013P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction013P2Lo, d2NearProduction013P2Hi, d2NearProduction013P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction013P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction013P2Literal.q2])
theorem envelope10 (x : ℝ) (hx : x ∈ Icc ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ) ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction013P3Lo : ℝ) (d2NearProduction013P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction013P3Lo, d2NearProduction013P3Hi, d2NearProduction013P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction013P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction013P3Literal.q2])
theorem envelope11 (x : ℝ) (hx : x ∈ Icc ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ) ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-300387081978698214540441 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction013P4Lo : ℝ) (d2NearProduction013P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction013P4Lo, d2NearProduction013P4Hi, d2NearProduction013P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction013P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction013P4Literal.q2])
theorem envelope12 (x : ℝ) (hx : x ∈ Icc ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ) ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-300391778012130389292723 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction013P5Lo : ℝ) (d2NearProduction013P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction013P5Lo, d2NearProduction013P5Hi, d2NearProduction013P5Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction013P5Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction013P5Literal.q2])
theorem envelope13 (x : ℝ) (hx : x ∈ Icc ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ) ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1201634326591760825390299 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction013P6Lo : ℝ) (d2NearProduction013P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction013P6Lo, d2NearProduction013P6Hi, d2NearProduction013P6Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction013P6Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction013P6Literal.q2])
theorem envelope14 (x : ℝ) (hx : x ∈ Icc ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ) ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1201701411402113605251881 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction013P7Lo : ℝ) (d2NearProduction013P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction013P7Lo, d2NearProduction013P7Hi, d2NearProduction013P7Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction013P7Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction013P7Literal.q2])
theorem envelope15 (x : ℝ) (hx : x ∈ Icc ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ) ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1201734905313769939513697 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction014P0Lo : ℝ) (d2NearProduction014P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction014P0Lo, d2NearProduction014P0Hi, d2NearProduction014P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction014P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction014P0Literal.q2])
theorem envelope16 (x : ℝ) (hx : x ∈ Icc ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ) ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1201840995907648229347337 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction014P1Lo : ℝ) (d2NearProduction014P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction014P1Lo, d2NearProduction014P1Hi, d2NearProduction014P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction014P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction014P1Literal.q2])
theorem envelope17 (x : ℝ) (hx : x ∈ Icc ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ) ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-300496078845958060995161 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction014P2Lo : ℝ) (d2NearProduction014P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction014P2Lo, d2NearProduction014P2Hi, d2NearProduction014P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction014P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction014P2Literal.q2])
theorem envelope18 (x : ℝ) (hx : x ∈ Icc ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1202056198637668290974021 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction014P3Lo : ℝ) (d2NearProduction014P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction014P3Lo, d2NearProduction014P3Hi, d2NearProduction014P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction014P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction014P3Literal.q2])
theorem envelope19 (x : ℝ) (hx : x ∈ Icc ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ) ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-601064115866816717935587 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction014P4Lo : ℝ) (d2NearProduction014P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction014P4Lo, d2NearProduction014P4Hi, d2NearProduction014P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction014P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction014P4Literal.q2])
theorem envelope20 (x : ℝ) (hx : x ∈ Icc ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ) ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1202200415300353547428239 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction014P5Lo : ℝ) (d2NearProduction014P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction014P5Lo, d2NearProduction014P5Hi, d2NearProduction014P5Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction014P5Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction014P5Literal.q2])
theorem envelope21 (x : ℝ) (hx : x ∈ Icc ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ) ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1202272749970414875060021 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction014P6Lo : ℝ) (d2NearProduction014P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction014P6Lo, d2NearProduction014P6Hi, d2NearProduction014P6Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction014P6Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction014P6Literal.q2])
theorem envelope22 (x : ℝ) (hx : x ∈ Icc ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-601172618190198696849979 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction014P7Lo : ℝ) (d2NearProduction014P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction014P7Lo, d2NearProduction014P7Hi, d2NearProduction014P7Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction014P7Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction014P7Literal.q2])
theorem envelope23 (x : ℝ) (hx : x ∈ Icc ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ) ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1202417875170908500321215 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction015P0Lo : ℝ) (d2NearProduction015P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction015P0Lo, d2NearProduction015P0Hi, d2NearProduction015P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction015P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction015P0Literal.q2])
theorem envelope24 (x : ℝ) (hx : x ∈ Icc ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ) ((((1354589953 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1202490666986617066578791 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction015P1Lo : ℝ) (d2NearProduction015P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction015P1Lo, d2NearProduction015P1Hi, d2NearProduction015P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction015P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction015P1Literal.q2])
theorem envelope25 (x : ℝ) (hx : x ∈ Icc ((((1354589953 : ℚ) / 2147483648) : ℚ) : ℝ) ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-601281806238143926049327 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction015P2Lo : ℝ) (d2NearProduction015P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction015P2Lo, d2NearProduction015P2Hi, d2NearProduction015P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction015P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction015P2Literal.q2])
theorem envelope26 (x : ℝ) (hx : x ∈ Icc ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1357945395 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-601318356146408141503579 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction015P3Lo : ℝ) (d2NearProduction015P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction015P3Lo, d2NearProduction015P3Hi, d2NearProduction015P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction015P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction015P3Literal.q2])
theorem envelope27 (x : ℝ) (hx : x ∈ Icc ((((1357945395 : ℚ) / 2147483648) : ℚ) : ℝ) ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-601354983546631800181201 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction015P4Lo : ℝ) (d2NearProduction015P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction015P4Lo, d2NearProduction015P4Hi, d2NearProduction015P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction015P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction015P4Literal.q2])
theorem envelope28 (x : ℝ) (hx : x ∈ Icc ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ) ((((1361300837 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1202783377538892383218737 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction015P5Lo : ℝ) (d2NearProduction015P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction015P5Lo, d2NearProduction015P5Hi, d2NearProduction015P5Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction015P5Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction015P5Literal.q2])
theorem envelope29 (x : ℝ) (hx : x ∈ Icc ((((1361300837 : ℚ) / 2147483648) : ℚ) : ℝ) ((((681489279 : ℚ) / 1073741824) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-601428472147601225563205 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction015P6Lo : ℝ) (d2NearProduction015P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction015P6Lo, d2NearProduction015P6Hi, d2NearProduction015P6Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction015P6Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction015P6Literal.q2])
theorem envelope30 (x : ℝ) (hx : x ∈ Icc ((((681489279 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1364656279 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1202930668031967150940253 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction015P7Lo : ℝ) (d2NearProduction015P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction015P7Lo, d2NearProduction015P7Hi, d2NearProduction015P7Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction015P7Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction015P7Literal.q2])
theorem envelope31 (x : ℝ) (hx : x ∈ Icc ((((1364656279 : ℚ) / 2147483648) : ℚ) : ℝ) ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1203004549423270032884565 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction016P0Lo : ℝ) (d2NearProduction016P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction016P0Lo, d2NearProduction016P0Hi, d2NearProduction016P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction016P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction016P0Literal.q2])
theorem envelope32 (x : ℝ) (hx : x ∈ Icc ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ) ((((1368011721 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1203078589147541920895757 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction016P1Lo : ℝ) (d2NearProduction016P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction016P1Lo, d2NearProduction016P1Hi, d2NearProduction016P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction016P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction016P1Literal.q2])
theorem envelope33 (x : ℝ) (hx : x ∈ Icc ((((1368011721 : ℚ) / 2147483648) : ℚ) : ℝ) ((((684844721 : ℚ) / 1073741824) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-601576393943799191170049 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction016P2Lo : ℝ) (d2NearProduction016P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction016P2Lo, d2NearProduction016P2Hi, d2NearProduction016P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction016P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction016P2Literal.q2])
theorem envelope34 (x : ℝ) (hx : x ∈ Icc ((((684844721 : ℚ) / 1073741824) : ℚ) : ℝ) ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1203301665168478667548123 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction016P3Lo : ℝ) (d2NearProduction016P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction016P3Lo, d2NearProduction016P3Hi, d2NearProduction016P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction016P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction016P3Literal.q2])
theorem envelope35 (x : ℝ) (hx : x ∈ Icc ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ) ((((688200163 : ℚ) / 1073741824) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-601725593408789902993491 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction016P4Lo : ℝ) (d2NearProduction016P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction016P4Lo, d2NearProduction016P4Hi, d2NearProduction016P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction016P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction016P4Literal.q2])
theorem envelope36 (x : ℝ) (hx : x ∈ Icc ((((688200163 : ℚ) / 1073741824) : ℚ) : ℝ) ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-300900339614798413786671 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction016P5Lo : ℝ) (d2NearProduction016P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction016P5Lo, d2NearProduction016P5Hi, d2NearProduction016P5Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction016P5Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction016P5Literal.q2])
theorem envelope37 (x : ℝ) (hx : x ∈ Icc ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ) ((((346616663 : ℚ) / 536870912) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1203903674587904375218619 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction016P6Lo : ℝ) (d2NearProduction016P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction016P6Lo, d2NearProduction016P6Hi, d2NearProduction016P6Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction016P6Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction016P6Literal.q2])
theorem envelope38 (x : ℝ) (hx : x ∈ Icc ((((346616663 : ℚ) / 536870912) : ℚ) : ℝ) ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1204208660050463752761767 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction016P7Lo : ℝ) (d2NearProduction016P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction016P7Lo, d2NearProduction016P7Hi, d2NearProduction016P7Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction016P7Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction016P7Literal.q2])
theorem envelope39 (x : ℝ) (hx : x ∈ Icc ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ) ((((175824913 : ℚ) / 268435456) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-301206707809351861958911 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction017P0Lo : ℝ) (d2NearProduction017P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction017P0Lo, d2NearProduction017P0Hi, d2NearProduction017P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction017P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction017P0Literal.q2])
theorem envelope40 (x : ℝ) (hx : x ∈ Icc ((((175824913 : ℚ) / 268435456) : ℚ) : ℝ) ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-75341016858634917701977 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction017P1Lo : ℝ) (d2NearProduction017P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction017P1Lo, d2NearProduction017P1Hi, d2NearProduction017P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction017P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction017P1Literal.q2])
theorem envelope41 (x : ℝ) (hx : x ∈ Icc ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ) ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-301687663082960030349841 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction017P2Lo : ℝ) (d2NearProduction017P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction017P2Lo, d2NearProduction017P2Hi, d2NearProduction017P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction017P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction017P2Literal.q2])
theorem envelope42 (x : ℝ) (hx : x ∈ Icc ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ) ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-604747406500786716099207 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction017P3Lo : ℝ) (d2NearProduction017P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction017P3Lo, d2NearProduction017P3Hi, d2NearProduction017P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction017P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction017P3Literal.q2])
theorem envelope43 (x : ℝ) (hx : x ∈ Icc ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ) ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1215739989231307193421455 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction017P4Lo : ℝ) (d2NearProduction017P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction017P4Lo, d2NearProduction017P4Hi, d2NearProduction017P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction017P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction017P4Literal.q2])
theorem envelope44 (x : ℝ) (hx : x ∈ Icc ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ) ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1223372623635611069590819 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction017P5Lo : ℝ) (d2NearProduction017P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction017P5Lo, d2NearProduction017P5Hi, d2NearProduction017P5Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction017P5Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction017P5Literal.q2])
theorem envelope45 (x : ℝ) (hx : x ∈ Icc ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ) ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-623493913835725770474485 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction017P6Lo : ℝ) (d2NearProduction017P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction017P6Lo, d2NearProduction017P6Hi, d2NearProduction017P6Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction017P6Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction017P6Literal.q2])
theorem envelope46 (x : ℝ) (hx : x ∈ Icc ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ) ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1270382488094418628452727 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction017P7Lo : ℝ) (d2NearProduction017P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction017P7Lo, d2NearProduction017P7Hi, d2NearProduction017P7Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction017P7Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction017P7Literal.q2])
theorem envelope47 (x : ℝ) (hx : x ∈ Icc ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ) ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1293365088196555690495641 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction018P0Lo : ℝ) (d2NearProduction018P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction018P0Lo, d2NearProduction018P0Hi, d2NearProduction018P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction018P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction018P0Literal.q2])
theorem envelope48 (x : ℝ) (hx : x ∈ Icc ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ) ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-1397899330428271968276247 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction018P1Lo : ℝ) (d2NearProduction018P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction018P1Lo, d2NearProduction018P1Hi, d2NearProduction018P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction018P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction018P1Literal.q2])
theorem envelope49 (x : ℝ) (hx : x ∈ Icc ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ) ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-351399171642520626107921 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction018P2Lo : ℝ) (d2NearProduction018P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction018P2Lo, d2NearProduction018P2Hi, d2NearProduction018P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction018P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction018P2Literal.q2])
theorem envelope50 (x : ℝ) (hx : x ∈ Icc ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ)) : (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) ≤ ((((-702799145730679485692875 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction018P3Lo : ℝ) (d2NearProduction018P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction018P3Lo, d2NearProduction018P3Hi, d2NearProduction018P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction018P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction018P3Literal.q2])
theorem delta0Check : fieldNFCheck D72.NearCorners002.delta0 (fqSum []) = true := by decide +kernel
theorem delta0Value (x : ℝ) : fval D72.NearCorners002.delta0 x = (0 : ℝ) := by
  have h := fieldNFCheck_sound delta0Check x
  change fval D72.NearCorners002.delta0 x = fval (fqSum []) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner0Identity (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x = (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) + ((0 : ℝ)) := by
  rw [D72.NearCorners002.corner0Value, delta0Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) x, D72.NearCorners002.corner0Terms, laurentNF_sound, ← D72.NearBinding002.termsValue x]
  ring
theorem corner0Piece0 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((828367 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope0 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece1 (x : ℝ) (hx : x ∈ Icc ((((828367 : ℚ) / 8388608) : ℚ) : ℝ) ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope1 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece2 (x : ℝ) (hx : x ∈ Icc ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ) ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope2 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece3 (x : ℝ) (hx : x ∈ Icc ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ) ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope3 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece4 (x : ℝ) (hx : x ∈ Icc ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ) ((((313261 : ℚ) / 1048576) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope4 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece5 (x : ℝ) (hx : x ∈ Icc ((((313261 : ℚ) / 1048576) : ℚ) : ℝ) ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope5 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece6 (x : ℝ) (hx : x ∈ Icc ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ) ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope6 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece7 (x : ℝ) (hx : x ∈ Icc ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ) ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope7 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece8 (x : ℝ) (hx : x ∈ Icc ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ) ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope8 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece9 (x : ℝ) (hx : x ∈ Icc ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ) ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope9 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece10 (x : ℝ) (hx : x ∈ Icc ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ) ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope10 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece11 (x : ℝ) (hx : x ∈ Icc ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ) ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope11 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece12 (x : ℝ) (hx : x ∈ Icc ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ) ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope12 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece13 (x : ℝ) (hx : x ∈ Icc ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ) ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope13 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece14 (x : ℝ) (hx : x ∈ Icc ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ) ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope14 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece15 (x : ℝ) (hx : x ∈ Icc ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ) ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope15 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece16 (x : ℝ) (hx : x ∈ Icc ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ) ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope16 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece17 (x : ℝ) (hx : x ∈ Icc ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ) ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope17 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece18 (x : ℝ) (hx : x ∈ Icc ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope18 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece19 (x : ℝ) (hx : x ∈ Icc ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ) ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope19 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece20 (x : ℝ) (hx : x ∈ Icc ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ) ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope20 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece21 (x : ℝ) (hx : x ∈ Icc ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ) ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope21 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece22 (x : ℝ) (hx : x ∈ Icc ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope22 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece23 (x : ℝ) (hx : x ∈ Icc ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ) ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope23 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece24 (x : ℝ) (hx : x ∈ Icc ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ) ((((1354589953 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope24 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece25 (x : ℝ) (hx : x ∈ Icc ((((1354589953 : ℚ) / 2147483648) : ℚ) : ℝ) ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope25 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece26 (x : ℝ) (hx : x ∈ Icc ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1357945395 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope26 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece27 (x : ℝ) (hx : x ∈ Icc ((((1357945395 : ℚ) / 2147483648) : ℚ) : ℝ) ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope27 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece28 (x : ℝ) (hx : x ∈ Icc ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ) ((((1361300837 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope28 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece29 (x : ℝ) (hx : x ∈ Icc ((((1361300837 : ℚ) / 2147483648) : ℚ) : ℝ) ((((681489279 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope29 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece30 (x : ℝ) (hx : x ∈ Icc ((((681489279 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1364656279 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope30 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece31 (x : ℝ) (hx : x ∈ Icc ((((1364656279 : ℚ) / 2147483648) : ℚ) : ℝ) ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope31 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece32 (x : ℝ) (hx : x ∈ Icc ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ) ((((1368011721 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope32 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece33 (x : ℝ) (hx : x ∈ Icc ((((1368011721 : ℚ) / 2147483648) : ℚ) : ℝ) ((((684844721 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope33 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece34 (x : ℝ) (hx : x ∈ Icc ((((684844721 : ℚ) / 1073741824) : ℚ) : ℝ) ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope34 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece35 (x : ℝ) (hx : x ∈ Icc ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ) ((((688200163 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope35 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece36 (x : ℝ) (hx : x ∈ Icc ((((688200163 : ℚ) / 1073741824) : ℚ) : ℝ) ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope36 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece37 (x : ℝ) (hx : x ∈ Icc ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ) ((((346616663 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope37 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece38 (x : ℝ) (hx : x ∈ Icc ((((346616663 : ℚ) / 536870912) : ℚ) : ℝ) ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope38 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece39 (x : ℝ) (hx : x ∈ Icc ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ) ((((175824913 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope39 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece40 (x : ℝ) (hx : x ∈ Icc ((((175824913 : ℚ) / 268435456) : ℚ) : ℝ) ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope40 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece41 (x : ℝ) (hx : x ∈ Icc ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ) ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope41 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece42 (x : ℝ) (hx : x ∈ Icc ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ) ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope42 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece43 (x : ℝ) (hx : x ∈ Icc ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ) ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope43 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece44 (x : ℝ) (hx : x ∈ Icc ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ) ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope44 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece45 (x : ℝ) (hx : x ∈ Icc ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ) ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope45 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece46 (x : ℝ) (hx : x ∈ Icc ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ) ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope46 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece47 (x : ℝ) (hx : x ∈ Icc ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ) ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope47 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece48 (x : ℝ) (hx : x ∈ Icc ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ) ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope48 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece49 (x : ℝ) (hx : x ∈ Icc ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ) ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope49 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece50 (x : ℝ) (hx : x ∈ Icc ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope50 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
def corner0Domain0Pieces : List (ℚ × ℚ) := [(((98749 : ℚ) / 1000000), ((828367 : ℚ) / 8388608)), (((828367 : ℚ) / 8388608), ((8304657 : ℚ) / 67108864)), (((8304657 : ℚ) / 67108864), ((4991189 : ℚ) / 33554432)), (((4991189 : ℚ) / 33554432), ((3334455 : ℚ) / 16777216)), (((3334455 : ℚ) / 16777216), ((313261 : ℚ) / 1048576)), (((313261 : ℚ) / 1048576), ((6689897 : ℚ) / 16777216)), (((6689897 : ℚ) / 16777216), ((4183809 : ℚ) / 8388608)), (((4183809 : ℚ) / 8388608), ((18412957 : ℚ) / 33554432)), (((18412957 : ℚ) / 33554432), ((38503635 : ℚ) / 67108864)), (((38503635 : ℚ) / 67108864), ((10045339 : ℚ) / 16777216)), (((10045339 : ℚ) / 16777216), ((162403145 : ℚ) / 268435456)), (((162403145 : ℚ) / 268435456), ((82040433 : ℚ) / 134217728)), (((82040433 : ℚ) / 134217728), ((329839453 : ℚ) / 536870912)), (((329839453 : ℚ) / 536870912), ((165758587 : ℚ) / 268435456)), (((165758587 : ℚ) / 268435456), ((333194895 : ℚ) / 536870912)), (((333194895 : ℚ) / 536870912), ((668067511 : ℚ) / 1073741824)), (((668067511 : ℚ) / 1073741824), ((41859077 : ℚ) / 67108864)), (((41859077 : ℚ) / 67108864), ((671422953 : ℚ) / 1073741824)), (((671422953 : ℚ) / 1073741824), ((1344523627 : ℚ) / 2147483648)), (((1344523627 : ℚ) / 2147483648), ((336550337 : ℚ) / 536870912)), (((336550337 : ℚ) / 536870912), ((1347879069 : ℚ) / 2147483648)), (((1347879069 : ℚ) / 2147483648), ((674778395 : ℚ) / 1073741824)), (((674778395 : ℚ) / 1073741824), ((1351234511 : ℚ) / 2147483648)), (((1351234511 : ℚ) / 2147483648), ((169114029 : ℚ) / 268435456)), (((169114029 : ℚ) / 268435456), ((1354589953 : ℚ) / 2147483648)), (((1354589953 : ℚ) / 2147483648), ((678133837 : ℚ) / 1073741824)), (((678133837 : ℚ) / 1073741824), ((1357945395 : ℚ) / 2147483648)), (((1357945395 : ℚ) / 2147483648), ((339905779 : ℚ) / 536870912)), (((339905779 : ℚ) / 536870912), ((1361300837 : ℚ) / 2147483648)), (((1361300837 : ℚ) / 2147483648), ((681489279 : ℚ) / 1073741824)), (((681489279 : ℚ) / 1073741824), ((1364656279 : ℚ) / 2147483648)), (((1364656279 : ℚ) / 2147483648), ((85395875 : ℚ) / 134217728)), (((85395875 : ℚ) / 134217728), ((1368011721 : ℚ) / 2147483648)), (((1368011721 : ℚ) / 2147483648), ((684844721 : ℚ) / 1073741824)), (((684844721 : ℚ) / 1073741824), ((343261221 : ℚ) / 536870912)), (((343261221 : ℚ) / 536870912), ((688200163 : ℚ) / 1073741824)), (((688200163 : ℚ) / 1073741824), ((172469471 : ℚ) / 268435456)), (((172469471 : ℚ) / 268435456), ((346616663 : ℚ) / 536870912)), (((346616663 : ℚ) / 536870912), ((21768399 : ℚ) / 33554432)), (((21768399 : ℚ) / 33554432), ((175824913 : ℚ) / 268435456)), (((175824913 : ℚ) / 268435456), ((88751317 : ℚ) / 134217728)), (((88751317 : ℚ) / 134217728), ((45214519 : ℚ) / 67108864)), (((45214519 : ℚ) / 67108864), ((2930765 : ℚ) / 4194304)), (((2930765 : ℚ) / 4194304), ((25123841 : ℚ) / 33554432)), (((25123841 : ℚ) / 33554432), ((13400781 : ℚ) / 16777216)), (((13400781 : ℚ) / 16777216), ((7539251 : ℚ) / 8388608)), (((7539251 : ℚ) / 8388608), ((31834725 : ℚ) / 33554432)), (((31834725 : ℚ) / 33554432), ((65347171 : ℚ) / 67108864)), (((65347171 : ℚ) / 67108864), ((16756223 : ℚ) / 16777216)), (((16756223 : ℚ) / 16777216), ((8380219 : ℚ) / 8388608)), (((8380219 : ℚ) / 8388608), ((999 : ℚ) / 1000))]
theorem corner0Domain0Cover : pieceCover ((999 : ℚ) / 1000) ((98749 : ℚ) / 1000000) corner0Domain0Pieces = true := by decide +kernel
theorem corner0Domain0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  apply pieceCover_bound ((999 : ℚ) / 1000) (fun x : ℝ => fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x) ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) ((98749 : ℚ) / 1000000) corner0Domain0Pieces (by decide +kernel) corner0Domain0Cover
  intro p hp
  simp only [corner0Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner0Piece0
  · exact corner0Piece1
  · exact corner0Piece2
  · exact corner0Piece3
  · exact corner0Piece4
  · exact corner0Piece5
  · exact corner0Piece6
  · exact corner0Piece7
  · exact corner0Piece8
  · exact corner0Piece9
  · exact corner0Piece10
  · exact corner0Piece11
  · exact corner0Piece12
  · exact corner0Piece13
  · exact corner0Piece14
  · exact corner0Piece15
  · exact corner0Piece16
  · exact corner0Piece17
  · exact corner0Piece18
  · exact corner0Piece19
  · exact corner0Piece20
  · exact corner0Piece21
  · exact corner0Piece22
  · exact corner0Piece23
  · exact corner0Piece24
  · exact corner0Piece25
  · exact corner0Piece26
  · exact corner0Piece27
  · exact corner0Piece28
  · exact corner0Piece29
  · exact corner0Piece30
  · exact corner0Piece31
  · exact corner0Piece32
  · exact corner0Piece33
  · exact corner0Piece34
  · exact corner0Piece35
  · exact corner0Piece36
  · exact corner0Piece37
  · exact corner0Piece38
  · exact corner0Piece39
  · exact corner0Piece40
  · exact corner0Piece41
  · exact corner0Piece42
  · exact corner0Piece43
  · exact corner0Piece44
  · exact corner0Piece45
  · exact corner0Piece46
  · exact corner0Piece47
  · exact corner0Piece48
  · exact corner0Piece49
  · exact corner0Piece50
#print axioms corner0Domain0Cover
#print axioms corner0Domain0
theorem delta1Check : fieldNFCheck D72.NearCorners002.delta1 (fqSum [logFQ ((-1 : ℚ) / 440) ((-1 : ℚ) / 1), logFQ ((-1 : ℚ) / 440) ((1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta1Value (x : ℝ) : fval D72.NearCorners002.delta1 x = ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta1Check x
  change fval D72.NearCorners002.delta1 x = fval (fqSum [logFQ ((-1 : ℚ) / 440) ((-1 : ℚ) / 1), logFQ ((-1 : ℚ) / 440) ((1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner1Identity (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x = (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) + (((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  rw [D72.NearCorners002.corner1Value, delta1Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) x, D72.NearCorners002.corner1Terms, laurentNF_sound, ← D72.NearBinding002.termsValue x]
  ring
theorem corner1Piece0 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((828367 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer250Lo : ℝ) (d2WiderTransfer250Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer250Lo, d2WiderTransfer250Hi, d2LitsNearWiderTransfers031.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer250Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer250Cap, d2LitsNearWiderTransfers031.q2, d2WiderTransfer250C0, d2WiderTransfer250S0, d2WiderTransfer250C1, d2WiderTransfer250S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece1 (x : ℝ) (hx : x ∈ Icc ((((828367 : ℚ) / 8388608) : ℚ) : ℝ) ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer253Lo : ℝ) (d2WiderTransfer253Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer253Lo, d2WiderTransfer253Hi, d2LitsNearWiderTransfers031.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer253Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer253Cap, d2LitsNearWiderTransfers031.q2, d2WiderTransfer253C0, d2WiderTransfer253S0, d2WiderTransfer253C1, d2WiderTransfer253S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece2 (x : ℝ) (hx : x ∈ Icc ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ) ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer256Lo : ℝ) (d2WiderTransfer256Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer256Lo, d2WiderTransfer256Hi, d2LitsNearWiderTransfers032.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer256Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer256Cap, d2LitsNearWiderTransfers032.q2, d2WiderTransfer256C0, d2WiderTransfer256S0, d2WiderTransfer256C1, d2WiderTransfer256S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece3 (x : ℝ) (hx : x ∈ Icc ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ) ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer259Lo : ℝ) (d2WiderTransfer259Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer259Lo, d2WiderTransfer259Hi, d2LitsNearWiderTransfers032.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer259Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer259Cap, d2LitsNearWiderTransfers032.q2, d2WiderTransfer259C0, d2WiderTransfer259S0, d2WiderTransfer259C1, d2WiderTransfer259S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece4 (x : ℝ) (hx : x ∈ Icc ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ) ((((313261 : ℚ) / 1048576) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer262Lo : ℝ) (d2WiderTransfer262Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer262Lo, d2WiderTransfer262Hi, d2LitsNearWiderTransfers032.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer262Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer262Cap, d2LitsNearWiderTransfers032.q2, d2WiderTransfer262C0, d2WiderTransfer262S0, d2WiderTransfer262C1, d2WiderTransfer262S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece5 (x : ℝ) (hx : x ∈ Icc ((((313261 : ℚ) / 1048576) : ℚ) : ℝ) ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer265Lo : ℝ) (d2WiderTransfer265Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer265Lo, d2WiderTransfer265Hi, d2LitsNearWiderTransfers033.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer265Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer265Cap, d2LitsNearWiderTransfers033.q2, d2WiderTransfer265C0, d2WiderTransfer265S0, d2WiderTransfer265C1, d2WiderTransfer265S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece6 (x : ℝ) (hx : x ∈ Icc ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ) ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer268Lo : ℝ) (d2WiderTransfer268Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer268Lo, d2WiderTransfer268Hi, d2LitsNearWiderTransfers033.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer268Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer268Cap, d2LitsNearWiderTransfers033.q2, d2WiderTransfer268C0, d2WiderTransfer268S0, d2WiderTransfer268C1, d2WiderTransfer268S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece7 (x : ℝ) (hx : x ∈ Icc ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ) ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer271Lo : ℝ) (d2WiderTransfer271Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer271Lo, d2WiderTransfer271Hi, d2LitsNearWiderTransfers033.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer271Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer271Cap, d2LitsNearWiderTransfers033.q2, d2WiderTransfer271C0, d2WiderTransfer271S0, d2WiderTransfer271C1, d2WiderTransfer271S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece8 (x : ℝ) (hx : x ∈ Icc ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ) ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer274Lo : ℝ) (d2WiderTransfer274Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer274Lo, d2WiderTransfer274Hi, d2LitsNearWiderTransfers034.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer274Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer274Cap, d2LitsNearWiderTransfers034.q2, d2WiderTransfer274C0, d2WiderTransfer274S0, d2WiderTransfer274C1, d2WiderTransfer274S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece9 (x : ℝ) (hx : x ∈ Icc ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ) ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope9 x hx
  have hxT : x ∈ Icc (d2WiderTransfer277Lo : ℝ) (d2WiderTransfer277Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer277Lo, d2WiderTransfer277Hi, d2LitsNearWiderTransfers034.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer277Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer277Cap, d2LitsNearWiderTransfers034.q2, d2WiderTransfer277C0, d2WiderTransfer277S0, d2WiderTransfer277C1, d2WiderTransfer277S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece10 (x : ℝ) (hx : x ∈ Icc ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ) ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope10 x hx
  have hxT : x ∈ Icc (d2WiderTransfer280Lo : ℝ) (d2WiderTransfer280Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer280Lo, d2WiderTransfer280Hi, d2LitsNearWiderTransfers035.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer280Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer280Cap, d2LitsNearWiderTransfers035.q2, d2WiderTransfer280C0, d2WiderTransfer280S0, d2WiderTransfer280C1, d2WiderTransfer280S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((1169469059 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece11 (x : ℝ) (hx : x ∈ Icc ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ) ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope11 x hx
  have hxT : x ∈ Icc (d2WiderTransfer283Lo : ℝ) (d2WiderTransfer283Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer283Lo, d2WiderTransfer283Hi, d2LitsNearWiderTransfers035.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer283Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((324000933795269575833 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer283Cap, d2LitsNearWiderTransfers035.q2, d2WiderTransfer283C0, d2WiderTransfer283S0, d2WiderTransfer283C1, d2WiderTransfer283S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-300387081978698214540441 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((324000933795269575833 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece12 (x : ℝ) (hx : x ∈ Icc ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ) ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope12 x hx
  have hxT : x ∈ Icc (d2WiderTransfer286Lo : ℝ) (d2WiderTransfer286Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer286Lo, d2WiderTransfer286Hi, d2LitsNearWiderTransfers035.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer286Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((328696967227444328115 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer286Cap, d2LitsNearWiderTransfers035.q2, d2WiderTransfer286C0, d2WiderTransfer286S0, d2WiderTransfer286C1, d2WiderTransfer286S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-300391778012130389292723 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((328696967227444328115 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece13 (x : ℝ) (hx : x ∈ Icc ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ) ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope13 x hx
  have hxT : x ∈ Icc (d2WiderTransfer289Lo : ℝ) (d2WiderTransfer289Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer289Lo, d2WiderTransfer289Hi, d2LitsNearWiderTransfers036.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer289Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1382002412149045531867 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer289Cap, d2LitsNearWiderTransfers036.q2, d2WiderTransfer289C0, d2WiderTransfer289S0, d2WiderTransfer289C1, d2WiderTransfer289S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1201634326591760825390299 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((1382002412149045531867 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece14 (x : ℝ) (hx : x ∈ Icc ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ) ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope14 x hx
  have hxT : x ∈ Icc (d2WiderTransfer292Lo : ℝ) (d2WiderTransfer292Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer292Lo, d2WiderTransfer292Hi, d2LitsNearWiderTransfers036.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer292Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1449087222501825393449 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer292Cap, d2LitsNearWiderTransfers036.q2, d2WiderTransfer292C0, d2WiderTransfer292S0, d2WiderTransfer292C1, d2WiderTransfer292S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1201701411402113605251881 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((1449087222501825393449 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece15 (x : ℝ) (hx : x ∈ Icc ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ) ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope15 x hx
  have hxT : x ∈ Icc (d2WiderTransfer295Lo : ℝ) (d2WiderTransfer295Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer295Lo, d2WiderTransfer295Hi, d2LitsNearWiderTransfers036.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer295Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1482581134158159655265 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer295Cap, d2LitsNearWiderTransfers036.q2, d2WiderTransfer295C0, d2WiderTransfer295S0, d2WiderTransfer295C1, d2WiderTransfer295S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1201734905313769939513697 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((1482581134158159655265 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece16 (x : ℝ) (hx : x ∈ Icc ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ) ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope16 x hx
  have hxT : x ∈ Icc (d2WiderTransfer298Lo : ℝ) (d2WiderTransfer298Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer298Lo, d2WiderTransfer298Hi, d2LitsNearWiderTransfers037.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer298Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1588671728036449488905 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer298Cap, d2LitsNearWiderTransfers037.q2, d2WiderTransfer298C0, d2WiderTransfer298S0, d2WiderTransfer298C1, d2WiderTransfer298S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1201840995907648229347337 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((1588671728036449488905 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece17 (x : ℝ) (hx : x ∈ Icc ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ) ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope17 x hx
  have hxT : x ∈ Icc (d2WiderTransfer301Lo : ℝ) (d2WiderTransfer301Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer301Lo, d2WiderTransfer301Hi, d2LitsNearWiderTransfers037.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer301Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((432997801055116030553 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer301Cap, d2LitsNearWiderTransfers037.q2, d2WiderTransfer301C0, d2WiderTransfer301S0, d2WiderTransfer301C1, d2WiderTransfer301S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-300496078845958060995161 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((432997801055116030553 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece18 (x : ℝ) (hx : x ∈ Icc ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope18 x hx
  have hxT : x ∈ Icc (d2WiderTransfer304Lo : ℝ) (d2WiderTransfer304Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer304Lo, d2WiderTransfer304Hi, d2LitsNearWiderTransfers038.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer304Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1803874458056511115589 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer304Cap, d2LitsNearWiderTransfers038.q2, d2WiderTransfer304C0, d2WiderTransfer304S0, d2WiderTransfer304C1, d2WiderTransfer304S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202056198637668290974021 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((1803874458056511115589 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece19 (x : ℝ) (hx : x ∈ Icc ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ) ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope19 x hx
  have hxT : x ∈ Icc (d2WiderTransfer307Lo : ℝ) (d2WiderTransfer307Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer307Lo, d2WiderTransfer307Hi, d2LitsNearWiderTransfers038.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer307Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((937953777010828006371 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer307Cap, d2LitsNearWiderTransfers038.q2, d2WiderTransfer307C0, d2WiderTransfer307S0, d2WiderTransfer307C1, d2WiderTransfer307S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601064115866816717935587 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((937953777010828006371 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece20 (x : ℝ) (hx : x ∈ Icc ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ) ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope20 x hx
  have hxT : x ∈ Icc (d2WiderTransfer310Lo : ℝ) (d2WiderTransfer310Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer310Lo, d2WiderTransfer310Hi, d2LitsNearWiderTransfers038.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer310Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1948091120741767569807 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer310Cap, d2LitsNearWiderTransfers038.q2, d2WiderTransfer310C0, d2WiderTransfer310S0, d2WiderTransfer310C1, d2WiderTransfer310S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202200415300353547428239 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((1948091120741767569807 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece21 (x : ℝ) (hx : x ∈ Icc ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ) ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope21 x hx
  have hxT : x ∈ Icc (d2WiderTransfer313Lo : ℝ) (d2WiderTransfer313Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer313Lo, d2WiderTransfer313Hi, d2LitsNearWiderTransfers039.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer313Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2020425790803095201589 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer313Cap, d2LitsNearWiderTransfers039.q2, d2WiderTransfer313C0, d2WiderTransfer313S0, d2WiderTransfer313C1, d2WiderTransfer313S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202272749970414875060021 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2020425790803095201589 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece22 (x : ℝ) (hx : x ∈ Icc ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope22 x hx
  have hxT : x ∈ Icc (d2WiderTransfer316Lo : ℝ) (d2WiderTransfer316Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer316Lo, d2WiderTransfer316Hi, d2LitsNearWiderTransfers039.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer316Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1046456100392806920763 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer316Cap, d2LitsNearWiderTransfers039.q2, d2WiderTransfer316C0, d2WiderTransfer316S0, d2WiderTransfer316C1, d2WiderTransfer316S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601172618190198696849979 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1046456100392806920763 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece23 (x : ℝ) (hx : x ∈ Icc ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ) ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope23 x hx
  have hxT : x ∈ Icc (d2WiderTransfer319Lo : ℝ) (d2WiderTransfer319Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer319Lo, d2WiderTransfer319Hi, d2LitsNearWiderTransfers039.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer319Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2165550991296720462783 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer319Cap, d2LitsNearWiderTransfers039.q2, d2WiderTransfer319C0, d2WiderTransfer319S0, d2WiderTransfer319C1, d2WiderTransfer319S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202417875170908500321215 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2165550991296720462783 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece24 (x : ℝ) (hx : x ∈ Icc ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ) ((((1354589953 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope24 x hx
  have hxT : x ∈ Icc (d2WiderTransfer322Lo : ℝ) (d2WiderTransfer322Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer322Lo, d2WiderTransfer322Hi, d2LitsNearWiderTransfers040.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer322Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2238342807005286720359 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer322Cap, d2LitsNearWiderTransfers040.q2, d2WiderTransfer322C0, d2WiderTransfer322S0, d2WiderTransfer322C1, d2WiderTransfer322S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202490666986617066578791 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2238342807005286720359 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece25 (x : ℝ) (hx : x ∈ Icc ((((1354589953 : ℚ) / 2147483648) : ℚ) : ℝ) ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope25 x hx
  have hxT : x ∈ Icc (d2WiderTransfer325Lo : ℝ) (d2WiderTransfer325Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer325Lo, d2WiderTransfer325Hi, d2LitsNearWiderTransfers040.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer325Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1155644148338036120111 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer325Cap, d2LitsNearWiderTransfers040.q2, d2WiderTransfer325C0, d2WiderTransfer325S0, d2WiderTransfer325C1, d2WiderTransfer325S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601281806238143926049327 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1155644148338036120111 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece26 (x : ℝ) (hx : x ∈ Icc ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1357945395 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope26 x hx
  have hxT : x ∈ Icc (d2WiderTransfer328Lo : ℝ) (d2WiderTransfer328Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer328Lo, d2WiderTransfer328Hi, d2LitsNearWiderTransfers041.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer328Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1192194056602251574363 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer328Cap, d2LitsNearWiderTransfers041.q2, d2WiderTransfer328C0, d2WiderTransfer328S0, d2WiderTransfer328C1, d2WiderTransfer328S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601318356146408141503579 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1192194056602251574363 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece27 (x : ℝ) (hx : x ∈ Icc ((((1357945395 : ℚ) / 2147483648) : ℚ) : ℝ) ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope27 x hx
  have hxT : x ∈ Icc (d2WiderTransfer331Lo : ℝ) (d2WiderTransfer331Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer331Lo, d2WiderTransfer331Hi, d2LitsNearWiderTransfers041.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer331Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1228821456825910251985 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer331Cap, d2LitsNearWiderTransfers041.q2, d2WiderTransfer331C0, d2WiderTransfer331S0, d2WiderTransfer331C1, d2WiderTransfer331S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601354983546631800181201 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1228821456825910251985 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece28 (x : ℝ) (hx : x ∈ Icc ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ) ((((1361300837 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope28 x hx
  have hxT : x ∈ Icc (d2WiderTransfer334Lo : ℝ) (d2WiderTransfer334Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer334Lo, d2WiderTransfer334Hi, d2LitsNearWiderTransfers041.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer334Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2531053359280603360305 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer334Cap, d2LitsNearWiderTransfers041.q2, d2WiderTransfer334C0, d2WiderTransfer334S0, d2WiderTransfer334C1, d2WiderTransfer334S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202783377538892383218737 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2531053359280603360305 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece29 (x : ℝ) (hx : x ∈ Icc ((((1361300837 : ℚ) / 2147483648) : ℚ) : ℝ) ((((681489279 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope29 x hx
  have hxT : x ∈ Icc (d2WiderTransfer337Lo : ℝ) (d2WiderTransfer337Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer337Lo, d2WiderTransfer337Hi, d2LitsNearWiderTransfers042.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer337Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1302310057795335633989 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer337Cap, d2LitsNearWiderTransfers042.q2, d2WiderTransfer337C0, d2WiderTransfer337S0, d2WiderTransfer337C1, d2WiderTransfer337S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601428472147601225563205 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1302310057795335633989 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece30 (x : ℝ) (hx : x ∈ Icc ((((681489279 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1364656279 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope30 x hx
  have hxT : x ∈ Icc (d2WiderTransfer340Lo : ℝ) (d2WiderTransfer340Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer340Lo, d2WiderTransfer340Hi, d2LitsNearWiderTransfers042.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer340Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2678343852355371081821 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer340Cap, d2LitsNearWiderTransfers042.q2, d2WiderTransfer340C0, d2WiderTransfer340S0, d2WiderTransfer340C1, d2WiderTransfer340S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202930668031967150940253 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2678343852355371081821 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece31 (x : ℝ) (hx : x ∈ Icc ((((1364656279 : ℚ) / 2147483648) : ℚ) : ℝ) ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope31 x hx
  have hxT : x ∈ Icc (d2WiderTransfer343Lo : ℝ) (d2WiderTransfer343Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer343Lo, d2WiderTransfer343Hi, d2LitsNearWiderTransfers042.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer343Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2752225243658253026133 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer343Cap, d2LitsNearWiderTransfers042.q2, d2WiderTransfer343C0, d2WiderTransfer343S0, d2WiderTransfer343C1, d2WiderTransfer343S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1203004549423270032884565 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2752225243658253026133 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece32 (x : ℝ) (hx : x ∈ Icc ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ) ((((1368011721 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope32 x hx
  have hxT : x ∈ Icc (d2WiderTransfer346Lo : ℝ) (d2WiderTransfer346Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer346Lo, d2WiderTransfer346Hi, d2LitsNearWiderTransfers043.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer346Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2826264967930141037325 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer346Cap, d2LitsNearWiderTransfers043.q2, d2WiderTransfer346C0, d2WiderTransfer346S0, d2WiderTransfer346C1, d2WiderTransfer346S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1203078589147541920895757 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2826264967930141037325 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece33 (x : ℝ) (hx : x ∈ Icc ((((1368011721 : ℚ) / 2147483648) : ℚ) : ℝ) ((((684844721 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope33 x hx
  have hxT : x ∈ Icc (d2WiderTransfer349Lo : ℝ) (d2WiderTransfer349Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer349Lo, d2WiderTransfer349Hi, d2LitsNearWiderTransfers043.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer349Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1450231853993301240833 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer349Cap, d2LitsNearWiderTransfers043.q2, d2WiderTransfer349C0, d2WiderTransfer349S0, d2WiderTransfer349C1, d2WiderTransfer349S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601576393943799191170049 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1450231853993301240833 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece34 (x : ℝ) (hx : x ∈ Icc ((((684844721 : ℚ) / 1073741824) : ℚ) : ℝ) ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope34 x hx
  have hxT : x ∈ Icc (d2WiderTransfer352Lo : ℝ) (d2WiderTransfer352Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer352Lo, d2WiderTransfer352Hi, d2LitsNearWiderTransfers044.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer352Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3049340988866887689691 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer352Cap, d2LitsNearWiderTransfers044.q2, d2WiderTransfer352C0, d2WiderTransfer352S0, d2WiderTransfer352C1, d2WiderTransfer352S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1203301665168478667548123 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((3049340988866887689691 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece35 (x : ℝ) (hx : x ∈ Icc ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ) ((((688200163 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope35 x hx
  have hxT : x ∈ Icc (d2WiderTransfer355Lo : ℝ) (d2WiderTransfer355Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer355Lo, d2WiderTransfer355Hi, d2LitsNearWiderTransfers044.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer355Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1599431318984013064275 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer355Cap, d2LitsNearWiderTransfers044.q2, d2WiderTransfer355C0, d2WiderTransfer355S0, d2WiderTransfer355C1, d2WiderTransfer355S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601725593408789902993491 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1599431318984013064275 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece36 (x : ℝ) (hx : x ∈ Icc ((((688200163 : ℚ) / 1073741824) : ℚ) : ℝ) ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope36 x hx
  have hxT : x ∈ Icc (d2WiderTransfer358Lo : ℝ) (d2WiderTransfer358Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer358Lo, d2WiderTransfer358Hi, d2LitsNearWiderTransfers044.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer358Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((837258569895468822063 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer358Cap, d2LitsNearWiderTransfers044.q2, d2WiderTransfer358C0, d2WiderTransfer358S0, d2WiderTransfer358C1, d2WiderTransfer358S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-300900339614798413786671 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((837258569895468822063 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece37 (x : ℝ) (hx : x ∈ Icc ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ) ((((346616663 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope37 x hx
  have hxT : x ∈ Icc (d2WiderTransfer361Lo : ℝ) (d2WiderTransfer361Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer361Lo, d2WiderTransfer361Hi, d2LitsNearWiderTransfers045.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer361Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3651350408292595360187 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer361Cap, d2LitsNearWiderTransfers045.q2, d2WiderTransfer361C0, d2WiderTransfer361S0, d2WiderTransfer361C1, d2WiderTransfer361S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1203903674587904375218619 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((3651350408292595360187 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece38 (x : ℝ) (hx : x ∈ Icc ((((346616663 : ℚ) / 536870912) : ℚ) : ℝ) ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope38 x hx
  have hxT : x ∈ Icc (d2WiderTransfer364Lo : ℝ) (d2WiderTransfer364Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer364Lo, d2WiderTransfer364Hi, d2LitsNearWiderTransfers045.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer364Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3956335870851972903335 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer364Cap, d2LitsNearWiderTransfers045.q2, d2WiderTransfer364C0, d2WiderTransfer364S0, d2WiderTransfer364C1, d2WiderTransfer364S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1204208660050463752761767 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((3956335870851972903335 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece39 (x : ℝ) (hx : x ∈ Icc ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ) ((((175824913 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope39 x hx
  have hxT : x ∈ Icc (d2WiderTransfer367Lo : ℝ) (d2WiderTransfer367Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer367Lo, d2WiderTransfer367Hi, d2LitsNearWiderTransfers045.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer367Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1143626764448916994303 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer367Cap, d2LitsNearWiderTransfers045.q2, d2WiderTransfer367C0, d2WiderTransfer367S0, d2WiderTransfer367C1, d2WiderTransfer367S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-301206707809351861958911 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((1143626764448916994303 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece40 (x : ℝ) (hx : x ∈ Icc ((((175824913 : ℚ) / 268435456) : ℚ) : ℝ) ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope40 x hx
  have hxT : x ∈ Icc (d2WiderTransfer370Lo : ℝ) (d2WiderTransfer370Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer370Lo, d2WiderTransfer370Hi, d2LitsNearWiderTransfers046.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer370Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((325246597409181460825 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer370Cap, d2LitsNearWiderTransfers046.q2, d2WiderTransfer370C0, d2WiderTransfer370S0, d2WiderTransfer370C1, d2WiderTransfer370S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-75341016858634917701977 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) + ((((325246597409181460825 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece41 (x : ℝ) (hx : x ∈ Icc ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ) ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope41 x hx
  have hxT : x ∈ Icc (d2WiderTransfer373Lo : ℝ) (d2WiderTransfer373Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer373Lo, d2WiderTransfer373Hi, d2LitsNearWiderTransfers046.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer373Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1624582038057085385233 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer373Cap, d2LitsNearWiderTransfers046.q2, d2WiderTransfer373C0, d2WiderTransfer373S0, d2WiderTransfer373C1, d2WiderTransfer373S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-301687663082960030349841 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((1624582038057085385233 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece42 (x : ℝ) (hx : x ∈ Icc ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ) ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope42 x hx
  have hxT : x ∈ Icc (d2WiderTransfer376Lo : ℝ) (d2WiderTransfer376Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer376Lo, d2WiderTransfer376Hi, d2LitsNearWiderTransfers047.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer376Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4621244410980826169991 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer376Cap, d2LitsNearWiderTransfers047.q2, d2WiderTransfer376C0, d2WiderTransfer376S0, d2WiderTransfer376C1, d2WiderTransfer376S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-604747406500786716099207 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((4621244410980826169991 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece43 (x : ℝ) (hx : x ∈ Icc ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ) ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope43 x hx
  have hxT : x ∈ Icc (d2WiderTransfer379Lo : ℝ) (d2WiderTransfer379Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer379Lo, d2WiderTransfer379Hi, d2LitsNearWiderTransfers047.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer379Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((15487665051695413563023 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer379Cap, d2LitsNearWiderTransfers047.q2, d2WiderTransfer379C0, d2WiderTransfer379S0, d2WiderTransfer379C1, d2WiderTransfer379S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1215739989231307193421455 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((15487665051695413563023 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece44 (x : ℝ) (hx : x ∈ Icc ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ) ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope44 x hx
  have hxT : x ∈ Icc (d2WiderTransfer382Lo : ℝ) (d2WiderTransfer382Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer382Lo, d2WiderTransfer382Hi, d2LitsNearWiderTransfers047.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer382Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((23120299455999289732387 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer382Cap, d2LitsNearWiderTransfers047.q2, d2WiderTransfer382C0, d2WiderTransfer382S0, d2WiderTransfer382C1, d2WiderTransfer382S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1223372623635611069590819 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((23120299455999289732387 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece45 (x : ℝ) (hx : x ∈ Icc ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ) ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope45 x hx
  have hxT : x ∈ Icc (d2WiderTransfer385Lo : ℝ) (d2WiderTransfer385Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer385Lo, d2WiderTransfer385Hi, d2LitsNearWiderTransfers048.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer385Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((23367751745919880545269 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer385Cap, d2LitsNearWiderTransfers048.q2, d2WiderTransfer385C0, d2WiderTransfer385S0, d2WiderTransfer385C1, d2WiderTransfer385S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-623493913835725770474485 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((23367751745919880545269 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece46 (x : ℝ) (hx : x ∈ Icc ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ) ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope46 x hx
  have hxT : x ∈ Icc (d2WiderTransfer388Lo : ℝ) (d2WiderTransfer388Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer388Lo, d2WiderTransfer388Hi, d2LitsNearWiderTransfers048.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer388Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((70130163914806848594295 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer388Cap, d2LitsNearWiderTransfers048.q2, d2WiderTransfer388C0, d2WiderTransfer388S0, d2WiderTransfer388C1, d2WiderTransfer388S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1270382488094418628452727 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((70130163914806848594295 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece47 (x : ℝ) (hx : x ∈ Icc ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ) ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope47 x hx
  have hxT : x ∈ Icc (d2WiderTransfer391Lo : ℝ) (d2WiderTransfer391Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer391Lo, d2WiderTransfer391Hi, d2LitsNearWiderTransfers048.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer391Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((93112764016943910637209 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer391Cap, d2LitsNearWiderTransfers048.q2, d2WiderTransfer391C0, d2WiderTransfer391S0, d2WiderTransfer391C1, d2WiderTransfer391S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1293365088196555690495641 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((93112764016943910637209 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece48 (x : ℝ) (hx : x ∈ Icc ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ) ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope48 x hx
  have hxT : x ∈ Icc (d2WiderTransfer394Lo : ℝ) (d2WiderTransfer394Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer394Lo, d2WiderTransfer394Hi, d2LitsNearWiderTransfers049.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer394Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((197647006248660188417815 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer394Cap, d2LitsNearWiderTransfers049.q2, d2WiderTransfer394C0, d2WiderTransfer394S0, d2WiderTransfer394C1, d2WiderTransfer394S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1397899330428271968276247 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((197647006248660188417815 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece49 (x : ℝ) (hx : x ∈ Icc ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ) ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope49 x hx
  have hxT : x ∈ Icc (d2WiderTransfer397Lo : ℝ) (d2WiderTransfer397Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer397Lo, d2WiderTransfer397Hi, d2LitsNearWiderTransfers049.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer397Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((51336090597617681143313 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer397Cap, d2LitsNearWiderTransfers049.q2, d2WiderTransfer397C0, d2WiderTransfer397S0, d2WiderTransfer397C1, d2WiderTransfer397S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-351399171642520626107921 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((51336090597617681143313 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece50 (x : ℝ) (hx : x ∈ Icc ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope50 x hx
  have hxT : x ∈ Icc (d2WiderTransfer400Lo : ℝ) (d2WiderTransfer400Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer400Lo, d2WiderTransfer400Hi, d2LitsNearWiderTransfers050.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer400Bound x hxT
  have hd : ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((102672983640873595763659 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer400Cap, d2LitsNearWiderTransfers050.q2, d2WiderTransfer400C0, d2WiderTransfer400S0, d2WiderTransfer400C1, d2WiderTransfer400S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-702799145730679485692875 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((102672983640873595763659 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner1Domain0Pieces : List (ℚ × ℚ) := [(((98749 : ℚ) / 1000000), ((828367 : ℚ) / 8388608)), (((828367 : ℚ) / 8388608), ((8304657 : ℚ) / 67108864)), (((8304657 : ℚ) / 67108864), ((4991189 : ℚ) / 33554432)), (((4991189 : ℚ) / 33554432), ((3334455 : ℚ) / 16777216)), (((3334455 : ℚ) / 16777216), ((313261 : ℚ) / 1048576)), (((313261 : ℚ) / 1048576), ((6689897 : ℚ) / 16777216)), (((6689897 : ℚ) / 16777216), ((4183809 : ℚ) / 8388608)), (((4183809 : ℚ) / 8388608), ((18412957 : ℚ) / 33554432)), (((18412957 : ℚ) / 33554432), ((38503635 : ℚ) / 67108864)), (((38503635 : ℚ) / 67108864), ((10045339 : ℚ) / 16777216)), (((10045339 : ℚ) / 16777216), ((162403145 : ℚ) / 268435456)), (((162403145 : ℚ) / 268435456), ((82040433 : ℚ) / 134217728)), (((82040433 : ℚ) / 134217728), ((329839453 : ℚ) / 536870912)), (((329839453 : ℚ) / 536870912), ((165758587 : ℚ) / 268435456)), (((165758587 : ℚ) / 268435456), ((333194895 : ℚ) / 536870912)), (((333194895 : ℚ) / 536870912), ((668067511 : ℚ) / 1073741824)), (((668067511 : ℚ) / 1073741824), ((41859077 : ℚ) / 67108864)), (((41859077 : ℚ) / 67108864), ((671422953 : ℚ) / 1073741824)), (((671422953 : ℚ) / 1073741824), ((1344523627 : ℚ) / 2147483648)), (((1344523627 : ℚ) / 2147483648), ((336550337 : ℚ) / 536870912)), (((336550337 : ℚ) / 536870912), ((1347879069 : ℚ) / 2147483648)), (((1347879069 : ℚ) / 2147483648), ((674778395 : ℚ) / 1073741824)), (((674778395 : ℚ) / 1073741824), ((1351234511 : ℚ) / 2147483648)), (((1351234511 : ℚ) / 2147483648), ((169114029 : ℚ) / 268435456)), (((169114029 : ℚ) / 268435456), ((1354589953 : ℚ) / 2147483648)), (((1354589953 : ℚ) / 2147483648), ((678133837 : ℚ) / 1073741824)), (((678133837 : ℚ) / 1073741824), ((1357945395 : ℚ) / 2147483648)), (((1357945395 : ℚ) / 2147483648), ((339905779 : ℚ) / 536870912)), (((339905779 : ℚ) / 536870912), ((1361300837 : ℚ) / 2147483648)), (((1361300837 : ℚ) / 2147483648), ((681489279 : ℚ) / 1073741824)), (((681489279 : ℚ) / 1073741824), ((1364656279 : ℚ) / 2147483648)), (((1364656279 : ℚ) / 2147483648), ((85395875 : ℚ) / 134217728)), (((85395875 : ℚ) / 134217728), ((1368011721 : ℚ) / 2147483648)), (((1368011721 : ℚ) / 2147483648), ((684844721 : ℚ) / 1073741824)), (((684844721 : ℚ) / 1073741824), ((343261221 : ℚ) / 536870912)), (((343261221 : ℚ) / 536870912), ((688200163 : ℚ) / 1073741824)), (((688200163 : ℚ) / 1073741824), ((172469471 : ℚ) / 268435456)), (((172469471 : ℚ) / 268435456), ((346616663 : ℚ) / 536870912)), (((346616663 : ℚ) / 536870912), ((21768399 : ℚ) / 33554432)), (((21768399 : ℚ) / 33554432), ((175824913 : ℚ) / 268435456)), (((175824913 : ℚ) / 268435456), ((88751317 : ℚ) / 134217728)), (((88751317 : ℚ) / 134217728), ((45214519 : ℚ) / 67108864)), (((45214519 : ℚ) / 67108864), ((2930765 : ℚ) / 4194304)), (((2930765 : ℚ) / 4194304), ((25123841 : ℚ) / 33554432)), (((25123841 : ℚ) / 33554432), ((13400781 : ℚ) / 16777216)), (((13400781 : ℚ) / 16777216), ((7539251 : ℚ) / 8388608)), (((7539251 : ℚ) / 8388608), ((31834725 : ℚ) / 33554432)), (((31834725 : ℚ) / 33554432), ((65347171 : ℚ) / 67108864)), (((65347171 : ℚ) / 67108864), ((16756223 : ℚ) / 16777216)), (((16756223 : ℚ) / 16777216), ((8380219 : ℚ) / 8388608)), (((8380219 : ℚ) / 8388608), ((999 : ℚ) / 1000))]
theorem corner1Domain0Cover : pieceCover ((999 : ℚ) / 1000) ((98749 : ℚ) / 1000000) corner1Domain0Pieces = true := by decide +kernel
theorem corner1Domain0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  apply pieceCover_bound ((999 : ℚ) / 1000) (fun x : ℝ => fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x) ((((-34113222801 : ℚ) / 34359738368) : ℚ) : ℝ) ((98749 : ℚ) / 1000000) corner1Domain0Pieces (by decide +kernel) corner1Domain0Cover
  intro p hp
  simp only [corner1Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner1Piece0
  · exact corner1Piece1
  · exact corner1Piece2
  · exact corner1Piece3
  · exact corner1Piece4
  · exact corner1Piece5
  · exact corner1Piece6
  · exact corner1Piece7
  · exact corner1Piece8
  · exact corner1Piece9
  · exact corner1Piece10
  · exact corner1Piece11
  · exact corner1Piece12
  · exact corner1Piece13
  · exact corner1Piece14
  · exact corner1Piece15
  · exact corner1Piece16
  · exact corner1Piece17
  · exact corner1Piece18
  · exact corner1Piece19
  · exact corner1Piece20
  · exact corner1Piece21
  · exact corner1Piece22
  · exact corner1Piece23
  · exact corner1Piece24
  · exact corner1Piece25
  · exact corner1Piece26
  · exact corner1Piece27
  · exact corner1Piece28
  · exact corner1Piece29
  · exact corner1Piece30
  · exact corner1Piece31
  · exact corner1Piece32
  · exact corner1Piece33
  · exact corner1Piece34
  · exact corner1Piece35
  · exact corner1Piece36
  · exact corner1Piece37
  · exact corner1Piece38
  · exact corner1Piece39
  · exact corner1Piece40
  · exact corner1Piece41
  · exact corner1Piece42
  · exact corner1Piece43
  · exact corner1Piece44
  · exact corner1Piece45
  · exact corner1Piece46
  · exact corner1Piece47
  · exact corner1Piece48
  · exact corner1Piece49
  · exact corner1Piece50
#print axioms corner1Domain0Cover
#print axioms corner1Domain0
theorem delta2Check : fieldNFCheck D72.NearCorners002.delta2 (fqSum [logFQ ((23 : ℚ) / 800) ((-1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta2Value (x : ℝ) : fval D72.NearCorners002.delta2 x = ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta2Check x
  change fval D72.NearCorners002.delta2 x = fval (fqSum [logFQ ((23 : ℚ) / 800) ((-1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner2Identity (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x = (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) + (((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  rw [D72.NearCorners002.corner2Value, delta2Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) x, D72.NearCorners002.corner2Terms, laurentNF_sound, ← D72.NearBinding002.termsValue x]
  ring
theorem corner2Piece0 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((828367 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer251Lo : ℝ) (d2WiderTransfer251Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer251Lo, d2WiderTransfer251Hi, d2LitsNearWiderTransfers031.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer251Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer251Cap, d2LitsNearWiderTransfers031.q2, d2WiderTransfer251C0, d2WiderTransfer251S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece1 (x : ℝ) (hx : x ∈ Icc ((((828367 : ℚ) / 8388608) : ℚ) : ℝ) ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer254Lo : ℝ) (d2WiderTransfer254Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer254Lo, d2WiderTransfer254Hi, d2LitsNearWiderTransfers031.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer254Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer254Cap, d2LitsNearWiderTransfers031.q2, d2WiderTransfer254C0, d2WiderTransfer254S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece2 (x : ℝ) (hx : x ∈ Icc ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ) ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer257Lo : ℝ) (d2WiderTransfer257Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer257Lo, d2WiderTransfer257Hi, d2LitsNearWiderTransfers032.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer257Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer257Cap, d2LitsNearWiderTransfers032.q2, d2WiderTransfer257C0, d2WiderTransfer257S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece3 (x : ℝ) (hx : x ∈ Icc ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ) ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer260Lo : ℝ) (d2WiderTransfer260Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer260Lo, d2WiderTransfer260Hi, d2LitsNearWiderTransfers032.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer260Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer260Cap, d2LitsNearWiderTransfers032.q2, d2WiderTransfer260C0, d2WiderTransfer260S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece4 (x : ℝ) (hx : x ∈ Icc ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ) ((((313261 : ℚ) / 1048576) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer263Lo : ℝ) (d2WiderTransfer263Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer263Lo, d2WiderTransfer263Hi, d2LitsNearWiderTransfers032.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer263Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer263Cap, d2LitsNearWiderTransfers032.q2, d2WiderTransfer263C0, d2WiderTransfer263S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece5 (x : ℝ) (hx : x ∈ Icc ((((313261 : ℚ) / 1048576) : ℚ) : ℝ) ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer266Lo : ℝ) (d2WiderTransfer266Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer266Lo, d2WiderTransfer266Hi, d2LitsNearWiderTransfers033.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer266Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer266Cap, d2LitsNearWiderTransfers033.q2, d2WiderTransfer266C0, d2WiderTransfer266S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece6 (x : ℝ) (hx : x ∈ Icc ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ) ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer269Lo : ℝ) (d2WiderTransfer269Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer269Lo, d2WiderTransfer269Hi, d2LitsNearWiderTransfers033.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer269Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer269Cap, d2LitsNearWiderTransfers033.q2, d2WiderTransfer269C0, d2WiderTransfer269S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece7 (x : ℝ) (hx : x ∈ Icc ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ) ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer272Lo : ℝ) (d2WiderTransfer272Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer272Lo, d2WiderTransfer272Hi, d2LitsNearWiderTransfers034.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer272Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer272Cap, d2LitsNearWiderTransfers034.q2, d2WiderTransfer272C0, d2WiderTransfer272S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece8 (x : ℝ) (hx : x ∈ Icc ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ) ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer275Lo : ℝ) (d2WiderTransfer275Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer275Lo, d2WiderTransfer275Hi, d2LitsNearWiderTransfers034.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer275Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer275Cap, d2LitsNearWiderTransfers034.q2, d2WiderTransfer275C0, d2WiderTransfer275S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece9 (x : ℝ) (hx : x ∈ Icc ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ) ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope9 x hx
  have hxT : x ∈ Icc (d2WiderTransfer278Lo : ℝ) (d2WiderTransfer278Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer278Lo, d2WiderTransfer278Hi, d2LitsNearWiderTransfers034.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer278Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer278Cap, d2LitsNearWiderTransfers034.q2, d2WiderTransfer278C0, d2WiderTransfer278S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece10 (x : ℝ) (hx : x ∈ Icc ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ) ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope10 x hx
  have hxT : x ∈ Icc (d2WiderTransfer281Lo : ℝ) (d2WiderTransfer281Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer281Lo, d2WiderTransfer281Hi, d2LitsNearWiderTransfers035.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer281Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer281Cap, d2LitsNearWiderTransfers035.q2, d2WiderTransfer281C0, d2WiderTransfer281S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((15113656175 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece11 (x : ℝ) (hx : x ∈ Icc ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ) ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope11 x hx
  have hxT : x ∈ Icc (d2WiderTransfer284Lo : ℝ) (d2WiderTransfer284Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer284Lo, d2WiderTransfer284Hi, d2LitsNearWiderTransfers035.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer284Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4156949902276841309337 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer284Cap, d2LitsNearWiderTransfers035.q2, d2WiderTransfer284C0, d2WiderTransfer284S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-300387081978698214540441 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((4156949902276841309337 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece12 (x : ℝ) (hx : x ∈ Icc ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ) ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope12 x hx
  have hxT : x ∈ Icc (d2WiderTransfer287Lo : ℝ) (d2WiderTransfer287Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer287Lo, d2WiderTransfer287Hi, d2LitsNearWiderTransfers035.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer287Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4161645935709016061619 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer287Cap, d2LitsNearWiderTransfers035.q2, d2WiderTransfer287C0, d2WiderTransfer287S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-300391778012130389292723 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((4161645935709016061619 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece13 (x : ℝ) (hx : x ∈ Icc ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ) ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope13 x hx
  have hxT : x ∈ Icc (d2WiderTransfer290Lo : ℝ) (d2WiderTransfer290Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer290Lo, d2WiderTransfer290Hi, d2LitsNearWiderTransfers036.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer290Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((16713798286075332465883 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer290Cap, d2LitsNearWiderTransfers036.q2, d2WiderTransfer290C0, d2WiderTransfer290S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1201634326591760825390299 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((16713798286075332465883 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece14 (x : ℝ) (hx : x ∈ Icc ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ) ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope14 x hx
  have hxT : x ∈ Icc (d2WiderTransfer293Lo : ℝ) (d2WiderTransfer293Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer293Lo, d2WiderTransfer293Hi, d2LitsNearWiderTransfers036.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer293Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((16780883096428112327465 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer293Cap, d2LitsNearWiderTransfers036.q2, d2WiderTransfer293C0, d2WiderTransfer293S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1201701411402113605251881 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((16780883096428112327465 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece15 (x : ℝ) (hx : x ∈ Icc ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ) ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope15 x hx
  have hxT : x ∈ Icc (d2WiderTransfer296Lo : ℝ) (d2WiderTransfer296Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer296Lo, d2WiderTransfer296Hi, d2LitsNearWiderTransfers037.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer296Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((16814377008084446589281 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer296Cap, d2LitsNearWiderTransfers037.q2, d2WiderTransfer296C0, d2WiderTransfer296S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1201734905313769939513697 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((16814377008084446589281 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece16 (x : ℝ) (hx : x ∈ Icc ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ) ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope16 x hx
  have hxT : x ∈ Icc (d2WiderTransfer299Lo : ℝ) (d2WiderTransfer299Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer299Lo, d2WiderTransfer299Hi, d2LitsNearWiderTransfers037.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer299Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((16920467601962736422921 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer299Cap, d2LitsNearWiderTransfers037.q2, d2WiderTransfer299C0, d2WiderTransfer299S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1201840995907648229347337 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((16920467601962736422921 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece17 (x : ℝ) (hx : x ∈ Icc ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ) ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope17 x hx
  have hxT : x ∈ Icc (d2WiderTransfer302Lo : ℝ) (d2WiderTransfer302Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer302Lo, d2WiderTransfer302Hi, d2LitsNearWiderTransfers037.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer302Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4265946769536687764057 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer302Cap, d2LitsNearWiderTransfers037.q2, d2WiderTransfer302C0, d2WiderTransfer302S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-300496078845958060995161 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((4265946769536687764057 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece18 (x : ℝ) (hx : x ∈ Icc ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope18 x hx
  have hxT : x ∈ Icc (d2WiderTransfer305Lo : ℝ) (d2WiderTransfer305Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer305Lo, d2WiderTransfer305Hi, d2LitsNearWiderTransfers038.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer305Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17135670331982798049605 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer305Cap, d2LitsNearWiderTransfers038.q2, d2WiderTransfer305C0, d2WiderTransfer305S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202056198637668290974021 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((17135670331982798049605 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece19 (x : ℝ) (hx : x ∈ Icc ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ) ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope19 x hx
  have hxT : x ∈ Icc (d2WiderTransfer308Lo : ℝ) (d2WiderTransfer308Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer308Lo, d2WiderTransfer308Hi, d2LitsNearWiderTransfers038.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer308Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((8603851713973971473379 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer308Cap, d2LitsNearWiderTransfers038.q2, d2WiderTransfer308C0, d2WiderTransfer308S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601064115866816717935587 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((8603851713973971473379 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece20 (x : ℝ) (hx : x ∈ Icc ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ) ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope20 x hx
  have hxT : x ∈ Icc (d2WiderTransfer311Lo : ℝ) (d2WiderTransfer311Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer311Lo, d2WiderTransfer311Hi, d2LitsNearWiderTransfers038.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer311Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17279886994668054503823 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer311Cap, d2LitsNearWiderTransfers038.q2, d2WiderTransfer311C0, d2WiderTransfer311S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202200415300353547428239 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((17279886994668054503823 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece21 (x : ℝ) (hx : x ∈ Icc ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ) ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope21 x hx
  have hxT : x ∈ Icc (d2WiderTransfer314Lo : ℝ) (d2WiderTransfer314Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer314Lo, d2WiderTransfer314Hi, d2LitsNearWiderTransfers039.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer314Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17352221664729382135605 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer314Cap, d2LitsNearWiderTransfers039.q2, d2WiderTransfer314C0, d2WiderTransfer314S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202272749970414875060021 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((17352221664729382135605 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece22 (x : ℝ) (hx : x ∈ Icc ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope22 x hx
  have hxT : x ∈ Icc (d2WiderTransfer317Lo : ℝ) (d2WiderTransfer317Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer317Lo, d2WiderTransfer317Hi, d2LitsNearWiderTransfers039.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer317Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((8712354037355950387771 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer317Cap, d2LitsNearWiderTransfers039.q2, d2WiderTransfer317C0, d2WiderTransfer317S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601172618190198696849979 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((8712354037355950387771 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece23 (x : ℝ) (hx : x ∈ Icc ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ) ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope23 x hx
  have hxT : x ∈ Icc (d2WiderTransfer320Lo : ℝ) (d2WiderTransfer320Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer320Lo, d2WiderTransfer320Hi, d2LitsNearWiderTransfers040.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer320Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17497346865223007396799 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer320Cap, d2LitsNearWiderTransfers040.q2, d2WiderTransfer320C0, d2WiderTransfer320S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202417875170908500321215 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((17497346865223007396799 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece24 (x : ℝ) (hx : x ∈ Icc ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ) ((((1354589953 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope24 x hx
  have hxT : x ∈ Icc (d2WiderTransfer323Lo : ℝ) (d2WiderTransfer323Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer323Lo, d2WiderTransfer323Hi, d2LitsNearWiderTransfers040.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer323Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17570138680931573654375 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer323Cap, d2LitsNearWiderTransfers040.q2, d2WiderTransfer323C0, d2WiderTransfer323S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202490666986617066578791 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((17570138680931573654375 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece25 (x : ℝ) (hx : x ∈ Icc ((((1354589953 : ℚ) / 2147483648) : ℚ) : ℝ) ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope25 x hx
  have hxT : x ∈ Icc (d2WiderTransfer326Lo : ℝ) (d2WiderTransfer326Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer326Lo, d2WiderTransfer326Hi, d2LitsNearWiderTransfers040.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer326Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((8821542085301179587119 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer326Cap, d2LitsNearWiderTransfers040.q2, d2WiderTransfer326C0, d2WiderTransfer326S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601281806238143926049327 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((8821542085301179587119 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece26 (x : ℝ) (hx : x ∈ Icc ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1357945395 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope26 x hx
  have hxT : x ∈ Icc (d2WiderTransfer329Lo : ℝ) (d2WiderTransfer329Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer329Lo, d2WiderTransfer329Hi, d2LitsNearWiderTransfers041.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer329Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((8858091993565395041371 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer329Cap, d2LitsNearWiderTransfers041.q2, d2WiderTransfer329C0, d2WiderTransfer329S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601318356146408141503579 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((8858091993565395041371 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece27 (x : ℝ) (hx : x ∈ Icc ((((1357945395 : ℚ) / 2147483648) : ℚ) : ℝ) ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope27 x hx
  have hxT : x ∈ Icc (d2WiderTransfer332Lo : ℝ) (d2WiderTransfer332Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer332Lo, d2WiderTransfer332Hi, d2LitsNearWiderTransfers041.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer332Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((8894719393789053718993 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer332Cap, d2LitsNearWiderTransfers041.q2, d2WiderTransfer332C0, d2WiderTransfer332S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601354983546631800181201 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((8894719393789053718993 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece28 (x : ℝ) (hx : x ∈ Icc ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ) ((((1361300837 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope28 x hx
  have hxT : x ∈ Icc (d2WiderTransfer335Lo : ℝ) (d2WiderTransfer335Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer335Lo, d2WiderTransfer335Hi, d2LitsNearWiderTransfers041.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer335Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17862849233206890294321 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer335Cap, d2LitsNearWiderTransfers041.q2, d2WiderTransfer335C0, d2WiderTransfer335S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202783377538892383218737 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((17862849233206890294321 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece29 (x : ℝ) (hx : x ∈ Icc ((((1361300837 : ℚ) / 2147483648) : ℚ) : ℝ) ((((681489279 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope29 x hx
  have hxT : x ∈ Icc (d2WiderTransfer338Lo : ℝ) (d2WiderTransfer338Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer338Lo, d2WiderTransfer338Hi, d2LitsNearWiderTransfers042.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer338Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((8968207994758479100997 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer338Cap, d2LitsNearWiderTransfers042.q2, d2WiderTransfer338C0, d2WiderTransfer338S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601428472147601225563205 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((8968207994758479100997 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece30 (x : ℝ) (hx : x ∈ Icc ((((681489279 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1364656279 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope30 x hx
  have hxT : x ∈ Icc (d2WiderTransfer341Lo : ℝ) (d2WiderTransfer341Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer341Lo, d2WiderTransfer341Hi, d2LitsNearWiderTransfers042.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer341Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((18010139726281658015837 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer341Cap, d2LitsNearWiderTransfers042.q2, d2WiderTransfer341C0, d2WiderTransfer341S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202930668031967150940253 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((18010139726281658015837 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece31 (x : ℝ) (hx : x ∈ Icc ((((1364656279 : ℚ) / 2147483648) : ℚ) : ℝ) ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope31 x hx
  have hxT : x ∈ Icc (d2WiderTransfer344Lo : ℝ) (d2WiderTransfer344Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer344Lo, d2WiderTransfer344Hi, d2LitsNearWiderTransfers043.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer344Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((18084021117584539960149 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer344Cap, d2LitsNearWiderTransfers043.q2, d2WiderTransfer344C0, d2WiderTransfer344S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1203004549423270032884565 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((18084021117584539960149 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece32 (x : ℝ) (hx : x ∈ Icc ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ) ((((1368011721 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope32 x hx
  have hxT : x ∈ Icc (d2WiderTransfer347Lo : ℝ) (d2WiderTransfer347Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer347Lo, d2WiderTransfer347Hi, d2LitsNearWiderTransfers043.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer347Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((18158060841856427971341 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer347Cap, d2LitsNearWiderTransfers043.q2, d2WiderTransfer347C0, d2WiderTransfer347S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1203078589147541920895757 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((18158060841856427971341 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece33 (x : ℝ) (hx : x ∈ Icc ((((1368011721 : ℚ) / 2147483648) : ℚ) : ℝ) ((((684844721 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope33 x hx
  have hxT : x ∈ Icc (d2WiderTransfer350Lo : ℝ) (d2WiderTransfer350Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer350Lo, d2WiderTransfer350Hi, d2LitsNearWiderTransfers043.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer350Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((9116129790956444707841 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer350Cap, d2LitsNearWiderTransfers043.q2, d2WiderTransfer350C0, d2WiderTransfer350S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601576393943799191170049 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((9116129790956444707841 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece34 (x : ℝ) (hx : x ∈ Icc ((((684844721 : ℚ) / 1073741824) : ℚ) : ℝ) ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope34 x hx
  have hxT : x ∈ Icc (d2WiderTransfer353Lo : ℝ) (d2WiderTransfer353Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer353Lo, d2WiderTransfer353Hi, d2LitsNearWiderTransfers044.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer353Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((18381136862793174623707 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer353Cap, d2LitsNearWiderTransfers044.q2, d2WiderTransfer353C0, d2WiderTransfer353S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1203301665168478667548123 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((18381136862793174623707 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece35 (x : ℝ) (hx : x ∈ Icc ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ) ((((688200163 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope35 x hx
  have hxT : x ∈ Icc (d2WiderTransfer356Lo : ℝ) (d2WiderTransfer356Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer356Lo, d2WiderTransfer356Hi, d2LitsNearWiderTransfers044.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer356Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((9265329255947156531283 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer356Cap, d2LitsNearWiderTransfers044.q2, d2WiderTransfer356C0, d2WiderTransfer356S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601725593408789902993491 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((9265329255947156531283 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece36 (x : ℝ) (hx : x ∈ Icc ((((688200163 : ℚ) / 1073741824) : ℚ) : ℝ) ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope36 x hx
  have hxT : x ∈ Icc (d2WiderTransfer359Lo : ℝ) (d2WiderTransfer359Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer359Lo, d2WiderTransfer359Hi, d2LitsNearWiderTransfers044.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer359Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4670207538377040555567 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer359Cap, d2LitsNearWiderTransfers044.q2, d2WiderTransfer359C0, d2WiderTransfer359S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-300900339614798413786671 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((4670207538377040555567 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece37 (x : ℝ) (hx : x ∈ Icc ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ) ((((346616663 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope37 x hx
  have hxT : x ∈ Icc (d2WiderTransfer362Lo : ℝ) (d2WiderTransfer362Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer362Lo, d2WiderTransfer362Hi, d2LitsNearWiderTransfers045.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer362Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((18983146282218882294203 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer362Cap, d2LitsNearWiderTransfers045.q2, d2WiderTransfer362C0, d2WiderTransfer362S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1203903674587904375218619 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((18983146282218882294203 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece38 (x : ℝ) (hx : x ∈ Icc ((((346616663 : ℚ) / 536870912) : ℚ) : ℝ) ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope38 x hx
  have hxT : x ∈ Icc (d2WiderTransfer365Lo : ℝ) (d2WiderTransfer365Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer365Lo, d2WiderTransfer365Hi, d2LitsNearWiderTransfers045.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer365Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((19288131744778259837351 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer365Cap, d2LitsNearWiderTransfers045.q2, d2WiderTransfer365C0, d2WiderTransfer365S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1204208660050463752761767 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((19288131744778259837351 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece39 (x : ℝ) (hx : x ∈ Icc ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ) ((((175824913 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope39 x hx
  have hxT : x ∈ Icc (d2WiderTransfer368Lo : ℝ) (d2WiderTransfer368Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer368Lo, d2WiderTransfer368Hi, d2LitsNearWiderTransfers046.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer368Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4976575732930488727807 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer368Cap, d2LitsNearWiderTransfers046.q2, d2WiderTransfer368C0, d2WiderTransfer368S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-301206707809351861958911 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((4976575732930488727807 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece40 (x : ℝ) (hx : x ∈ Icc ((((175824913 : ℚ) / 268435456) : ℚ) : ℝ) ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope40 x hx
  have hxT : x ∈ Icc (d2WiderTransfer371Lo : ℝ) (d2WiderTransfer371Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer371Lo, d2WiderTransfer371Hi, d2LitsNearWiderTransfers046.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer371Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1283483839529574394201 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer371Cap, d2LitsNearWiderTransfers046.q2, d2WiderTransfer371C0, d2WiderTransfer371S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-75341016858634917701977 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) + ((((1283483839529574394201 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece41 (x : ℝ) (hx : x ∈ Icc ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ) ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope41 x hx
  have hxT : x ∈ Icc (d2WiderTransfer374Lo : ℝ) (d2WiderTransfer374Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer374Lo, d2WiderTransfer374Hi, d2LitsNearWiderTransfers046.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer374Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((5457531006538657118737 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer374Cap, d2LitsNearWiderTransfers046.q2, d2WiderTransfer374C0, d2WiderTransfer374S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-301687663082960030349841 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((5457531006538657118737 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece42 (x : ℝ) (hx : x ∈ Icc ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ) ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope42 x hx
  have hxT : x ∈ Icc (d2WiderTransfer377Lo : ℝ) (d2WiderTransfer377Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer377Lo, d2WiderTransfer377Hi, d2LitsNearWiderTransfers047.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer377Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((12287142347943969636999 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer377Cap, d2LitsNearWiderTransfers047.q2, d2WiderTransfer377C0, d2WiderTransfer377S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-604747406500786716099207 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((12287142347943969636999 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece43 (x : ℝ) (hx : x ∈ Icc ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ) ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope43 x hx
  have hxT : x ∈ Icc (d2WiderTransfer380Lo : ℝ) (d2WiderTransfer380Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer380Lo, d2WiderTransfer380Hi, d2LitsNearWiderTransfers047.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer380Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((30819460925621700497039 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer380Cap, d2LitsNearWiderTransfers047.q2, d2WiderTransfer380C0, d2WiderTransfer380S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1215739989231307193421455 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((30819460925621700497039 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece44 (x : ℝ) (hx : x ∈ Icc ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ) ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope44 x hx
  have hxT : x ∈ Icc (d2WiderTransfer383Lo : ℝ) (d2WiderTransfer383Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer383Lo, d2WiderTransfer383Hi, d2LitsNearWiderTransfers047.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer383Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((38452095329925576666403 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer383Cap, d2LitsNearWiderTransfers047.q2, d2WiderTransfer383C0, d2WiderTransfer383S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1223372623635611069590819 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((38452095329925576666403 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece45 (x : ℝ) (hx : x ∈ Icc ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ) ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope45 x hx
  have hxT : x ∈ Icc (d2WiderTransfer386Lo : ℝ) (d2WiderTransfer386Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer386Lo, d2WiderTransfer386Hi, d2LitsNearWiderTransfers048.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer386Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((31033649682883024012277 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer386Cap, d2LitsNearWiderTransfers048.q2, d2WiderTransfer386C0, d2WiderTransfer386S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-623493913835725770474485 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((31033649682883024012277 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece46 (x : ℝ) (hx : x ∈ Icc ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ) ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope46 x hx
  have hxT : x ∈ Icc (d2WiderTransfer389Lo : ℝ) (d2WiderTransfer389Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer389Lo, d2WiderTransfer389Hi, d2LitsNearWiderTransfers048.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer389Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((85461959788733135528311 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer389Cap, d2LitsNearWiderTransfers048.q2, d2WiderTransfer389C0, d2WiderTransfer389S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1270382488094418628452727 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((85461959788733135528311 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece47 (x : ℝ) (hx : x ∈ Icc ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ) ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope47 x hx
  have hxT : x ∈ Icc (d2WiderTransfer392Lo : ℝ) (d2WiderTransfer392Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer392Lo, d2WiderTransfer392Hi, d2LitsNearWiderTransfers049.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer392Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((108444559890870197571225 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer392Cap, d2LitsNearWiderTransfers049.q2, d2WiderTransfer392C0, d2WiderTransfer392S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1293365088196555690495641 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((108444559890870197571225 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece48 (x : ℝ) (hx : x ∈ Icc ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ) ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope48 x hx
  have hxT : x ∈ Icc (d2WiderTransfer395Lo : ℝ) (d2WiderTransfer395Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer395Lo, d2WiderTransfer395Hi, d2LitsNearWiderTransfers049.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer395Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((212978802122586475351831 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer395Cap, d2LitsNearWiderTransfers049.q2, d2WiderTransfer395C0, d2WiderTransfer395S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1397899330428271968276247 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((212978802122586475351831 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece49 (x : ℝ) (hx : x ∈ Icc ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ) ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope49 x hx
  have hxT : x ∈ Icc (d2WiderTransfer398Lo : ℝ) (d2WiderTransfer398Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer398Lo, d2WiderTransfer398Hi, d2LitsNearWiderTransfers049.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer398Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((55169039566099252876817 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer398Cap, d2LitsNearWiderTransfers049.q2, d2WiderTransfer398C0, d2WiderTransfer398S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-351399171642520626107921 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((55169039566099252876817 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece50 (x : ℝ) (hx : x ∈ Icc ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope50 x hx
  have hxT : x ∈ Icc (d2WiderTransfer401Lo : ℝ) (d2WiderTransfer401Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer401Lo, d2WiderTransfer401Hi, d2LitsNearWiderTransfers050.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer401Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((110338881577836739230667 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer401Cap, d2LitsNearWiderTransfers050.q2, d2WiderTransfer401C0, d2WiderTransfer401S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-702799145730679485692875 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((110338881577836739230667 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner2Domain0Pieces : List (ℚ × ℚ) := [(((98749 : ℚ) / 1000000), ((828367 : ℚ) / 8388608)), (((828367 : ℚ) / 8388608), ((8304657 : ℚ) / 67108864)), (((8304657 : ℚ) / 67108864), ((4991189 : ℚ) / 33554432)), (((4991189 : ℚ) / 33554432), ((3334455 : ℚ) / 16777216)), (((3334455 : ℚ) / 16777216), ((313261 : ℚ) / 1048576)), (((313261 : ℚ) / 1048576), ((6689897 : ℚ) / 16777216)), (((6689897 : ℚ) / 16777216), ((4183809 : ℚ) / 8388608)), (((4183809 : ℚ) / 8388608), ((18412957 : ℚ) / 33554432)), (((18412957 : ℚ) / 33554432), ((38503635 : ℚ) / 67108864)), (((38503635 : ℚ) / 67108864), ((10045339 : ℚ) / 16777216)), (((10045339 : ℚ) / 16777216), ((162403145 : ℚ) / 268435456)), (((162403145 : ℚ) / 268435456), ((82040433 : ℚ) / 134217728)), (((82040433 : ℚ) / 134217728), ((329839453 : ℚ) / 536870912)), (((329839453 : ℚ) / 536870912), ((165758587 : ℚ) / 268435456)), (((165758587 : ℚ) / 268435456), ((333194895 : ℚ) / 536870912)), (((333194895 : ℚ) / 536870912), ((668067511 : ℚ) / 1073741824)), (((668067511 : ℚ) / 1073741824), ((41859077 : ℚ) / 67108864)), (((41859077 : ℚ) / 67108864), ((671422953 : ℚ) / 1073741824)), (((671422953 : ℚ) / 1073741824), ((1344523627 : ℚ) / 2147483648)), (((1344523627 : ℚ) / 2147483648), ((336550337 : ℚ) / 536870912)), (((336550337 : ℚ) / 536870912), ((1347879069 : ℚ) / 2147483648)), (((1347879069 : ℚ) / 2147483648), ((674778395 : ℚ) / 1073741824)), (((674778395 : ℚ) / 1073741824), ((1351234511 : ℚ) / 2147483648)), (((1351234511 : ℚ) / 2147483648), ((169114029 : ℚ) / 268435456)), (((169114029 : ℚ) / 268435456), ((1354589953 : ℚ) / 2147483648)), (((1354589953 : ℚ) / 2147483648), ((678133837 : ℚ) / 1073741824)), (((678133837 : ℚ) / 1073741824), ((1357945395 : ℚ) / 2147483648)), (((1357945395 : ℚ) / 2147483648), ((339905779 : ℚ) / 536870912)), (((339905779 : ℚ) / 536870912), ((1361300837 : ℚ) / 2147483648)), (((1361300837 : ℚ) / 2147483648), ((681489279 : ℚ) / 1073741824)), (((681489279 : ℚ) / 1073741824), ((1364656279 : ℚ) / 2147483648)), (((1364656279 : ℚ) / 2147483648), ((85395875 : ℚ) / 134217728)), (((85395875 : ℚ) / 134217728), ((1368011721 : ℚ) / 2147483648)), (((1368011721 : ℚ) / 2147483648), ((684844721 : ℚ) / 1073741824)), (((684844721 : ℚ) / 1073741824), ((343261221 : ℚ) / 536870912)), (((343261221 : ℚ) / 536870912), ((688200163 : ℚ) / 1073741824)), (((688200163 : ℚ) / 1073741824), ((172469471 : ℚ) / 268435456)), (((172469471 : ℚ) / 268435456), ((346616663 : ℚ) / 536870912)), (((346616663 : ℚ) / 536870912), ((21768399 : ℚ) / 33554432)), (((21768399 : ℚ) / 33554432), ((175824913 : ℚ) / 268435456)), (((175824913 : ℚ) / 268435456), ((88751317 : ℚ) / 134217728)), (((88751317 : ℚ) / 134217728), ((45214519 : ℚ) / 67108864)), (((45214519 : ℚ) / 67108864), ((2930765 : ℚ) / 4194304)), (((2930765 : ℚ) / 4194304), ((25123841 : ℚ) / 33554432)), (((25123841 : ℚ) / 33554432), ((13400781 : ℚ) / 16777216)), (((13400781 : ℚ) / 16777216), ((7539251 : ℚ) / 8388608)), (((7539251 : ℚ) / 8388608), ((31834725 : ℚ) / 33554432)), (((31834725 : ℚ) / 33554432), ((65347171 : ℚ) / 67108864)), (((65347171 : ℚ) / 67108864), ((16756223 : ℚ) / 16777216)), (((16756223 : ℚ) / 16777216), ((8380219 : ℚ) / 8388608)), (((8380219 : ℚ) / 8388608), ((999 : ℚ) / 1000))]
theorem corner2Domain0Cover : pieceCover ((999 : ℚ) / 1000) ((98749 : ℚ) / 1000000) corner2Domain0Pieces = true := by decide +kernel
theorem corner2Domain0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  apply pieceCover_bound ((999 : ℚ) / 1000) (fun x : ℝ => fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x) ((((-269419735629 : ℚ) / 274877906944) : ℚ) : ℝ) ((98749 : ℚ) / 1000000) corner2Domain0Pieces (by decide +kernel) corner2Domain0Cover
  intro p hp
  simp only [corner2Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner2Piece0
  · exact corner2Piece1
  · exact corner2Piece2
  · exact corner2Piece3
  · exact corner2Piece4
  · exact corner2Piece5
  · exact corner2Piece6
  · exact corner2Piece7
  · exact corner2Piece8
  · exact corner2Piece9
  · exact corner2Piece10
  · exact corner2Piece11
  · exact corner2Piece12
  · exact corner2Piece13
  · exact corner2Piece14
  · exact corner2Piece15
  · exact corner2Piece16
  · exact corner2Piece17
  · exact corner2Piece18
  · exact corner2Piece19
  · exact corner2Piece20
  · exact corner2Piece21
  · exact corner2Piece22
  · exact corner2Piece23
  · exact corner2Piece24
  · exact corner2Piece25
  · exact corner2Piece26
  · exact corner2Piece27
  · exact corner2Piece28
  · exact corner2Piece29
  · exact corner2Piece30
  · exact corner2Piece31
  · exact corner2Piece32
  · exact corner2Piece33
  · exact corner2Piece34
  · exact corner2Piece35
  · exact corner2Piece36
  · exact corner2Piece37
  · exact corner2Piece38
  · exact corner2Piece39
  · exact corner2Piece40
  · exact corner2Piece41
  · exact corner2Piece42
  · exact corner2Piece43
  · exact corner2Piece44
  · exact corner2Piece45
  · exact corner2Piece46
  · exact corner2Piece47
  · exact corner2Piece48
  · exact corner2Piece49
  · exact corner2Piece50
#print axioms corner2Domain0Cover
#print axioms corner2Domain0
theorem delta3Check : fieldNFCheck D72.NearCorners002.delta3 (fqSum [logFQ ((3 : ℚ) / 8800) ((-1 : ℚ) / 1), logFQ ((-5 : ℚ) / 176) ((1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta3Value (x : ℝ) : fval D72.NearCorners002.delta3 x = ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta3Check x
  change fval D72.NearCorners002.delta3 x = fval (fqSum [logFQ ((3 : ℚ) / 8800) ((-1 : ℚ) / 1), logFQ ((-5 : ℚ) / 176) ((1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner3Identity (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x = (fval D72.NearBinding002.literalField x + lfieldTower D72.NearBinding002.literalTerms 0 x) + (((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  rw [D72.NearCorners002.corner3Value, delta3Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) x, D72.NearCorners002.corner3Terms, laurentNF_sound, ← D72.NearBinding002.termsValue x]
  ring
theorem corner3Piece0 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((828367 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer252Lo : ℝ) (d2WiderTransfer252Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer252Lo, d2WiderTransfer252Hi, d2LitsNearWiderTransfers031.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer252Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer252Cap, d2LitsNearWiderTransfers031.q2, d2WiderTransfer252C0, d2WiderTransfer252S0, d2WiderTransfer252C1, d2WiderTransfer252S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece1 (x : ℝ) (hx : x ∈ Icc ((((828367 : ℚ) / 8388608) : ℚ) : ℝ) ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer255Lo : ℝ) (d2WiderTransfer255Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer255Lo, d2WiderTransfer255Hi, d2LitsNearWiderTransfers031.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer255Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer255Cap, d2LitsNearWiderTransfers031.q2, d2WiderTransfer255C0, d2WiderTransfer255S0, d2WiderTransfer255C1, d2WiderTransfer255S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece2 (x : ℝ) (hx : x ∈ Icc ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ) ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer258Lo : ℝ) (d2WiderTransfer258Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer258Lo, d2WiderTransfer258Hi, d2LitsNearWiderTransfers032.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer258Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer258Cap, d2LitsNearWiderTransfers032.q2, d2WiderTransfer258C0, d2WiderTransfer258S0, d2WiderTransfer258C1, d2WiderTransfer258S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece3 (x : ℝ) (hx : x ∈ Icc ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ) ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer261Lo : ℝ) (d2WiderTransfer261Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer261Lo, d2WiderTransfer261Hi, d2LitsNearWiderTransfers032.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer261Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer261Cap, d2LitsNearWiderTransfers032.q2, d2WiderTransfer261C0, d2WiderTransfer261S0, d2WiderTransfer261C1, d2WiderTransfer261S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece4 (x : ℝ) (hx : x ∈ Icc ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ) ((((313261 : ℚ) / 1048576) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer264Lo : ℝ) (d2WiderTransfer264Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer264Lo, d2WiderTransfer264Hi, d2LitsNearWiderTransfers033.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer264Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer264Cap, d2LitsNearWiderTransfers033.q2, d2WiderTransfer264C0, d2WiderTransfer264S0, d2WiderTransfer264C1, d2WiderTransfer264S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece5 (x : ℝ) (hx : x ∈ Icc ((((313261 : ℚ) / 1048576) : ℚ) : ℝ) ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer267Lo : ℝ) (d2WiderTransfer267Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer267Lo, d2WiderTransfer267Hi, d2LitsNearWiderTransfers033.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer267Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer267Cap, d2LitsNearWiderTransfers033.q2, d2WiderTransfer267C0, d2WiderTransfer267S0, d2WiderTransfer267C1, d2WiderTransfer267S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece6 (x : ℝ) (hx : x ∈ Icc ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ) ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer270Lo : ℝ) (d2WiderTransfer270Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer270Lo, d2WiderTransfer270Hi, d2LitsNearWiderTransfers033.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer270Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer270Cap, d2LitsNearWiderTransfers033.q2, d2WiderTransfer270C0, d2WiderTransfer270S0, d2WiderTransfer270C1, d2WiderTransfer270S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece7 (x : ℝ) (hx : x ∈ Icc ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ) ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer273Lo : ℝ) (d2WiderTransfer273Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer273Lo, d2WiderTransfer273Hi, d2LitsNearWiderTransfers034.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer273Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer273Cap, d2LitsNearWiderTransfers034.q2, d2WiderTransfer273C0, d2WiderTransfer273S0, d2WiderTransfer273C1, d2WiderTransfer273S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece8 (x : ℝ) (hx : x ∈ Icc ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ) ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer276Lo : ℝ) (d2WiderTransfer276Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer276Lo, d2WiderTransfer276Hi, d2LitsNearWiderTransfers034.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer276Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer276Cap, d2LitsNearWiderTransfers034.q2, d2WiderTransfer276C0, d2WiderTransfer276S0, d2WiderTransfer276C1, d2WiderTransfer276S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece9 (x : ℝ) (hx : x ∈ Icc ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ) ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope9 x hx
  have hxT : x ∈ Icc (d2WiderTransfer279Lo : ℝ) (d2WiderTransfer279Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer279Lo, d2WiderTransfer279Hi, d2LitsNearWiderTransfers034.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer279Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer279Cap, d2LitsNearWiderTransfers034.q2, d2WiderTransfer279C0, d2WiderTransfer279S0, d2WiderTransfer279C1, d2WiderTransfer279S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece10 (x : ℝ) (hx : x ∈ Icc ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ) ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope10 x hx
  have hxT : x ∈ Icc (d2WiderTransfer282Lo : ℝ) (d2WiderTransfer282Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer282Lo, d2WiderTransfer282Hi, d2LitsNearWiderTransfers035.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer282Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer282Cap, d2LitsNearWiderTransfers035.q2, d2WiderTransfer282C0, d2WiderTransfer282S0, d2WiderTransfer282C1, d2WiderTransfer282S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1092792598691 : ℚ) / 1099511627776) : ℚ) : ℝ) + ((((30439539927 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece11 (x : ℝ) (hx : x ∈ Icc ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ) ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope11 x hx
  have hxT : x ∈ Icc (d2WiderTransfer285Lo : ℝ) (d2WiderTransfer285Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer285Lo, d2WiderTransfer285Hi, d2LitsNearWiderTransfers035.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer285Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((8369696750093658883225 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer285Cap, d2LitsNearWiderTransfers035.q2, d2WiderTransfer285C0, d2WiderTransfer285S0, d2WiderTransfer285C1, d2WiderTransfer285S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-300387081978698214540441 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((8369696750093658883225 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece12 (x : ℝ) (hx : x ∈ Icc ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ) ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope12 x hx
  have hxT : x ∈ Icc (d2WiderTransfer288Lo : ℝ) (d2WiderTransfer288Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer288Lo, d2WiderTransfer288Hi, d2LitsNearWiderTransfers036.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer288Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((8374392783525833635507 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer288Cap, d2LitsNearWiderTransfers036.q2, d2WiderTransfer288C0, d2WiderTransfer288S0, d2WiderTransfer288C1, d2WiderTransfer288S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-300391778012130389292723 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((8374392783525833635507 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece13 (x : ℝ) (hx : x ∈ Icc ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ) ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope13 x hx
  have hxT : x ∈ Icc (d2WiderTransfer291Lo : ℝ) (d2WiderTransfer291Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer291Lo, d2WiderTransfer291Hi, d2LitsNearWiderTransfers036.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer291Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((33564785677342602761435 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer291Cap, d2LitsNearWiderTransfers036.q2, d2WiderTransfer291C0, d2WiderTransfer291S0, d2WiderTransfer291C1, d2WiderTransfer291S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1201634326591760825390299 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((33564785677342602761435 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece14 (x : ℝ) (hx : x ∈ Icc ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ) ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope14 x hx
  have hxT : x ∈ Icc (d2WiderTransfer294Lo : ℝ) (d2WiderTransfer294Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer294Lo, d2WiderTransfer294Hi, d2LitsNearWiderTransfers036.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer294Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((33631870487695382623017 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer294Cap, d2LitsNearWiderTransfers036.q2, d2WiderTransfer294C0, d2WiderTransfer294S0, d2WiderTransfer294C1, d2WiderTransfer294S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1201701411402113605251881 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((33631870487695382623017 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece15 (x : ℝ) (hx : x ∈ Icc ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ) ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope15 x hx
  have hxT : x ∈ Icc (d2WiderTransfer297Lo : ℝ) (d2WiderTransfer297Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer297Lo, d2WiderTransfer297Hi, d2LitsNearWiderTransfers037.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer297Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((33665364399351716884833 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer297Cap, d2LitsNearWiderTransfers037.q2, d2WiderTransfer297C0, d2WiderTransfer297S0, d2WiderTransfer297C1, d2WiderTransfer297S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1201734905313769939513697 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((33665364399351716884833 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece16 (x : ℝ) (hx : x ∈ Icc ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ) ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope16 x hx
  have hxT : x ∈ Icc (d2WiderTransfer300Lo : ℝ) (d2WiderTransfer300Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer300Lo, d2WiderTransfer300Hi, d2LitsNearWiderTransfers037.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer300Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((33771454993230006718473 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer300Cap, d2LitsNearWiderTransfers037.q2, d2WiderTransfer300C0, d2WiderTransfer300S0, d2WiderTransfer300C1, d2WiderTransfer300S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1201840995907648229347337 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((33771454993230006718473 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece17 (x : ℝ) (hx : x ∈ Icc ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ) ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope17 x hx
  have hxT : x ∈ Icc (d2WiderTransfer303Lo : ℝ) (d2WiderTransfer303Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer303Lo, d2WiderTransfer303Hi, d2LitsNearWiderTransfers037.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer303Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((8478693617353505337945 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer303Cap, d2LitsNearWiderTransfers037.q2, d2WiderTransfer303C0, d2WiderTransfer303S0, d2WiderTransfer303C1, d2WiderTransfer303S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-300496078845958060995161 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((8478693617353505337945 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece18 (x : ℝ) (hx : x ∈ Icc ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope18 x hx
  have hxT : x ∈ Icc (d2WiderTransfer306Lo : ℝ) (d2WiderTransfer306Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer306Lo, d2WiderTransfer306Hi, d2LitsNearWiderTransfers038.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer306Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((33986657723250068345157 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer306Cap, d2LitsNearWiderTransfers038.q2, d2WiderTransfer306C0, d2WiderTransfer306S0, d2WiderTransfer306C1, d2WiderTransfer306S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202056198637668290974021 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((33986657723250068345157 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece19 (x : ℝ) (hx : x ∈ Icc ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ) ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope19 x hx
  have hxT : x ∈ Icc (d2WiderTransfer309Lo : ℝ) (d2WiderTransfer309Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer309Lo, d2WiderTransfer309Hi, d2LitsNearWiderTransfers038.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer309Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17029345409607606621155 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer309Cap, d2LitsNearWiderTransfers038.q2, d2WiderTransfer309C0, d2WiderTransfer309S0, d2WiderTransfer309C1, d2WiderTransfer309S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601064115866816717935587 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((17029345409607606621155 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece20 (x : ℝ) (hx : x ∈ Icc ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ) ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope20 x hx
  have hxT : x ∈ Icc (d2WiderTransfer312Lo : ℝ) (d2WiderTransfer312Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer312Lo, d2WiderTransfer312Hi, d2LitsNearWiderTransfers039.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer312Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((34130874385935324799375 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer312Cap, d2LitsNearWiderTransfers039.q2, d2WiderTransfer312C0, d2WiderTransfer312S0, d2WiderTransfer312C1, d2WiderTransfer312S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202200415300353547428239 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((34130874385935324799375 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece21 (x : ℝ) (hx : x ∈ Icc ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ) ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope21 x hx
  have hxT : x ∈ Icc (d2WiderTransfer315Lo : ℝ) (d2WiderTransfer315Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer315Lo, d2WiderTransfer315Hi, d2LitsNearWiderTransfers039.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer315Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((34203209055996652431157 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer315Cap, d2LitsNearWiderTransfers039.q2, d2WiderTransfer315C0, d2WiderTransfer315S0, d2WiderTransfer315C1, d2WiderTransfer315S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202272749970414875060021 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((34203209055996652431157 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece22 (x : ℝ) (hx : x ∈ Icc ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope22 x hx
  have hxT : x ∈ Icc (d2WiderTransfer318Lo : ℝ) (d2WiderTransfer318Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer318Lo, d2WiderTransfer318Hi, d2LitsNearWiderTransfers039.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer318Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17137847732989585535547 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer318Cap, d2LitsNearWiderTransfers039.q2, d2WiderTransfer318C0, d2WiderTransfer318S0, d2WiderTransfer318C1, d2WiderTransfer318S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601172618190198696849979 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((17137847732989585535547 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece23 (x : ℝ) (hx : x ∈ Icc ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ) ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope23 x hx
  have hxT : x ∈ Icc (d2WiderTransfer321Lo : ℝ) (d2WiderTransfer321Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer321Lo, d2WiderTransfer321Hi, d2LitsNearWiderTransfers040.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer321Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((34348334256490277692351 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer321Cap, d2LitsNearWiderTransfers040.q2, d2WiderTransfer321C0, d2WiderTransfer321S0, d2WiderTransfer321C1, d2WiderTransfer321S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202417875170908500321215 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((34348334256490277692351 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece24 (x : ℝ) (hx : x ∈ Icc ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ) ((((1354589953 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope24 x hx
  have hxT : x ∈ Icc (d2WiderTransfer324Lo : ℝ) (d2WiderTransfer324Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer324Lo, d2WiderTransfer324Hi, d2LitsNearWiderTransfers040.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer324Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((34421126072198843949927 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer324Cap, d2LitsNearWiderTransfers040.q2, d2WiderTransfer324C0, d2WiderTransfer324S0, d2WiderTransfer324C1, d2WiderTransfer324S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202490666986617066578791 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((34421126072198843949927 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece25 (x : ℝ) (hx : x ∈ Icc ((((1354589953 : ℚ) / 2147483648) : ℚ) : ℝ) ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope25 x hx
  have hxT : x ∈ Icc (d2WiderTransfer327Lo : ℝ) (d2WiderTransfer327Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer327Lo, d2WiderTransfer327Hi, d2LitsNearWiderTransfers040.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer327Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17247035780934814734895 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer327Cap, d2LitsNearWiderTransfers040.q2, d2WiderTransfer327C0, d2WiderTransfer327S0, d2WiderTransfer327C1, d2WiderTransfer327S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601281806238143926049327 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((17247035780934814734895 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece26 (x : ℝ) (hx : x ∈ Icc ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1357945395 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope26 x hx
  have hxT : x ∈ Icc (d2WiderTransfer330Lo : ℝ) (d2WiderTransfer330Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer330Lo, d2WiderTransfer330Hi, d2LitsNearWiderTransfers041.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer330Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17283585689199030189147 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer330Cap, d2LitsNearWiderTransfers041.q2, d2WiderTransfer330C0, d2WiderTransfer330S0, d2WiderTransfer330C1, d2WiderTransfer330S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601318356146408141503579 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((17283585689199030189147 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece27 (x : ℝ) (hx : x ∈ Icc ((((1357945395 : ℚ) / 2147483648) : ℚ) : ℝ) ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope27 x hx
  have hxT : x ∈ Icc (d2WiderTransfer333Lo : ℝ) (d2WiderTransfer333Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer333Lo, d2WiderTransfer333Hi, d2LitsNearWiderTransfers041.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer333Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17320213089422688866769 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer333Cap, d2LitsNearWiderTransfers041.q2, d2WiderTransfer333C0, d2WiderTransfer333S0, d2WiderTransfer333C1, d2WiderTransfer333S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601354983546631800181201 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((17320213089422688866769 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece28 (x : ℝ) (hx : x ∈ Icc ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ) ((((1361300837 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope28 x hx
  have hxT : x ∈ Icc (d2WiderTransfer336Lo : ℝ) (d2WiderTransfer336Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer336Lo, d2WiderTransfer336Hi, d2LitsNearWiderTransfers042.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer336Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((34713836624474160589873 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer336Cap, d2LitsNearWiderTransfers042.q2, d2WiderTransfer336C0, d2WiderTransfer336S0, d2WiderTransfer336C1, d2WiderTransfer336S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202783377538892383218737 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((34713836624474160589873 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece29 (x : ℝ) (hx : x ∈ Icc ((((1361300837 : ℚ) / 2147483648) : ℚ) : ℝ) ((((681489279 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope29 x hx
  have hxT : x ∈ Icc (d2WiderTransfer339Lo : ℝ) (d2WiderTransfer339Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer339Lo, d2WiderTransfer339Hi, d2LitsNearWiderTransfers042.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer339Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17393701690392114248773 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer339Cap, d2LitsNearWiderTransfers042.q2, d2WiderTransfer339C0, d2WiderTransfer339S0, d2WiderTransfer339C1, d2WiderTransfer339S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601428472147601225563205 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((17393701690392114248773 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece30 (x : ℝ) (hx : x ∈ Icc ((((681489279 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1364656279 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope30 x hx
  have hxT : x ∈ Icc (d2WiderTransfer342Lo : ℝ) (d2WiderTransfer342Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer342Lo, d2WiderTransfer342Hi, d2LitsNearWiderTransfers042.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer342Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((34861127117548928311389 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer342Cap, d2LitsNearWiderTransfers042.q2, d2WiderTransfer342C0, d2WiderTransfer342S0, d2WiderTransfer342C1, d2WiderTransfer342S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1202930668031967150940253 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((34861127117548928311389 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece31 (x : ℝ) (hx : x ∈ Icc ((((1364656279 : ℚ) / 2147483648) : ℚ) : ℝ) ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope31 x hx
  have hxT : x ∈ Icc (d2WiderTransfer345Lo : ℝ) (d2WiderTransfer345Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer345Lo, d2WiderTransfer345Hi, d2LitsNearWiderTransfers043.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer345Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((34935008508851810255701 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer345Cap, d2LitsNearWiderTransfers043.q2, d2WiderTransfer345C0, d2WiderTransfer345S0, d2WiderTransfer345C1, d2WiderTransfer345S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1203004549423270032884565 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((34935008508851810255701 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece32 (x : ℝ) (hx : x ∈ Icc ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ) ((((1368011721 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope32 x hx
  have hxT : x ∈ Icc (d2WiderTransfer348Lo : ℝ) (d2WiderTransfer348Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer348Lo, d2WiderTransfer348Hi, d2LitsNearWiderTransfers043.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer348Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((35009048233123698266893 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer348Cap, d2LitsNearWiderTransfers043.q2, d2WiderTransfer348C0, d2WiderTransfer348S0, d2WiderTransfer348C1, d2WiderTransfer348S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1203078589147541920895757 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((35009048233123698266893 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece33 (x : ℝ) (hx : x ∈ Icc ((((1368011721 : ℚ) / 2147483648) : ℚ) : ℝ) ((((684844721 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope33 x hx
  have hxT : x ∈ Icc (d2WiderTransfer351Lo : ℝ) (d2WiderTransfer351Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer351Lo, d2WiderTransfer351Hi, d2LitsNearWiderTransfers043.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer351Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17541623486590079855617 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer351Cap, d2LitsNearWiderTransfers043.q2, d2WiderTransfer351C0, d2WiderTransfer351S0, d2WiderTransfer351C1, d2WiderTransfer351S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601576393943799191170049 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((17541623486590079855617 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece34 (x : ℝ) (hx : x ∈ Icc ((((684844721 : ℚ) / 1073741824) : ℚ) : ℝ) ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope34 x hx
  have hxT : x ∈ Icc (d2WiderTransfer354Lo : ℝ) (d2WiderTransfer354Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer354Lo, d2WiderTransfer354Hi, d2LitsNearWiderTransfers044.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer354Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((35232124254060444919259 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer354Cap, d2LitsNearWiderTransfers044.q2, d2WiderTransfer354C0, d2WiderTransfer354S0, d2WiderTransfer354C1, d2WiderTransfer354S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1203301665168478667548123 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((35232124254060444919259 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece35 (x : ℝ) (hx : x ∈ Icc ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ) ((((688200163 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope35 x hx
  have hxT : x ∈ Icc (d2WiderTransfer357Lo : ℝ) (d2WiderTransfer357Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer357Lo, d2WiderTransfer357Hi, d2LitsNearWiderTransfers044.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer357Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17690822951580791679059 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer357Cap, d2LitsNearWiderTransfers044.q2, d2WiderTransfer357C0, d2WiderTransfer357S0, d2WiderTransfer357C1, d2WiderTransfer357S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-601725593408789902993491 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((17690822951580791679059 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece36 (x : ℝ) (hx : x ∈ Icc ((((688200163 : ℚ) / 1073741824) : ℚ) : ℝ) ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope36 x hx
  have hxT : x ∈ Icc (d2WiderTransfer360Lo : ℝ) (d2WiderTransfer360Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer360Lo, d2WiderTransfer360Hi, d2LitsNearWiderTransfers045.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer360Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((8882954386193858129455 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer360Cap, d2LitsNearWiderTransfers045.q2, d2WiderTransfer360C0, d2WiderTransfer360S0, d2WiderTransfer360C1, d2WiderTransfer360S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-300900339614798413786671 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((8882954386193858129455 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece37 (x : ℝ) (hx : x ∈ Icc ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ) ((((346616663 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope37 x hx
  have hxT : x ∈ Icc (d2WiderTransfer363Lo : ℝ) (d2WiderTransfer363Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer363Lo, d2WiderTransfer363Hi, d2LitsNearWiderTransfers045.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer363Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((35834133673486152589755 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer363Cap, d2LitsNearWiderTransfers045.q2, d2WiderTransfer363C0, d2WiderTransfer363S0, d2WiderTransfer363C1, d2WiderTransfer363S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1203903674587904375218619 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((35834133673486152589755 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece38 (x : ℝ) (hx : x ∈ Icc ((((346616663 : ℚ) / 536870912) : ℚ) : ℝ) ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope38 x hx
  have hxT : x ∈ Icc (d2WiderTransfer366Lo : ℝ) (d2WiderTransfer366Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer366Lo, d2WiderTransfer366Hi, d2LitsNearWiderTransfers045.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer366Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((36139119136045530132903 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer366Cap, d2LitsNearWiderTransfers045.q2, d2WiderTransfer366C0, d2WiderTransfer366S0, d2WiderTransfer366C1, d2WiderTransfer366S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1204208660050463752761767 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((36139119136045530132903 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece39 (x : ℝ) (hx : x ∈ Icc ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ) ((((175824913 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope39 x hx
  have hxT : x ∈ Icc (d2WiderTransfer369Lo : ℝ) (d2WiderTransfer369Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer369Lo, d2WiderTransfer369Hi, d2LitsNearWiderTransfers046.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer369Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((9189322580747306301695 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer369Cap, d2LitsNearWiderTransfers046.q2, d2WiderTransfer369C0, d2WiderTransfer369S0, d2WiderTransfer369C1, d2WiderTransfer369S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-301206707809351861958911 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((9189322580747306301695 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece40 (x : ℝ) (hx : x ∈ Icc ((((175824913 : ℚ) / 268435456) : ℚ) : ℝ) ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope40 x hx
  have hxT : x ∈ Icc (d2WiderTransfer372Lo : ℝ) (d2WiderTransfer372Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer372Lo, d2WiderTransfer372Hi, d2LitsNearWiderTransfers046.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer372Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2336670551483778787673 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer372Cap, d2LitsNearWiderTransfers046.q2, d2WiderTransfer372C0, d2WiderTransfer372S0, d2WiderTransfer372C1, d2WiderTransfer372S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-75341016858634917701977 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) + ((((2336670551483778787673 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece41 (x : ℝ) (hx : x ∈ Icc ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ) ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope41 x hx
  have hxT : x ∈ Icc (d2WiderTransfer375Lo : ℝ) (d2WiderTransfer375Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer375Lo, d2WiderTransfer375Hi, d2LitsNearWiderTransfers046.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer375Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((9670277854355474692625 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer375Cap, d2LitsNearWiderTransfers046.q2, d2WiderTransfer375C0, d2WiderTransfer375S0, d2WiderTransfer375C1, d2WiderTransfer375S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-301687663082960030349841 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((9670277854355474692625 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece42 (x : ℝ) (hx : x ∈ Icc ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ) ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope42 x hx
  have hxT : x ∈ Icc (d2WiderTransfer378Lo : ℝ) (d2WiderTransfer378Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer378Lo, d2WiderTransfer378Hi, d2LitsNearWiderTransfers047.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer378Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((20712636043577604784775 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer378Cap, d2LitsNearWiderTransfers047.q2, d2WiderTransfer378C0, d2WiderTransfer378S0, d2WiderTransfer378C1, d2WiderTransfer378S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-604747406500786716099207 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((20712636043577604784775 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece43 (x : ℝ) (hx : x ∈ Icc ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ) ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope43 x hx
  have hxT : x ∈ Icc (d2WiderTransfer381Lo : ℝ) (d2WiderTransfer381Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer381Lo, d2WiderTransfer381Hi, d2LitsNearWiderTransfers047.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer381Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((47670448316888970792591 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer381Cap, d2LitsNearWiderTransfers047.q2, d2WiderTransfer381C0, d2WiderTransfer381S0, d2WiderTransfer381C1, d2WiderTransfer381S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1215739989231307193421455 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((47670448316888970792591 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece44 (x : ℝ) (hx : x ∈ Icc ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ) ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope44 x hx
  have hxT : x ∈ Icc (d2WiderTransfer384Lo : ℝ) (d2WiderTransfer384Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer384Lo, d2WiderTransfer384Hi, d2LitsNearWiderTransfers048.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer384Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((55303082721192846961955 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer384Cap, d2LitsNearWiderTransfers048.q2, d2WiderTransfer384C0, d2WiderTransfer384S0, d2WiderTransfer384C1, d2WiderTransfer384S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1223372623635611069590819 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((55303082721192846961955 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece45 (x : ℝ) (hx : x ∈ Icc ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ) ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope45 x hx
  have hxT : x ∈ Icc (d2WiderTransfer387Lo : ℝ) (d2WiderTransfer387Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer387Lo, d2WiderTransfer387Hi, d2LitsNearWiderTransfers048.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer387Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((39459143378516659160053 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer387Cap, d2LitsNearWiderTransfers048.q2, d2WiderTransfer387C0, d2WiderTransfer387S0, d2WiderTransfer387C1, d2WiderTransfer387S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-623493913835725770474485 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((39459143378516659160053 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece46 (x : ℝ) (hx : x ∈ Icc ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ) ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope46 x hx
  have hxT : x ∈ Icc (d2WiderTransfer390Lo : ℝ) (d2WiderTransfer390Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer390Lo, d2WiderTransfer390Hi, d2LitsNearWiderTransfers048.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer390Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((102312947180000405823863 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer390Cap, d2LitsNearWiderTransfers048.q2, d2WiderTransfer390C0, d2WiderTransfer390S0, d2WiderTransfer390C1, d2WiderTransfer390S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1270382488094418628452727 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((102312947180000405823863 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece47 (x : ℝ) (hx : x ∈ Icc ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ) ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope47 x hx
  have hxT : x ∈ Icc (d2WiderTransfer393Lo : ℝ) (d2WiderTransfer393Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer393Lo, d2WiderTransfer393Hi, d2LitsNearWiderTransfers049.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer393Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((125295547282137467866777 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer393Cap, d2LitsNearWiderTransfers049.q2, d2WiderTransfer393C0, d2WiderTransfer393S0, d2WiderTransfer393C1, d2WiderTransfer393S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1293365088196555690495641 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((125295547282137467866777 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece48 (x : ℝ) (hx : x ∈ Icc ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ) ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope48 x hx
  have hxT : x ∈ Icc (d2WiderTransfer396Lo : ℝ) (d2WiderTransfer396Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer396Lo, d2WiderTransfer396Hi, d2LitsNearWiderTransfers049.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer396Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((229829789513853745647383 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer396Cap, d2LitsNearWiderTransfers049.q2, d2WiderTransfer396C0, d2WiderTransfer396S0, d2WiderTransfer396C1, d2WiderTransfer396S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1397899330428271968276247 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((229829789513853745647383 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece49 (x : ℝ) (hx : x ∈ Icc ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ) ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope49 x hx
  have hxT : x ∈ Icc (d2WiderTransfer399Lo : ℝ) (d2WiderTransfer399Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer399Lo, d2WiderTransfer399Hi, d2LitsNearWiderTransfers049.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer399Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((59381786413916070450705 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer399Cap, d2LitsNearWiderTransfers049.q2, d2WiderTransfer399C0, d2WiderTransfer399S0, d2WiderTransfer399C1, d2WiderTransfer399S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-351399171642520626107921 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((59381786413916070450705 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece50 (x : ℝ) (hx : x ∈ Icc ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope50 x hx
  have hxT : x ∈ Icc (d2WiderTransfer402Lo : ℝ) (d2WiderTransfer402Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer402Lo, d2WiderTransfer402Hi, d2LitsNearWiderTransfers050.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer402Bound x hxT
  have hd : ((((3 : ℚ) / 8800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((118764375273470374378443 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer402Cap, d2LitsNearWiderTransfers050.q2, d2WiderTransfer402C0, d2WiderTransfer402S0, d2WiderTransfer402C1, d2WiderTransfer402S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-702799145730679485692875 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((118764375273470374378443 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner3Domain0Pieces : List (ℚ × ℚ) := [(((98749 : ℚ) / 1000000), ((828367 : ℚ) / 8388608)), (((828367 : ℚ) / 8388608), ((8304657 : ℚ) / 67108864)), (((8304657 : ℚ) / 67108864), ((4991189 : ℚ) / 33554432)), (((4991189 : ℚ) / 33554432), ((3334455 : ℚ) / 16777216)), (((3334455 : ℚ) / 16777216), ((313261 : ℚ) / 1048576)), (((313261 : ℚ) / 1048576), ((6689897 : ℚ) / 16777216)), (((6689897 : ℚ) / 16777216), ((4183809 : ℚ) / 8388608)), (((4183809 : ℚ) / 8388608), ((18412957 : ℚ) / 33554432)), (((18412957 : ℚ) / 33554432), ((38503635 : ℚ) / 67108864)), (((38503635 : ℚ) / 67108864), ((10045339 : ℚ) / 16777216)), (((10045339 : ℚ) / 16777216), ((162403145 : ℚ) / 268435456)), (((162403145 : ℚ) / 268435456), ((82040433 : ℚ) / 134217728)), (((82040433 : ℚ) / 134217728), ((329839453 : ℚ) / 536870912)), (((329839453 : ℚ) / 536870912), ((165758587 : ℚ) / 268435456)), (((165758587 : ℚ) / 268435456), ((333194895 : ℚ) / 536870912)), (((333194895 : ℚ) / 536870912), ((668067511 : ℚ) / 1073741824)), (((668067511 : ℚ) / 1073741824), ((41859077 : ℚ) / 67108864)), (((41859077 : ℚ) / 67108864), ((671422953 : ℚ) / 1073741824)), (((671422953 : ℚ) / 1073741824), ((1344523627 : ℚ) / 2147483648)), (((1344523627 : ℚ) / 2147483648), ((336550337 : ℚ) / 536870912)), (((336550337 : ℚ) / 536870912), ((1347879069 : ℚ) / 2147483648)), (((1347879069 : ℚ) / 2147483648), ((674778395 : ℚ) / 1073741824)), (((674778395 : ℚ) / 1073741824), ((1351234511 : ℚ) / 2147483648)), (((1351234511 : ℚ) / 2147483648), ((169114029 : ℚ) / 268435456)), (((169114029 : ℚ) / 268435456), ((1354589953 : ℚ) / 2147483648)), (((1354589953 : ℚ) / 2147483648), ((678133837 : ℚ) / 1073741824)), (((678133837 : ℚ) / 1073741824), ((1357945395 : ℚ) / 2147483648)), (((1357945395 : ℚ) / 2147483648), ((339905779 : ℚ) / 536870912)), (((339905779 : ℚ) / 536870912), ((1361300837 : ℚ) / 2147483648)), (((1361300837 : ℚ) / 2147483648), ((681489279 : ℚ) / 1073741824)), (((681489279 : ℚ) / 1073741824), ((1364656279 : ℚ) / 2147483648)), (((1364656279 : ℚ) / 2147483648), ((85395875 : ℚ) / 134217728)), (((85395875 : ℚ) / 134217728), ((1368011721 : ℚ) / 2147483648)), (((1368011721 : ℚ) / 2147483648), ((684844721 : ℚ) / 1073741824)), (((684844721 : ℚ) / 1073741824), ((343261221 : ℚ) / 536870912)), (((343261221 : ℚ) / 536870912), ((688200163 : ℚ) / 1073741824)), (((688200163 : ℚ) / 1073741824), ((172469471 : ℚ) / 268435456)), (((172469471 : ℚ) / 268435456), ((346616663 : ℚ) / 536870912)), (((346616663 : ℚ) / 536870912), ((21768399 : ℚ) / 33554432)), (((21768399 : ℚ) / 33554432), ((175824913 : ℚ) / 268435456)), (((175824913 : ℚ) / 268435456), ((88751317 : ℚ) / 134217728)), (((88751317 : ℚ) / 134217728), ((45214519 : ℚ) / 67108864)), (((45214519 : ℚ) / 67108864), ((2930765 : ℚ) / 4194304)), (((2930765 : ℚ) / 4194304), ((25123841 : ℚ) / 33554432)), (((25123841 : ℚ) / 33554432), ((13400781 : ℚ) / 16777216)), (((13400781 : ℚ) / 16777216), ((7539251 : ℚ) / 8388608)), (((7539251 : ℚ) / 8388608), ((31834725 : ℚ) / 33554432)), (((31834725 : ℚ) / 33554432), ((65347171 : ℚ) / 67108864)), (((65347171 : ℚ) / 67108864), ((16756223 : ℚ) / 16777216)), (((16756223 : ℚ) / 16777216), ((8380219 : ℚ) / 8388608)), (((8380219 : ℚ) / 8388608), ((999 : ℚ) / 1000))]
theorem corner3Domain0Cover : pieceCover ((999 : ℚ) / 1000) ((98749 : ℚ) / 1000000) corner3Domain0Pieces = true := by decide +kernel
theorem corner3Domain0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  apply pieceCover_bound ((999 : ℚ) / 1000) (fun x : ℝ => fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x) ((((-265588264691 : ℚ) / 274877906944) : ℚ) : ℝ) ((98749 : ℚ) / 1000000) corner3Domain0Pieces (by decide +kernel) corner3Domain0Cover
  intro p hp
  simp only [corner3Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner3Piece0
  · exact corner3Piece1
  · exact corner3Piece2
  · exact corner3Piece3
  · exact corner3Piece4
  · exact corner3Piece5
  · exact corner3Piece6
  · exact corner3Piece7
  · exact corner3Piece8
  · exact corner3Piece9
  · exact corner3Piece10
  · exact corner3Piece11
  · exact corner3Piece12
  · exact corner3Piece13
  · exact corner3Piece14
  · exact corner3Piece15
  · exact corner3Piece16
  · exact corner3Piece17
  · exact corner3Piece18
  · exact corner3Piece19
  · exact corner3Piece20
  · exact corner3Piece21
  · exact corner3Piece22
  · exact corner3Piece23
  · exact corner3Piece24
  · exact corner3Piece25
  · exact corner3Piece26
  · exact corner3Piece27
  · exact corner3Piece28
  · exact corner3Piece29
  · exact corner3Piece30
  · exact corner3Piece31
  · exact corner3Piece32
  · exact corner3Piece33
  · exact corner3Piece34
  · exact corner3Piece35
  · exact corner3Piece36
  · exact corner3Piece37
  · exact corner3Piece38
  · exact corner3Piece39
  · exact corner3Piece40
  · exact corner3Piece41
  · exact corner3Piece42
  · exact corner3Piece43
  · exact corner3Piece44
  · exact corner3Piece45
  · exact corner3Piece46
  · exact corner3Piece47
  · exact corner3Piece48
  · exact corner3Piece49
  · exact corner3Piece50
#print axioms corner3Domain0Cover
#print axioms corner3Domain0
end D72.NearCornerCover002
end CatalanMeasure.GenD.Signed.Data.Cells
