module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AnchoredLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearCorners001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers014
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers015
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers023
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers030
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers031
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open CatalanMeasure.GenD.Signed.Data.Trial
namespace D72.NearCornerCover001
theorem envelope0 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((828367 : ℚ) / 8388608) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction005P0Lo : ℝ) (d2NearProduction005P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction005P0Lo, d2NearProduction005P0Hi, d2NearProduction005P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction005P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction005P0Literal.q2])
theorem envelope1 (x : ℝ) (hx : x ∈ Icc ((((828367 : ℚ) / 8388608) : ℚ) : ℝ) ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction011P0Lo : ℝ) (d2NearProduction011P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction011P0Lo, d2NearProduction011P0Hi, d2NearProduction011P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction011P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction011P0Literal.q2])
theorem envelope2 (x : ℝ) (hx : x ∈ Icc ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ) ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction011P1Lo : ℝ) (d2NearProduction011P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction011P1Lo, d2NearProduction011P1Hi, d2NearProduction011P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction011P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction011P1Literal.q2])
theorem envelope3 (x : ℝ) (hx : x ∈ Icc ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ) ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction011P2Lo : ℝ) (d2NearProduction011P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction011P2Lo, d2NearProduction011P2Hi, d2NearProduction011P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction011P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction011P2Literal.q2])
theorem envelope4 (x : ℝ) (hx : x ∈ Icc ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ) ((((313261 : ℚ) / 1048576) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction011P3Lo : ℝ) (d2NearProduction011P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction011P3Lo, d2NearProduction011P3Hi, d2NearProduction011P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction011P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction011P3Literal.q2])
theorem envelope5 (x : ℝ) (hx : x ∈ Icc ((((313261 : ℚ) / 1048576) : ℚ) : ℝ) ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction012P0Lo : ℝ) (d2NearProduction012P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction012P0Lo, d2NearProduction012P0Hi, d2NearProduction012P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction012P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction012P0Literal.q2])
theorem envelope6 (x : ℝ) (hx : x ∈ Icc ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ) ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction012P1Lo : ℝ) (d2NearProduction012P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction012P1Lo, d2NearProduction012P1Hi, d2NearProduction012P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction012P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction012P1Literal.q2])
theorem envelope7 (x : ℝ) (hx : x ∈ Icc ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ) ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction005P1Lo : ℝ) (d2NearProduction005P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction005P1Lo, d2NearProduction005P1Hi, d2NearProduction005P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction005P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction005P1Literal.q2])
theorem envelope8 (x : ℝ) (hx : x ∈ Icc ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ) ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction005P2Lo : ℝ) (d2NearProduction005P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction005P2Lo, d2NearProduction005P2Hi, d2NearProduction005P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction005P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction005P2Literal.q2])
theorem envelope9 (x : ℝ) (hx : x ∈ Icc ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ) ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction005P3Lo : ℝ) (d2NearProduction005P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction005P3Lo, d2NearProduction005P3Hi, d2NearProduction005P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction005P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction005P3Literal.q2])
theorem envelope10 (x : ℝ) (hx : x ∈ Icc ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ) ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction005P4Lo : ℝ) (d2NearProduction005P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction005P4Lo, d2NearProduction005P4Hi, d2NearProduction005P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction005P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction005P4Literal.q2])
theorem envelope11 (x : ℝ) (hx : x ∈ Icc ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ) ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-304635849631809526527407 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction005P5Lo : ℝ) (d2NearProduction005P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction005P5Lo, d2NearProduction005P5Hi, d2NearProduction005P5Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction005P5Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction005P5Literal.q2])
theorem envelope12 (x : ℝ) (hx : x ∈ Icc ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ) ((((326484011 : ℚ) / 536870912) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1218585796493313133547233 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction005P6Lo : ℝ) (d2NearProduction005P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction005P6Lo, d2NearProduction005P6Hi, d2NearProduction005P6Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction005P6Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction005P6Literal.q2])
theorem envelope13 (x : ℝ) (hx : x ∈ Icc ((((326484011 : ℚ) / 536870912) : ℚ) : ℝ) ((((654645743 : ℚ) / 1073741824) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-152327810721238626632069 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction005P7Lo : ℝ) (d2NearProduction005P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction005P7Lo, d2NearProduction005P7Hi, d2NearProduction005P7Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction005P7Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction005P7Literal.q2])
theorem envelope14 (x : ℝ) (hx : x ∈ Icc ((((654645743 : ℚ) / 1073741824) : ℚ) : ℝ) ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-609329569725010844567481 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction006P0Lo : ℝ) (d2NearProduction006P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction006P0Lo, d2NearProduction006P0Hi, d2NearProduction006P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction006P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction006P0Literal.q2])
theorem envelope15 (x : ℝ) (hx : x ∈ Icc ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ) ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1218732340296619100284281 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction006P1Lo : ℝ) (d2NearProduction006P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction006P1Lo, d2NearProduction006P1Hi, d2NearProduction006P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction006P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction006P1Literal.q2])
theorem envelope16 (x : ℝ) (hx : x ∈ Icc ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ) ((((661356627 : ℚ) / 1073741824) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-304696870642480576297815 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction006P2Lo : ℝ) (d2NearProduction006P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction006P2Lo, d2NearProduction006P2Hi, d2NearProduction006P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction006P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction006P2Literal.q2])
theorem envelope17 (x : ℝ) (hx : x ∈ Icc ((((661356627 : ℚ) / 1073741824) : ℚ) : ℝ) ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1218930811691471068749663 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction006P3Lo : ℝ) (d2NearProduction006P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction006P3Lo, d2NearProduction006P3Hi, d2NearProduction006P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction006P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction006P3Literal.q2])
theorem envelope18 (x : ℝ) (hx : x ∈ Icc ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ) ((((1327746417 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-304750672417914923860963 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction006P4Lo : ℝ) (d2NearProduction006P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction006P4Lo, d2NearProduction006P4Hi, d2NearProduction006P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction006P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction006P4Literal.q2])
theorem envelope19 (x : ℝ) (hx : x ∈ Icc ((((1327746417 : ℚ) / 2147483648) : ℚ) : ℝ) ((((664712069 : ℚ) / 1073741824) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-38096084709814325844035 : ℚ) / 37778931862957161709568) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction006P5Lo : ℝ) (d2NearProduction006P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction006P5Lo, d2NearProduction006P5Hi, d2NearProduction006P5Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction006P5Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction006P5Literal.q2])
theorem envelope20 (x : ℝ) (hx : x ∈ Icc ((((664712069 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1331101859 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-4762292482070814866175 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction006P6Lo : ℝ) (d2NearProduction006P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction006P6Lo, d2NearProduction006P6Hi, d2NearProduction006P6Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction006P6Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction006P6Literal.q2])
theorem envelope21 (x : ℝ) (hx : x ∈ Icc ((((1331101859 : ℚ) / 2147483648) : ℚ) : ℝ) ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1219219184354975928218547 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction006P7Lo : ℝ) (d2NearProduction006P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction006P7Lo, d2NearProduction006P7Hi, d2NearProduction006P7Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction006P7Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction006P7Literal.q2])
theorem envelope22 (x : ℝ) (hx : x ∈ Icc ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ) ((((1334457301 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-9525715923026410210605 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction007P0Lo : ℝ) (d2NearProduction007P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction007P0Lo, d2NearProduction007P0Hi, d2NearProduction007P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction007P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction007P0Literal.q2])
theorem envelope23 (x : ℝ) (hx : x ∈ Icc ((((1334457301 : ℚ) / 2147483648) : ℚ) : ℝ) ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1219364237389827242521351 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction007P1Lo : ℝ) (d2NearProduction007P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction007P1Lo, d2NearProduction007P1Hi, d2NearProduction007P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction007P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction007P1Literal.q2])
theorem envelope24 (x : ℝ) (hx : x ∈ Icc ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1337812743 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-609718491344268254977273 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction007P2Lo : ℝ) (d2NearProduction007P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction007P2Lo, d2NearProduction007P2Hi, d2NearProduction007P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction007P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction007P2Literal.q2])
theorem envelope25 (x : ℝ) (hx : x ∈ Icc ((((1337812743 : ℚ) / 2147483648) : ℚ) : ℝ) ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-76219367165843447715215 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction007P3Lo : ℝ) (d2NearProduction007P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction007P3Lo, d2NearProduction007P3Hi, d2NearProduction007P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction007P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction007P3Literal.q2])
theorem envelope26 (x : ℝ) (hx : x ∈ Icc ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ) ((((1341168185 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1219582913898487863177381 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction007P4Lo : ℝ) (d2NearProduction007P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction007P4Lo, d2NearProduction007P4Hi, d2NearProduction007P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction007P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction007P4Literal.q2])
theorem envelope27 (x : ℝ) (hx : x ∈ Icc ((((1341168185 : ℚ) / 2147483648) : ℚ) : ℝ) ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-152457012630141091054397 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction007P5Lo : ℝ) (d2NearProduction007P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction007P5Lo, d2NearProduction007P5Hi, d2NearProduction007P5Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction007P5Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction007P5Literal.q2])
theorem envelope28 (x : ℝ) (hx : x ∈ Icc ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1219729436702893320982917 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction007P6Lo : ℝ) (d2NearProduction007P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction007P6Lo, d2NearProduction007P6Hi, d2NearProduction007P6Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction007P6Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction007P6Literal.q2])
theorem envelope29 (x : ℝ) (hx : x ∈ Icc ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ) ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1219802921509150962928489 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction007P7Lo : ℝ) (d2NearProduction007P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction007P7Lo, d2NearProduction007P7Hi, d2NearProduction007P7Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction007P7Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction007P7Literal.q2])
theorem envelope30 (x : ℝ) (hx : x ∈ Icc ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ) ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1219876556089197393238949 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction008P0Lo : ℝ) (d2NearProduction008P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction008P0Lo, d2NearProduction008P0Hi, d2NearProduction008P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction008P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction008P0Literal.q2])
theorem envelope31 (x : ℝ) (hx : x ∈ Icc ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ) ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1219950341076287767188817 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction008P1Lo : ℝ) (d2NearProduction008P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction008P1Lo, d2NearProduction008P1Hi, d2NearProduction008P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction008P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction008P1Literal.q2])
theorem envelope32 (x : ℝ) (hx : x ∈ Icc ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-610012138553835001535099 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction008P2Lo : ℝ) (d2NearProduction008P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction008P2Lo, d2NearProduction008P2Hi, d2NearProduction008P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction008P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction008P2Literal.q2])
theorem envelope33 (x : ℝ) (hx : x ∈ Icc ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ) ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-610049182412309240279803 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction008P3Lo : ℝ) (d2NearProduction008P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction008P3Lo, d2NearProduction008P3Hi, d2NearProduction008P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction008P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction008P3Literal.q2])
theorem envelope34 (x : ℝ) (hx : x ∈ Icc ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ) ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-610123498950324336766861 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction008P4Lo : ℝ) (d2NearProduction008P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction008P4Lo, d2NearProduction008P4Hi, d2NearProduction008P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction008P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction008P4Literal.q2])
theorem envelope35 (x : ℝ) (hx : x ∈ Icc ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ) ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1220396245516405734461221 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction008P5Lo : ℝ) (d2NearProduction008P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction008P5Lo, d2NearProduction008P5Hi, d2NearProduction008P5Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction008P5Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction008P5Literal.q2])
theorem envelope36 (x : ℝ) (hx : x ∈ Icc ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ) ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1220696605549556873027817 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction008P6Lo : ℝ) (d2NearProduction008P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction008P6Lo, d2NearProduction008P6Hi, d2NearProduction008P6Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction008P6Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction008P6Literal.q2])
theorem envelope37 (x : ℝ) (hx : x ∈ Icc ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ) ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1220999487973852498260983 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction008P7Lo : ℝ) (d2NearProduction008P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction008P7Lo, d2NearProduction008P7Hi, d2NearProduction008P7Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction008P7Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction008P7Literal.q2])
theorem envelope38 (x : ℝ) (hx : x ∈ Icc ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ) ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1221304936961585226119193 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction009P0Lo : ℝ) (d2NearProduction009P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction009P0Lo, d2NearProduction009P0Hi, d2NearProduction009P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction009P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction009P0Literal.q2])
theorem envelope39 (x : ℝ) (hx : x ∈ Icc ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ) ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1221923717167441567017077 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction009P1Lo : ℝ) (d2NearProduction009P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction009P1Lo, d2NearProduction009P1Hi, d2NearProduction009P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction009P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction009P1Literal.q2])
theorem envelope40 (x : ℝ) (hx : x ∈ Icc ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ) ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-611597077060307729497941 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction009P2Lo : ℝ) (d2NearProduction009P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction009P2Lo, d2NearProduction009P2Hi, d2NearProduction009P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction009P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction009P2Literal.q2])
theorem envelope41 (x : ℝ) (hx : x ∈ Icc ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ) ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-306127798214794372543651 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction009P3Lo : ℝ) (d2NearProduction009P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction009P3Lo, d2NearProduction009P3Hi, d2NearProduction009P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction009P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction009P3Literal.q2])
theorem envelope42 (x : ℝ) (hx : x ∈ Icc ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ) ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1227300162586350059567175 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction009P4Lo : ℝ) (d2NearProduction009P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction009P4Lo, d2NearProduction009P4Hi, d2NearProduction009P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction009P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction009P4Literal.q2])
theorem envelope43 (x : ℝ) (hx : x ∈ Icc ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ) ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-308408252959834813524885 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction009P5Lo : ℝ) (d2NearProduction009P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction009P5Lo, d2NearProduction009P5Hi, d2NearProduction009P5Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction009P5Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction009P5Literal.q2])
theorem envelope44 (x : ℝ) (hx : x ∈ Icc ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ) ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1241350847530952434699973 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction009P6Lo : ℝ) (d2NearProduction009P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction009P6Lo, d2NearProduction009P6Hi, d2NearProduction009P6Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction009P6Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction009P6Literal.q2])
theorem envelope45 (x : ℝ) (hx : x ∈ Icc ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ) ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1265129570305762358708821 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction009P7Lo : ℝ) (d2NearProduction009P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction009P7Lo, d2NearProduction009P7Hi, d2NearProduction009P7Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction009P7Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction009P7Literal.q2])
theorem envelope46 (x : ℝ) (hx : x ∈ Icc ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ) ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-644301393929573224026735 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction010P0Lo : ℝ) (d2NearProduction010P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction010P0Lo, d2NearProduction010P0Hi, d2NearProduction010P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction010P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction010P0Literal.q2])
theorem envelope47 (x : ℝ) (hx : x ∈ Icc ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ) ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-655811956927391204724129 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction010P1Lo : ℝ) (d2NearProduction010P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction010P1Lo, d2NearProduction010P1Hi, d2NearProduction010P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction010P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction010P1Literal.q2])
theorem envelope48 (x : ℝ) (hx : x ∈ Icc ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ) ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-354049049264891768769157 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction010P2Lo : ℝ) (d2NearProduction010P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction010P2Lo, d2NearProduction010P2Hi, d2NearProduction010P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction010P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction010P2Literal.q2])
theorem envelope49 (x : ℝ) (hx : x ∈ Icc ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ) ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1423893933068628051281921 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction010P3Lo : ℝ) (d2NearProduction010P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction010P3Lo, d2NearProduction010P3Hi, d2NearProduction010P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction010P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction010P3Literal.q2])
theorem envelope50 (x : ℝ) (hx : x ∈ Icc ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ)) : (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) ≤ ((((-1423895538030556287102979 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction010P4Lo : ℝ) (d2NearProduction010P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction010P4Lo, d2NearProduction010P4Hi, d2NearProduction010P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction010P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction010P4Literal.q2])
theorem delta0Check : fieldNFCheck D72.NearCorners001.delta0 (fqSum []) = true := by decide +kernel
theorem delta0Value (x : ℝ) : fval D72.NearCorners001.delta0 x = (0 : ℝ) := by
  have h := fieldNFCheck_sound delta0Check x
  change fval D72.NearCorners001.delta0 x = fval (fqSum []) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner0Identity (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x = (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) + ((0 : ℝ)) := by
  have hf : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x = fval D72.NearBinding001.literalField x + fval D72.NearCorners001.delta0 x := by
    convert D72.NearCorners001.corner0Value x using 1 <;> norm_num [d2LitsNearCorners001.q2]
  have ht : lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x = lfieldTower D72.NearBinding001.literalTerms 0 x :=
    (laurent_eq_of_nf (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) D72.NearCorners001.corner0Terms x).trans (D72.NearBinding001.termsValue x).symm
  calc
    _ = (fval D72.NearBinding001.literalField x + fval D72.NearCorners001.delta0 x) + lfieldTower D72.NearBinding001.literalTerms 0 x :=
      congrArg₂ (fun u v : ℝ => u + v) hf ht
    _ = (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) + ((0 : ℝ)) := by rw [delta0Value]; ring
theorem corner0Piece0 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((828367 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope0 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece1 (x : ℝ) (hx : x ∈ Icc ((((828367 : ℚ) / 8388608) : ℚ) : ℝ) ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope1 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece2 (x : ℝ) (hx : x ∈ Icc ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ) ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope2 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece3 (x : ℝ) (hx : x ∈ Icc ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ) ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope3 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece4 (x : ℝ) (hx : x ∈ Icc ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ) ((((313261 : ℚ) / 1048576) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope4 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece5 (x : ℝ) (hx : x ∈ Icc ((((313261 : ℚ) / 1048576) : ℚ) : ℝ) ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope5 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece6 (x : ℝ) (hx : x ∈ Icc ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ) ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope6 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece7 (x : ℝ) (hx : x ∈ Icc ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ) ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope7 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece8 (x : ℝ) (hx : x ∈ Icc ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ) ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope8 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece9 (x : ℝ) (hx : x ∈ Icc ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ) ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope9 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece10 (x : ℝ) (hx : x ∈ Icc ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ) ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope10 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece11 (x : ℝ) (hx : x ∈ Icc ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ) ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope11 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece12 (x : ℝ) (hx : x ∈ Icc ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ) ((((326484011 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope12 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece13 (x : ℝ) (hx : x ∈ Icc ((((326484011 : ℚ) / 536870912) : ℚ) : ℝ) ((((654645743 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope13 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece14 (x : ℝ) (hx : x ∈ Icc ((((654645743 : ℚ) / 1073741824) : ℚ) : ℝ) ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope14 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece15 (x : ℝ) (hx : x ∈ Icc ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ) ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope15 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece16 (x : ℝ) (hx : x ∈ Icc ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ) ((((661356627 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope16 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece17 (x : ℝ) (hx : x ∈ Icc ((((661356627 : ℚ) / 1073741824) : ℚ) : ℝ) ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope17 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece18 (x : ℝ) (hx : x ∈ Icc ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ) ((((1327746417 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope18 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece19 (x : ℝ) (hx : x ∈ Icc ((((1327746417 : ℚ) / 2147483648) : ℚ) : ℝ) ((((664712069 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope19 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece20 (x : ℝ) (hx : x ∈ Icc ((((664712069 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1331101859 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope20 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece21 (x : ℝ) (hx : x ∈ Icc ((((1331101859 : ℚ) / 2147483648) : ℚ) : ℝ) ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope21 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece22 (x : ℝ) (hx : x ∈ Icc ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ) ((((1334457301 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope22 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece23 (x : ℝ) (hx : x ∈ Icc ((((1334457301 : ℚ) / 2147483648) : ℚ) : ℝ) ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope23 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece24 (x : ℝ) (hx : x ∈ Icc ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1337812743 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope24 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece25 (x : ℝ) (hx : x ∈ Icc ((((1337812743 : ℚ) / 2147483648) : ℚ) : ℝ) ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope25 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece26 (x : ℝ) (hx : x ∈ Icc ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ) ((((1341168185 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope26 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece27 (x : ℝ) (hx : x ∈ Icc ((((1341168185 : ℚ) / 2147483648) : ℚ) : ℝ) ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope27 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece28 (x : ℝ) (hx : x ∈ Icc ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope28 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece29 (x : ℝ) (hx : x ∈ Icc ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ) ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope29 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece30 (x : ℝ) (hx : x ∈ Icc ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ) ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope30 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece31 (x : ℝ) (hx : x ∈ Icc ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ) ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope31 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece32 (x : ℝ) (hx : x ∈ Icc ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope32 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece33 (x : ℝ) (hx : x ∈ Icc ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ) ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope33 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece34 (x : ℝ) (hx : x ∈ Icc ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ) ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope34 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece35 (x : ℝ) (hx : x ∈ Icc ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ) ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope35 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece36 (x : ℝ) (hx : x ∈ Icc ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ) ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope36 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece37 (x : ℝ) (hx : x ∈ Icc ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ) ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope37 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece38 (x : ℝ) (hx : x ∈ Icc ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ) ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope38 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece39 (x : ℝ) (hx : x ∈ Icc ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ) ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope39 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece40 (x : ℝ) (hx : x ∈ Icc ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ) ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope40 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece41 (x : ℝ) (hx : x ∈ Icc ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ) ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope41 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece42 (x : ℝ) (hx : x ∈ Icc ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ) ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope42 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece43 (x : ℝ) (hx : x ∈ Icc ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ) ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope43 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece44 (x : ℝ) (hx : x ∈ Icc ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ) ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope44 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece45 (x : ℝ) (hx : x ∈ Icc ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ) ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope45 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece46 (x : ℝ) (hx : x ∈ Icc ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ) ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope46 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece47 (x : ℝ) (hx : x ∈ Icc ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ) ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope47 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece48 (x : ℝ) (hx : x ∈ Icc ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ) ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope48 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece49 (x : ℝ) (hx : x ∈ Icc ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ) ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope49 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece50 (x : ℝ) (hx : x ∈ Icc ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope50 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
def corner0Domain0Pieces : List (ℚ × ℚ) := [(((98749 : ℚ) / 1000000), ((828367 : ℚ) / 8388608)), (((828367 : ℚ) / 8388608), ((8304657 : ℚ) / 67108864)), (((8304657 : ℚ) / 67108864), ((4991189 : ℚ) / 33554432)), (((4991189 : ℚ) / 33554432), ((3334455 : ℚ) / 16777216)), (((3334455 : ℚ) / 16777216), ((313261 : ℚ) / 1048576)), (((313261 : ℚ) / 1048576), ((6689897 : ℚ) / 16777216)), (((6689897 : ℚ) / 16777216), ((4183809 : ℚ) / 8388608)), (((4183809 : ℚ) / 8388608), ((18412957 : ℚ) / 33554432)), (((18412957 : ℚ) / 33554432), ((38503635 : ℚ) / 67108864)), (((38503635 : ℚ) / 67108864), ((78684991 : ℚ) / 134217728)), (((78684991 : ℚ) / 134217728), ((10045339 : ℚ) / 16777216)), (((10045339 : ℚ) / 16777216), ((162403145 : ℚ) / 268435456)), (((162403145 : ℚ) / 268435456), ((326484011 : ℚ) / 536870912)), (((326484011 : ℚ) / 536870912), ((654645743 : ℚ) / 1073741824)), (((654645743 : ℚ) / 1073741824), ((82040433 : ℚ) / 134217728)), (((82040433 : ℚ) / 134217728), ((329839453 : ℚ) / 536870912)), (((329839453 : ℚ) / 536870912), ((661356627 : ℚ) / 1073741824)), (((661356627 : ℚ) / 1073741824), ((165758587 : ℚ) / 268435456)), (((165758587 : ℚ) / 268435456), ((1327746417 : ℚ) / 2147483648)), (((1327746417 : ℚ) / 2147483648), ((664712069 : ℚ) / 1073741824)), (((664712069 : ℚ) / 1073741824), ((1331101859 : ℚ) / 2147483648)), (((1331101859 : ℚ) / 2147483648), ((333194895 : ℚ) / 536870912)), (((333194895 : ℚ) / 536870912), ((1334457301 : ℚ) / 2147483648)), (((1334457301 : ℚ) / 2147483648), ((668067511 : ℚ) / 1073741824)), (((668067511 : ℚ) / 1073741824), ((1337812743 : ℚ) / 2147483648)), (((1337812743 : ℚ) / 2147483648), ((41859077 : ℚ) / 67108864)), (((41859077 : ℚ) / 67108864), ((1341168185 : ℚ) / 2147483648)), (((1341168185 : ℚ) / 2147483648), ((671422953 : ℚ) / 1073741824)), (((671422953 : ℚ) / 1073741824), ((1344523627 : ℚ) / 2147483648)), (((1344523627 : ℚ) / 2147483648), ((336550337 : ℚ) / 536870912)), (((336550337 : ℚ) / 536870912), ((1347879069 : ℚ) / 2147483648)), (((1347879069 : ℚ) / 2147483648), ((674778395 : ℚ) / 1073741824)), (((674778395 : ℚ) / 1073741824), ((1351234511 : ℚ) / 2147483648)), (((1351234511 : ℚ) / 2147483648), ((169114029 : ℚ) / 268435456)), (((169114029 : ℚ) / 268435456), ((678133837 : ℚ) / 1073741824)), (((678133837 : ℚ) / 1073741824), ((339905779 : ℚ) / 536870912)), (((339905779 : ℚ) / 536870912), ((85395875 : ℚ) / 134217728)), (((85395875 : ℚ) / 134217728), ((343261221 : ℚ) / 536870912)), (((343261221 : ℚ) / 536870912), ((172469471 : ℚ) / 268435456)), (((172469471 : ℚ) / 268435456), ((21768399 : ℚ) / 33554432)), (((21768399 : ℚ) / 33554432), ((88751317 : ℚ) / 134217728)), (((88751317 : ℚ) / 134217728), ((45214519 : ℚ) / 67108864)), (((45214519 : ℚ) / 67108864), ((2930765 : ℚ) / 4194304)), (((2930765 : ℚ) / 4194304), ((25123841 : ℚ) / 33554432)), (((25123841 : ℚ) / 33554432), ((13400781 : ℚ) / 16777216)), (((13400781 : ℚ) / 16777216), ((7539251 : ℚ) / 8388608)), (((7539251 : ℚ) / 8388608), ((31834725 : ℚ) / 33554432)), (((31834725 : ℚ) / 33554432), ((65347171 : ℚ) / 67108864)), (((65347171 : ℚ) / 67108864), ((16756223 : ℚ) / 16777216)), (((16756223 : ℚ) / 16777216), ((8380219 : ℚ) / 8388608)), (((8380219 : ℚ) / 8388608), ((999 : ℚ) / 1000))]
theorem corner0Domain0Cover : pieceCover ((999 : ℚ) / 1000) ((98749 : ℚ) / 1000000) corner0Domain0Pieces = true := by decide +kernel
theorem corner0Domain0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  apply pieceCover_bound ((999 : ℚ) / 1000) (fun x : ℝ => fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x) ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) ((98749 : ℚ) / 1000000) corner0Domain0Pieces (by decide +kernel) corner0Domain0Cover
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
theorem delta1Check : fieldNFCheck D72.NearCorners001.delta1 (fqSum [logFQ ((1 : ℚ) / 400) ((-1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta1Value (x : ℝ) : fval D72.NearCorners001.delta1 x = ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta1Check x
  change fval D72.NearCorners001.delta1 x = fval (fqSum [logFQ ((1 : ℚ) / 400) ((-1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner1Identity (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x = (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) + (((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  have hf : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x = fval D72.NearBinding001.literalField x + fval D72.NearCorners001.delta1 x := by
    convert D72.NearCorners001.corner1Value x using 1 <;> norm_num [d2LitsNearCorners001.q2]
  have ht : lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x = lfieldTower D72.NearBinding001.literalTerms 0 x :=
    (laurent_eq_of_nf (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) D72.NearCorners001.corner1Terms x).trans (D72.NearBinding001.termsValue x).symm
  calc
    _ = (fval D72.NearBinding001.literalField x + fval D72.NearCorners001.delta1 x) + lfieldTower D72.NearBinding001.literalTerms 0 x :=
      congrArg₂ (fun u v : ℝ => u + v) hf ht
    _ = (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) + (((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by rw [delta1Value]; ring
theorem corner1Piece0 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((828367 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer46Lo : ℝ) (d2WiderTransfer46Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer46Lo, d2WiderTransfer46Hi, d2LitsNearWiderTransfers005.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer46Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer46Cap, d2LitsNearWiderTransfers005.q2, d2WiderTransfer46C0, d2WiderTransfer46S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece1 (x : ℝ) (hx : x ∈ Icc ((((828367 : ℚ) / 8388608) : ℚ) : ℝ) ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer50Lo : ℝ) (d2WiderTransfer50Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer50Lo, d2WiderTransfer50Hi, d2LitsNearWiderTransfers006.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer50Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer50Cap, d2LitsNearWiderTransfers006.q2, d2WiderTransfer50C0, d2WiderTransfer50S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece2 (x : ℝ) (hx : x ∈ Icc ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ) ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer54Lo : ℝ) (d2WiderTransfer54Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer54Lo, d2WiderTransfer54Hi, d2LitsNearWiderTransfers006.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer54Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer54Cap, d2LitsNearWiderTransfers006.q2, d2WiderTransfer54C0, d2WiderTransfer54S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece3 (x : ℝ) (hx : x ∈ Icc ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ) ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer58Lo : ℝ) (d2WiderTransfer58Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer58Lo, d2WiderTransfer58Hi, d2LitsNearWiderTransfers007.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer58Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer58Cap, d2LitsNearWiderTransfers007.q2, d2WiderTransfer58C0, d2WiderTransfer58S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece4 (x : ℝ) (hx : x ∈ Icc ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ) ((((313261 : ℚ) / 1048576) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer62Lo : ℝ) (d2WiderTransfer62Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer62Lo, d2WiderTransfer62Hi, d2LitsNearWiderTransfers007.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer62Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer62Cap, d2LitsNearWiderTransfers007.q2, d2WiderTransfer62C0, d2WiderTransfer62S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece5 (x : ℝ) (hx : x ∈ Icc ((((313261 : ℚ) / 1048576) : ℚ) : ℝ) ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer66Lo : ℝ) (d2WiderTransfer66Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer66Lo, d2WiderTransfer66Hi, d2LitsNearWiderTransfers008.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer66Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer66Cap, d2LitsNearWiderTransfers008.q2, d2WiderTransfer66C0, d2WiderTransfer66S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece6 (x : ℝ) (hx : x ∈ Icc ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ) ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer70Lo : ℝ) (d2WiderTransfer70Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer70Lo, d2WiderTransfer70Hi, d2LitsNearWiderTransfers008.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer70Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer70Cap, d2LitsNearWiderTransfers008.q2, d2WiderTransfer70C0, d2WiderTransfer70S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece7 (x : ℝ) (hx : x ∈ Icc ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ) ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer74Lo : ℝ) (d2WiderTransfer74Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer74Lo, d2WiderTransfer74Hi, d2LitsNearWiderTransfers009.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer74Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer74Cap, d2LitsNearWiderTransfers009.q2, d2WiderTransfer74C0, d2WiderTransfer74S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece8 (x : ℝ) (hx : x ∈ Icc ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ) ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer78Lo : ℝ) (d2WiderTransfer78Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer78Lo, d2WiderTransfer78Hi, d2LitsNearWiderTransfers009.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer78Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer78Cap, d2LitsNearWiderTransfers009.q2, d2WiderTransfer78C0, d2WiderTransfer78S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece9 (x : ℝ) (hx : x ∈ Icc ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ) ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope9 x hx
  have hxT : x ∈ Icc (d2WiderTransfer82Lo : ℝ) (d2WiderTransfer82Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer82Lo, d2WiderTransfer82Hi, d2LitsNearWiderTransfers010.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer82Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer82Cap, d2LitsNearWiderTransfers010.q2, d2WiderTransfer82C0, d2WiderTransfer82S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece10 (x : ℝ) (hx : x ∈ Icc ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ) ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope10 x hx
  have hxT : x ∈ Icc (d2WiderTransfer86Lo : ℝ) (d2WiderTransfer86Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer86Lo, d2WiderTransfer86Hi, d2LitsNearWiderTransfers010.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer86Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer86Cap, d2LitsNearWiderTransfers010.q2, d2WiderTransfer86C0, d2WiderTransfer86S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((649441385 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece11 (x : ℝ) (hx : x ∈ Icc ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ) ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope11 x hx
  have hxT : x ∈ Icc (d2WiderTransfer90Lo : ℝ) (d2WiderTransfer90Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer90Lo, d2WiderTransfer90Hi, d2LitsNearWiderTransfers011.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer90Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((357952183878138426799 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer90Cap, d2LitsNearWiderTransfers011.q2, d2WiderTransfer90C0, d2WiderTransfer90S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-304635849631809526527407 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((357952183878138426799 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece12 (x : ℝ) (hx : x ∈ Icc ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ) ((((326484011 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope12 x hx
  have hxT : x ∈ Icc (d2WiderTransfer94Lo : ℝ) (d2WiderTransfer94Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer94Lo, d2WiderTransfer94Hi, d2LitsNearWiderTransfers011.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer94Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1474206701587581144801 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer94Cap, d2LitsNearWiderTransfers011.q2, d2WiderTransfer94C0, d2WiderTransfer94S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1218585796493313133547233 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((1474206701587581144801 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece13 (x : ℝ) (hx : x ∈ Icc ((((326484011 : ℚ) / 536870912) : ℚ) : ℝ) ((((654645743 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope13 x hx
  have hxT : x ∈ Icc (d2WiderTransfer98Lo : ℝ) (d2WiderTransfer98Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer98Lo, d2WiderTransfer98Hi, d2LitsNearWiderTransfers012.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer98Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((188861997272932581765 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer98Cap, d2LitsNearWiderTransfers012.q2, d2WiderTransfer98C0, d2WiderTransfer98S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-152327810721238626632069 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) + ((((188861997272932581765 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece14 (x : ℝ) (hx : x ∈ Icc ((((654645743 : ℚ) / 1073741824) : ℚ) : ℝ) ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope14 x hx
  have hxT : x ∈ Icc (d2WiderTransfer102Lo : ℝ) (d2WiderTransfer102Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer102Lo, d2WiderTransfer102Hi, d2LitsNearWiderTransfers012.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer102Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((773774829148068366265 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer102Cap, d2LitsNearWiderTransfers012.q2, d2WiderTransfer102C0, d2WiderTransfer102S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-609329569725010844567481 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((773774829148068366265 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece15 (x : ℝ) (hx : x ∈ Icc ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ) ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope15 x hx
  have hxT : x ∈ Icc (d2WiderTransfer106Lo : ℝ) (d2WiderTransfer106Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer106Lo, d2WiderTransfer106Hi, d2LitsNearWiderTransfers013.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer106Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1620750504893547881849 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer106Cap, d2LitsNearWiderTransfers013.q2, d2WiderTransfer106C0, d2WiderTransfer106S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1218732340296619100284281 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((1620750504893547881849 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece16 (x : ℝ) (hx : x ∈ Icc ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ) ((((661356627 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope16 x hx
  have hxT : x ∈ Icc (d2WiderTransfer110Lo : ℝ) (d2WiderTransfer110Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer110Lo, d2WiderTransfer110Hi, d2LitsNearWiderTransfers013.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer110Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((418973194549188197207 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer110Cap, d2LitsNearWiderTransfers013.q2, d2WiderTransfer110C0, d2WiderTransfer110S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-304696870642480576297815 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((418973194549188197207 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece17 (x : ℝ) (hx : x ∈ Icc ((((661356627 : ℚ) / 1073741824) : ℚ) : ℝ) ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope17 x hx
  have hxT : x ∈ Icc (d2WiderTransfer114Lo : ℝ) (d2WiderTransfer114Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer114Lo, d2WiderTransfer114Hi, d2LitsNearWiderTransfers014.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer114Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1819221899745516347231 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer114Cap, d2LitsNearWiderTransfers014.q2, d2WiderTransfer114C0, d2WiderTransfer114S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1218930811691471068749663 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((1819221899745516347231 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece18 (x : ℝ) (hx : x ∈ Icc ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ) ((((1327746417 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope18 x hx
  have hxT : x ∈ Icc (d2WiderTransfer118Lo : ℝ) (d2WiderTransfer118Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer118Lo, d2WiderTransfer118Hi, d2LitsNearWiderTransfers014.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer118Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((472774969983535760355 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer118Cap, d2LitsNearWiderTransfers014.q2, d2WiderTransfer118C0, d2WiderTransfer118S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-304750672417914923860963 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((472774969983535760355 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece19 (x : ℝ) (hx : x ∈ Icc ((((1327746417 : ℚ) / 2147483648) : ℚ) : ℝ) ((((664712069 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope19 x hx
  have hxT : x ∈ Icc (d2WiderTransfer122Lo : ℝ) (d2WiderTransfer122Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer122Lo, d2WiderTransfer122Hi, d2LitsNearWiderTransfers015.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer122Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((61347528822902331459 : ℚ) / 37778931862957161709568) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer122Cap, d2LitsNearWiderTransfers015.q2, d2WiderTransfer122C0, d2WiderTransfer122S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-38096084709814325844035 : ℚ) / 37778931862957161709568) : ℚ) : ℝ) + ((((61347528822902331459 : ℚ) / 37778931862957161709568) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece20 (x : ℝ) (hx : x ∈ Icc ((((664712069 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1331101859 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope20 x hx
  have hxT : x ∈ Icc (d2WiderTransfer126Lo : ℝ) (d2WiderTransfer126Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer126Lo, d2WiderTransfer126Hi, d2LitsNearWiderTransfers015.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer126Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((7950334446886927103 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer126Cap, d2LitsNearWiderTransfers015.q2, d2WiderTransfer126C0, d2WiderTransfer126S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-4762292482070814866175 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) + ((((7950334446886927103 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece21 (x : ℝ) (hx : x ∈ Icc ((((1331101859 : ℚ) / 2147483648) : ℚ) : ℝ) ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope21 x hx
  have hxT : x ∈ Icc (d2WiderTransfer130Lo : ℝ) (d2WiderTransfer130Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer130Lo, d2WiderTransfer130Hi, d2LitsNearWiderTransfers016.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer130Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2107594563250375816115 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer130Cap, d2LitsNearWiderTransfers016.q2, d2WiderTransfer130C0, d2WiderTransfer130S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219219184354975928218547 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2107594563250375816115 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece22 (x : ℝ) (hx : x ∈ Icc ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ) ((((1334457301 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope22 x hx
  have hxT : x ∈ Icc (d2WiderTransfer134Lo : ℝ) (d2WiderTransfer134Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer134Lo, d2WiderTransfer134Hi, d2LitsNearWiderTransfers016.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer134Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17031627778554332461 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer134Cap, d2LitsNearWiderTransfers016.q2, d2WiderTransfer134C0, d2WiderTransfer134S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-9525715923026410210605 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) + ((((17031627778554332461 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece23 (x : ℝ) (hx : x ∈ Icc ((((1334457301 : ℚ) / 2147483648) : ℚ) : ℝ) ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope23 x hx
  have hxT : x ∈ Icc (d2WiderTransfer138Lo : ℝ) (d2WiderTransfer138Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer138Lo, d2WiderTransfer138Hi, d2LitsNearWiderTransfers017.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer138Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2252647598101690118919 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer138Cap, d2LitsNearWiderTransfers017.q2, d2WiderTransfer138C0, d2WiderTransfer138S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219364237389827242521351 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2252647598101690118919 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece24 (x : ℝ) (hx : x ∈ Icc ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1337812743 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope24 x hx
  have hxT : x ∈ Icc (d2WiderTransfer142Lo : ℝ) (d2WiderTransfer142Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer142Lo, d2WiderTransfer142Hi, d2LitsNearWiderTransfers017.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer142Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1162696448405478776057 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer142Cap, d2LitsNearWiderTransfers017.q2, d2WiderTransfer142C0, d2WiderTransfer142S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-609718491344268254977273 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1162696448405478776057 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece25 (x : ℝ) (hx : x ∈ Icc ((((1337812743 : ℚ) / 2147483648) : ℚ) : ℝ) ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope25 x hx
  have hxT : x ∈ Icc (d2WiderTransfer146Lo : ℝ) (d2WiderTransfer146Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer146Lo, d2WiderTransfer146Hi, d2LitsNearWiderTransfers018.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer146Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((149892803860600690063 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer146Cap, d2LitsNearWiderTransfers018.q2, d2WiderTransfer146C0, d2WiderTransfer146S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-76219367165843447715215 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) + ((((149892803860600690063 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece26 (x : ℝ) (hx : x ∈ Icc ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ) ((((1341168185 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope26 x hx
  have hxT : x ∈ Icc (d2WiderTransfer150Lo : ℝ) (d2WiderTransfer150Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer150Lo, d2WiderTransfer150Hi, d2LitsNearWiderTransfers018.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer150Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2471324106762310774949 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer150Cap, d2LitsNearWiderTransfers018.q2, d2WiderTransfer150C0, d2WiderTransfer150S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219582913898487863177381 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2471324106762310774949 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece27 (x : ℝ) (hx : x ∈ Icc ((((1341168185 : ℚ) / 2147483648) : ℚ) : ℝ) ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope27 x hx
  have hxT : x ∈ Icc (d2WiderTransfer154Lo : ℝ) (d2WiderTransfer154Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer154Lo, d2WiderTransfer154Hi, d2LitsNearWiderTransfers019.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer154Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((318063906175397004093 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer154Cap, d2LitsNearWiderTransfers019.q2, d2WiderTransfer154C0, d2WiderTransfer154S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-152457012630141091054397 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) + ((((318063906175397004093 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece28 (x : ℝ) (hx : x ∈ Icc ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope28 x hx
  have hxT : x ∈ Icc (d2WiderTransfer158Lo : ℝ) (d2WiderTransfer158Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer158Lo, d2WiderTransfer158Hi, d2LitsNearWiderTransfers019.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer158Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2617846911167768580485 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer158Cap, d2LitsNearWiderTransfers019.q2, d2WiderTransfer158C0, d2WiderTransfer158S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219729436702893320982917 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2617846911167768580485 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece29 (x : ℝ) (hx : x ∈ Icc ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ) ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope29 x hx
  have hxT : x ∈ Icc (d2WiderTransfer162Lo : ℝ) (d2WiderTransfer162Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer162Lo, d2WiderTransfer162Hi, d2LitsNearWiderTransfers020.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer162Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2691331717425410526057 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer162Cap, d2LitsNearWiderTransfers020.q2, d2WiderTransfer162C0, d2WiderTransfer162S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219802921509150962928489 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2691331717425410526057 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece30 (x : ℝ) (hx : x ∈ Icc ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ) ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope30 x hx
  have hxT : x ∈ Icc (d2WiderTransfer166Lo : ℝ) (d2WiderTransfer166Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer166Lo, d2WiderTransfer166Hi, d2LitsNearWiderTransfers020.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer166Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2764966297471840836517 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer166Cap, d2LitsNearWiderTransfers020.q2, d2WiderTransfer166C0, d2WiderTransfer166S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219876556089197393238949 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2764966297471840836517 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece31 (x : ℝ) (hx : x ∈ Icc ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ) ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope31 x hx
  have hxT : x ∈ Icc (d2WiderTransfer170Lo : ℝ) (d2WiderTransfer170Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer170Lo, d2WiderTransfer170Hi, d2LitsNearWiderTransfers021.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer170Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2838751284562214786385 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer170Cap, d2LitsNearWiderTransfers021.q2, d2WiderTransfer170C0, d2WiderTransfer170S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219950341076287767188817 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2838751284562214786385 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece32 (x : ℝ) (hx : x ∈ Icc ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope32 x hx
  have hxT : x ∈ Icc (d2WiderTransfer174Lo : ℝ) (d2WiderTransfer174Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer174Lo, d2WiderTransfer174Hi, d2LitsNearWiderTransfers021.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer174Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1456343657972225333883 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer174Cap, d2LitsNearWiderTransfers021.q2, d2WiderTransfer174C0, d2WiderTransfer174S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-610012138553835001535099 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1456343657972225333883 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece33 (x : ℝ) (hx : x ∈ Icc ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ) ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope33 x hx
  have hxT : x ∈ Icc (d2WiderTransfer178Lo : ℝ) (d2WiderTransfer178Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer178Lo, d2WiderTransfer178Hi, d2LitsNearWiderTransfers022.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer178Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1493387516446464078587 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer178Cap, d2LitsNearWiderTransfers022.q2, d2WiderTransfer178C0, d2WiderTransfer178S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-610049182412309240279803 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1493387516446464078587 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece34 (x : ℝ) (hx : x ∈ Icc ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ) ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope34 x hx
  have hxT : x ∈ Icc (d2WiderTransfer182Lo : ℝ) (d2WiderTransfer182Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer182Lo, d2WiderTransfer182Hi, d2LitsNearWiderTransfers022.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer182Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1567704054461560565645 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer182Cap, d2LitsNearWiderTransfers022.q2, d2WiderTransfer182C0, d2WiderTransfer182S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-610123498950324336766861 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1567704054461560565645 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece35 (x : ℝ) (hx : x ∈ Icc ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ) ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope35 x hx
  have hxT : x ∈ Icc (d2WiderTransfer186Lo : ℝ) (d2WiderTransfer186Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer186Lo, d2WiderTransfer186Hi, d2LitsNearWiderTransfers023.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer186Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3284655724680182058789 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer186Cap, d2LitsNearWiderTransfers023.q2, d2WiderTransfer186C0, d2WiderTransfer186S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1220396245516405734461221 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((3284655724680182058789 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece36 (x : ℝ) (hx : x ∈ Icc ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ) ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope36 x hx
  have hxT : x ∈ Icc (d2WiderTransfer190Lo : ℝ) (d2WiderTransfer190Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer190Lo, d2WiderTransfer190Hi, d2LitsNearWiderTransfers023.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer190Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3585015757831320625385 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer190Cap, d2LitsNearWiderTransfers023.q2, d2WiderTransfer190C0, d2WiderTransfer190S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1220696605549556873027817 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((3585015757831320625385 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece37 (x : ℝ) (hx : x ∈ Icc ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ) ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope37 x hx
  have hxT : x ∈ Icc (d2WiderTransfer194Lo : ℝ) (d2WiderTransfer194Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer194Lo, d2WiderTransfer194Hi, d2LitsNearWiderTransfers024.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer194Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3887898182126945858551 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer194Cap, d2LitsNearWiderTransfers024.q2, d2WiderTransfer194C0, d2WiderTransfer194S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1220999487973852498260983 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((3887898182126945858551 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece38 (x : ℝ) (hx : x ∈ Icc ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ) ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope38 x hx
  have hxT : x ∈ Icc (d2WiderTransfer198Lo : ℝ) (d2WiderTransfer198Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer198Lo, d2WiderTransfer198Hi, d2LitsNearWiderTransfers024.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer198Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4193347169859673716761 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer198Cap, d2LitsNearWiderTransfers024.q2, d2WiderTransfer198C0, d2WiderTransfer198S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1221304936961585226119193 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((4193347169859673716761 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece39 (x : ℝ) (hx : x ∈ Icc ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ) ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope39 x hx
  have hxT : x ∈ Icc (d2WiderTransfer202Lo : ℝ) (d2WiderTransfer202Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer202Lo, d2WiderTransfer202Hi, d2LitsNearWiderTransfers025.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer202Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4812127375716014614645 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer202Cap, d2LitsNearWiderTransfers025.q2, d2WiderTransfer202C0, d2WiderTransfer202S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1221923717167441567017077 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((4812127375716014614645 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece40 (x : ℝ) (hx : x ∈ Icc ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ) ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope40 x hx
  have hxT : x ∈ Icc (d2WiderTransfer206Lo : ℝ) (d2WiderTransfer206Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer206Lo, d2WiderTransfer206Hi, d2LitsNearWiderTransfers025.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer206Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3041282164444953296725 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer206Cap, d2LitsNearWiderTransfers025.q2, d2WiderTransfer206C0, d2WiderTransfer206S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-611597077060307729497941 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((3041282164444953296725 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece41 (x : ℝ) (hx : x ∈ Icc ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ) ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope41 x hx
  have hxT : x ∈ Icc (d2WiderTransfer210Lo : ℝ) (d2WiderTransfer210Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer210Lo, d2WiderTransfer210Hi, d2LitsNearWiderTransfers026.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer210Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1849900766862984443043 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer210Cap, d2LitsNearWiderTransfers026.q2, d2WiderTransfer210C0, d2WiderTransfer210S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-306127798214794372543651 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((1849900766862984443043 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece42 (x : ℝ) (hx : x ∈ Icc ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ) ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope42 x hx
  have hxT : x ∈ Icc (d2WiderTransfer214Lo : ℝ) (d2WiderTransfer214Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer214Lo, d2WiderTransfer214Hi, d2LitsNearWiderTransfers026.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer214Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((10188572794624507164743 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer214Cap, d2LitsNearWiderTransfers026.q2, d2WiderTransfer214C0, d2WiderTransfer214S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1227300162586350059567175 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((10188572794624507164743 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece43 (x : ℝ) (hx : x ∈ Icc ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ) ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope43 x hx
  have hxT : x ∈ Icc (d2WiderTransfer218Lo : ℝ) (d2WiderTransfer218Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer218Lo, d2WiderTransfer218Hi, d2LitsNearWiderTransfers027.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer218Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4130355511903425424277 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer218Cap, d2LitsNearWiderTransfers027.q2, d2WiderTransfer218C0, d2WiderTransfer218S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-308408252959834813524885 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((4130355511903425424277 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece44 (x : ℝ) (hx : x ∈ Icc ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ) ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope44 x hx
  have hxT : x ∈ Icc (d2WiderTransfer222Lo : ℝ) (d2WiderTransfer222Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer222Lo, d2WiderTransfer222Hi, d2LitsNearWiderTransfers027.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer222Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((24239257739226882297541 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer222Cap, d2LitsNearWiderTransfers027.q2, d2WiderTransfer222C0, d2WiderTransfer222S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1241350847530952434699973 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((24239257739226882297541 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece45 (x : ℝ) (hx : x ∈ Icc ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ) ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope45 x hx
  have hxT : x ∈ Icc (d2WiderTransfer226Lo : ℝ) (d2WiderTransfer226Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer226Lo, d2WiderTransfer226Hi, d2LitsNearWiderTransfers028.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer226Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((48017980514036806306389 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer226Cap, d2LitsNearWiderTransfers028.q2, d2WiderTransfer226C0, d2WiderTransfer226S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1265129570305762358708821 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((48017980514036806306389 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece46 (x : ℝ) (hx : x ∈ Icc ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ) ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope46 x hx
  have hxT : x ∈ Icc (d2WiderTransfer230Lo : ℝ) (d2WiderTransfer230Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer230Lo, d2WiderTransfer230Hi, d2LitsNearWiderTransfers028.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer230Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((35745599033710447825519 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer230Cap, d2LitsNearWiderTransfers028.q2, d2WiderTransfer230C0, d2WiderTransfer230S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-644301393929573224026735 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((35745599033710447825519 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece47 (x : ℝ) (hx : x ∈ Icc ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ) ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope47 x hx
  have hxT : x ∈ Icc (d2WiderTransfer234Lo : ℝ) (d2WiderTransfer234Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer234Lo, d2WiderTransfer234Hi, d2LitsNearWiderTransfers029.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer234Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((47256162031528428522913 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer234Cap, d2LitsNearWiderTransfers029.q2, d2WiderTransfer234C0, d2WiderTransfer234S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-655811956927391204724129 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((47256162031528428522913 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece48 (x : ℝ) (hx : x ∈ Icc ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ) ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope48 x hx
  have hxT : x ∈ Icc (d2WiderTransfer238Lo : ℝ) (d2WiderTransfer238Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer238Lo, d2WiderTransfer238Hi, d2LitsNearWiderTransfers029.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer238Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((49771151816960380668549 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer238Cap, d2LitsNearWiderTransfers029.q2, d2WiderTransfer238C0, d2WiderTransfer238S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-354049049264891768769157 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((49771151816960380668549 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece49 (x : ℝ) (hx : x ∈ Icc ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ) ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope49 x hx
  have hxT : x ∈ Icc (d2WiderTransfer242Lo : ℝ) (d2WiderTransfer242Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer242Lo, d2WiderTransfer242Hi, d2LitsNearWiderTransfers030.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer242Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((206782343276902498879489 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer242Cap, d2LitsNearWiderTransfers030.q2, d2WiderTransfer242C0, d2WiderTransfer242S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1423893933068628051281921 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((206782343276902498879489 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece50 (x : ℝ) (hx : x ∈ Icc ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope50 x hx
  have hxT : x ∈ Icc (d2WiderTransfer246Lo : ℝ) (d2WiderTransfer246Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer246Lo, d2WiderTransfer246Hi, d2LitsNearWiderTransfers030.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer246Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((206783948238830734700547 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer246Cap, d2LitsNearWiderTransfers030.q2, d2WiderTransfer246C0, d2WiderTransfer246S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1423895538030556287102979 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((206783948238830734700547 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner1Domain0Pieces : List (ℚ × ℚ) := [(((98749 : ℚ) / 1000000), ((828367 : ℚ) / 8388608)), (((828367 : ℚ) / 8388608), ((8304657 : ℚ) / 67108864)), (((8304657 : ℚ) / 67108864), ((4991189 : ℚ) / 33554432)), (((4991189 : ℚ) / 33554432), ((3334455 : ℚ) / 16777216)), (((3334455 : ℚ) / 16777216), ((313261 : ℚ) / 1048576)), (((313261 : ℚ) / 1048576), ((6689897 : ℚ) / 16777216)), (((6689897 : ℚ) / 16777216), ((4183809 : ℚ) / 8388608)), (((4183809 : ℚ) / 8388608), ((18412957 : ℚ) / 33554432)), (((18412957 : ℚ) / 33554432), ((38503635 : ℚ) / 67108864)), (((38503635 : ℚ) / 67108864), ((78684991 : ℚ) / 134217728)), (((78684991 : ℚ) / 134217728), ((10045339 : ℚ) / 16777216)), (((10045339 : ℚ) / 16777216), ((162403145 : ℚ) / 268435456)), (((162403145 : ℚ) / 268435456), ((326484011 : ℚ) / 536870912)), (((326484011 : ℚ) / 536870912), ((654645743 : ℚ) / 1073741824)), (((654645743 : ℚ) / 1073741824), ((82040433 : ℚ) / 134217728)), (((82040433 : ℚ) / 134217728), ((329839453 : ℚ) / 536870912)), (((329839453 : ℚ) / 536870912), ((661356627 : ℚ) / 1073741824)), (((661356627 : ℚ) / 1073741824), ((165758587 : ℚ) / 268435456)), (((165758587 : ℚ) / 268435456), ((1327746417 : ℚ) / 2147483648)), (((1327746417 : ℚ) / 2147483648), ((664712069 : ℚ) / 1073741824)), (((664712069 : ℚ) / 1073741824), ((1331101859 : ℚ) / 2147483648)), (((1331101859 : ℚ) / 2147483648), ((333194895 : ℚ) / 536870912)), (((333194895 : ℚ) / 536870912), ((1334457301 : ℚ) / 2147483648)), (((1334457301 : ℚ) / 2147483648), ((668067511 : ℚ) / 1073741824)), (((668067511 : ℚ) / 1073741824), ((1337812743 : ℚ) / 2147483648)), (((1337812743 : ℚ) / 2147483648), ((41859077 : ℚ) / 67108864)), (((41859077 : ℚ) / 67108864), ((1341168185 : ℚ) / 2147483648)), (((1341168185 : ℚ) / 2147483648), ((671422953 : ℚ) / 1073741824)), (((671422953 : ℚ) / 1073741824), ((1344523627 : ℚ) / 2147483648)), (((1344523627 : ℚ) / 2147483648), ((336550337 : ℚ) / 536870912)), (((336550337 : ℚ) / 536870912), ((1347879069 : ℚ) / 2147483648)), (((1347879069 : ℚ) / 2147483648), ((674778395 : ℚ) / 1073741824)), (((674778395 : ℚ) / 1073741824), ((1351234511 : ℚ) / 2147483648)), (((1351234511 : ℚ) / 2147483648), ((169114029 : ℚ) / 268435456)), (((169114029 : ℚ) / 268435456), ((678133837 : ℚ) / 1073741824)), (((678133837 : ℚ) / 1073741824), ((339905779 : ℚ) / 536870912)), (((339905779 : ℚ) / 536870912), ((85395875 : ℚ) / 134217728)), (((85395875 : ℚ) / 134217728), ((343261221 : ℚ) / 536870912)), (((343261221 : ℚ) / 536870912), ((172469471 : ℚ) / 268435456)), (((172469471 : ℚ) / 268435456), ((21768399 : ℚ) / 33554432)), (((21768399 : ℚ) / 33554432), ((88751317 : ℚ) / 134217728)), (((88751317 : ℚ) / 134217728), ((45214519 : ℚ) / 67108864)), (((45214519 : ℚ) / 67108864), ((2930765 : ℚ) / 4194304)), (((2930765 : ℚ) / 4194304), ((25123841 : ℚ) / 33554432)), (((25123841 : ℚ) / 33554432), ((13400781 : ℚ) / 16777216)), (((13400781 : ℚ) / 16777216), ((7539251 : ℚ) / 8388608)), (((7539251 : ℚ) / 8388608), ((31834725 : ℚ) / 33554432)), (((31834725 : ℚ) / 33554432), ((65347171 : ℚ) / 67108864)), (((65347171 : ℚ) / 67108864), ((16756223 : ℚ) / 16777216)), (((16756223 : ℚ) / 16777216), ((8380219 : ℚ) / 8388608)), (((8380219 : ℚ) / 8388608), ((999 : ℚ) / 1000))]
theorem corner1Domain0Cover : pieceCover ((999 : ℚ) / 1000) ((98749 : ℚ) / 1000000) corner1Domain0Pieces = true := by decide +kernel
theorem corner1Domain0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  apply pieceCover_bound ((999 : ℚ) / 1000) (fun x : ℝ => fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x) ((((-553478271191 : ℚ) / 549755813888) : ℚ) : ℝ) ((98749 : ℚ) / 1000000) corner1Domain0Pieces (by decide +kernel) corner1Domain0Cover
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
theorem delta2Check : fieldNFCheck D72.NearCorners001.delta2 (fqSum [logFQ ((1 : ℚ) / 4400) ((-1 : ℚ) / 1), logFQ ((-1 : ℚ) / 440) ((1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta2Value (x : ℝ) : fval D72.NearCorners001.delta2 x = ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta2Check x
  change fval D72.NearCorners001.delta2 x = fval (fqSum [logFQ ((1 : ℚ) / 4400) ((-1 : ℚ) / 1), logFQ ((-1 : ℚ) / 440) ((1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner2Identity (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x = (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) + (((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  have hf : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x = fval D72.NearBinding001.literalField x + fval D72.NearCorners001.delta2 x := by
    convert D72.NearCorners001.corner2Value x using 1 <;> norm_num [d2LitsNearCorners001.q2]
  have ht : lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x = lfieldTower D72.NearBinding001.literalTerms 0 x :=
    (laurent_eq_of_nf (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) D72.NearCorners001.corner2Terms x).trans (D72.NearBinding001.termsValue x).symm
  calc
    _ = (fval D72.NearBinding001.literalField x + fval D72.NearCorners001.delta2 x) + lfieldTower D72.NearBinding001.literalTerms 0 x :=
      congrArg₂ (fun u v : ℝ => u + v) hf ht
    _ = (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) + (((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)|) := by rw [delta2Value]; ring
theorem corner2Piece0 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((828367 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer47Lo : ℝ) (d2WiderTransfer47Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer47Lo, d2WiderTransfer47Hi, d2LitsNearWiderTransfers005.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer47Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer47Cap, d2LitsNearWiderTransfers005.q2, d2WiderTransfer47C0, d2WiderTransfer47S0, d2WiderTransfer47C1, d2WiderTransfer47S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece1 (x : ℝ) (hx : x ∈ Icc ((((828367 : ℚ) / 8388608) : ℚ) : ℝ) ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer51Lo : ℝ) (d2WiderTransfer51Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer51Lo, d2WiderTransfer51Hi, d2LitsNearWiderTransfers006.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer51Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer51Cap, d2LitsNearWiderTransfers006.q2, d2WiderTransfer51C0, d2WiderTransfer51S0, d2WiderTransfer51C1, d2WiderTransfer51S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece2 (x : ℝ) (hx : x ∈ Icc ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ) ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer55Lo : ℝ) (d2WiderTransfer55Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer55Lo, d2WiderTransfer55Hi, d2LitsNearWiderTransfers006.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer55Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer55Cap, d2LitsNearWiderTransfers006.q2, d2WiderTransfer55C0, d2WiderTransfer55S0, d2WiderTransfer55C1, d2WiderTransfer55S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece3 (x : ℝ) (hx : x ∈ Icc ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ) ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer59Lo : ℝ) (d2WiderTransfer59Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer59Lo, d2WiderTransfer59Hi, d2LitsNearWiderTransfers007.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer59Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer59Cap, d2LitsNearWiderTransfers007.q2, d2WiderTransfer59C0, d2WiderTransfer59S0, d2WiderTransfer59C1, d2WiderTransfer59S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece4 (x : ℝ) (hx : x ∈ Icc ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ) ((((313261 : ℚ) / 1048576) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer63Lo : ℝ) (d2WiderTransfer63Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer63Lo, d2WiderTransfer63Hi, d2LitsNearWiderTransfers007.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer63Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer63Cap, d2LitsNearWiderTransfers007.q2, d2WiderTransfer63C0, d2WiderTransfer63S0, d2WiderTransfer63C1, d2WiderTransfer63S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece5 (x : ℝ) (hx : x ∈ Icc ((((313261 : ℚ) / 1048576) : ℚ) : ℝ) ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer67Lo : ℝ) (d2WiderTransfer67Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer67Lo, d2WiderTransfer67Hi, d2LitsNearWiderTransfers008.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer67Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer67Cap, d2LitsNearWiderTransfers008.q2, d2WiderTransfer67C0, d2WiderTransfer67S0, d2WiderTransfer67C1, d2WiderTransfer67S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece6 (x : ℝ) (hx : x ∈ Icc ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ) ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer71Lo : ℝ) (d2WiderTransfer71Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer71Lo, d2WiderTransfer71Hi, d2LitsNearWiderTransfers008.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer71Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer71Cap, d2LitsNearWiderTransfers008.q2, d2WiderTransfer71C0, d2WiderTransfer71S0, d2WiderTransfer71C1, d2WiderTransfer71S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece7 (x : ℝ) (hx : x ∈ Icc ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ) ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer75Lo : ℝ) (d2WiderTransfer75Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer75Lo, d2WiderTransfer75Hi, d2LitsNearWiderTransfers009.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer75Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer75Cap, d2LitsNearWiderTransfers009.q2, d2WiderTransfer75C0, d2WiderTransfer75S0, d2WiderTransfer75C1, d2WiderTransfer75S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece8 (x : ℝ) (hx : x ∈ Icc ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ) ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer79Lo : ℝ) (d2WiderTransfer79Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer79Lo, d2WiderTransfer79Hi, d2LitsNearWiderTransfers009.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer79Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer79Cap, d2LitsNearWiderTransfers009.q2, d2WiderTransfer79C0, d2WiderTransfer79S0, d2WiderTransfer79C1, d2WiderTransfer79S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece9 (x : ℝ) (hx : x ∈ Icc ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ) ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope9 x hx
  have hxT : x ∈ Icc (d2WiderTransfer83Lo : ℝ) (d2WiderTransfer83Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer83Lo, d2WiderTransfer83Hi, d2LitsNearWiderTransfers010.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer83Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer83Cap, d2LitsNearWiderTransfers010.q2, d2WiderTransfer83C0, d2WiderTransfer83S0, d2WiderTransfer83C1, d2WiderTransfer83S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece10 (x : ℝ) (hx : x ∈ Icc ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ) ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope10 x hx
  have hxT : x ∈ Icc (d2WiderTransfer87Lo : ℝ) (d2WiderTransfer87Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer87Lo, d2WiderTransfer87Hi, d2LitsNearWiderTransfers010.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer87Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer87Cap, d2LitsNearWiderTransfers010.q2, d2WiderTransfer87C0, d2WiderTransfer87S0, d2WiderTransfer87C1, d2WiderTransfer87S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((2436024149 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece11 (x : ℝ) (hx : x ∈ Icc ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ) ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope11 x hx
  have hxT : x ∈ Icc (d2WiderTransfer91Lo : ℝ) (d2WiderTransfer91Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer91Lo, d2WiderTransfer91Hi, d2LitsNearWiderTransfers011.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer91Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((670527226037072262575 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer91Cap, d2LitsNearWiderTransfers011.q2, d2WiderTransfer91C0, d2WiderTransfer91S0, d2WiderTransfer91C1, d2WiderTransfer91S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-304635849631809526527407 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((670527226037072262575 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece12 (x : ℝ) (hx : x ∈ Icc ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ) ((((326484011 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope12 x hx
  have hxT : x ∈ Icc (d2WiderTransfer95Lo : ℝ) (d2WiderTransfer95Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer95Lo, d2WiderTransfer95Hi, d2LitsNearWiderTransfers011.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer95Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2724506870223316487905 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer95Cap, d2LitsNearWiderTransfers011.q2, d2WiderTransfer95C0, d2WiderTransfer95S0, d2WiderTransfer95C1, d2WiderTransfer95S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1218585796493313133547233 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2724506870223316487905 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece13 (x : ℝ) (hx : x ∈ Icc ((((326484011 : ℚ) / 536870912) : ℚ) : ℝ) ((((654645743 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope13 x hx
  have hxT : x ∈ Icc (d2WiderTransfer99Lo : ℝ) (d2WiderTransfer99Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer99Lo, d2WiderTransfer99Hi, d2LitsNearWiderTransfers012.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer99Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((345149518352399499653 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer99Cap, d2LitsNearWiderTransfers012.q2, d2WiderTransfer99C0, d2WiderTransfer99S0, d2WiderTransfer99C1, d2WiderTransfer99S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-152327810721238626632069 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) + ((((345149518352399499653 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece14 (x : ℝ) (hx : x ∈ Icc ((((654645743 : ℚ) / 1073741824) : ℚ) : ℝ) ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope14 x hx
  have hxT : x ∈ Icc (d2WiderTransfer103Lo : ℝ) (d2WiderTransfer103Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer103Lo, d2WiderTransfer103Hi, d2LitsNearWiderTransfers012.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer103Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1398924913465936037817 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer103Cap, d2LitsNearWiderTransfers012.q2, d2WiderTransfer103C0, d2WiderTransfer103S0, d2WiderTransfer103C1, d2WiderTransfer103S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-609329569725010844567481 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1398924913465936037817 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece15 (x : ℝ) (hx : x ∈ Icc ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ) ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope15 x hx
  have hxT : x ∈ Icc (d2WiderTransfer107Lo : ℝ) (d2WiderTransfer107Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer107Lo, d2WiderTransfer107Hi, d2LitsNearWiderTransfers013.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer107Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2871050673529283224953 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer107Cap, d2LitsNearWiderTransfers013.q2, d2WiderTransfer107C0, d2WiderTransfer107S0, d2WiderTransfer107C1, d2WiderTransfer107S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1218732340296619100284281 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2871050673529283224953 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece16 (x : ℝ) (hx : x ∈ Icc ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ) ((((661356627 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope16 x hx
  have hxT : x ∈ Icc (d2WiderTransfer111Lo : ℝ) (d2WiderTransfer111Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer111Lo, d2WiderTransfer111Hi, d2LitsNearWiderTransfers013.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer111Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((731548236708122032983 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer111Cap, d2LitsNearWiderTransfers013.q2, d2WiderTransfer111C0, d2WiderTransfer111S0, d2WiderTransfer111C1, d2WiderTransfer111S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-304696870642480576297815 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((731548236708122032983 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece17 (x : ℝ) (hx : x ∈ Icc ((((661356627 : ℚ) / 1073741824) : ℚ) : ℝ) ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope17 x hx
  have hxT : x ∈ Icc (d2WiderTransfer115Lo : ℝ) (d2WiderTransfer115Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer115Lo, d2WiderTransfer115Hi, d2LitsNearWiderTransfers014.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer115Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3069522068381251690335 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer115Cap, d2LitsNearWiderTransfers014.q2, d2WiderTransfer115C0, d2WiderTransfer115S0, d2WiderTransfer115C1, d2WiderTransfer115S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1218930811691471068749663 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((3069522068381251690335 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece18 (x : ℝ) (hx : x ∈ Icc ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ) ((((1327746417 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope18 x hx
  have hxT : x ∈ Icc (d2WiderTransfer119Lo : ℝ) (d2WiderTransfer119Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer119Lo, d2WiderTransfer119Hi, d2LitsNearWiderTransfers014.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer119Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((785350012142469596131 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer119Cap, d2LitsNearWiderTransfers014.q2, d2WiderTransfer119C0, d2WiderTransfer119S0, d2WiderTransfer119C1, d2WiderTransfer119S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-304750672417914923860963 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((785350012142469596131 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece19 (x : ℝ) (hx : x ∈ Icc ((((1327746417 : ℚ) / 2147483648) : ℚ) : ℝ) ((((664712069 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope19 x hx
  have hxT : x ∈ Icc (d2WiderTransfer123Lo : ℝ) (d2WiderTransfer123Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer123Lo, d2WiderTransfer123Hi, d2LitsNearWiderTransfers015.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer123Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((100419409092769060931 : ℚ) / 37778931862957161709568) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer123Cap, d2LitsNearWiderTransfers015.q2, d2WiderTransfer123C0, d2WiderTransfer123S0, d2WiderTransfer123C1, d2WiderTransfer123S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-38096084709814325844035 : ℚ) / 37778931862957161709568) : ℚ) : ℝ) + ((((100419409092769060931 : ℚ) / 37778931862957161709568) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece20 (x : ℝ) (hx : x ∈ Icc ((((664712069 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1331101859 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope20 x hx
  have hxT : x ∈ Icc (d2WiderTransfer127Lo : ℝ) (d2WiderTransfer127Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer127Lo, d2WiderTransfer127Hi, d2LitsNearWiderTransfers015.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer127Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((12834319480620268287 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer127Cap, d2LitsNearWiderTransfers015.q2, d2WiderTransfer127C0, d2WiderTransfer127S0, d2WiderTransfer127C1, d2WiderTransfer127S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-4762292482070814866175 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) + ((((12834319480620268287 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece21 (x : ℝ) (hx : x ∈ Icc ((((1331101859 : ℚ) / 2147483648) : ℚ) : ℝ) ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope21 x hx
  have hxT : x ∈ Icc (d2WiderTransfer131Lo : ℝ) (d2WiderTransfer131Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer131Lo, d2WiderTransfer131Hi, d2LitsNearWiderTransfers016.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer131Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3357894731886111159219 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer131Cap, d2LitsNearWiderTransfers016.q2, d2WiderTransfer131C0, d2WiderTransfer131S0, d2WiderTransfer131C1, d2WiderTransfer131S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219219184354975928218547 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((3357894731886111159219 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece22 (x : ℝ) (hx : x ∈ Icc ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ) ((((1334457301 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope22 x hx
  have hxT : x ∈ Icc (d2WiderTransfer135Lo : ℝ) (d2WiderTransfer135Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer135Lo, d2WiderTransfer135Hi, d2LitsNearWiderTransfers016.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer135Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((26799597846021014829 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer135Cap, d2LitsNearWiderTransfers016.q2, d2WiderTransfer135C0, d2WiderTransfer135S0, d2WiderTransfer135C1, d2WiderTransfer135S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-9525715923026410210605 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) + ((((26799597846021014829 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece23 (x : ℝ) (hx : x ∈ Icc ((((1334457301 : ℚ) / 2147483648) : ℚ) : ℝ) ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope23 x hx
  have hxT : x ∈ Icc (d2WiderTransfer139Lo : ℝ) (d2WiderTransfer139Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer139Lo, d2WiderTransfer139Hi, d2LitsNearWiderTransfers017.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer139Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3502947766737425462023 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer139Cap, d2LitsNearWiderTransfers017.q2, d2WiderTransfer139C0, d2WiderTransfer139S0, d2WiderTransfer139C1, d2WiderTransfer139S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219364237389827242521351 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((3502947766737425462023 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece24 (x : ℝ) (hx : x ∈ Icc ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1337812743 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope24 x hx
  have hxT : x ∈ Icc (d2WiderTransfer143Lo : ℝ) (d2WiderTransfer143Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer143Lo, d2WiderTransfer143Hi, d2LitsNearWiderTransfers017.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer143Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1787846532723346447609 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer143Cap, d2LitsNearWiderTransfers017.q2, d2WiderTransfer143C0, d2WiderTransfer143S0, d2WiderTransfer143C1, d2WiderTransfer143S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-609718491344268254977273 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1787846532723346447609 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece25 (x : ℝ) (hx : x ∈ Icc ((((1337812743 : ℚ) / 2147483648) : ℚ) : ℝ) ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope25 x hx
  have hxT : x ∈ Icc (d2WiderTransfer147Lo : ℝ) (d2WiderTransfer147Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer147Lo, d2WiderTransfer147Hi, d2LitsNearWiderTransfers018.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer147Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((228036564400334149007 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer147Cap, d2LitsNearWiderTransfers018.q2, d2WiderTransfer147C0, d2WiderTransfer147S0, d2WiderTransfer147C1, d2WiderTransfer147S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-76219367165843447715215 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) + ((((228036564400334149007 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece26 (x : ℝ) (hx : x ∈ Icc ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ) ((((1341168185 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope26 x hx
  have hxT : x ∈ Icc (d2WiderTransfer151Lo : ℝ) (d2WiderTransfer151Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer151Lo, d2WiderTransfer151Hi, d2LitsNearWiderTransfers018.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer151Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3721624275398046118053 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer151Cap, d2LitsNearWiderTransfers018.q2, d2WiderTransfer151C0, d2WiderTransfer151S0, d2WiderTransfer151C1, d2WiderTransfer151S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219582913898487863177381 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((3721624275398046118053 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece27 (x : ℝ) (hx : x ∈ Icc ((((1341168185 : ℚ) / 2147483648) : ℚ) : ℝ) ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope27 x hx
  have hxT : x ∈ Icc (d2WiderTransfer155Lo : ℝ) (d2WiderTransfer155Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer155Lo, d2WiderTransfer155Hi, d2LitsNearWiderTransfers019.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer155Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((474351427254863921981 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer155Cap, d2LitsNearWiderTransfers019.q2, d2WiderTransfer155C0, d2WiderTransfer155S0, d2WiderTransfer155C1, d2WiderTransfer155S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-152457012630141091054397 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) + ((((474351427254863921981 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece28 (x : ℝ) (hx : x ∈ Icc ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope28 x hx
  have hxT : x ∈ Icc (d2WiderTransfer159Lo : ℝ) (d2WiderTransfer159Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer159Lo, d2WiderTransfer159Hi, d2LitsNearWiderTransfers019.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer159Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3868147079803503923589 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer159Cap, d2LitsNearWiderTransfers019.q2, d2WiderTransfer159C0, d2WiderTransfer159S0, d2WiderTransfer159C1, d2WiderTransfer159S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219729436702893320982917 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((3868147079803503923589 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece29 (x : ℝ) (hx : x ∈ Icc ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ) ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope29 x hx
  have hxT : x ∈ Icc (d2WiderTransfer163Lo : ℝ) (d2WiderTransfer163Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer163Lo, d2WiderTransfer163Hi, d2LitsNearWiderTransfers020.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer163Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3941631886061145869161 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer163Cap, d2LitsNearWiderTransfers020.q2, d2WiderTransfer163C0, d2WiderTransfer163S0, d2WiderTransfer163C1, d2WiderTransfer163S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219802921509150962928489 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((3941631886061145869161 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece30 (x : ℝ) (hx : x ∈ Icc ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ) ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope30 x hx
  have hxT : x ∈ Icc (d2WiderTransfer167Lo : ℝ) (d2WiderTransfer167Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer167Lo, d2WiderTransfer167Hi, d2LitsNearWiderTransfers020.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer167Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4015266466107576179621 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer167Cap, d2LitsNearWiderTransfers020.q2, d2WiderTransfer167C0, d2WiderTransfer167S0, d2WiderTransfer167C1, d2WiderTransfer167S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219876556089197393238949 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((4015266466107576179621 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece31 (x : ℝ) (hx : x ∈ Icc ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ) ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope31 x hx
  have hxT : x ∈ Icc (d2WiderTransfer171Lo : ℝ) (d2WiderTransfer171Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer171Lo, d2WiderTransfer171Hi, d2LitsNearWiderTransfers021.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer171Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4089051453197950129489 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer171Cap, d2LitsNearWiderTransfers021.q2, d2WiderTransfer171C0, d2WiderTransfer171S0, d2WiderTransfer171C1, d2WiderTransfer171S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219950341076287767188817 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((4089051453197950129489 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece32 (x : ℝ) (hx : x ∈ Icc ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope32 x hx
  have hxT : x ∈ Icc (d2WiderTransfer175Lo : ℝ) (d2WiderTransfer175Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer175Lo, d2WiderTransfer175Hi, d2LitsNearWiderTransfers021.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer175Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2081493742290093005435 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer175Cap, d2LitsNearWiderTransfers021.q2, d2WiderTransfer175C0, d2WiderTransfer175S0, d2WiderTransfer175C1, d2WiderTransfer175S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-610012138553835001535099 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((2081493742290093005435 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece33 (x : ℝ) (hx : x ∈ Icc ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ) ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope33 x hx
  have hxT : x ∈ Icc (d2WiderTransfer179Lo : ℝ) (d2WiderTransfer179Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer179Lo, d2WiderTransfer179Hi, d2LitsNearWiderTransfers022.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer179Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2118537600764331750139 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer179Cap, d2LitsNearWiderTransfers022.q2, d2WiderTransfer179C0, d2WiderTransfer179S0, d2WiderTransfer179C1, d2WiderTransfer179S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-610049182412309240279803 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((2118537600764331750139 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece34 (x : ℝ) (hx : x ∈ Icc ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ) ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope34 x hx
  have hxT : x ∈ Icc (d2WiderTransfer183Lo : ℝ) (d2WiderTransfer183Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer183Lo, d2WiderTransfer183Hi, d2LitsNearWiderTransfers022.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer183Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2192854138779428237197 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer183Cap, d2LitsNearWiderTransfers022.q2, d2WiderTransfer183C0, d2WiderTransfer183S0, d2WiderTransfer183C1, d2WiderTransfer183S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-610123498950324336766861 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((2192854138779428237197 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece35 (x : ℝ) (hx : x ∈ Icc ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ) ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope35 x hx
  have hxT : x ∈ Icc (d2WiderTransfer187Lo : ℝ) (d2WiderTransfer187Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer187Lo, d2WiderTransfer187Hi, d2LitsNearWiderTransfers023.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer187Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4534955893315917401893 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer187Cap, d2LitsNearWiderTransfers023.q2, d2WiderTransfer187C0, d2WiderTransfer187S0, d2WiderTransfer187C1, d2WiderTransfer187S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1220396245516405734461221 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((4534955893315917401893 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece36 (x : ℝ) (hx : x ∈ Icc ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ) ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope36 x hx
  have hxT : x ∈ Icc (d2WiderTransfer191Lo : ℝ) (d2WiderTransfer191Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer191Lo, d2WiderTransfer191Hi, d2LitsNearWiderTransfers023.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer191Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4835315926467055968489 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer191Cap, d2LitsNearWiderTransfers023.q2, d2WiderTransfer191C0, d2WiderTransfer191S0, d2WiderTransfer191C1, d2WiderTransfer191S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1220696605549556873027817 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((4835315926467055968489 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece37 (x : ℝ) (hx : x ∈ Icc ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ) ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope37 x hx
  have hxT : x ∈ Icc (d2WiderTransfer195Lo : ℝ) (d2WiderTransfer195Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer195Lo, d2WiderTransfer195Hi, d2LitsNearWiderTransfers024.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer195Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((5138198350762681201655 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer195Cap, d2LitsNearWiderTransfers024.q2, d2WiderTransfer195C0, d2WiderTransfer195S0, d2WiderTransfer195C1, d2WiderTransfer195S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1220999487973852498260983 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((5138198350762681201655 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece38 (x : ℝ) (hx : x ∈ Icc ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ) ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope38 x hx
  have hxT : x ∈ Icc (d2WiderTransfer199Lo : ℝ) (d2WiderTransfer199Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer199Lo, d2WiderTransfer199Hi, d2LitsNearWiderTransfers024.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer199Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((5443647338495409059865 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer199Cap, d2LitsNearWiderTransfers024.q2, d2WiderTransfer199C0, d2WiderTransfer199S0, d2WiderTransfer199C1, d2WiderTransfer199S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1221304936961585226119193 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((5443647338495409059865 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece39 (x : ℝ) (hx : x ∈ Icc ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ) ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope39 x hx
  have hxT : x ∈ Icc (d2WiderTransfer203Lo : ℝ) (d2WiderTransfer203Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer203Lo, d2WiderTransfer203Hi, d2LitsNearWiderTransfers025.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer203Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((6062427544351749957749 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer203Cap, d2LitsNearWiderTransfers025.q2, d2WiderTransfer203C0, d2WiderTransfer203S0, d2WiderTransfer203C1, d2WiderTransfer203S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1221923717167441567017077 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((6062427544351749957749 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece40 (x : ℝ) (hx : x ∈ Icc ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ) ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope40 x hx
  have hxT : x ∈ Icc (d2WiderTransfer207Lo : ℝ) (d2WiderTransfer207Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer207Lo, d2WiderTransfer207Hi, d2LitsNearWiderTransfers025.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer207Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3666432248762820968277 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer207Cap, d2LitsNearWiderTransfers025.q2, d2WiderTransfer207C0, d2WiderTransfer207S0, d2WiderTransfer207C1, d2WiderTransfer207S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-611597077060307729497941 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((3666432248762820968277 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece41 (x : ℝ) (hx : x ∈ Icc ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ) ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope41 x hx
  have hxT : x ∈ Icc (d2WiderTransfer211Lo : ℝ) (d2WiderTransfer211Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer211Lo, d2WiderTransfer211Hi, d2LitsNearWiderTransfers026.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer211Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2162475809021918278819 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer211Cap, d2LitsNearWiderTransfers026.q2, d2WiderTransfer211C0, d2WiderTransfer211S0, d2WiderTransfer211C1, d2WiderTransfer211S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-306127798214794372543651 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((2162475809021918278819 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece42 (x : ℝ) (hx : x ∈ Icc ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ) ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope42 x hx
  have hxT : x ∈ Icc (d2WiderTransfer215Lo : ℝ) (d2WiderTransfer215Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer215Lo, d2WiderTransfer215Hi, d2LitsNearWiderTransfers026.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer215Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((11438872963260242507847 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer215Cap, d2LitsNearWiderTransfers026.q2, d2WiderTransfer215C0, d2WiderTransfer215S0, d2WiderTransfer215C1, d2WiderTransfer215S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1227300162586350059567175 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((11438872963260242507847 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece43 (x : ℝ) (hx : x ∈ Icc ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ) ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope43 x hx
  have hxT : x ∈ Icc (d2WiderTransfer219Lo : ℝ) (d2WiderTransfer219Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer219Lo, d2WiderTransfer219Hi, d2LitsNearWiderTransfers027.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer219Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4442930554062359260053 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer219Cap, d2LitsNearWiderTransfers027.q2, d2WiderTransfer219C0, d2WiderTransfer219S0, d2WiderTransfer219C1, d2WiderTransfer219S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-308408252959834813524885 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((4442930554062359260053 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece44 (x : ℝ) (hx : x ∈ Icc ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ) ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope44 x hx
  have hxT : x ∈ Icc (d2WiderTransfer223Lo : ℝ) (d2WiderTransfer223Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer223Lo, d2WiderTransfer223Hi, d2LitsNearWiderTransfers027.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer223Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((25489557907862617640645 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer223Cap, d2LitsNearWiderTransfers027.q2, d2WiderTransfer223C0, d2WiderTransfer223S0, d2WiderTransfer223C1, d2WiderTransfer223S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1241350847530952434699973 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((25489557907862617640645 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece45 (x : ℝ) (hx : x ∈ Icc ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ) ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope45 x hx
  have hxT : x ∈ Icc (d2WiderTransfer227Lo : ℝ) (d2WiderTransfer227Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer227Lo, d2WiderTransfer227Hi, d2LitsNearWiderTransfers028.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer227Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((49268280682672541649493 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer227Cap, d2LitsNearWiderTransfers028.q2, d2WiderTransfer227C0, d2WiderTransfer227S0, d2WiderTransfer227C1, d2WiderTransfer227S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1265129570305762358708821 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((49268280682672541649493 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece46 (x : ℝ) (hx : x ∈ Icc ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ) ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope46 x hx
  have hxT : x ∈ Icc (d2WiderTransfer231Lo : ℝ) (d2WiderTransfer231Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer231Lo, d2WiderTransfer231Hi, d2LitsNearWiderTransfers028.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer231Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((36370749118028315497071 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer231Cap, d2LitsNearWiderTransfers028.q2, d2WiderTransfer231C0, d2WiderTransfer231S0, d2WiderTransfer231C1, d2WiderTransfer231S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-644301393929573224026735 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((36370749118028315497071 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece47 (x : ℝ) (hx : x ∈ Icc ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ) ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope47 x hx
  have hxT : x ∈ Icc (d2WiderTransfer235Lo : ℝ) (d2WiderTransfer235Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer235Lo, d2WiderTransfer235Hi, d2LitsNearWiderTransfers029.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer235Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((47881312115846296194465 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer235Cap, d2LitsNearWiderTransfers029.q2, d2WiderTransfer235C0, d2WiderTransfer235S0, d2WiderTransfer235C1, d2WiderTransfer235S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-655811956927391204724129 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((47881312115846296194465 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece48 (x : ℝ) (hx : x ∈ Icc ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ) ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope48 x hx
  have hxT : x ∈ Icc (d2WiderTransfer239Lo : ℝ) (d2WiderTransfer239Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer239Lo, d2WiderTransfer239Hi, d2LitsNearWiderTransfers029.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer239Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((50083726859119314504325 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer239Cap, d2LitsNearWiderTransfers029.q2, d2WiderTransfer239C0, d2WiderTransfer239S0, d2WiderTransfer239C1, d2WiderTransfer239S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-354049049264891768769157 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((50083726859119314504325 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece49 (x : ℝ) (hx : x ∈ Icc ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ) ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope49 x hx
  have hxT : x ∈ Icc (d2WiderTransfer243Lo : ℝ) (d2WiderTransfer243Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer243Lo, d2WiderTransfer243Hi, d2LitsNearWiderTransfers030.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer243Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((208032643445538234222593 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer243Cap, d2LitsNearWiderTransfers030.q2, d2WiderTransfer243C0, d2WiderTransfer243S0, d2WiderTransfer243C1, d2WiderTransfer243S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1423893933068628051281921 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((208032643445538234222593 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece50 (x : ℝ) (hx : x ∈ Icc ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope50 x hx
  have hxT : x ∈ Icc (d2WiderTransfer247Lo : ℝ) (d2WiderTransfer247Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer247Lo, d2WiderTransfer247Hi, d2LitsNearWiderTransfers030.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer247Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((208034248407466470043651 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer247Cap, d2LitsNearWiderTransfers030.q2, d2WiderTransfer247C0, d2WiderTransfer247S0, d2WiderTransfer247C1, d2WiderTransfer247S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1423895538030556287102979 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((208034248407466470043651 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner2Domain0Pieces : List (ℚ × ℚ) := [(((98749 : ℚ) / 1000000), ((828367 : ℚ) / 8388608)), (((828367 : ℚ) / 8388608), ((8304657 : ℚ) / 67108864)), (((8304657 : ℚ) / 67108864), ((4991189 : ℚ) / 33554432)), (((4991189 : ℚ) / 33554432), ((3334455 : ℚ) / 16777216)), (((3334455 : ℚ) / 16777216), ((313261 : ℚ) / 1048576)), (((313261 : ℚ) / 1048576), ((6689897 : ℚ) / 16777216)), (((6689897 : ℚ) / 16777216), ((4183809 : ℚ) / 8388608)), (((4183809 : ℚ) / 8388608), ((18412957 : ℚ) / 33554432)), (((18412957 : ℚ) / 33554432), ((38503635 : ℚ) / 67108864)), (((38503635 : ℚ) / 67108864), ((78684991 : ℚ) / 134217728)), (((78684991 : ℚ) / 134217728), ((10045339 : ℚ) / 16777216)), (((10045339 : ℚ) / 16777216), ((162403145 : ℚ) / 268435456)), (((162403145 : ℚ) / 268435456), ((326484011 : ℚ) / 536870912)), (((326484011 : ℚ) / 536870912), ((654645743 : ℚ) / 1073741824)), (((654645743 : ℚ) / 1073741824), ((82040433 : ℚ) / 134217728)), (((82040433 : ℚ) / 134217728), ((329839453 : ℚ) / 536870912)), (((329839453 : ℚ) / 536870912), ((661356627 : ℚ) / 1073741824)), (((661356627 : ℚ) / 1073741824), ((165758587 : ℚ) / 268435456)), (((165758587 : ℚ) / 268435456), ((1327746417 : ℚ) / 2147483648)), (((1327746417 : ℚ) / 2147483648), ((664712069 : ℚ) / 1073741824)), (((664712069 : ℚ) / 1073741824), ((1331101859 : ℚ) / 2147483648)), (((1331101859 : ℚ) / 2147483648), ((333194895 : ℚ) / 536870912)), (((333194895 : ℚ) / 536870912), ((1334457301 : ℚ) / 2147483648)), (((1334457301 : ℚ) / 2147483648), ((668067511 : ℚ) / 1073741824)), (((668067511 : ℚ) / 1073741824), ((1337812743 : ℚ) / 2147483648)), (((1337812743 : ℚ) / 2147483648), ((41859077 : ℚ) / 67108864)), (((41859077 : ℚ) / 67108864), ((1341168185 : ℚ) / 2147483648)), (((1341168185 : ℚ) / 2147483648), ((671422953 : ℚ) / 1073741824)), (((671422953 : ℚ) / 1073741824), ((1344523627 : ℚ) / 2147483648)), (((1344523627 : ℚ) / 2147483648), ((336550337 : ℚ) / 536870912)), (((336550337 : ℚ) / 536870912), ((1347879069 : ℚ) / 2147483648)), (((1347879069 : ℚ) / 2147483648), ((674778395 : ℚ) / 1073741824)), (((674778395 : ℚ) / 1073741824), ((1351234511 : ℚ) / 2147483648)), (((1351234511 : ℚ) / 2147483648), ((169114029 : ℚ) / 268435456)), (((169114029 : ℚ) / 268435456), ((678133837 : ℚ) / 1073741824)), (((678133837 : ℚ) / 1073741824), ((339905779 : ℚ) / 536870912)), (((339905779 : ℚ) / 536870912), ((85395875 : ℚ) / 134217728)), (((85395875 : ℚ) / 134217728), ((343261221 : ℚ) / 536870912)), (((343261221 : ℚ) / 536870912), ((172469471 : ℚ) / 268435456)), (((172469471 : ℚ) / 268435456), ((21768399 : ℚ) / 33554432)), (((21768399 : ℚ) / 33554432), ((88751317 : ℚ) / 134217728)), (((88751317 : ℚ) / 134217728), ((45214519 : ℚ) / 67108864)), (((45214519 : ℚ) / 67108864), ((2930765 : ℚ) / 4194304)), (((2930765 : ℚ) / 4194304), ((25123841 : ℚ) / 33554432)), (((25123841 : ℚ) / 33554432), ((13400781 : ℚ) / 16777216)), (((13400781 : ℚ) / 16777216), ((7539251 : ℚ) / 8388608)), (((7539251 : ℚ) / 8388608), ((31834725 : ℚ) / 33554432)), (((31834725 : ℚ) / 33554432), ((65347171 : ℚ) / 67108864)), (((65347171 : ℚ) / 67108864), ((16756223 : ℚ) / 16777216)), (((16756223 : ℚ) / 16777216), ((8380219 : ℚ) / 8388608)), (((8380219 : ℚ) / 8388608), ((999 : ℚ) / 1000))]
theorem corner2Domain0Cover : pieceCover ((999 : ℚ) / 1000) ((98749 : ℚ) / 1000000) corner2Domain0Pieces = true := by decide +kernel
theorem corner2Domain0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  apply pieceCover_bound ((999 : ℚ) / 1000) (fun x : ℝ => fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x) ((((-1105819401003 : ℚ) / 1099511627776) : ℚ) : ℝ) ((98749 : ℚ) / 1000000) corner2Domain0Pieces (by decide +kernel) corner2Domain0Cover
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
theorem delta3Check : fieldNFCheck D72.NearCorners001.delta3 (fqSum [logFQ ((1 : ℚ) / 32) ((-1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta3Value (x : ℝ) : fval D72.NearCorners001.delta3 x = ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta3Check x
  change fval D72.NearCorners001.delta3 x = fval (fqSum [logFQ ((1 : ℚ) / 32) ((-1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner3Identity (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x = (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) + (((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  have hf : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x = fval D72.NearBinding001.literalField x + fval D72.NearCorners001.delta3 x := by
    convert D72.NearCorners001.corner3Value x using 1 <;> norm_num [d2LitsNearCorners001.q2]
  have ht : lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x = lfieldTower D72.NearBinding001.literalTerms 0 x :=
    (laurent_eq_of_nf (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) D72.NearCorners001.corner3Terms x).trans (D72.NearBinding001.termsValue x).symm
  calc
    _ = (fval D72.NearBinding001.literalField x + fval D72.NearCorners001.delta3 x) + lfieldTower D72.NearBinding001.literalTerms 0 x :=
      congrArg₂ (fun u v : ℝ => u + v) hf ht
    _ = (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) + (((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by rw [delta3Value]; ring
theorem corner3Piece0 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((828367 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer48Lo : ℝ) (d2WiderTransfer48Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer48Lo, d2WiderTransfer48Hi, d2LitsNearWiderTransfers006.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer48Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer48Cap, d2LitsNearWiderTransfers006.q2, d2WiderTransfer48C0, d2WiderTransfer48S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece1 (x : ℝ) (hx : x ∈ Icc ((((828367 : ℚ) / 8388608) : ℚ) : ℝ) ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer52Lo : ℝ) (d2WiderTransfer52Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer52Lo, d2WiderTransfer52Hi, d2LitsNearWiderTransfers006.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer52Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer52Cap, d2LitsNearWiderTransfers006.q2, d2WiderTransfer52C0, d2WiderTransfer52S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece2 (x : ℝ) (hx : x ∈ Icc ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ) ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer56Lo : ℝ) (d2WiderTransfer56Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer56Lo, d2WiderTransfer56Hi, d2LitsNearWiderTransfers007.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer56Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer56Cap, d2LitsNearWiderTransfers007.q2, d2WiderTransfer56C0, d2WiderTransfer56S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece3 (x : ℝ) (hx : x ∈ Icc ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ) ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer60Lo : ℝ) (d2WiderTransfer60Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer60Lo, d2WiderTransfer60Hi, d2LitsNearWiderTransfers007.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer60Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer60Cap, d2LitsNearWiderTransfers007.q2, d2WiderTransfer60C0, d2WiderTransfer60S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece4 (x : ℝ) (hx : x ∈ Icc ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ) ((((313261 : ℚ) / 1048576) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer64Lo : ℝ) (d2WiderTransfer64Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer64Lo, d2WiderTransfer64Hi, d2LitsNearWiderTransfers008.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer64Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer64Cap, d2LitsNearWiderTransfers008.q2, d2WiderTransfer64C0, d2WiderTransfer64S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece5 (x : ℝ) (hx : x ∈ Icc ((((313261 : ℚ) / 1048576) : ℚ) : ℝ) ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer68Lo : ℝ) (d2WiderTransfer68Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer68Lo, d2WiderTransfer68Hi, d2LitsNearWiderTransfers008.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer68Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer68Cap, d2LitsNearWiderTransfers008.q2, d2WiderTransfer68C0, d2WiderTransfer68S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece6 (x : ℝ) (hx : x ∈ Icc ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ) ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer72Lo : ℝ) (d2WiderTransfer72Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer72Lo, d2WiderTransfer72Hi, d2LitsNearWiderTransfers009.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer72Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer72Cap, d2LitsNearWiderTransfers009.q2, d2WiderTransfer72C0, d2WiderTransfer72S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece7 (x : ℝ) (hx : x ∈ Icc ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ) ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer76Lo : ℝ) (d2WiderTransfer76Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer76Lo, d2WiderTransfer76Hi, d2LitsNearWiderTransfers009.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer76Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer76Cap, d2LitsNearWiderTransfers009.q2, d2WiderTransfer76C0, d2WiderTransfer76S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece8 (x : ℝ) (hx : x ∈ Icc ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ) ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer80Lo : ℝ) (d2WiderTransfer80Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer80Lo, d2WiderTransfer80Hi, d2LitsNearWiderTransfers010.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer80Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer80Cap, d2LitsNearWiderTransfers010.q2, d2WiderTransfer80C0, d2WiderTransfer80S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece9 (x : ℝ) (hx : x ∈ Icc ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ) ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope9 x hx
  have hxT : x ∈ Icc (d2WiderTransfer84Lo : ℝ) (d2WiderTransfer84Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer84Lo, d2WiderTransfer84Hi, d2LitsNearWiderTransfers010.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer84Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer84Cap, d2LitsNearWiderTransfers010.q2, d2WiderTransfer84C0, d2WiderTransfer84S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece10 (x : ℝ) (hx : x ∈ Icc ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ) ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope10 x hx
  have hxT : x ∈ Icc (d2WiderTransfer88Lo : ℝ) (d2WiderTransfer88Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer88Lo, d2WiderTransfer88Hi, d2LitsNearWiderTransfers011.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer88Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer88Cap, d2LitsNearWiderTransfers011.q2, d2WiderTransfer88C0, d2WiderTransfer88S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((16281318465 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece11 (x : ℝ) (hx : x ∈ Icc ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ) ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope11 x hx
  have hxT : x ∈ Icc (d2WiderTransfer92Lo : ℝ) (d2WiderTransfer92Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer92Lo, d2WiderTransfer92Hi, d2LitsNearWiderTransfers011.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer92Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4476292748642812392879 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer92Cap, d2LitsNearWiderTransfers011.q2, d2WiderTransfer92C0, d2WiderTransfer92S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-304635849631809526527407 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((4476292748642812392879 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece12 (x : ℝ) (hx : x ∈ Icc ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ) ((((326484011 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope12 x hx
  have hxT : x ∈ Icc (d2WiderTransfer96Lo : ℝ) (d2WiderTransfer96Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer96Lo, d2WiderTransfer96Hi, d2LitsNearWiderTransfers012.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer96Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17947568960646277009121 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer96Cap, d2LitsNearWiderTransfers012.q2, d2WiderTransfer96C0, d2WiderTransfer96S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1218585796493313133547233 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((17947568960646277009121 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece13 (x : ℝ) (hx : x ∈ Icc ((((326484011 : ℚ) / 536870912) : ℚ) : ℝ) ((((654645743 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope13 x hx
  have hxT : x ∈ Icc (d2WiderTransfer100Lo : ℝ) (d2WiderTransfer100Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer100Lo, d2WiderTransfer100Hi, d2LitsNearWiderTransfers012.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer100Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2248032279655269564805 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer100Cap, d2LitsNearWiderTransfers012.q2, d2WiderTransfer100C0, d2WiderTransfer100S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-152327810721238626632069 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) + ((((2248032279655269564805 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece14 (x : ℝ) (hx : x ∈ Icc ((((654645743 : ℚ) / 1073741824) : ℚ) : ℝ) ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope14 x hx
  have hxT : x ∈ Icc (d2WiderTransfer104Lo : ℝ) (d2WiderTransfer104Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer104Lo, d2WiderTransfer104Hi, d2LitsNearWiderTransfers013.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer104Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((9010455958677416298425 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer104Cap, d2LitsNearWiderTransfers013.q2, d2WiderTransfer104C0, d2WiderTransfer104S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-609329569725010844567481 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((9010455958677416298425 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece15 (x : ℝ) (hx : x ∈ Icc ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ) ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope15 x hx
  have hxT : x ∈ Icc (d2WiderTransfer108Lo : ℝ) (d2WiderTransfer108Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer108Lo, d2WiderTransfer108Hi, d2LitsNearWiderTransfers013.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer108Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((18094112763952243746169 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer108Cap, d2LitsNearWiderTransfers013.q2, d2WiderTransfer108C0, d2WiderTransfer108S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1218732340296619100284281 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((18094112763952243746169 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece16 (x : ℝ) (hx : x ∈ Icc ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ) ((((661356627 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope16 x hx
  have hxT : x ∈ Icc (d2WiderTransfer112Lo : ℝ) (d2WiderTransfer112Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer112Lo, d2WiderTransfer112Hi, d2LitsNearWiderTransfers014.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer112Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4537313759313862163287 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer112Cap, d2LitsNearWiderTransfers014.q2, d2WiderTransfer112C0, d2WiderTransfer112S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-304696870642480576297815 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((4537313759313862163287 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece17 (x : ℝ) (hx : x ∈ Icc ((((661356627 : ℚ) / 1073741824) : ℚ) : ℝ) ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope17 x hx
  have hxT : x ∈ Icc (d2WiderTransfer116Lo : ℝ) (d2WiderTransfer116Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer116Lo, d2WiderTransfer116Hi, d2LitsNearWiderTransfers014.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer116Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((18292584158804212211551 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer116Cap, d2LitsNearWiderTransfers014.q2, d2WiderTransfer116C0, d2WiderTransfer116S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1218930811691471068749663 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((18292584158804212211551 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece18 (x : ℝ) (hx : x ∈ Icc ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ) ((((1327746417 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope18 x hx
  have hxT : x ∈ Icc (d2WiderTransfer120Lo : ℝ) (d2WiderTransfer120Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer120Lo, d2WiderTransfer120Hi, d2LitsNearWiderTransfers015.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer120Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4591115534748209726435 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer120Cap, d2LitsNearWiderTransfers015.q2, d2WiderTransfer120C0, d2WiderTransfer120S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-304750672417914923860963 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((4591115534748209726435 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece19 (x : ℝ) (hx : x ∈ Icc ((((1327746417 : ℚ) / 2147483648) : ℚ) : ℝ) ((((664712069 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope19 x hx
  have hxT : x ∈ Icc (d2WiderTransfer124Lo : ℝ) (d2WiderTransfer124Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer124Lo, d2WiderTransfer124Hi, d2LitsNearWiderTransfers015.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer124Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((576140099418486577219 : ℚ) / 37778931862957161709568) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer124Cap, d2LitsNearWiderTransfers015.q2, d2WiderTransfer124C0, d2WiderTransfer124S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-38096084709814325844035 : ℚ) / 37778931862957161709568) : ℚ) : ℝ) + ((((576140099418486577219 : ℚ) / 37778931862957161709568) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece20 (x : ℝ) (hx : x ∈ Icc ((((664712069 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1331101859 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope20 x hx
  have hxT : x ∈ Icc (d2WiderTransfer128Lo : ℝ) (d2WiderTransfer128Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer128Lo, d2WiderTransfer128Hi, d2LitsNearWiderTransfers016.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer128Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((72299405771334957823 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer128Cap, d2LitsNearWiderTransfers016.q2, d2WiderTransfer128C0, d2WiderTransfer128S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-4762292482070814866175 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) + ((((72299405771334957823 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece21 (x : ℝ) (hx : x ∈ Icc ((((1331101859 : ℚ) / 2147483648) : ℚ) : ℝ) ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope21 x hx
  have hxT : x ∈ Icc (d2WiderTransfer132Lo : ℝ) (d2WiderTransfer132Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer132Lo, d2WiderTransfer132Hi, d2LitsNearWiderTransfers016.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer132Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((18580956822309071680435 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer132Cap, d2LitsNearWiderTransfers016.q2, d2WiderTransfer132C0, d2WiderTransfer132S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219219184354975928218547 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((18580956822309071680435 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece22 (x : ℝ) (hx : x ∈ Icc ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ) ((((1334457301 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope22 x hx
  have hxT : x ∈ Icc (d2WiderTransfer136Lo : ℝ) (d2WiderTransfer136Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer136Lo, d2WiderTransfer136Hi, d2LitsNearWiderTransfers017.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer136Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((145729770427450393901 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer136Cap, d2LitsNearWiderTransfers017.q2, d2WiderTransfer136C0, d2WiderTransfer136S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-9525715923026410210605 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) + ((((145729770427450393901 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece23 (x : ℝ) (hx : x ∈ Icc ((((1334457301 : ℚ) / 2147483648) : ℚ) : ℝ) ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope23 x hx
  have hxT : x ∈ Icc (d2WiderTransfer140Lo : ℝ) (d2WiderTransfer140Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer140Lo, d2WiderTransfer140Hi, d2LitsNearWiderTransfers017.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer140Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((18726009857160385983239 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer140Cap, d2LitsNearWiderTransfers017.q2, d2WiderTransfer140C0, d2WiderTransfer140S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219364237389827242521351 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((18726009857160385983239 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece24 (x : ℝ) (hx : x ∈ Icc ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1337812743 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope24 x hx
  have hxT : x ∈ Icc (d2WiderTransfer144Lo : ℝ) (d2WiderTransfer144Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer144Lo, d2WiderTransfer144Hi, d2LitsNearWiderTransfers018.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer144Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((9399377577934826708217 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer144Cap, d2LitsNearWiderTransfers018.q2, d2WiderTransfer144C0, d2WiderTransfer144S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-609718491344268254977273 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((9399377577934826708217 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece25 (x : ℝ) (hx : x ∈ Icc ((((1337812743 : ℚ) / 2147483648) : ℚ) : ℝ) ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope25 x hx
  have hxT : x ∈ Icc (d2WiderTransfer148Lo : ℝ) (d2WiderTransfer148Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer148Lo, d2WiderTransfer148Hi, d2LitsNearWiderTransfers018.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer148Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1179477945051769181583 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer148Cap, d2LitsNearWiderTransfers018.q2, d2WiderTransfer148C0, d2WiderTransfer148S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-76219367165843447715215 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) + ((((1179477945051769181583 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece26 (x : ℝ) (hx : x ∈ Icc ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ) ((((1341168185 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope26 x hx
  have hxT : x ∈ Icc (d2WiderTransfer152Lo : ℝ) (d2WiderTransfer152Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer152Lo, d2WiderTransfer152Hi, d2LitsNearWiderTransfers019.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer152Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((18944686365821006639269 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer152Cap, d2LitsNearWiderTransfers019.q2, d2WiderTransfer152C0, d2WiderTransfer152S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219582913898487863177381 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((18944686365821006639269 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece27 (x : ℝ) (hx : x ∈ Icc ((((1341168185 : ℚ) / 2147483648) : ℚ) : ℝ) ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope27 x hx
  have hxT : x ∈ Icc (d2WiderTransfer156Lo : ℝ) (d2WiderTransfer156Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer156Lo, d2WiderTransfer156Hi, d2LitsNearWiderTransfers019.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer156Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2377234188557733987133 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer156Cap, d2LitsNearWiderTransfers019.q2, d2WiderTransfer156C0, d2WiderTransfer156S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-152457012630141091054397 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) + ((((2377234188557733987133 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece28 (x : ℝ) (hx : x ∈ Icc ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope28 x hx
  have hxT : x ∈ Icc (d2WiderTransfer160Lo : ℝ) (d2WiderTransfer160Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer160Lo, d2WiderTransfer160Hi, d2LitsNearWiderTransfers020.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer160Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((19091209170226464444805 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer160Cap, d2LitsNearWiderTransfers020.q2, d2WiderTransfer160C0, d2WiderTransfer160S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219729436702893320982917 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((19091209170226464444805 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece29 (x : ℝ) (hx : x ∈ Icc ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ) ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope29 x hx
  have hxT : x ∈ Icc (d2WiderTransfer164Lo : ℝ) (d2WiderTransfer164Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer164Lo, d2WiderTransfer164Hi, d2LitsNearWiderTransfers020.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer164Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((19164693976484106390377 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer164Cap, d2LitsNearWiderTransfers020.q2, d2WiderTransfer164C0, d2WiderTransfer164S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219802921509150962928489 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((19164693976484106390377 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece30 (x : ℝ) (hx : x ∈ Icc ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ) ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope30 x hx
  have hxT : x ∈ Icc (d2WiderTransfer168Lo : ℝ) (d2WiderTransfer168Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer168Lo, d2WiderTransfer168Hi, d2LitsNearWiderTransfers021.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer168Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((19238328556530536700837 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer168Cap, d2LitsNearWiderTransfers021.q2, d2WiderTransfer168C0, d2WiderTransfer168S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219876556089197393238949 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((19238328556530536700837 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece31 (x : ℝ) (hx : x ∈ Icc ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ) ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope31 x hx
  have hxT : x ∈ Icc (d2WiderTransfer172Lo : ℝ) (d2WiderTransfer172Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer172Lo, d2WiderTransfer172Hi, d2LitsNearWiderTransfers021.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer172Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((19312113543620910650705 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer172Cap, d2LitsNearWiderTransfers021.q2, d2WiderTransfer172C0, d2WiderTransfer172S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219950341076287767188817 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((19312113543620910650705 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece32 (x : ℝ) (hx : x ∈ Icc ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope32 x hx
  have hxT : x ∈ Icc (d2WiderTransfer176Lo : ℝ) (d2WiderTransfer176Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer176Lo, d2WiderTransfer176Hi, d2LitsNearWiderTransfers022.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer176Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((9693024787501573266043 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer176Cap, d2LitsNearWiderTransfers022.q2, d2WiderTransfer176C0, d2WiderTransfer176S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-610012138553835001535099 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((9693024787501573266043 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece33 (x : ℝ) (hx : x ∈ Icc ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ) ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope33 x hx
  have hxT : x ∈ Icc (d2WiderTransfer180Lo : ℝ) (d2WiderTransfer180Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer180Lo, d2WiderTransfer180Hi, d2LitsNearWiderTransfers022.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer180Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((9730068645975812010747 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer180Cap, d2LitsNearWiderTransfers022.q2, d2WiderTransfer180C0, d2WiderTransfer180S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-610049182412309240279803 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((9730068645975812010747 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece34 (x : ℝ) (hx : x ∈ Icc ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ) ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope34 x hx
  have hxT : x ∈ Icc (d2WiderTransfer184Lo : ℝ) (d2WiderTransfer184Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer184Lo, d2WiderTransfer184Hi, d2LitsNearWiderTransfers023.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer184Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((9804385183990908497805 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer184Cap, d2LitsNearWiderTransfers023.q2, d2WiderTransfer184C0, d2WiderTransfer184S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-610123498950324336766861 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((9804385183990908497805 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece35 (x : ℝ) (hx : x ∈ Icc ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ) ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope35 x hx
  have hxT : x ∈ Icc (d2WiderTransfer188Lo : ℝ) (d2WiderTransfer188Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer188Lo, d2WiderTransfer188Hi, d2LitsNearWiderTransfers023.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer188Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((19758017983738877923109 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer188Cap, d2LitsNearWiderTransfers023.q2, d2WiderTransfer188C0, d2WiderTransfer188S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1220396245516405734461221 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((19758017983738877923109 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece36 (x : ℝ) (hx : x ∈ Icc ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ) ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope36 x hx
  have hxT : x ∈ Icc (d2WiderTransfer192Lo : ℝ) (d2WiderTransfer192Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer192Lo, d2WiderTransfer192Hi, d2LitsNearWiderTransfers024.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer192Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((20058378016890016489705 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer192Cap, d2LitsNearWiderTransfers024.q2, d2WiderTransfer192C0, d2WiderTransfer192S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1220696605549556873027817 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((20058378016890016489705 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece37 (x : ℝ) (hx : x ∈ Icc ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ) ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope37 x hx
  have hxT : x ∈ Icc (d2WiderTransfer196Lo : ℝ) (d2WiderTransfer196Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer196Lo, d2WiderTransfer196Hi, d2LitsNearWiderTransfers024.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer196Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((20361260441185641722871 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer196Cap, d2LitsNearWiderTransfers024.q2, d2WiderTransfer196C0, d2WiderTransfer196S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1220999487973852498260983 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((20361260441185641722871 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece38 (x : ℝ) (hx : x ∈ Icc ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ) ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope38 x hx
  have hxT : x ∈ Icc (d2WiderTransfer200Lo : ℝ) (d2WiderTransfer200Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer200Lo, d2WiderTransfer200Hi, d2LitsNearWiderTransfers025.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer200Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((20666709428918369581081 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer200Cap, d2LitsNearWiderTransfers025.q2, d2WiderTransfer200C0, d2WiderTransfer200S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1221304936961585226119193 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((20666709428918369581081 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece39 (x : ℝ) (hx : x ∈ Icc ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ) ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope39 x hx
  have hxT : x ∈ Icc (d2WiderTransfer204Lo : ℝ) (d2WiderTransfer204Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer204Lo, d2WiderTransfer204Hi, d2LitsNearWiderTransfers025.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer204Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((21285489634774710478965 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer204Cap, d2LitsNearWiderTransfers025.q2, d2WiderTransfer204C0, d2WiderTransfer204S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1221923717167441567017077 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((21285489634774710478965 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece40 (x : ℝ) (hx : x ∈ Icc ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ) ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope40 x hx
  have hxT : x ∈ Icc (d2WiderTransfer208Lo : ℝ) (d2WiderTransfer208Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer208Lo, d2WiderTransfer208Hi, d2LitsNearWiderTransfers026.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer208Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((11277963293974301228885 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer208Cap, d2LitsNearWiderTransfers026.q2, d2WiderTransfer208C0, d2WiderTransfer208S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-611597077060307729497941 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((11277963293974301228885 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece41 (x : ℝ) (hx : x ∈ Icc ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ) ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope41 x hx
  have hxT : x ∈ Icc (d2WiderTransfer212Lo : ℝ) (d2WiderTransfer212Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer212Lo, d2WiderTransfer212Hi, d2LitsNearWiderTransfers026.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer212Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((5968241331627658409123 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer212Cap, d2LitsNearWiderTransfers026.q2, d2WiderTransfer212C0, d2WiderTransfer212S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-306127798214794372543651 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((5968241331627658409123 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece42 (x : ℝ) (hx : x ∈ Icc ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ) ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope42 x hx
  have hxT : x ∈ Icc (d2WiderTransfer216Lo : ℝ) (d2WiderTransfer216Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer216Lo, d2WiderTransfer216Hi, d2LitsNearWiderTransfers027.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer216Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((26661935053683203029063 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer216Cap, d2LitsNearWiderTransfers027.q2, d2WiderTransfer216C0, d2WiderTransfer216S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1227300162586350059567175 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((26661935053683203029063 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece43 (x : ℝ) (hx : x ∈ Icc ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ) ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope43 x hx
  have hxT : x ∈ Icc (d2WiderTransfer220Lo : ℝ) (d2WiderTransfer220Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer220Lo, d2WiderTransfer220Hi, d2LitsNearWiderTransfers027.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer220Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((8248696076668099390357 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer220Cap, d2LitsNearWiderTransfers027.q2, d2WiderTransfer220C0, d2WiderTransfer220S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-308408252959834813524885 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((8248696076668099390357 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece44 (x : ℝ) (hx : x ∈ Icc ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ) ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope44 x hx
  have hxT : x ∈ Icc (d2WiderTransfer224Lo : ℝ) (d2WiderTransfer224Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer224Lo, d2WiderTransfer224Hi, d2LitsNearWiderTransfers028.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer224Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((40712619998285578161861 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer224Cap, d2LitsNearWiderTransfers028.q2, d2WiderTransfer224C0, d2WiderTransfer224S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1241350847530952434699973 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((40712619998285578161861 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece45 (x : ℝ) (hx : x ∈ Icc ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ) ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope45 x hx
  have hxT : x ∈ Icc (d2WiderTransfer228Lo : ℝ) (d2WiderTransfer228Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer228Lo, d2WiderTransfer228Hi, d2LitsNearWiderTransfers028.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer228Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((64491342773095502170709 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer228Cap, d2LitsNearWiderTransfers028.q2, d2WiderTransfer228C0, d2WiderTransfer228S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1265129570305762358708821 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((64491342773095502170709 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece46 (x : ℝ) (hx : x ∈ Icc ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ) ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope46 x hx
  have hxT : x ∈ Icc (d2WiderTransfer232Lo : ℝ) (d2WiderTransfer232Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer232Lo, d2WiderTransfer232Hi, d2LitsNearWiderTransfers029.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer232Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((43982280163239795757679 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer232Cap, d2LitsNearWiderTransfers029.q2, d2WiderTransfer232C0, d2WiderTransfer232S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-644301393929573224026735 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((43982280163239795757679 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece47 (x : ℝ) (hx : x ∈ Icc ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ) ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope47 x hx
  have hxT : x ∈ Icc (d2WiderTransfer236Lo : ℝ) (d2WiderTransfer236Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer236Lo, d2WiderTransfer236Hi, d2LitsNearWiderTransfers029.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer236Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((55492843161057776455073 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer236Cap, d2LitsNearWiderTransfers029.q2, d2WiderTransfer236C0, d2WiderTransfer236S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-655811956927391204724129 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((55492843161057776455073 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece48 (x : ℝ) (hx : x ∈ Icc ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ) ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope48 x hx
  have hxT : x ∈ Icc (d2WiderTransfer240Lo : ℝ) (d2WiderTransfer240Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer240Lo, d2WiderTransfer240Hi, d2LitsNearWiderTransfers030.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer240Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((53889492381725054634629 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer240Cap, d2LitsNearWiderTransfers030.q2, d2WiderTransfer240C0, d2WiderTransfer240S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-354049049264891768769157 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((53889492381725054634629 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece49 (x : ℝ) (hx : x ∈ Icc ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ) ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope49 x hx
  have hxT : x ∈ Icc (d2WiderTransfer244Lo : ℝ) (d2WiderTransfer244Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer244Lo, d2WiderTransfer244Hi, d2LitsNearWiderTransfers030.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer244Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((223255705535961194743809 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer244Cap, d2LitsNearWiderTransfers030.q2, d2WiderTransfer244C0, d2WiderTransfer244S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1423893933068628051281921 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((223255705535961194743809 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece50 (x : ℝ) (hx : x ∈ Icc ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope50 x hx
  have hxT : x ∈ Icc (d2WiderTransfer248Lo : ℝ) (d2WiderTransfer248Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer248Lo, d2WiderTransfer248Hi, d2LitsNearWiderTransfers031.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer248Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((223257310497889430564867 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer248Cap, d2LitsNearWiderTransfers031.q2, d2WiderTransfer248C0, d2WiderTransfer248S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1423895538030556287102979 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((223257310497889430564867 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner3Domain0Pieces : List (ℚ × ℚ) := [(((98749 : ℚ) / 1000000), ((828367 : ℚ) / 8388608)), (((828367 : ℚ) / 8388608), ((8304657 : ℚ) / 67108864)), (((8304657 : ℚ) / 67108864), ((4991189 : ℚ) / 33554432)), (((4991189 : ℚ) / 33554432), ((3334455 : ℚ) / 16777216)), (((3334455 : ℚ) / 16777216), ((313261 : ℚ) / 1048576)), (((313261 : ℚ) / 1048576), ((6689897 : ℚ) / 16777216)), (((6689897 : ℚ) / 16777216), ((4183809 : ℚ) / 8388608)), (((4183809 : ℚ) / 8388608), ((18412957 : ℚ) / 33554432)), (((18412957 : ℚ) / 33554432), ((38503635 : ℚ) / 67108864)), (((38503635 : ℚ) / 67108864), ((78684991 : ℚ) / 134217728)), (((78684991 : ℚ) / 134217728), ((10045339 : ℚ) / 16777216)), (((10045339 : ℚ) / 16777216), ((162403145 : ℚ) / 268435456)), (((162403145 : ℚ) / 268435456), ((326484011 : ℚ) / 536870912)), (((326484011 : ℚ) / 536870912), ((654645743 : ℚ) / 1073741824)), (((654645743 : ℚ) / 1073741824), ((82040433 : ℚ) / 134217728)), (((82040433 : ℚ) / 134217728), ((329839453 : ℚ) / 536870912)), (((329839453 : ℚ) / 536870912), ((661356627 : ℚ) / 1073741824)), (((661356627 : ℚ) / 1073741824), ((165758587 : ℚ) / 268435456)), (((165758587 : ℚ) / 268435456), ((1327746417 : ℚ) / 2147483648)), (((1327746417 : ℚ) / 2147483648), ((664712069 : ℚ) / 1073741824)), (((664712069 : ℚ) / 1073741824), ((1331101859 : ℚ) / 2147483648)), (((1331101859 : ℚ) / 2147483648), ((333194895 : ℚ) / 536870912)), (((333194895 : ℚ) / 536870912), ((1334457301 : ℚ) / 2147483648)), (((1334457301 : ℚ) / 2147483648), ((668067511 : ℚ) / 1073741824)), (((668067511 : ℚ) / 1073741824), ((1337812743 : ℚ) / 2147483648)), (((1337812743 : ℚ) / 2147483648), ((41859077 : ℚ) / 67108864)), (((41859077 : ℚ) / 67108864), ((1341168185 : ℚ) / 2147483648)), (((1341168185 : ℚ) / 2147483648), ((671422953 : ℚ) / 1073741824)), (((671422953 : ℚ) / 1073741824), ((1344523627 : ℚ) / 2147483648)), (((1344523627 : ℚ) / 2147483648), ((336550337 : ℚ) / 536870912)), (((336550337 : ℚ) / 536870912), ((1347879069 : ℚ) / 2147483648)), (((1347879069 : ℚ) / 2147483648), ((674778395 : ℚ) / 1073741824)), (((674778395 : ℚ) / 1073741824), ((1351234511 : ℚ) / 2147483648)), (((1351234511 : ℚ) / 2147483648), ((169114029 : ℚ) / 268435456)), (((169114029 : ℚ) / 268435456), ((678133837 : ℚ) / 1073741824)), (((678133837 : ℚ) / 1073741824), ((339905779 : ℚ) / 536870912)), (((339905779 : ℚ) / 536870912), ((85395875 : ℚ) / 134217728)), (((85395875 : ℚ) / 134217728), ((343261221 : ℚ) / 536870912)), (((343261221 : ℚ) / 536870912), ((172469471 : ℚ) / 268435456)), (((172469471 : ℚ) / 268435456), ((21768399 : ℚ) / 33554432)), (((21768399 : ℚ) / 33554432), ((88751317 : ℚ) / 134217728)), (((88751317 : ℚ) / 134217728), ((45214519 : ℚ) / 67108864)), (((45214519 : ℚ) / 67108864), ((2930765 : ℚ) / 4194304)), (((2930765 : ℚ) / 4194304), ((25123841 : ℚ) / 33554432)), (((25123841 : ℚ) / 33554432), ((13400781 : ℚ) / 16777216)), (((13400781 : ℚ) / 16777216), ((7539251 : ℚ) / 8388608)), (((7539251 : ℚ) / 8388608), ((31834725 : ℚ) / 33554432)), (((31834725 : ℚ) / 33554432), ((65347171 : ℚ) / 67108864)), (((65347171 : ℚ) / 67108864), ((16756223 : ℚ) / 16777216)), (((16756223 : ℚ) / 16777216), ((8380219 : ℚ) / 8388608)), (((8380219 : ℚ) / 8388608), ((999 : ℚ) / 1000))]
theorem corner3Domain0Cover : pieceCover ((999 : ℚ) / 1000) ((98749 : ℚ) / 1000000) corner3Domain0Pieces = true := by decide +kernel
theorem corner3Domain0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  apply pieceCover_bound ((999 : ℚ) / 1000) (fun x : ℝ => fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x) ((((-1091974106687 : ℚ) / 1099511627776) : ℚ) : ℝ) ((98749 : ℚ) / 1000000) corner3Domain0Pieces (by decide +kernel) corner3Domain0Cover
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
theorem delta4Check : fieldNFCheck D72.NearCorners001.delta4 (fqSum [logFQ ((1 : ℚ) / 352) ((-1 : ℚ) / 1), logFQ ((-5 : ℚ) / 176) ((1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta4Value (x : ℝ) : fval D72.NearCorners001.delta4 x = ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta4Check x
  change fval D72.NearCorners001.delta4 x = fval (fqSum [logFQ ((1 : ℚ) / 352) ((-1 : ℚ) / 1), logFQ ((-5 : ℚ) / 176) ((1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner4Identity (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x = (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) + (((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  have hf : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x = fval D72.NearBinding001.literalField x + fval D72.NearCorners001.delta4 x := by
    convert D72.NearCorners001.corner4Value x using 1 <;> norm_num [d2LitsNearCorners001.q2]
  have ht : lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x = lfieldTower D72.NearBinding001.literalTerms 0 x :=
    (laurent_eq_of_nf (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) D72.NearCorners001.corner4Terms x).trans (D72.NearBinding001.termsValue x).symm
  calc
    _ = (fval D72.NearBinding001.literalField x + fval D72.NearCorners001.delta4 x) + lfieldTower D72.NearBinding001.literalTerms 0 x :=
      congrArg₂ (fun u v : ℝ => u + v) hf ht
    _ = (fval D72.NearBinding001.literalField x + lfieldTower D72.NearBinding001.literalTerms 0 x) + (((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)|) := by rw [delta4Value]; ring
theorem corner4Piece0 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((828367 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer49Lo : ℝ) (d2WiderTransfer49Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer49Lo, d2WiderTransfer49Hi, d2LitsNearWiderTransfers006.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer49Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer49Cap, d2LitsNearWiderTransfers006.q2, d2WiderTransfer49C0, d2WiderTransfer49S0, d2WiderTransfer49C1, d2WiderTransfer49S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece1 (x : ℝ) (hx : x ∈ Icc ((((828367 : ℚ) / 8388608) : ℚ) : ℝ) ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer53Lo : ℝ) (d2WiderTransfer53Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer53Lo, d2WiderTransfer53Hi, d2LitsNearWiderTransfers006.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer53Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer53Cap, d2LitsNearWiderTransfers006.q2, d2WiderTransfer53C0, d2WiderTransfer53S0, d2WiderTransfer53C1, d2WiderTransfer53S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece2 (x : ℝ) (hx : x ∈ Icc ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ) ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer57Lo : ℝ) (d2WiderTransfer57Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer57Lo, d2WiderTransfer57Hi, d2LitsNearWiderTransfers007.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer57Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer57Cap, d2LitsNearWiderTransfers007.q2, d2WiderTransfer57C0, d2WiderTransfer57S0, d2WiderTransfer57C1, d2WiderTransfer57S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece3 (x : ℝ) (hx : x ∈ Icc ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ) ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer61Lo : ℝ) (d2WiderTransfer61Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer61Lo, d2WiderTransfer61Hi, d2LitsNearWiderTransfers007.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer61Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer61Cap, d2LitsNearWiderTransfers007.q2, d2WiderTransfer61C0, d2WiderTransfer61S0, d2WiderTransfer61C1, d2WiderTransfer61S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece4 (x : ℝ) (hx : x ∈ Icc ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ) ((((313261 : ℚ) / 1048576) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer65Lo : ℝ) (d2WiderTransfer65Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer65Lo, d2WiderTransfer65Hi, d2LitsNearWiderTransfers008.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer65Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer65Cap, d2LitsNearWiderTransfers008.q2, d2WiderTransfer65C0, d2WiderTransfer65S0, d2WiderTransfer65C1, d2WiderTransfer65S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece5 (x : ℝ) (hx : x ∈ Icc ((((313261 : ℚ) / 1048576) : ℚ) : ℝ) ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer69Lo : ℝ) (d2WiderTransfer69Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer69Lo, d2WiderTransfer69Hi, d2LitsNearWiderTransfers008.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer69Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer69Cap, d2LitsNearWiderTransfers008.q2, d2WiderTransfer69C0, d2WiderTransfer69S0, d2WiderTransfer69C1, d2WiderTransfer69S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece6 (x : ℝ) (hx : x ∈ Icc ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ) ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer73Lo : ℝ) (d2WiderTransfer73Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer73Lo, d2WiderTransfer73Hi, d2LitsNearWiderTransfers009.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer73Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer73Cap, d2LitsNearWiderTransfers009.q2, d2WiderTransfer73C0, d2WiderTransfer73S0, d2WiderTransfer73C1, d2WiderTransfer73S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece7 (x : ℝ) (hx : x ∈ Icc ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ) ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer77Lo : ℝ) (d2WiderTransfer77Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer77Lo, d2WiderTransfer77Hi, d2LitsNearWiderTransfers009.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer77Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer77Cap, d2LitsNearWiderTransfers009.q2, d2WiderTransfer77C0, d2WiderTransfer77S0, d2WiderTransfer77C1, d2WiderTransfer77S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece8 (x : ℝ) (hx : x ∈ Icc ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ) ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer81Lo : ℝ) (d2WiderTransfer81Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer81Lo, d2WiderTransfer81Hi, d2LitsNearWiderTransfers010.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer81Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer81Cap, d2LitsNearWiderTransfers010.q2, d2WiderTransfer81C0, d2WiderTransfer81S0, d2WiderTransfer81C1, d2WiderTransfer81S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece9 (x : ℝ) (hx : x ∈ Icc ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ) ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope9 x hx
  have hxT : x ∈ Icc (d2WiderTransfer85Lo : ℝ) (d2WiderTransfer85Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer85Lo, d2WiderTransfer85Hi, d2LitsNearWiderTransfers010.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer85Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer85Cap, d2LitsNearWiderTransfers010.q2, d2WiderTransfer85C0, d2WiderTransfer85S0, d2WiderTransfer85C1, d2WiderTransfer85S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece10 (x : ℝ) (hx : x ∈ Icc ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ) ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope10 x hx
  have hxT : x ∈ Icc (d2WiderTransfer89Lo : ℝ) (d2WiderTransfer89Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer89Lo, d2WiderTransfer89Hi, d2LitsNearWiderTransfers011.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer89Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer89Cap, d2LitsNearWiderTransfers011.q2, d2WiderTransfer89C0, d2WiderTransfer89S0, d2WiderTransfer89C1, d2WiderTransfer89S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-8658245509 : ℚ) / 8589934592) : ℚ) : ℝ) + ((((31165051305 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece11 (x : ℝ) (hx : x ∈ Icc ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ) ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope11 x hx
  have hxT : x ∈ Icc (d2WiderTransfer93Lo : ℝ) (d2WiderTransfer93Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer93Lo, d2WiderTransfer93Hi, d2LitsNearWiderTransfers011.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer93Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((8567502079215689233839 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer93Cap, d2LitsNearWiderTransfers011.q2, d2WiderTransfer93C0, d2WiderTransfer93S0, d2WiderTransfer93C1, d2WiderTransfer93S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-304635849631809526527407 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((8567502079215689233839 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece12 (x : ℝ) (hx : x ∈ Icc ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ) ((((326484011 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope12 x hx
  have hxT : x ∈ Icc (d2WiderTransfer97Lo : ℝ) (d2WiderTransfer97Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer97Lo, d2WiderTransfer97Hi, d2LitsNearWiderTransfers012.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer97Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((34312406282937784372961 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer97Cap, d2LitsNearWiderTransfers012.q2, d2WiderTransfer97C0, d2WiderTransfer97S0, d2WiderTransfer97C1, d2WiderTransfer97S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1218585796493313133547233 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((34312406282937784372961 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece13 (x : ℝ) (hx : x ∈ Icc ((((326484011 : ℚ) / 536870912) : ℚ) : ℝ) ((((654645743 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope13 x hx
  have hxT : x ∈ Icc (d2WiderTransfer101Lo : ℝ) (d2WiderTransfer101Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer101Lo, d2WiderTransfer101Hi, d2LitsNearWiderTransfers012.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer101Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4293636944941707985285 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer101Cap, d2LitsNearWiderTransfers012.q2, d2WiderTransfer101C0, d2WiderTransfer101S0, d2WiderTransfer101C1, d2WiderTransfer101S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-152327810721238626632069 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) + ((((4293636944941707985285 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece14 (x : ℝ) (hx : x ∈ Icc ((((654645743 : ℚ) / 1073741824) : ℚ) : ℝ) ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope14 x hx
  have hxT : x ∈ Icc (d2WiderTransfer105Lo : ℝ) (d2WiderTransfer105Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer105Lo, d2WiderTransfer105Hi, d2LitsNearWiderTransfers013.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer105Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17192874619823169980345 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer105Cap, d2LitsNearWiderTransfers013.q2, d2WiderTransfer105C0, d2WiderTransfer105S0, d2WiderTransfer105C1, d2WiderTransfer105S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-609329569725010844567481 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((17192874619823169980345 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece15 (x : ℝ) (hx : x ∈ Icc ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ) ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope15 x hx
  have hxT : x ∈ Icc (d2WiderTransfer109Lo : ℝ) (d2WiderTransfer109Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer109Lo, d2WiderTransfer109Hi, d2LitsNearWiderTransfers013.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer109Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((34458950086243751110009 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer109Cap, d2LitsNearWiderTransfers013.q2, d2WiderTransfer109C0, d2WiderTransfer109S0, d2WiderTransfer109C1, d2WiderTransfer109S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1218732340296619100284281 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((34458950086243751110009 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece16 (x : ℝ) (hx : x ∈ Icc ((((329839453 : ℚ) / 536870912) : ℚ) : ℝ) ((((661356627 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope16 x hx
  have hxT : x ∈ Icc (d2WiderTransfer113Lo : ℝ) (d2WiderTransfer113Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer113Lo, d2WiderTransfer113Hi, d2LitsNearWiderTransfers014.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer113Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((8628523089886739004247 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer113Cap, d2LitsNearWiderTransfers014.q2, d2WiderTransfer113C0, d2WiderTransfer113S0, d2WiderTransfer113C1, d2WiderTransfer113S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-304696870642480576297815 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((8628523089886739004247 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece17 (x : ℝ) (hx : x ∈ Icc ((((661356627 : ℚ) / 1073741824) : ℚ) : ℝ) ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope17 x hx
  have hxT : x ∈ Icc (d2WiderTransfer117Lo : ℝ) (d2WiderTransfer117Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer117Lo, d2WiderTransfer117Hi, d2LitsNearWiderTransfers014.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer117Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((34657421481095719575391 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer117Cap, d2LitsNearWiderTransfers014.q2, d2WiderTransfer117C0, d2WiderTransfer117S0, d2WiderTransfer117C1, d2WiderTransfer117S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1218930811691471068749663 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((34657421481095719575391 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece18 (x : ℝ) (hx : x ∈ Icc ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ) ((((1327746417 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope18 x hx
  have hxT : x ∈ Icc (d2WiderTransfer121Lo : ℝ) (d2WiderTransfer121Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer121Lo, d2WiderTransfer121Hi, d2LitsNearWiderTransfers015.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer121Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((8682324865321086567395 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer121Cap, d2LitsNearWiderTransfers015.q2, d2WiderTransfer121C0, d2WiderTransfer121S0, d2WiderTransfer121C1, d2WiderTransfer121S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-304750672417914923860963 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((8682324865321086567395 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece19 (x : ℝ) (hx : x ∈ Icc ((((1327746417 : ℚ) / 2147483648) : ℚ) : ℝ) ((((664712069 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope19 x hx
  have hxT : x ∈ Icc (d2WiderTransfer125Lo : ℝ) (d2WiderTransfer125Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer125Lo, d2WiderTransfer125Hi, d2LitsNearWiderTransfers015.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer125Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1087541265740096182339 : ℚ) / 37778931862957161709568) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer125Cap, d2LitsNearWiderTransfers015.q2, d2WiderTransfer125C0, d2WiderTransfer125S0, d2WiderTransfer125C1, d2WiderTransfer125S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-38096084709814325844035 : ℚ) / 37778931862957161709568) : ℚ) : ℝ) + ((((1087541265740096182339 : ℚ) / 37778931862957161709568) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece20 (x : ℝ) (hx : x ∈ Icc ((((664712069 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1331101859 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope20 x hx
  have hxT : x ∈ Icc (d2WiderTransfer129Lo : ℝ) (d2WiderTransfer129Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer129Lo, d2WiderTransfer129Hi, d2LitsNearWiderTransfers016.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer129Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((136224551561536158463 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer129Cap, d2LitsNearWiderTransfers016.q2, d2WiderTransfer129C0, d2WiderTransfer129S0, d2WiderTransfer129C1, d2WiderTransfer129S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-4762292482070814866175 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) + ((((136224551561536158463 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece21 (x : ℝ) (hx : x ∈ Icc ((((1331101859 : ℚ) / 2147483648) : ℚ) : ℝ) ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope21 x hx
  have hxT : x ∈ Icc (d2WiderTransfer133Lo : ℝ) (d2WiderTransfer133Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer133Lo, d2WiderTransfer133Hi, d2LitsNearWiderTransfers016.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer133Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((34945794144600579044275 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer133Cap, d2LitsNearWiderTransfers016.q2, d2WiderTransfer133C0, d2WiderTransfer133S0, d2WiderTransfer133C1, d2WiderTransfer133S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219219184354975928218547 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((34945794144600579044275 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece22 (x : ℝ) (hx : x ∈ Icc ((((333194895 : ℚ) / 536870912) : ℚ) : ℝ) ((((1334457301 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope22 x hx
  have hxT : x ∈ Icc (d2WiderTransfer137Lo : ℝ) (d2WiderTransfer137Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer137Lo, d2WiderTransfer137Hi, d2LitsNearWiderTransfers017.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer137Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((273580062007852795181 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer137Cap, d2LitsNearWiderTransfers017.q2, d2WiderTransfer137C0, d2WiderTransfer137S0, d2WiderTransfer137C1, d2WiderTransfer137S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-9525715923026410210605 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) + ((((273580062007852795181 : ℚ) / 9444732965739290427392) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece23 (x : ℝ) (hx : x ∈ Icc ((((1334457301 : ℚ) / 2147483648) : ℚ) : ℝ) ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope23 x hx
  have hxT : x ∈ Icc (d2WiderTransfer141Lo : ℝ) (d2WiderTransfer141Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer141Lo, d2WiderTransfer141Hi, d2LitsNearWiderTransfers017.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer141Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((35090847179451893347079 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer141Cap, d2LitsNearWiderTransfers017.q2, d2WiderTransfer141C0, d2WiderTransfer141S0, d2WiderTransfer141C1, d2WiderTransfer141S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219364237389827242521351 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((35090847179451893347079 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece24 (x : ℝ) (hx : x ∈ Icc ((((668067511 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1337812743 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope24 x hx
  have hxT : x ∈ Icc (d2WiderTransfer145Lo : ℝ) (d2WiderTransfer145Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer145Lo, d2WiderTransfer145Hi, d2LitsNearWiderTransfers018.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer145Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17581796239080580390137 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer145Cap, d2LitsNearWiderTransfers018.q2, d2WiderTransfer145C0, d2WiderTransfer145S0, d2WiderTransfer145C1, d2WiderTransfer145S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-609718491344268254977273 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((17581796239080580390137 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece25 (x : ℝ) (hx : x ∈ Icc ((((1337812743 : ℚ) / 2147483648) : ℚ) : ℝ) ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope25 x hx
  have hxT : x ∈ Icc (d2WiderTransfer149Lo : ℝ) (d2WiderTransfer149Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer149Lo, d2WiderTransfer149Hi, d2LitsNearWiderTransfers018.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer149Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2202280277694988391823 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer149Cap, d2LitsNearWiderTransfers018.q2, d2WiderTransfer149C0, d2WiderTransfer149S0, d2WiderTransfer149C1, d2WiderTransfer149S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-76219367165843447715215 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) + ((((2202280277694988391823 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece26 (x : ℝ) (hx : x ∈ Icc ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ) ((((1341168185 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope26 x hx
  have hxT : x ∈ Icc (d2WiderTransfer153Lo : ℝ) (d2WiderTransfer153Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer153Lo, d2WiderTransfer153Hi, d2LitsNearWiderTransfers019.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer153Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((35309523688112514003109 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer153Cap, d2LitsNearWiderTransfers019.q2, d2WiderTransfer153C0, d2WiderTransfer153S0, d2WiderTransfer153C1, d2WiderTransfer153S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219582913898487863177381 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((35309523688112514003109 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece27 (x : ℝ) (hx : x ∈ Icc ((((1341168185 : ℚ) / 2147483648) : ℚ) : ℝ) ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope27 x hx
  have hxT : x ∈ Icc (d2WiderTransfer157Lo : ℝ) (d2WiderTransfer157Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer157Lo, d2WiderTransfer157Hi, d2LitsNearWiderTransfers019.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer157Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4422838853844172407613 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer157Cap, d2LitsNearWiderTransfers019.q2, d2WiderTransfer157C0, d2WiderTransfer157S0, d2WiderTransfer157C1, d2WiderTransfer157S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-152457012630141091054397 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) + ((((4422838853844172407613 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece28 (x : ℝ) (hx : x ∈ Icc ((((671422953 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope28 x hx
  have hxT : x ∈ Icc (d2WiderTransfer161Lo : ℝ) (d2WiderTransfer161Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer161Lo, d2WiderTransfer161Hi, d2LitsNearWiderTransfers020.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer161Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((35456046492517971808645 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer161Cap, d2LitsNearWiderTransfers020.q2, d2WiderTransfer161C0, d2WiderTransfer161S0, d2WiderTransfer161C1, d2WiderTransfer161S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219729436702893320982917 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((35456046492517971808645 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece29 (x : ℝ) (hx : x ∈ Icc ((((1344523627 : ℚ) / 2147483648) : ℚ) : ℝ) ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope29 x hx
  have hxT : x ∈ Icc (d2WiderTransfer165Lo : ℝ) (d2WiderTransfer165Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer165Lo, d2WiderTransfer165Hi, d2LitsNearWiderTransfers020.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer165Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((35529531298775613754217 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer165Cap, d2LitsNearWiderTransfers020.q2, d2WiderTransfer165C0, d2WiderTransfer165S0, d2WiderTransfer165C1, d2WiderTransfer165S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219802921509150962928489 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((35529531298775613754217 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece30 (x : ℝ) (hx : x ∈ Icc ((((336550337 : ℚ) / 536870912) : ℚ) : ℝ) ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope30 x hx
  have hxT : x ∈ Icc (d2WiderTransfer169Lo : ℝ) (d2WiderTransfer169Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer169Lo, d2WiderTransfer169Hi, d2LitsNearWiderTransfers021.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer169Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((35603165878822044064677 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer169Cap, d2LitsNearWiderTransfers021.q2, d2WiderTransfer169C0, d2WiderTransfer169S0, d2WiderTransfer169C1, d2WiderTransfer169S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219876556089197393238949 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((35603165878822044064677 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece31 (x : ℝ) (hx : x ∈ Icc ((((1347879069 : ℚ) / 2147483648) : ℚ) : ℝ) ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope31 x hx
  have hxT : x ∈ Icc (d2WiderTransfer173Lo : ℝ) (d2WiderTransfer173Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer173Lo, d2WiderTransfer173Hi, d2LitsNearWiderTransfers021.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer173Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((35676950865912418014545 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer173Cap, d2LitsNearWiderTransfers021.q2, d2WiderTransfer173C0, d2WiderTransfer173S0, d2WiderTransfer173C1, d2WiderTransfer173S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1219950341076287767188817 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((35676950865912418014545 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece32 (x : ℝ) (hx : x ∈ Icc ((((674778395 : ℚ) / 1073741824) : ℚ) : ℝ) ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope32 x hx
  have hxT : x ∈ Icc (d2WiderTransfer177Lo : ℝ) (d2WiderTransfer177Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer177Lo, d2WiderTransfer177Hi, d2LitsNearWiderTransfers022.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer177Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17875443448647326947963 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer177Cap, d2LitsNearWiderTransfers022.q2, d2WiderTransfer177C0, d2WiderTransfer177S0, d2WiderTransfer177C1, d2WiderTransfer177S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-610012138553835001535099 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((17875443448647326947963 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece33 (x : ℝ) (hx : x ∈ Icc ((((1351234511 : ℚ) / 2147483648) : ℚ) : ℝ) ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope33 x hx
  have hxT : x ∈ Icc (d2WiderTransfer181Lo : ℝ) (d2WiderTransfer181Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer181Lo, d2WiderTransfer181Hi, d2LitsNearWiderTransfers022.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer181Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17912487307121565692667 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer181Cap, d2LitsNearWiderTransfers022.q2, d2WiderTransfer181C0, d2WiderTransfer181S0, d2WiderTransfer181C1, d2WiderTransfer181S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-610049182412309240279803 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((17912487307121565692667 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece34 (x : ℝ) (hx : x ∈ Icc ((((169114029 : ℚ) / 268435456) : ℚ) : ℝ) ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope34 x hx
  have hxT : x ∈ Icc (d2WiderTransfer185Lo : ℝ) (d2WiderTransfer185Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer185Lo, d2WiderTransfer185Hi, d2LitsNearWiderTransfers023.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer185Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17986803845136662179725 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer185Cap, d2LitsNearWiderTransfers023.q2, d2WiderTransfer185C0, d2WiderTransfer185S0, d2WiderTransfer185C1, d2WiderTransfer185S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-610123498950324336766861 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((17986803845136662179725 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece35 (x : ℝ) (hx : x ∈ Icc ((((678133837 : ℚ) / 1073741824) : ℚ) : ℝ) ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope35 x hx
  have hxT : x ∈ Icc (d2WiderTransfer189Lo : ℝ) (d2WiderTransfer189Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer189Lo, d2WiderTransfer189Hi, d2LitsNearWiderTransfers023.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer189Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((36122855306030385286949 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer189Cap, d2LitsNearWiderTransfers023.q2, d2WiderTransfer189C0, d2WiderTransfer189S0, d2WiderTransfer189C1, d2WiderTransfer189S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1220396245516405734461221 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((36122855306030385286949 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece36 (x : ℝ) (hx : x ∈ Icc ((((339905779 : ℚ) / 536870912) : ℚ) : ℝ) ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope36 x hx
  have hxT : x ∈ Icc (d2WiderTransfer193Lo : ℝ) (d2WiderTransfer193Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer193Lo, d2WiderTransfer193Hi, d2LitsNearWiderTransfers024.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer193Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((36423215339181523853545 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer193Cap, d2LitsNearWiderTransfers024.q2, d2WiderTransfer193C0, d2WiderTransfer193S0, d2WiderTransfer193C1, d2WiderTransfer193S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1220696605549556873027817 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((36423215339181523853545 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece37 (x : ℝ) (hx : x ∈ Icc ((((85395875 : ℚ) / 134217728) : ℚ) : ℝ) ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope37 x hx
  have hxT : x ∈ Icc (d2WiderTransfer197Lo : ℝ) (d2WiderTransfer197Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer197Lo, d2WiderTransfer197Hi, d2LitsNearWiderTransfers024.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer197Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((36726097763477149086711 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer197Cap, d2LitsNearWiderTransfers024.q2, d2WiderTransfer197C0, d2WiderTransfer197S0, d2WiderTransfer197C1, d2WiderTransfer197S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1220999487973852498260983 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((36726097763477149086711 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece38 (x : ℝ) (hx : x ∈ Icc ((((343261221 : ℚ) / 536870912) : ℚ) : ℝ) ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope38 x hx
  have hxT : x ∈ Icc (d2WiderTransfer201Lo : ℝ) (d2WiderTransfer201Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer201Lo, d2WiderTransfer201Hi, d2LitsNearWiderTransfers025.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer201Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((37031546751209876944921 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer201Cap, d2LitsNearWiderTransfers025.q2, d2WiderTransfer201C0, d2WiderTransfer201S0, d2WiderTransfer201C1, d2WiderTransfer201S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1221304936961585226119193 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((37031546751209876944921 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece39 (x : ℝ) (hx : x ∈ Icc ((((172469471 : ℚ) / 268435456) : ℚ) : ℝ) ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope39 x hx
  have hxT : x ∈ Icc (d2WiderTransfer205Lo : ℝ) (d2WiderTransfer205Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer205Lo, d2WiderTransfer205Hi, d2LitsNearWiderTransfers025.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer205Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((37650326957066217842805 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer205Cap, d2LitsNearWiderTransfers025.q2, d2WiderTransfer205C0, d2WiderTransfer205S0, d2WiderTransfer205C1, d2WiderTransfer205S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1221923717167441567017077 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((37650326957066217842805 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece40 (x : ℝ) (hx : x ∈ Icc ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ) ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope40 x hx
  have hxT : x ∈ Icc (d2WiderTransfer209Lo : ℝ) (d2WiderTransfer209Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer209Lo, d2WiderTransfer209Hi, d2LitsNearWiderTransfers026.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer209Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((19460381955120054910805 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer209Cap, d2LitsNearWiderTransfers026.q2, d2WiderTransfer209C0, d2WiderTransfer209S0, d2WiderTransfer209C1, d2WiderTransfer209S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-611597077060307729497941 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((19460381955120054910805 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece41 (x : ℝ) (hx : x ∈ Icc ((((88751317 : ℚ) / 134217728) : ℚ) : ℝ) ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope41 x hx
  have hxT : x ∈ Icc (d2WiderTransfer213Lo : ℝ) (d2WiderTransfer213Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer213Lo, d2WiderTransfer213Hi, d2LitsNearWiderTransfers026.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer213Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((10059450662200535250083 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer213Cap, d2LitsNearWiderTransfers026.q2, d2WiderTransfer213C0, d2WiderTransfer213S0, d2WiderTransfer213C1, d2WiderTransfer213S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-306127798214794372543651 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((10059450662200535250083 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece42 (x : ℝ) (hx : x ∈ Icc ((((45214519 : ℚ) / 67108864) : ℚ) : ℝ) ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope42 x hx
  have hxT : x ∈ Icc (d2WiderTransfer217Lo : ℝ) (d2WiderTransfer217Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer217Lo, d2WiderTransfer217Hi, d2LitsNearWiderTransfers027.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer217Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((43026772375974710392903 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer217Cap, d2LitsNearWiderTransfers027.q2, d2WiderTransfer217C0, d2WiderTransfer217S0, d2WiderTransfer217C1, d2WiderTransfer217S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1227300162586350059567175 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((43026772375974710392903 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece43 (x : ℝ) (hx : x ∈ Icc ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ) ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope43 x hx
  have hxT : x ∈ Icc (d2WiderTransfer221Lo : ℝ) (d2WiderTransfer221Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer221Lo, d2WiderTransfer221Hi, d2LitsNearWiderTransfers027.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer221Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((12339905407240976231317 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer221Cap, d2LitsNearWiderTransfers027.q2, d2WiderTransfer221C0, d2WiderTransfer221S0, d2WiderTransfer221C1, d2WiderTransfer221S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-308408252959834813524885 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((12339905407240976231317 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece44 (x : ℝ) (hx : x ∈ Icc ((((25123841 : ℚ) / 33554432) : ℚ) : ℝ) ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope44 x hx
  have hxT : x ∈ Icc (d2WiderTransfer225Lo : ℝ) (d2WiderTransfer225Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer225Lo, d2WiderTransfer225Hi, d2LitsNearWiderTransfers028.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer225Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((57077457320577085525701 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer225Cap, d2LitsNearWiderTransfers028.q2, d2WiderTransfer225C0, d2WiderTransfer225S0, d2WiderTransfer225C1, d2WiderTransfer225S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1241350847530952434699973 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((57077457320577085525701 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece45 (x : ℝ) (hx : x ∈ Icc ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ) ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope45 x hx
  have hxT : x ∈ Icc (d2WiderTransfer229Lo : ℝ) (d2WiderTransfer229Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer229Lo, d2WiderTransfer229Hi, d2LitsNearWiderTransfers028.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer229Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((80856180095387009534549 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer229Cap, d2LitsNearWiderTransfers028.q2, d2WiderTransfer229C0, d2WiderTransfer229S0, d2WiderTransfer229C1, d2WiderTransfer229S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1265129570305762358708821 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((80856180095387009534549 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece46 (x : ℝ) (hx : x ∈ Icc ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ) ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope46 x hx
  have hxT : x ∈ Icc (d2WiderTransfer233Lo : ℝ) (d2WiderTransfer233Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer233Lo, d2WiderTransfer233Hi, d2LitsNearWiderTransfers029.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer233Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((52164698824385549439599 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer233Cap, d2LitsNearWiderTransfers029.q2, d2WiderTransfer233C0, d2WiderTransfer233S0, d2WiderTransfer233C1, d2WiderTransfer233S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-644301393929573224026735 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((52164698824385549439599 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece47 (x : ℝ) (hx : x ∈ Icc ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ) ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope47 x hx
  have hxT : x ∈ Icc (d2WiderTransfer237Lo : ℝ) (d2WiderTransfer237Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer237Lo, d2WiderTransfer237Hi, d2LitsNearWiderTransfers029.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer237Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((63675261822203530136993 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer237Cap, d2LitsNearWiderTransfers029.q2, d2WiderTransfer237C0, d2WiderTransfer237S0, d2WiderTransfer237C1, d2WiderTransfer237S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-655811956927391204724129 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((63675261822203530136993 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece48 (x : ℝ) (hx : x ∈ Icc ((((65347171 : ℚ) / 67108864) : ℚ) : ℝ) ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope48 x hx
  have hxT : x ∈ Icc (d2WiderTransfer241Lo : ℝ) (d2WiderTransfer241Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer241Lo, d2WiderTransfer241Hi, d2LitsNearWiderTransfers030.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer241Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((57980701712297931475589 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer241Cap, d2LitsNearWiderTransfers030.q2, d2WiderTransfer241C0, d2WiderTransfer241S0, d2WiderTransfer241C1, d2WiderTransfer241S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-354049049264891768769157 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((57980701712297931475589 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece49 (x : ℝ) (hx : x ∈ Icc ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ) ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope49 x hx
  have hxT : x ∈ Icc (d2WiderTransfer245Lo : ℝ) (d2WiderTransfer245Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer245Lo, d2WiderTransfer245Hi, d2LitsNearWiderTransfers030.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer245Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((239620542858252702107649 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer245Cap, d2LitsNearWiderTransfers030.q2, d2WiderTransfer245C0, d2WiderTransfer245S0, d2WiderTransfer245C1, d2WiderTransfer245S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1423893933068628051281921 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((239620542858252702107649 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece50 (x : ℝ) (hx : x ∈ Icc ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope50 x hx
  have hxT : x ∈ Icc (d2WiderTransfer249Lo : ℝ) (d2WiderTransfer249Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer249Lo, d2WiderTransfer249Hi, d2LitsNearWiderTransfers031.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer249Bound x hxT
  have hd : ((((1 : ℚ) / 352) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-5 : ℚ) / 176) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((239622147820180937928707 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer249Cap, d2LitsNearWiderTransfers031.q2, d2WiderTransfer249C0, d2WiderTransfer249S0, d2WiderTransfer249C1, d2WiderTransfer249S1, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1423895538030556287102979 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((239622147820180937928707 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner4Domain0Pieces : List (ℚ × ℚ) := [(((98749 : ℚ) / 1000000), ((828367 : ℚ) / 8388608)), (((828367 : ℚ) / 8388608), ((8304657 : ℚ) / 67108864)), (((8304657 : ℚ) / 67108864), ((4991189 : ℚ) / 33554432)), (((4991189 : ℚ) / 33554432), ((3334455 : ℚ) / 16777216)), (((3334455 : ℚ) / 16777216), ((313261 : ℚ) / 1048576)), (((313261 : ℚ) / 1048576), ((6689897 : ℚ) / 16777216)), (((6689897 : ℚ) / 16777216), ((4183809 : ℚ) / 8388608)), (((4183809 : ℚ) / 8388608), ((18412957 : ℚ) / 33554432)), (((18412957 : ℚ) / 33554432), ((38503635 : ℚ) / 67108864)), (((38503635 : ℚ) / 67108864), ((78684991 : ℚ) / 134217728)), (((78684991 : ℚ) / 134217728), ((10045339 : ℚ) / 16777216)), (((10045339 : ℚ) / 16777216), ((162403145 : ℚ) / 268435456)), (((162403145 : ℚ) / 268435456), ((326484011 : ℚ) / 536870912)), (((326484011 : ℚ) / 536870912), ((654645743 : ℚ) / 1073741824)), (((654645743 : ℚ) / 1073741824), ((82040433 : ℚ) / 134217728)), (((82040433 : ℚ) / 134217728), ((329839453 : ℚ) / 536870912)), (((329839453 : ℚ) / 536870912), ((661356627 : ℚ) / 1073741824)), (((661356627 : ℚ) / 1073741824), ((165758587 : ℚ) / 268435456)), (((165758587 : ℚ) / 268435456), ((1327746417 : ℚ) / 2147483648)), (((1327746417 : ℚ) / 2147483648), ((664712069 : ℚ) / 1073741824)), (((664712069 : ℚ) / 1073741824), ((1331101859 : ℚ) / 2147483648)), (((1331101859 : ℚ) / 2147483648), ((333194895 : ℚ) / 536870912)), (((333194895 : ℚ) / 536870912), ((1334457301 : ℚ) / 2147483648)), (((1334457301 : ℚ) / 2147483648), ((668067511 : ℚ) / 1073741824)), (((668067511 : ℚ) / 1073741824), ((1337812743 : ℚ) / 2147483648)), (((1337812743 : ℚ) / 2147483648), ((41859077 : ℚ) / 67108864)), (((41859077 : ℚ) / 67108864), ((1341168185 : ℚ) / 2147483648)), (((1341168185 : ℚ) / 2147483648), ((671422953 : ℚ) / 1073741824)), (((671422953 : ℚ) / 1073741824), ((1344523627 : ℚ) / 2147483648)), (((1344523627 : ℚ) / 2147483648), ((336550337 : ℚ) / 536870912)), (((336550337 : ℚ) / 536870912), ((1347879069 : ℚ) / 2147483648)), (((1347879069 : ℚ) / 2147483648), ((674778395 : ℚ) / 1073741824)), (((674778395 : ℚ) / 1073741824), ((1351234511 : ℚ) / 2147483648)), (((1351234511 : ℚ) / 2147483648), ((169114029 : ℚ) / 268435456)), (((169114029 : ℚ) / 268435456), ((678133837 : ℚ) / 1073741824)), (((678133837 : ℚ) / 1073741824), ((339905779 : ℚ) / 536870912)), (((339905779 : ℚ) / 536870912), ((85395875 : ℚ) / 134217728)), (((85395875 : ℚ) / 134217728), ((343261221 : ℚ) / 536870912)), (((343261221 : ℚ) / 536870912), ((172469471 : ℚ) / 268435456)), (((172469471 : ℚ) / 268435456), ((21768399 : ℚ) / 33554432)), (((21768399 : ℚ) / 33554432), ((88751317 : ℚ) / 134217728)), (((88751317 : ℚ) / 134217728), ((45214519 : ℚ) / 67108864)), (((45214519 : ℚ) / 67108864), ((2930765 : ℚ) / 4194304)), (((2930765 : ℚ) / 4194304), ((25123841 : ℚ) / 33554432)), (((25123841 : ℚ) / 33554432), ((13400781 : ℚ) / 16777216)), (((13400781 : ℚ) / 16777216), ((7539251 : ℚ) / 8388608)), (((7539251 : ℚ) / 8388608), ((31834725 : ℚ) / 33554432)), (((31834725 : ℚ) / 33554432), ((65347171 : ℚ) / 67108864)), (((65347171 : ℚ) / 67108864), ((16756223 : ℚ) / 16777216)), (((16756223 : ℚ) / 16777216), ((8380219 : ℚ) / 8388608)), (((8380219 : ℚ) / 8388608), ((999 : ℚ) / 1000))]
theorem corner4Domain0Cover : pieceCover ((999 : ℚ) / 1000) ((98749 : ℚ) / 1000000) corner4Domain0Pieces = true := by decide +kernel
theorem corner4Domain0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  apply pieceCover_bound ((999 : ℚ) / 1000) (fun x : ℝ => fval (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x) ((((-1077090373847 : ℚ) / 1099511627776) : ℚ) : ℝ) ((98749 : ℚ) / 1000000) corner4Domain0Pieces (by decide +kernel) corner4Domain0Cover
  intro p hp
  simp only [corner4Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner4Piece0
  · exact corner4Piece1
  · exact corner4Piece2
  · exact corner4Piece3
  · exact corner4Piece4
  · exact corner4Piece5
  · exact corner4Piece6
  · exact corner4Piece7
  · exact corner4Piece8
  · exact corner4Piece9
  · exact corner4Piece10
  · exact corner4Piece11
  · exact corner4Piece12
  · exact corner4Piece13
  · exact corner4Piece14
  · exact corner4Piece15
  · exact corner4Piece16
  · exact corner4Piece17
  · exact corner4Piece18
  · exact corner4Piece19
  · exact corner4Piece20
  · exact corner4Piece21
  · exact corner4Piece22
  · exact corner4Piece23
  · exact corner4Piece24
  · exact corner4Piece25
  · exact corner4Piece26
  · exact corner4Piece27
  · exact corner4Piece28
  · exact corner4Piece29
  · exact corner4Piece30
  · exact corner4Piece31
  · exact corner4Piece32
  · exact corner4Piece33
  · exact corner4Piece34
  · exact corner4Piece35
  · exact corner4Piece36
  · exact corner4Piece37
  · exact corner4Piece38
  · exact corner4Piece39
  · exact corner4Piece40
  · exact corner4Piece41
  · exact corner4Piece42
  · exact corner4Piece43
  · exact corner4Piece44
  · exact corner4Piece45
  · exact corner4Piece46
  · exact corner4Piece47
  · exact corner4Piece48
  · exact corner4Piece49
  · exact corner4Piece50
#print axioms corner4Domain0Cover
#print axioms corner4Domain0
end D72.NearCornerCover001
end CatalanMeasure.GenD.Signed.Data.Cells
