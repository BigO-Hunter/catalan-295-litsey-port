module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearCorners000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers005
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open CatalanMeasure.GenD.Signed.Data.Trial
namespace D72.NearCornerCover000
theorem envelope0 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((828367 : ℚ) / 8388608) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction000P0Lo : ℝ) (d2NearProduction000P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction000P0Lo, d2NearProduction000P0Hi, d2NearProduction000P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction000P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction000P0Literal.q2])
theorem envelope1 (x : ℝ) (hx : x ∈ Icc ((((828367 : ℚ) / 8388608) : ℚ) : ℝ) ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction003P0Lo : ℝ) (d2NearProduction003P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction003P0Lo, d2NearProduction003P0Hi, d2NearProduction003P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction003P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction003P0Literal.q2])
theorem envelope2 (x : ℝ) (hx : x ∈ Icc ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ) ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction003P1Lo : ℝ) (d2NearProduction003P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction003P1Lo, d2NearProduction003P1Hi, d2NearProduction003P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction003P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction003P1Literal.q2])
theorem envelope3 (x : ℝ) (hx : x ∈ Icc ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ) ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction003P2Lo : ℝ) (d2NearProduction003P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction003P2Lo, d2NearProduction003P2Hi, d2NearProduction003P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction003P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction003P2Literal.q2])
theorem envelope4 (x : ℝ) (hx : x ∈ Icc ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ) ((((313261 : ℚ) / 1048576) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction003P3Lo : ℝ) (d2NearProduction003P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction003P3Lo, d2NearProduction003P3Hi, d2NearProduction003P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction003P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction003P3Literal.q2])
theorem envelope5 (x : ℝ) (hx : x ∈ Icc ((((313261 : ℚ) / 1048576) : ℚ) : ℝ) ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction004P0Lo : ℝ) (d2NearProduction004P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction004P0Lo, d2NearProduction004P0Hi, d2NearProduction004P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction004P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction004P0Literal.q2])
theorem envelope6 (x : ℝ) (hx : x ∈ Icc ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ) ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction004P1Lo : ℝ) (d2NearProduction004P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction004P1Lo, d2NearProduction004P1Hi, d2NearProduction004P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction004P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction004P1Literal.q2])
theorem envelope7 (x : ℝ) (hx : x ∈ Icc ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ) ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction000P1Lo : ℝ) (d2NearProduction000P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction000P1Lo, d2NearProduction000P1Hi, d2NearProduction000P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction000P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction000P1Literal.q2])
theorem envelope8 (x : ℝ) (hx : x ∈ Icc ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ) ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction000P2Lo : ℝ) (d2NearProduction000P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction000P2Lo, d2NearProduction000P2Hi, d2NearProduction000P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction000P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction000P2Literal.q2])
theorem envelope9 (x : ℝ) (hx : x ∈ Icc ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ) ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction000P3Lo : ℝ) (d2NearProduction000P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction000P3Lo, d2NearProduction000P3Hi, d2NearProduction000P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction000P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction000P3Literal.q2])
theorem envelope10 (x : ℝ) (hx : x ∈ Icc ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ) ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction000P4Lo : ℝ) (d2NearProduction000P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction000P4Lo, d2NearProduction000P4Hi, d2NearProduction000P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction000P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction000P4Literal.q2])
theorem envelope11 (x : ℝ) (hx : x ∈ Icc ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ) ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-300378249535897389200815 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction000P5Lo : ℝ) (d2NearProduction000P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction000P5Lo, d2NearProduction000P5Hi, d2NearProduction000P5Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction000P5Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction000P5Literal.q2])
theorem envelope12 (x : ℝ) (hx : x ∈ Icc ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ) ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-1201557887486092256687799 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction000P6Lo : ℝ) (d2NearProduction000P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction000P6Lo, d2NearProduction000P6Hi, d2NearProduction000P6Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction000P6Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction000P6Literal.q2])
theorem envelope13 (x : ℝ) (hx : x ∈ Icc ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ) ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-75100217684870557832437 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction000P7Lo : ℝ) (d2NearProduction000P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction000P7Lo, d2NearProduction000P7Hi, d2NearProduction000P7Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction000P7Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction000P7Literal.q2])
theorem envelope14 (x : ℝ) (hx : x ∈ Icc ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ) ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-600824903997445426447247 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction001P0Lo : ℝ) (d2NearProduction001P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction001P0Lo, d2NearProduction001P0Hi, d2NearProduction001P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction001P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction001P0Literal.q2])
theorem envelope15 (x : ℝ) (hx : x ∈ Icc ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ) ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-1201842915396006565180385 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction001P1Lo : ℝ) (d2NearProduction001P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction001P1Lo, d2NearProduction001P1Hi, d2NearProduction001P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction001P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction001P1Literal.q2])
theorem envelope16 (x : ℝ) (hx : x ∈ Icc ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ) ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-1202273031029519244584393 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction001P2Lo : ℝ) (d2NearProduction001P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction001P2Lo, d2NearProduction001P2Hi, d2NearProduction001P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction001P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction001P2Literal.q2])
theorem envelope17 (x : ℝ) (hx : x ∈ Icc ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ) ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-1203397085825087434595017 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction001P3Lo : ℝ) (d2NearProduction001P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction001P3Lo, d2NearProduction001P3Hi, d2NearProduction001P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction001P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction001P3Literal.q2])
theorem envelope18 (x : ℝ) (hx : x ∈ Icc ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ) ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-301324845911768057128931 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction001P4Lo : ℝ) (d2NearProduction001P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction001P4Lo, d2NearProduction001P4Hi, d2NearProduction001P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction001P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction001P4Literal.q2])
theorem envelope19 (x : ℝ) (hx : x ∈ Icc ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ) ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-18862144391427233682239 : ℚ) / 18889465931478580854784) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction001P5Lo : ℝ) (d2NearProduction001P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction001P5Lo, d2NearProduction001P5Hi, d2NearProduction001P5Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction001P5Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction001P5Literal.q2])
theorem envelope20 (x : ℝ) (hx : x ∈ Icc ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ) ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-1217384713787376605825149 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction001P6Lo : ℝ) (d2NearProduction001P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction001P6Lo, d2NearProduction001P6Hi, d2NearProduction001P6Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction001P6Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction001P6Literal.q2])
theorem envelope21 (x : ℝ) (hx : x ∈ Icc ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ) ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-304500133167025370980393 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction001P7Lo : ℝ) (d2NearProduction001P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction001P7Lo, d2NearProduction001P7Hi, d2NearProduction001P7Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction001P7Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction001P7Literal.q2])
theorem envelope22 (x : ℝ) (hx : x ∈ Icc ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ)) : (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) ≤ ((((-1218000661065055742787257 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction002P0Lo : ℝ) (d2NearProduction002P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction002P0Lo, d2NearProduction002P0Hi, d2NearProduction002P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction002P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction002P0Literal.q2])
theorem delta0Check : fieldNFCheck D72.NearCorners000.delta0 (fqSum []) = true := by decide +kernel
theorem delta0Value (x : ℝ) : fval D72.NearCorners000.delta0 x = (0 : ℝ) := by
  have h := fieldNFCheck_sound delta0Check x
  change fval D72.NearCorners000.delta0 x = fval (fqSum []) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner0Identity (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x = (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) + ((0 : ℝ)) := by
  rw [D72.NearCorners000.corner0Value, delta0Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) x, D72.NearCorners000.corner0Terms, laurentNF_sound, ← D72.NearBinding000.termsValue x]
  ring
theorem corner0Piece0 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((828367 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope0 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece1 (x : ℝ) (hx : x ∈ Icc ((((828367 : ℚ) / 8388608) : ℚ) : ℝ) ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope1 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece2 (x : ℝ) (hx : x ∈ Icc ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ) ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope2 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece3 (x : ℝ) (hx : x ∈ Icc ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ) ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope3 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece4 (x : ℝ) (hx : x ∈ Icc ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ) ((((313261 : ℚ) / 1048576) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope4 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece5 (x : ℝ) (hx : x ∈ Icc ((((313261 : ℚ) / 1048576) : ℚ) : ℝ) ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope5 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece6 (x : ℝ) (hx : x ∈ Icc ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ) ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope6 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece7 (x : ℝ) (hx : x ∈ Icc ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ) ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope7 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece8 (x : ℝ) (hx : x ∈ Icc ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ) ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope8 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece9 (x : ℝ) (hx : x ∈ Icc ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ) ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope9 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece10 (x : ℝ) (hx : x ∈ Icc ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ) ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope10 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece11 (x : ℝ) (hx : x ∈ Icc ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ) ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope11 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece12 (x : ℝ) (hx : x ∈ Icc ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ) ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope12 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece13 (x : ℝ) (hx : x ∈ Icc ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ) ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope13 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece14 (x : ℝ) (hx : x ∈ Icc ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ) ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope14 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece15 (x : ℝ) (hx : x ∈ Icc ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ) ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope15 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece16 (x : ℝ) (hx : x ∈ Icc ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ) ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope16 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece17 (x : ℝ) (hx : x ∈ Icc ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ) ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope17 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece18 (x : ℝ) (hx : x ∈ Icc ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ) ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope18 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece19 (x : ℝ) (hx : x ∈ Icc ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ) ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope19 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece20 (x : ℝ) (hx : x ∈ Icc ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ) ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope20 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece21 (x : ℝ) (hx : x ∈ Icc ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ) ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope21 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece22 (x : ℝ) (hx : x ∈ Icc ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope22 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
def corner0Domain0Pieces : List (ℚ × ℚ) := [(((98749 : ℚ) / 1000000), ((828367 : ℚ) / 8388608)), (((828367 : ℚ) / 8388608), ((8304657 : ℚ) / 67108864)), (((8304657 : ℚ) / 67108864), ((4991189 : ℚ) / 33554432)), (((4991189 : ℚ) / 33554432), ((3334455 : ℚ) / 16777216)), (((3334455 : ℚ) / 16777216), ((313261 : ℚ) / 1048576)), (((313261 : ℚ) / 1048576), ((6689897 : ℚ) / 16777216)), (((6689897 : ℚ) / 16777216), ((4183809 : ℚ) / 8388608)), (((4183809 : ℚ) / 8388608), ((18412957 : ℚ) / 33554432)), (((18412957 : ℚ) / 33554432), ((38503635 : ℚ) / 67108864)), (((38503635 : ℚ) / 67108864), ((78684991 : ℚ) / 134217728)), (((78684991 : ℚ) / 134217728), ((10045339 : ℚ) / 16777216)), (((10045339 : ℚ) / 16777216), ((162403145 : ℚ) / 268435456)), (((162403145 : ℚ) / 268435456), ((82040433 : ℚ) / 134217728)), (((82040433 : ℚ) / 134217728), ((165758587 : ℚ) / 268435456)), (((165758587 : ℚ) / 268435456), ((41859077 : ℚ) / 67108864)), (((41859077 : ℚ) / 67108864), ((21768399 : ℚ) / 33554432)), (((21768399 : ℚ) / 33554432), ((2930765 : ℚ) / 4194304)), (((2930765 : ℚ) / 4194304), ((13400781 : ℚ) / 16777216)), (((13400781 : ℚ) / 16777216), ((7539251 : ℚ) / 8388608)), (((7539251 : ℚ) / 8388608), ((31834725 : ℚ) / 33554432)), (((31834725 : ℚ) / 33554432), ((16756223 : ℚ) / 16777216)), (((16756223 : ℚ) / 16777216), ((8380219 : ℚ) / 8388608)), (((8380219 : ℚ) / 8388608), ((999 : ℚ) / 1000))]
theorem corner0Domain0Cover : pieceCover ((999 : ℚ) / 1000) ((98749 : ℚ) / 1000000) corner0Domain0Pieces = true := by decide +kernel
theorem corner0Domain0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  apply pieceCover_bound ((999 : ℚ) / 1000) (fun x : ℝ => fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x) ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) ((98749 : ℚ) / 1000000) corner0Domain0Pieces (by decide +kernel) corner0Domain0Cover
  intro p hp
  simp only [corner0Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
#print axioms corner0Domain0Cover
#print axioms corner0Domain0
theorem delta1Check : fieldNFCheck D72.NearCorners000.delta1 (fqSum [logFQ ((1 : ℚ) / 400) ((-1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta1Value (x : ℝ) : fval D72.NearCorners000.delta1 x = ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta1Check x
  change fval D72.NearCorners000.delta1 x = fval (fqSum [logFQ ((1 : ℚ) / 400) ((-1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner1Identity (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x = (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) + (((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  rw [D72.NearCorners000.corner1Value, delta1Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) x, D72.NearCorners000.corner1Terms, laurentNF_sound, ← D72.NearBinding000.termsValue x]
  ring
theorem corner1Piece0 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((828367 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer0Lo : ℝ) (d2WiderTransfer0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer0Lo, d2WiderTransfer0Hi, d2LitsNearWiderTransfers000.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer0Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer0Cap, d2LitsNearWiderTransfers000.q2, d2WiderTransfer0C0, d2WiderTransfer0S0] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece1 (x : ℝ) (hx : x ∈ Icc ((((828367 : ℚ) / 8388608) : ℚ) : ℝ) ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer2Lo : ℝ) (d2WiderTransfer2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer2Lo, d2WiderTransfer2Hi, d2LitsNearWiderTransfers000.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer2Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer2Cap, d2LitsNearWiderTransfers000.q2, d2WiderTransfer2C0, d2WiderTransfer2S0] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece2 (x : ℝ) (hx : x ∈ Icc ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ) ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer4Lo : ℝ) (d2WiderTransfer4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer4Lo, d2WiderTransfer4Hi, d2LitsNearWiderTransfers000.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer4Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer4Cap, d2LitsNearWiderTransfers000.q2, d2WiderTransfer4C0, d2WiderTransfer4S0] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece3 (x : ℝ) (hx : x ∈ Icc ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ) ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer6Lo : ℝ) (d2WiderTransfer6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer6Lo, d2WiderTransfer6Hi, d2LitsNearWiderTransfers000.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer6Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer6Cap, d2LitsNearWiderTransfers000.q2, d2WiderTransfer6C0, d2WiderTransfer6S0] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece4 (x : ℝ) (hx : x ∈ Icc ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ) ((((313261 : ℚ) / 1048576) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer8Lo : ℝ) (d2WiderTransfer8Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer8Lo, d2WiderTransfer8Hi, d2LitsNearWiderTransfers001.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer8Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer8Cap, d2LitsNearWiderTransfers001.q2, d2WiderTransfer8C0, d2WiderTransfer8S0] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece5 (x : ℝ) (hx : x ∈ Icc ((((313261 : ℚ) / 1048576) : ℚ) : ℝ) ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer10Lo : ℝ) (d2WiderTransfer10Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer10Lo, d2WiderTransfer10Hi, d2LitsNearWiderTransfers001.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer10Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer10Cap, d2LitsNearWiderTransfers001.q2, d2WiderTransfer10C0, d2WiderTransfer10S0] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece6 (x : ℝ) (hx : x ∈ Icc ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ) ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer12Lo : ℝ) (d2WiderTransfer12Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer12Lo, d2WiderTransfer12Hi, d2LitsNearWiderTransfers001.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer12Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer12Cap, d2LitsNearWiderTransfers001.q2, d2WiderTransfer12C0, d2WiderTransfer12S0] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece7 (x : ℝ) (hx : x ∈ Icc ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ) ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer14Lo : ℝ) (d2WiderTransfer14Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer14Lo, d2WiderTransfer14Hi, d2LitsNearWiderTransfers001.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer14Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer14Cap, d2LitsNearWiderTransfers001.q2, d2WiderTransfer14C0, d2WiderTransfer14S0] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece8 (x : ℝ) (hx : x ∈ Icc ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ) ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer16Lo : ℝ) (d2WiderTransfer16Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer16Lo, d2WiderTransfer16Hi, d2LitsNearWiderTransfers002.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer16Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer16Cap, d2LitsNearWiderTransfers002.q2, d2WiderTransfer16C0, d2WiderTransfer16S0] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece9 (x : ℝ) (hx : x ∈ Icc ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ) ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope9 x hx
  have hxT : x ∈ Icc (d2WiderTransfer18Lo : ℝ) (d2WiderTransfer18Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer18Lo, d2WiderTransfer18Hi, d2LitsNearWiderTransfers002.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer18Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer18Cap, d2LitsNearWiderTransfers002.q2, d2WiderTransfer18C0, d2WiderTransfer18S0] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece10 (x : ℝ) (hx : x ∈ Icc ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ) ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope10 x hx
  have hxT : x ∈ Icc (d2WiderTransfer20Lo : ℝ) (d2WiderTransfer20Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer20Lo, d2WiderTransfer20Hi, d2LitsNearWiderTransfers002.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer20Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer20Cap, d2LitsNearWiderTransfers002.q2, d2WiderTransfer20C0, d2WiderTransfer20S0] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((648894057 : ℚ) / 549755813888) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece11 (x : ℝ) (hx : x ∈ Icc ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ) ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope11 x hx
  have hxT : x ∈ Icc (d2WiderTransfer22Lo : ℝ) (d2WiderTransfer22Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer22Lo, d2WiderTransfer22Hi, d2LitsNearWiderTransfers002.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer22Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((358616464823175574959 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer22Cap, d2LitsNearWiderTransfers002.q2, d2WiderTransfer22C0, d2WiderTransfer22S0] using hD
  have hcap : ((((-300378249535897389200815 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((358616464823175574959 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece12 (x : ℝ) (hx : x ∈ Icc ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ) ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope12 x hx
  have hxT : x ∈ Icc (d2WiderTransfer24Lo : ℝ) (d2WiderTransfer24Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer24Lo, d2WiderTransfer24Hi, d2LitsNearWiderTransfers003.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer24Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1479355201795402184375 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer24Cap, d2LitsNearWiderTransfers003.q2, d2WiderTransfer24C0, d2WiderTransfer24S0] using hD
  have hcap : ((((-1201557887486092256687799 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((1479355201795402184375 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece13 (x : ℝ) (hx : x ∈ Icc ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ) ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope13 x hx
  have hxT : x ∈ Icc (d2WiderTransfer26Lo : ℝ) (d2WiderTransfer26Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer26Lo, d2WiderTransfer26Hi, d2LitsNearWiderTransfers003.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer26Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((95309417102004425973 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer26Cap, d2LitsNearWiderTransfers003.q2, d2WiderTransfer26C0, d2WiderTransfer26S0] using hD
  have hcap : ((((-75100217684870557832437 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) + ((((95309417102004425973 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece14 (x : ℝ) (hx : x ∈ Icc ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ) ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope14 x hx
  have hxT : x ∈ Icc (d2WiderTransfer28Lo : ℝ) (d2WiderTransfer28Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer28Lo, d2WiderTransfer28Hi, d2LitsNearWiderTransfers003.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer28Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((785637855296999195535 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer28Cap, d2LitsNearWiderTransfers003.q2, d2WiderTransfer28C0, d2WiderTransfer28S0] using hD
  have hcap : ((((-600824903997445426447247 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((785637855296999195535 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece15 (x : ℝ) (hx : x ∈ Icc ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ) ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope15 x hx
  have hxT : x ∈ Icc (d2WiderTransfer30Lo : ℝ) (d2WiderTransfer30Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer30Lo, d2WiderTransfer30Hi, d2LitsNearWiderTransfers003.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer30Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1764383111709710676961 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer30Cap, d2LitsNearWiderTransfers003.q2, d2WiderTransfer30C0, d2WiderTransfer30S0] using hD
  have hcap : ((((-1201842915396006565180385 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((1764383111709710676961 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece16 (x : ℝ) (hx : x ∈ Icc ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ) ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope16 x hx
  have hxT : x ∈ Icc (d2WiderTransfer32Lo : ℝ) (d2WiderTransfer32Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer32Lo, d2WiderTransfer32Hi, d2LitsNearWiderTransfers004.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer32Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2194498745222390080969 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer32Cap, d2LitsNearWiderTransfers004.q2, d2WiderTransfer32C0, d2WiderTransfer32S0] using hD
  have hcap : ((((-1202273031029519244584393 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2194498745222390080969 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece17 (x : ℝ) (hx : x ∈ Icc ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ) ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope17 x hx
  have hxT : x ∈ Icc (d2WiderTransfer34Lo : ℝ) (d2WiderTransfer34Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer34Lo, d2WiderTransfer34Hi, d2LitsNearWiderTransfers004.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer34Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3318553540790580091593 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer34Cap, d2LitsNearWiderTransfers004.q2, d2WiderTransfer34C0, d2WiderTransfer34S0] using hD
  have hcap : ((((-1203397085825087434595017 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((3318553540790580091593 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece18 (x : ℝ) (hx : x ∈ Icc ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ) ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope18 x hx
  have hxT : x ∈ Icc (d2WiderTransfer36Lo : ℝ) (d2WiderTransfer36Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer36Lo, d2WiderTransfer36Hi, d2LitsNearWiderTransfers004.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer36Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1305212840693843503075 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer36Cap, d2LitsNearWiderTransfers004.q2, d2WiderTransfer36C0, d2WiderTransfer36S0] using hD
  have hcap : ((((-301324845911768057128931 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((1305212840693843503075 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece19 (x : ℝ) (hx : x ∈ Icc ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ) ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope19 x hx
  have hxT : x ∈ Icc (d2WiderTransfer38Lo : ℝ) (d2WiderTransfer38Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer38Lo, d2WiderTransfer38Hi, d2LitsNearWiderTransfers004.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer38Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((110917324485095330623 : ℚ) / 18889465931478580854784) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer38Cap, d2LitsNearWiderTransfers004.q2, d2WiderTransfer38C0, d2WiderTransfer38S0] using hD
  have hcap : ((((-18862144391427233682239 : ℚ) / 18889465931478580854784) : ℚ) : ℝ) + ((((110917324485095330623 : ℚ) / 18889465931478580854784) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece20 (x : ℝ) (hx : x ∈ Icc ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ) ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope20 x hx
  have hxT : x ∈ Icc (d2WiderTransfer40Lo : ℝ) (d2WiderTransfer40Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer40Lo, d2WiderTransfer40Hi, d2LitsNearWiderTransfers005.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer40Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17306181503079751321725 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer40Cap, d2LitsNearWiderTransfers005.q2, d2WiderTransfer40C0, d2WiderTransfer40S0] using hD
  have hcap : ((((-1217384713787376605825149 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((17306181503079751321725 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece21 (x : ℝ) (hx : x ∈ Icc ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ) ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope21 x hx
  have hxT : x ∈ Icc (d2WiderTransfer42Lo : ℝ) (d2WiderTransfer42Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer42Lo, d2WiderTransfer42Hi, d2LitsNearWiderTransfers005.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer42Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4480500095951157354537 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer42Cap, d2LitsNearWiderTransfers005.q2, d2WiderTransfer42C0, d2WiderTransfer42S0] using hD
  have hcap : ((((-304500133167025370980393 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((4480500095951157354537 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece22 (x : ℝ) (hx : x ∈ Icc ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope22 x hx
  have hxT : x ∈ Icc (d2WiderTransfer44Lo : ℝ) (d2WiderTransfer44Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer44Lo, d2WiderTransfer44Hi, d2LitsNearWiderTransfers005.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer44Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((17922128780758888283833 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer44Cap, d2LitsNearWiderTransfers005.q2, d2WiderTransfer44C0, d2WiderTransfer44S0] using hD
  have hcap : ((((-1218000661065055742787257 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((17922128780758888283833 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner1Domain0Pieces : List (ℚ × ℚ) := [(((98749 : ℚ) / 1000000), ((828367 : ℚ) / 8388608)), (((828367 : ℚ) / 8388608), ((8304657 : ℚ) / 67108864)), (((8304657 : ℚ) / 67108864), ((4991189 : ℚ) / 33554432)), (((4991189 : ℚ) / 33554432), ((3334455 : ℚ) / 16777216)), (((3334455 : ℚ) / 16777216), ((313261 : ℚ) / 1048576)), (((313261 : ℚ) / 1048576), ((6689897 : ℚ) / 16777216)), (((6689897 : ℚ) / 16777216), ((4183809 : ℚ) / 8388608)), (((4183809 : ℚ) / 8388608), ((18412957 : ℚ) / 33554432)), (((18412957 : ℚ) / 33554432), ((38503635 : ℚ) / 67108864)), (((38503635 : ℚ) / 67108864), ((78684991 : ℚ) / 134217728)), (((78684991 : ℚ) / 134217728), ((10045339 : ℚ) / 16777216)), (((10045339 : ℚ) / 16777216), ((162403145 : ℚ) / 268435456)), (((162403145 : ℚ) / 268435456), ((82040433 : ℚ) / 134217728)), (((82040433 : ℚ) / 134217728), ((165758587 : ℚ) / 268435456)), (((165758587 : ℚ) / 268435456), ((41859077 : ℚ) / 67108864)), (((41859077 : ℚ) / 67108864), ((21768399 : ℚ) / 33554432)), (((21768399 : ℚ) / 33554432), ((2930765 : ℚ) / 4194304)), (((2930765 : ℚ) / 4194304), ((13400781 : ℚ) / 16777216)), (((13400781 : ℚ) / 16777216), ((7539251 : ℚ) / 8388608)), (((7539251 : ℚ) / 8388608), ((31834725 : ℚ) / 33554432)), (((31834725 : ℚ) / 33554432), ((16756223 : ℚ) / 16777216)), (((16756223 : ℚ) / 16777216), ((8380219 : ℚ) / 8388608)), (((8380219 : ℚ) / 8388608), ((999 : ℚ) / 1000))]
theorem corner1Domain0Cover : pieceCover ((999 : ℚ) / 1000) ((98749 : ℚ) / 1000000) corner1Domain0Pieces = true := by decide +kernel
theorem corner1Domain0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  apply pieceCover_bound ((999 : ℚ) / 1000) (fun x : ℝ => fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x) ((((-136433133353 : ℚ) / 137438953472) : ℚ) : ℝ) ((98749 : ℚ) / 1000000) corner1Domain0Pieces (by decide +kernel) corner1Domain0Cover
  intro p hp
  simp only [corner1Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
#print axioms corner1Domain0Cover
#print axioms corner1Domain0
theorem delta2Check : fieldNFCheck D72.NearCorners000.delta2 (fqSum [logFQ ((1 : ℚ) / 4400) ((-1 : ℚ) / 1), logFQ ((-1 : ℚ) / 440) ((1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta2Value (x : ℝ) : fval D72.NearCorners000.delta2 x = ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta2Check x
  change fval D72.NearCorners000.delta2 x = fval (fqSum [logFQ ((1 : ℚ) / 4400) ((-1 : ℚ) / 1), logFQ ((-1 : ℚ) / 440) ((1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner2Identity (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x = (fval D72.NearBinding000.literalField x + lfieldTower D72.NearBinding000.literalTerms 0 x) + (((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  rw [D72.NearCorners000.corner2Value, delta2Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) x, D72.NearCorners000.corner2Terms, laurentNF_sound, ← D72.NearBinding000.termsValue x]
  ring
theorem corner2Piece0 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((828367 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer1Lo : ℝ) (d2WiderTransfer1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer1Lo, d2WiderTransfer1Hi, d2LitsNearWiderTransfers000.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer1Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer1Cap, d2LitsNearWiderTransfers000.q2, d2WiderTransfer1C0, d2WiderTransfer1S0, d2WiderTransfer1C1, d2WiderTransfer1S1] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece1 (x : ℝ) (hx : x ∈ Icc ((((828367 : ℚ) / 8388608) : ℚ) : ℝ) ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer3Lo : ℝ) (d2WiderTransfer3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer3Lo, d2WiderTransfer3Hi, d2LitsNearWiderTransfers000.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer3Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer3Cap, d2LitsNearWiderTransfers000.q2, d2WiderTransfer3C0, d2WiderTransfer3S0, d2WiderTransfer3C1, d2WiderTransfer3S1] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece2 (x : ℝ) (hx : x ∈ Icc ((((8304657 : ℚ) / 67108864) : ℚ) : ℝ) ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer5Lo : ℝ) (d2WiderTransfer5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer5Lo, d2WiderTransfer5Hi, d2LitsNearWiderTransfers000.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer5Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer5Cap, d2LitsNearWiderTransfers000.q2, d2WiderTransfer5C0, d2WiderTransfer5S0, d2WiderTransfer5C1, d2WiderTransfer5S1] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece3 (x : ℝ) (hx : x ∈ Icc ((((4991189 : ℚ) / 33554432) : ℚ) : ℝ) ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer7Lo : ℝ) (d2WiderTransfer7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer7Lo, d2WiderTransfer7Hi, d2LitsNearWiderTransfers000.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer7Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer7Cap, d2LitsNearWiderTransfers000.q2, d2WiderTransfer7C0, d2WiderTransfer7S0, d2WiderTransfer7C1, d2WiderTransfer7S1] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece4 (x : ℝ) (hx : x ∈ Icc ((((3334455 : ℚ) / 16777216) : ℚ) : ℝ) ((((313261 : ℚ) / 1048576) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer9Lo : ℝ) (d2WiderTransfer9Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer9Lo, d2WiderTransfer9Hi, d2LitsNearWiderTransfers001.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer9Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer9Cap, d2LitsNearWiderTransfers001.q2, d2WiderTransfer9C0, d2WiderTransfer9S0, d2WiderTransfer9C1, d2WiderTransfer9S1] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece5 (x : ℝ) (hx : x ∈ Icc ((((313261 : ℚ) / 1048576) : ℚ) : ℝ) ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer11Lo : ℝ) (d2WiderTransfer11Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer11Lo, d2WiderTransfer11Hi, d2LitsNearWiderTransfers001.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer11Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer11Cap, d2LitsNearWiderTransfers001.q2, d2WiderTransfer11C0, d2WiderTransfer11S0, d2WiderTransfer11C1, d2WiderTransfer11S1] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece6 (x : ℝ) (hx : x ∈ Icc ((((6689897 : ℚ) / 16777216) : ℚ) : ℝ) ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer13Lo : ℝ) (d2WiderTransfer13Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer13Lo, d2WiderTransfer13Hi, d2LitsNearWiderTransfers001.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer13Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer13Cap, d2LitsNearWiderTransfers001.q2, d2WiderTransfer13C0, d2WiderTransfer13S0, d2WiderTransfer13C1, d2WiderTransfer13S1] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece7 (x : ℝ) (hx : x ∈ Icc ((((4183809 : ℚ) / 8388608) : ℚ) : ℝ) ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer15Lo : ℝ) (d2WiderTransfer15Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer15Lo, d2WiderTransfer15Hi, d2LitsNearWiderTransfers001.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer15Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer15Cap, d2LitsNearWiderTransfers001.q2, d2WiderTransfer15C0, d2WiderTransfer15S0, d2WiderTransfer15C1, d2WiderTransfer15S1] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece8 (x : ℝ) (hx : x ∈ Icc ((((18412957 : ℚ) / 33554432) : ℚ) : ℝ) ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer17Lo : ℝ) (d2WiderTransfer17Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer17Lo, d2WiderTransfer17Hi, d2LitsNearWiderTransfers002.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer17Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer17Cap, d2LitsNearWiderTransfers002.q2, d2WiderTransfer17C0, d2WiderTransfer17S0, d2WiderTransfer17C1, d2WiderTransfer17S1] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece9 (x : ℝ) (hx : x ∈ Icc ((((38503635 : ℚ) / 67108864) : ℚ) : ℝ) ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope9 x hx
  have hxT : x ∈ Icc (d2WiderTransfer19Lo : ℝ) (d2WiderTransfer19Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer19Lo, d2WiderTransfer19Hi, d2LitsNearWiderTransfers002.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer19Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer19Cap, d2LitsNearWiderTransfers002.q2, d2WiderTransfer19C0, d2WiderTransfer19S0, d2WiderTransfer19C1, d2WiderTransfer19S1] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece10 (x : ℝ) (hx : x ∈ Icc ((((78684991 : ℚ) / 134217728) : ℚ) : ℝ) ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope10 x hx
  have hxT : x ∈ Icc (d2WiderTransfer21Lo : ℝ) (d2WiderTransfer21Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer21Lo, d2WiderTransfer21Hi, d2LitsNearWiderTransfers002.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer21Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer21Cap, d2LitsNearWiderTransfers002.q2, d2WiderTransfer21C0, d2WiderTransfer21S0, d2WiderTransfer21C1, d2WiderTransfer21S1] using hD
  have hcap : ((((-546381427469 : ℚ) / 549755813888) : ℚ) : ℝ) + ((((2432512853 : ℚ) / 1099511627776) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece11 (x : ℝ) (hx : x ∈ Icc ((((10045339 : ℚ) / 16777216) : ℚ) : ℝ) ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope11 x hx
  have hxT : x ∈ Icc (d2WiderTransfer23Lo : ℝ) (d2WiderTransfer23Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer23Lo, d2WiderTransfer23Hi, d2LitsNearWiderTransfers002.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer23Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((670527226037072262575 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer23Cap, d2LitsNearWiderTransfers002.q2, d2WiderTransfer23C0, d2WiderTransfer23S0, d2WiderTransfer23C1, d2WiderTransfer23S1] using hD
  have hcap : ((((-300378249535897389200815 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((670527226037072262575 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece12 (x : ℝ) (hx : x ∈ Icc ((((162403145 : ℚ) / 268435456) : ℚ) : ℝ) ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope12 x hx
  have hxT : x ∈ Icc (d2WiderTransfer25Lo : ℝ) (d2WiderTransfer25Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer25Lo, d2WiderTransfer25Hi, d2LitsNearWiderTransfers003.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer25Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2726998246650988934839 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer25Cap, d2LitsNearWiderTransfers003.q2, d2WiderTransfer25C0, d2WiderTransfer25S0, d2WiderTransfer25C1, d2WiderTransfer25S1] using hD
  have hcap : ((((-1201557887486092256687799 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2726998246650988934839 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece13 (x : ℝ) (hx : x ∈ Icc ((((82040433 : ℚ) / 134217728) : ℚ) : ℝ) ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope13 x hx
  have hxT : x ∈ Icc (d2WiderTransfer27Lo : ℝ) (d2WiderTransfer27Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer27Lo, d2WiderTransfer27Hi, d2LitsNearWiderTransfers003.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer27Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((173287107405478597877 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer27Cap, d2LitsNearWiderTransfers003.q2, d2WiderTransfer27C0, d2WiderTransfer27S0, d2WiderTransfer27C1, d2WiderTransfer27S1] using hD
  have hcap : ((((-75100217684870557832437 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) + ((((173287107405478597877 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece14 (x : ℝ) (hx : x ∈ Icc ((((165758587 : ℚ) / 268435456) : ℚ) : ℝ) ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope14 x hx
  have hxT : x ∈ Icc (d2WiderTransfer29Lo : ℝ) (d2WiderTransfer29Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer29Lo, d2WiderTransfer29Hi, d2LitsNearWiderTransfers003.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer29Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1409459377724792570767 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer29Cap, d2LitsNearWiderTransfers003.q2, d2WiderTransfer29C0, d2WiderTransfer29S0, d2WiderTransfer29C1, d2WiderTransfer29S1] using hD
  have hcap : ((((-600824903997445426447247 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1409459377724792570767 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece15 (x : ℝ) (hx : x ∈ Icc ((((41859077 : ℚ) / 67108864) : ℚ) : ℝ) ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope15 x hx
  have hxT : x ∈ Icc (d2WiderTransfer31Lo : ℝ) (d2WiderTransfer31Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer31Lo, d2WiderTransfer31Hi, d2LitsNearWiderTransfers003.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer31Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3012026156565297427425 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer31Cap, d2LitsNearWiderTransfers003.q2, d2WiderTransfer31C0, d2WiderTransfer31S0, d2WiderTransfer31C1, d2WiderTransfer31S1] using hD
  have hcap : ((((-1201842915396006565180385 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((3012026156565297427425 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece16 (x : ℝ) (hx : x ∈ Icc ((((21768399 : ℚ) / 33554432) : ℚ) : ℝ) ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope16 x hx
  have hxT : x ∈ Icc (d2WiderTransfer33Lo : ℝ) (d2WiderTransfer33Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer33Lo, d2WiderTransfer33Hi, d2LitsNearWiderTransfers004.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer33Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3442141790077976831433 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer33Cap, d2LitsNearWiderTransfers004.q2, d2WiderTransfer33C0, d2WiderTransfer33S0, d2WiderTransfer33C1, d2WiderTransfer33S1] using hD
  have hcap : ((((-1202273031029519244584393 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((3442141790077976831433 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece17 (x : ℝ) (hx : x ∈ Icc ((((2930765 : ℚ) / 4194304) : ℚ) : ℝ) ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope17 x hx
  have hxT : x ∈ Icc (d2WiderTransfer35Lo : ℝ) (d2WiderTransfer35Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer35Lo, d2WiderTransfer35Hi, d2LitsNearWiderTransfers004.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer35Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4566196585646166842057 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer35Cap, d2LitsNearWiderTransfers004.q2, d2WiderTransfer35C0, d2WiderTransfer35S0, d2WiderTransfer35C1, d2WiderTransfer35S1] using hD
  have hcap : ((((-1203397085825087434595017 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((4566196585646166842057 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece18 (x : ℝ) (hx : x ∈ Icc ((((13400781 : ℚ) / 16777216) : ℚ) : ℝ) ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope18 x hx
  have hxT : x ∈ Icc (d2WiderTransfer37Lo : ℝ) (d2WiderTransfer37Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer37Lo, d2WiderTransfer37Hi, d2LitsNearWiderTransfers004.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer37Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1617123601907740190691 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer37Cap, d2LitsNearWiderTransfers004.q2, d2WiderTransfer37C0, d2WiderTransfer37S0, d2WiderTransfer37C1, d2WiderTransfer37S1] using hD
  have hcap : ((((-301324845911768057128931 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((1617123601907740190691 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece19 (x : ℝ) (hx : x ∈ Icc ((((7539251 : ℚ) / 8388608) : ℚ) : ℝ) ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope19 x hx
  have hxT : x ∈ Icc (d2WiderTransfer39Lo : ℝ) (d2WiderTransfer39Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer39Lo, d2WiderTransfer39Hi, d2LitsNearWiderTransfers004.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer39Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((130411747060963873599 : ℚ) / 18889465931478580854784) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer39Cap, d2LitsNearWiderTransfers004.q2, d2WiderTransfer39C0, d2WiderTransfer39S0, d2WiderTransfer39C1, d2WiderTransfer39S1] using hD
  have hcap : ((((-18862144391427233682239 : ℚ) / 18889465931478580854784) : ℚ) : ℝ) + ((((130411747060963873599 : ℚ) / 18889465931478580854784) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece20 (x : ℝ) (hx : x ∈ Icc ((((31834725 : ℚ) / 33554432) : ℚ) : ℝ) ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope20 x hx
  have hxT : x ∈ Icc (d2WiderTransfer41Lo : ℝ) (d2WiderTransfer41Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer41Lo, d2WiderTransfer41Hi, d2LitsNearWiderTransfers005.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer41Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((18553824547935338072189 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer41Cap, d2LitsNearWiderTransfers005.q2, d2WiderTransfer41C0, d2WiderTransfer41S0, d2WiderTransfer41C1, d2WiderTransfer41S1] using hD
  have hcap : ((((-1217384713787376605825149 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((18553824547935338072189 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece21 (x : ℝ) (hx : x ∈ Icc ((((16756223 : ℚ) / 16777216) : ℚ) : ℝ) ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope21 x hx
  have hxT : x ∈ Icc (d2WiderTransfer43Lo : ℝ) (d2WiderTransfer43Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer43Lo, d2WiderTransfer43Hi, d2LitsNearWiderTransfers005.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer43Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4792410857165054042153 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer43Cap, d2LitsNearWiderTransfers005.q2, d2WiderTransfer43C0, d2WiderTransfer43S0, d2WiderTransfer43C1, d2WiderTransfer43S1] using hD
  have hcap : ((((-304500133167025370980393 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((4792410857165054042153 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece22 (x : ℝ) (hx : x ∈ Icc ((((8380219 : ℚ) / 8388608) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ)) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope22 x hx
  have hxT : x ∈ Icc (d2WiderTransfer45Lo : ℝ) (d2WiderTransfer45Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer45Lo, d2WiderTransfer45Hi, d2LitsNearWiderTransfers005.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer45Bound x hxT
  have hd : ((((1 : ℚ) / 4400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| + ((((-1 : ℚ) / 440) : ℚ) : ℝ) * Real.log |x - ((((1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((19169771825614475034297 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer45Cap, d2LitsNearWiderTransfers005.q2, d2WiderTransfer45C0, d2WiderTransfer45S0, d2WiderTransfer45C1, d2WiderTransfer45S1] using hD
  have hcap : ((((-1218000661065055742787257 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((19169771825614475034297 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner2Domain0Pieces : List (ℚ × ℚ) := [(((98749 : ℚ) / 1000000), ((828367 : ℚ) / 8388608)), (((828367 : ℚ) / 8388608), ((8304657 : ℚ) / 67108864)), (((8304657 : ℚ) / 67108864), ((4991189 : ℚ) / 33554432)), (((4991189 : ℚ) / 33554432), ((3334455 : ℚ) / 16777216)), (((3334455 : ℚ) / 16777216), ((313261 : ℚ) / 1048576)), (((313261 : ℚ) / 1048576), ((6689897 : ℚ) / 16777216)), (((6689897 : ℚ) / 16777216), ((4183809 : ℚ) / 8388608)), (((4183809 : ℚ) / 8388608), ((18412957 : ℚ) / 33554432)), (((18412957 : ℚ) / 33554432), ((38503635 : ℚ) / 67108864)), (((38503635 : ℚ) / 67108864), ((78684991 : ℚ) / 134217728)), (((78684991 : ℚ) / 134217728), ((10045339 : ℚ) / 16777216)), (((10045339 : ℚ) / 16777216), ((162403145 : ℚ) / 268435456)), (((162403145 : ℚ) / 268435456), ((82040433 : ℚ) / 134217728)), (((82040433 : ℚ) / 134217728), ((165758587 : ℚ) / 268435456)), (((165758587 : ℚ) / 268435456), ((41859077 : ℚ) / 67108864)), (((41859077 : ℚ) / 67108864), ((21768399 : ℚ) / 33554432)), (((21768399 : ℚ) / 33554432), ((2930765 : ℚ) / 4194304)), (((2930765 : ℚ) / 4194304), ((13400781 : ℚ) / 16777216)), (((13400781 : ℚ) / 16777216), ((7539251 : ℚ) / 8388608)), (((7539251 : ℚ) / 8388608), ((31834725 : ℚ) / 33554432)), (((31834725 : ℚ) / 33554432), ((16756223 : ℚ) / 16777216)), (((16756223 : ℚ) / 16777216), ((8380219 : ℚ) / 8388608)), (((8380219 : ℚ) / 8388608), ((999 : ℚ) / 1000))]
theorem corner2Domain0Cover : pieceCover ((999 : ℚ) / 1000) ((98749 : ℚ) / 1000000) corner2Domain0Pieces = true := by decide +kernel
theorem corner2Domain0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  apply pieceCover_bound ((999 : ℚ) / 1000) (fun x : ℝ => fval (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x) ((((-1090330342085 : ℚ) / 1099511627776) : ℚ) : ℝ) ((98749 : ℚ) / 1000000) corner2Domain0Pieces (by decide +kernel) corner2Domain0Cover
  intro p hp
  simp only [corner2Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
#print axioms corner2Domain0Cover
#print axioms corner2Domain0
end D72.NearCornerCover000
end CatalanMeasure.GenD.Signed.Data.Cells
