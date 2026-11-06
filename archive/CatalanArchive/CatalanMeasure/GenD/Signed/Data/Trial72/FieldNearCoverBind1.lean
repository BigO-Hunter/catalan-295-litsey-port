module
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCorners1
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearCornerCover001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearCornerCover004
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCoverBind1
open CatalanMeasure.GenD.Signed.Data.Cells
theorem cover : FieldNearCorners1.Covers where
  off0 := D72.NearCornerCover001.corner0Domain0
  top0 := D72.NearCornerCover004.corner0Domain0
  jump0 := D72.NearCornerCover004.corner0Domain1
  off1 := D72.NearCornerCover001.corner1Domain0
  top1 := D72.NearCornerCover004.corner1Domain0
  jump1 := D72.NearCornerCover004.corner1Domain1
  off2 := D72.NearCornerCover001.corner2Domain0
  top2 := D72.NearCornerCover004.corner2Domain0
  jump2 := D72.NearCornerCover004.corner2Domain1
  off3 := D72.NearCornerCover001.corner3Domain0
  top3 := D72.NearCornerCover004.corner3Domain0
  jump3 := D72.NearCornerCover004.corner3Domain1
  off4 := D72.NearCornerCover001.corner4Domain0
  top4 := D72.NearCornerCover004.corner4Domain0
  jump4 := D72.NearCornerCover004.corner4Domain1
#print axioms cover
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCoverBind1
