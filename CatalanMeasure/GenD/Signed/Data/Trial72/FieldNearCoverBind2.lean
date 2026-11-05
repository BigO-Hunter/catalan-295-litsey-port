module
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCorners2
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearCornerCover002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearCornerCover005
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCoverBind2
open CatalanMeasure.GenD.Signed.Data.Cells
theorem cover : FieldNearCorners2.Covers where
  off0 := D72.NearCornerCover002.corner0Domain0
  top0 := D72.NearCornerCover005.corner0Domain0
  jump0 := D72.NearCornerCover005.corner0Domain1
  off1 := D72.NearCornerCover002.corner1Domain0
  top1 := D72.NearCornerCover005.corner1Domain0
  jump1 := D72.NearCornerCover005.corner1Domain1
  off2 := D72.NearCornerCover002.corner2Domain0
  top2 := D72.NearCornerCover005.corner2Domain0
  jump2 := D72.NearCornerCover005.corner2Domain1
  off3 := D72.NearCornerCover002.corner3Domain0
  top3 := D72.NearCornerCover005.corner3Domain0
  jump3 := D72.NearCornerCover005.corner3Domain1
#print axioms cover
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCoverBind2
