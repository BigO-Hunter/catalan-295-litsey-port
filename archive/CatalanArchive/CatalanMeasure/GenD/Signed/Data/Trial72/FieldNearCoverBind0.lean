module
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCorners0
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearCornerCover000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearCornerCover003
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCoverBind0
open CatalanMeasure.GenD.Signed.Data.Cells
theorem cover : FieldNearCorners0.Covers where
  off0 := D72.NearCornerCover000.corner0Domain0
  top0 := D72.NearCornerCover003.corner0Domain0
  jump0 := D72.NearCornerCover003.corner0Domain1
  off1 := D72.NearCornerCover000.corner1Domain0
  top1 := D72.NearCornerCover003.corner1Domain0
  jump1 := D72.NearCornerCover003.corner1Domain1
  off2 := D72.NearCornerCover000.corner2Domain0
  top2 := D72.NearCornerCover003.corner2Domain0
  jump2 := D72.NearCornerCover003.corner2Domain1
#print axioms cover
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCoverBind0
