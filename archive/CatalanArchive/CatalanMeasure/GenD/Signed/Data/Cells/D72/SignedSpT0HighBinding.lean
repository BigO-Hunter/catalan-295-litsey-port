module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0End01
public import CatalanMeasure.GenD.Signed.Data.Trial72.T0Fields
public import CatalanMeasure.GenD.Signed.Data.Assembly.RowsCell

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0LowBinding

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Endpoints
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

abbrev oneC : ℚ := endC ceSignedSpT0End01FullFq ceSignedSpT0End01FullTs ceSignedSpT0End01Site
theorem highFieldCheck : fieldNFCheck ceSignedSpT0End01FullFq CatalanMeasure.GenD.Signed.Data.Trial72.T0.spFq = true := by decide +kernel
theorem highTermsCheck : laurentNF ceSignedSpT0End01FullTs = laurentNF terms := by decide +kernel

#print axioms highFieldCheck
#print axioms highTermsCheck
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Endpoints
