module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1End01
public import CatalanMeasure.GenD.Signed.Data.Trial72.T1Fields
public import CatalanMeasure.GenD.Signed.Data.Assembly.RowsCell

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1LowBinding

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Endpoints
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

abbrev oneC : ℚ := endC ceSignedSpT1End01FullFq ceSignedSpT1End01FullTs ceSignedSpT1End01Site
theorem highFieldCheck : fieldNFCheck ceSignedSpT1End01FullFq CatalanMeasure.GenD.Signed.Data.Trial72.T1.spFq = true := by decide +kernel
theorem highTermsCheck : laurentNF ceSignedSpT1End01FullTs = laurentNF terms := by decide +kernel

#print axioms highFieldCheck
#print axioms highTermsCheck
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Endpoints
