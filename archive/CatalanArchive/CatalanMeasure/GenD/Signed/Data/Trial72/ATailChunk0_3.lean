module

public import CatalanMeasure.GenD.Signed.Data.Trial72.TailChunk
public import CatalanMeasure.GenD.Signed.Data.Trial72.ATailChunkData0

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.ATailChunk0_3
open CatalanMeasure.Cert.Iv CatalanMeasure.CellCert
open CatalanMeasure.GenD.Signed.Data.Trial72 CatalanMeasure.GenD.Signed.Data.Trial
noncomputable section

open ATailChunkData0
theorem checked : TailChunk.chunk poles 250 state3 = (part3, state4) := by
  -- kcost: 3.6 s transferred from C25, 5000 exact fixed-scale pole updates.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.ATailChunk0_3
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.ATailChunk0_3.checked
