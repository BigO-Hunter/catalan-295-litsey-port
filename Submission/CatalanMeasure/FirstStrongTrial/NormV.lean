module
public import Submission.CatalanMeasure.FirstStrongTrial.Data
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem hNV : normOK Vc V NV = true := by decide +kernel
end CatalanMeasure.FirstStrongTrial
