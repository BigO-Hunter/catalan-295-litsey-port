module
public import Submission.CatalanMeasure.FirstStrongTrial.Data
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem tailsP : tailsInDisk P = true := by decide +kernel
theorem tailsV : tailsInDisk V = true := by decide +kernel
end CatalanMeasure.FirstStrongTrial
